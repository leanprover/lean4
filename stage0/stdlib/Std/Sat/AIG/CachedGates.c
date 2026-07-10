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
uint8_t lean_bool_xor(uint8_t, uint8_t);
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
lean_object* v_gate_3_; uint8_t v_invert_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_14_; 
v_gate_3_ = lean_ctor_get(v_gate_2_, 0);
v_invert_4_ = lean_ctor_get_uint8(v_gate_2_, sizeof(void*)*1);
v_isSharedCheck_14_ = !lean_is_exclusive(v_gate_2_);
if (v_isSharedCheck_14_ == 0)
{
v___x_6_ = v_gate_2_;
v_isShared_7_ = v_isSharedCheck_14_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_gate_3_);
lean_dec(v_gate_2_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_14_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
uint8_t v___x_8_; uint8_t v___x_9_; lean_object* v___x_11_; 
v___x_8_ = 1;
v___x_9_ = lean_bool_xor(v___x_8_, v_invert_4_);
if (v_isShared_7_ == 0)
{
v___x_11_ = v___x_6_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_gate_3_);
v___x_11_ = v_reuseFailAlloc_13_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
lean_object* v___x_12_; 
lean_ctor_set_uint8(v___x_11_, sizeof(void*)*1, v___x_9_);
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v_aig_1_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
return v___x_12_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_aig_18_, lean_object* v_gate_19_){
_start:
{
lean_object* v_gate_20_; uint8_t v_invert_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_31_; 
v_gate_20_ = lean_ctor_get(v_gate_19_, 0);
v_invert_21_ = lean_ctor_get_uint8(v_gate_19_, sizeof(void*)*1);
v_isSharedCheck_31_ = !lean_is_exclusive(v_gate_19_);
if (v_isSharedCheck_31_ == 0)
{
v___x_23_ = v_gate_19_;
v_isShared_24_ = v_isSharedCheck_31_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_gate_20_);
lean_dec(v_gate_19_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_31_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
uint8_t v___x_25_; uint8_t v___x_26_; lean_object* v___x_28_; 
v___x_25_ = 1;
v___x_26_ = lean_bool_xor(v___x_25_, v_invert_21_);
if (v_isShared_24_ == 0)
{
v___x_28_ = v___x_23_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_gate_20_);
v___x_28_ = v_reuseFailAlloc_30_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_29_; 
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*1, v___x_26_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v_aig_18_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
return v___x_29_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___boxed(lean_object* v_00_u03b1_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_aig_35_, lean_object* v_gate_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Sat_AIG_mkNotCached(v_00_u03b1_32_, v_inst_33_, v_inst_34_, v_aig_35_, v_gate_36_);
lean_dec_ref(v_inst_34_);
lean_dec_ref(v_inst_33_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached___redArg(lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_aig_40_, lean_object* v_input_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_38_, v_inst_39_, v_aig_40_, v_input_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached(lean_object* v_00_u03b1_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_aig_46_, lean_object* v_input_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_44_, v_inst_45_, v_aig_46_, v_input_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___redArg(lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_aig_51_, lean_object* v_input_52_){
_start:
{
lean_object* v_lhs_53_; lean_object* v_rhs_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_102_; 
v_lhs_53_ = lean_ctor_get(v_input_52_, 0);
v_rhs_54_ = lean_ctor_get(v_input_52_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v_input_52_);
if (v_isSharedCheck_102_ == 0)
{
v___x_56_ = v_input_52_;
v_isShared_57_ = v_isSharedCheck_102_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_rhs_54_);
lean_inc(v_lhs_53_);
lean_dec(v_input_52_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_102_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v_gate_58_; uint8_t v_invert_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_101_; 
v_gate_58_ = lean_ctor_get(v_lhs_53_, 0);
v_invert_59_ = lean_ctor_get_uint8(v_lhs_53_, sizeof(void*)*1);
v_isSharedCheck_101_ = !lean_is_exclusive(v_lhs_53_);
if (v_isSharedCheck_101_ == 0)
{
v___x_61_ = v_lhs_53_;
v_isShared_62_ = v_isSharedCheck_101_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_gate_58_);
lean_dec(v_lhs_53_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_101_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v_gate_63_; uint8_t v_invert_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_100_; 
v_gate_63_ = lean_ctor_get(v_rhs_54_, 0);
v_invert_64_ = lean_ctor_get_uint8(v_rhs_54_, sizeof(void*)*1);
v_isSharedCheck_100_ = !lean_is_exclusive(v_rhs_54_);
if (v_isSharedCheck_100_ == 0)
{
v___x_66_ = v_rhs_54_;
v_isShared_67_ = v_isSharedCheck_100_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_gate_63_);
lean_dec(v_rhs_54_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_100_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
uint8_t v___x_68_; uint8_t v___x_69_; lean_object* v___x_71_; 
v___x_68_ = 1;
v___x_69_ = lean_bool_xor(v___x_68_, v_invert_59_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 0, v_gate_58_);
v___x_71_ = v___x_66_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_gate_58_);
v___x_71_ = v_reuseFailAlloc_99_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
uint8_t v___x_72_; lean_object* v___x_74_; 
lean_ctor_set_uint8(v___x_71_, sizeof(void*)*1, v___x_69_);
v___x_72_ = lean_bool_xor(v___x_68_, v_invert_64_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v_gate_63_);
v___x_74_ = v___x_61_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_gate_63_);
v___x_74_ = v_reuseFailAlloc_98_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
lean_object* v___x_76_; 
lean_ctor_set_uint8(v___x_74_, sizeof(void*)*1, v___x_72_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 1, v___x_74_);
lean_ctor_set(v___x_56_, 0, v___x_71_);
v___x_76_ = v___x_56_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_71_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v___x_74_);
v___x_76_ = v_reuseFailAlloc_97_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v_res_77_; lean_object* v_ref_78_; lean_object* v_aig_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_96_; 
v_res_77_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_49_, v_inst_50_, v_aig_51_, v___x_76_);
v_ref_78_ = lean_ctor_get(v_res_77_, 1);
v_aig_79_ = lean_ctor_get(v_res_77_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v_res_77_);
if (v_isSharedCheck_96_ == 0)
{
v___x_81_ = v_res_77_;
v_isShared_82_ = v_isSharedCheck_96_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_ref_78_);
lean_inc(v_aig_79_);
lean_dec(v_res_77_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_96_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v_gate_83_; uint8_t v_invert_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_95_; 
v_gate_83_ = lean_ctor_get(v_ref_78_, 0);
v_invert_84_ = lean_ctor_get_uint8(v_ref_78_, sizeof(void*)*1);
v_isSharedCheck_95_ = !lean_is_exclusive(v_ref_78_);
if (v_isSharedCheck_95_ == 0)
{
v___x_86_ = v_ref_78_;
v_isShared_87_ = v_isSharedCheck_95_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_gate_83_);
lean_dec(v_ref_78_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_95_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
uint8_t v___x_88_; lean_object* v___x_90_; 
v___x_88_ = lean_bool_xor(v___x_68_, v_invert_84_);
if (v_isShared_87_ == 0)
{
v___x_90_ = v___x_86_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_gate_83_);
v___x_90_ = v_reuseFailAlloc_94_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_92_; 
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*1, v___x_88_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v___x_90_);
v___x_92_ = v___x_81_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_aig_79_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached(lean_object* v_00_u03b1_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_aig_106_, lean_object* v_input_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Std_Sat_AIG_mkOrCached___redArg(v_inst_104_, v_inst_105_, v_aig_106_, v_input_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___redArg(lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_aig_111_, lean_object* v_input_112_){
_start:
{
lean_object* v_res_113_; lean_object* v_lhs_114_; lean_object* v_rhs_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_176_; 
lean_inc_ref(v_input_112_);
lean_inc_ref(v_inst_110_);
lean_inc_ref(v_inst_109_);
v_res_113_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_109_, v_inst_110_, v_aig_111_, v_input_112_);
v_lhs_114_ = lean_ctor_get(v_input_112_, 0);
v_rhs_115_ = lean_ctor_get(v_input_112_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_input_112_);
if (v_isSharedCheck_176_ == 0)
{
v___x_117_ = v_input_112_;
v_isShared_118_ = v_isSharedCheck_176_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_rhs_115_);
lean_inc(v_lhs_114_);
lean_dec(v_input_112_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_176_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v_aig_119_; lean_object* v_ref_120_; lean_object* v_gate_121_; uint8_t v_invert_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_175_; 
v_aig_119_ = lean_ctor_get(v_res_113_, 0);
lean_inc_ref(v_aig_119_);
v_ref_120_ = lean_ctor_get(v_res_113_, 1);
lean_inc_ref(v_ref_120_);
lean_dec_ref(v_res_113_);
v_gate_121_ = lean_ctor_get(v_lhs_114_, 0);
v_invert_122_ = lean_ctor_get_uint8(v_lhs_114_, sizeof(void*)*1);
v_isSharedCheck_175_ = !lean_is_exclusive(v_lhs_114_);
if (v_isSharedCheck_175_ == 0)
{
v___x_124_ = v_lhs_114_;
v_isShared_125_ = v_isSharedCheck_175_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_gate_121_);
lean_dec(v_lhs_114_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_175_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v_gate_126_; uint8_t v_invert_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_174_; 
v_gate_126_ = lean_ctor_get(v_rhs_115_, 0);
v_invert_127_ = lean_ctor_get_uint8(v_rhs_115_, sizeof(void*)*1);
v_isSharedCheck_174_ = !lean_is_exclusive(v_rhs_115_);
if (v_isSharedCheck_174_ == 0)
{
v___x_129_ = v_rhs_115_;
v_isShared_130_ = v_isSharedCheck_174_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_gate_126_);
lean_dec(v_rhs_115_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_174_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
uint8_t v___x_131_; uint8_t v___x_132_; lean_object* v___x_134_; 
v___x_131_ = 1;
v___x_132_ = lean_bool_xor(v___x_131_, v_invert_122_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v_gate_121_);
v___x_134_ = v___x_129_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_gate_121_);
v___x_134_ = v_reuseFailAlloc_173_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
uint8_t v___x_135_; lean_object* v___x_137_; 
lean_ctor_set_uint8(v___x_134_, sizeof(void*)*1, v___x_132_);
v___x_135_ = lean_bool_xor(v___x_131_, v_invert_127_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v_gate_126_);
v___x_137_ = v___x_124_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_gate_126_);
v___x_137_ = v_reuseFailAlloc_172_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_139_; 
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*1, v___x_135_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___x_137_);
lean_ctor_set(v___x_117_, 0, v___x_134_);
v___x_139_ = v___x_117_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_137_);
v___x_139_ = v_reuseFailAlloc_171_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v_res_140_; lean_object* v_ref_141_; lean_object* v_aig_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_170_; 
lean_inc_ref(v_inst_110_);
lean_inc_ref(v_inst_109_);
v_res_140_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_109_, v_inst_110_, v_aig_119_, v___x_139_);
v_ref_141_ = lean_ctor_get(v_res_140_, 1);
v_aig_142_ = lean_ctor_get(v_res_140_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v_res_140_);
if (v_isSharedCheck_170_ == 0)
{
v___x_144_ = v_res_140_;
v_isShared_145_ = v_isSharedCheck_170_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_ref_141_);
lean_inc(v_aig_142_);
lean_dec(v_res_140_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_170_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v_gate_146_; uint8_t v_invert_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_169_; 
v_gate_146_ = lean_ctor_get(v_ref_120_, 0);
v_invert_147_ = lean_ctor_get_uint8(v_ref_120_, sizeof(void*)*1);
v_isSharedCheck_169_ = !lean_is_exclusive(v_ref_120_);
if (v_isSharedCheck_169_ == 0)
{
v___x_149_ = v_ref_120_;
v_isShared_150_ = v_isSharedCheck_169_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_gate_146_);
lean_dec(v_ref_120_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_169_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v_gate_151_; uint8_t v_invert_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_168_; 
v_gate_151_ = lean_ctor_get(v_ref_141_, 0);
v_invert_152_ = lean_ctor_get_uint8(v_ref_141_, sizeof(void*)*1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_ref_141_);
if (v_isSharedCheck_168_ == 0)
{
v___x_154_ = v_ref_141_;
v_isShared_155_ = v_isSharedCheck_168_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_gate_151_);
lean_dec(v_ref_141_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_168_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
uint8_t v___x_156_; lean_object* v___x_158_; 
v___x_156_ = lean_bool_xor(v___x_131_, v_invert_147_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v_gate_146_);
v___x_158_ = v___x_154_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_gate_146_);
v___x_158_ = v_reuseFailAlloc_167_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
uint8_t v___x_159_; lean_object* v___x_161_; 
lean_ctor_set_uint8(v___x_158_, sizeof(void*)*1, v___x_156_);
v___x_159_ = lean_bool_xor(v___x_131_, v_invert_152_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v_gate_151_);
v___x_161_ = v___x_149_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_gate_151_);
v___x_161_ = v_reuseFailAlloc_166_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_163_; 
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*1, v___x_159_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 1, v___x_161_);
lean_ctor_set(v___x_144_, 0, v___x_158_);
v___x_163_ = v___x_144_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___x_161_);
v___x_163_ = v_reuseFailAlloc_165_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_109_, v_inst_110_, v_aig_142_, v___x_163_);
return v___x_164_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached(lean_object* v_00_u03b1_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_aig_180_, lean_object* v_input_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Std_Sat_AIG_mkXorCached___redArg(v_inst_178_, v_inst_179_, v_aig_180_, v_input_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___redArg(lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_aig_185_, lean_object* v_input_186_){
_start:
{
lean_object* v_lhs_187_; lean_object* v_rhs_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_262_; 
v_lhs_187_ = lean_ctor_get(v_input_186_, 0);
v_rhs_188_ = lean_ctor_get(v_input_186_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_input_186_);
if (v_isSharedCheck_262_ == 0)
{
v___x_190_ = v_input_186_;
v_isShared_191_ = v_isSharedCheck_262_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_rhs_188_);
lean_inc(v_lhs_187_);
lean_dec(v_input_186_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_262_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v_gate_192_; uint8_t v_invert_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_261_; 
v_gate_192_ = lean_ctor_get(v_lhs_187_, 0);
v_invert_193_ = lean_ctor_get_uint8(v_lhs_187_, sizeof(void*)*1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_lhs_187_);
if (v_isSharedCheck_261_ == 0)
{
v___x_195_ = v_lhs_187_;
v_isShared_196_ = v_isSharedCheck_261_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_gate_192_);
lean_dec(v_lhs_187_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_261_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v_gate_197_; uint8_t v_invert_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_260_; 
v_gate_197_ = lean_ctor_get(v_rhs_188_, 0);
v_invert_198_ = lean_ctor_get_uint8(v_rhs_188_, sizeof(void*)*1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_rhs_188_);
if (v_isSharedCheck_260_ == 0)
{
v___x_200_ = v_rhs_188_;
v_isShared_201_ = v_isSharedCheck_260_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_gate_197_);
lean_dec(v_rhs_188_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_260_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
uint8_t v___x_202_; uint8_t v___x_203_; uint8_t v___x_204_; lean_object* v___x_206_; 
v___x_202_ = 0;
v___x_203_ = 1;
v___x_204_ = lean_bool_xor(v___x_202_, v_invert_193_);
lean_inc(v_gate_192_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v_gate_192_);
v___x_206_ = v___x_200_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_gate_192_);
v___x_206_ = v_reuseFailAlloc_259_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
uint8_t v___x_207_; lean_object* v___x_209_; 
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*1, v___x_204_);
v___x_207_ = lean_bool_xor(v___x_203_, v_invert_198_);
lean_inc(v_gate_197_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v_gate_197_);
v___x_209_ = v___x_195_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_gate_197_);
v___x_209_ = v_reuseFailAlloc_258_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_211_; 
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*1, v___x_207_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 1, v___x_209_);
lean_ctor_set(v___x_190_, 0, v___x_206_);
v___x_211_ = v___x_190_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_257_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v_res_212_; lean_object* v_aig_213_; lean_object* v_ref_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_256_; 
lean_inc_ref(v_inst_184_);
lean_inc_ref(v_inst_183_);
v_res_212_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_183_, v_inst_184_, v_aig_185_, v___x_211_);
v_aig_213_ = lean_ctor_get(v_res_212_, 0);
v_ref_214_ = lean_ctor_get(v_res_212_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v_res_212_);
if (v_isSharedCheck_256_ == 0)
{
v___x_216_ = v_res_212_;
v_isShared_217_ = v_isSharedCheck_256_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_ref_214_);
lean_inc(v_aig_213_);
lean_dec(v_res_212_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_256_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
uint8_t v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_218_ = lean_bool_xor(v___x_203_, v_invert_193_);
v___x_219_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_219_, 0, v_gate_192_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*1, v___x_218_);
v___x_220_ = lean_bool_xor(v___x_202_, v_invert_198_);
v___x_221_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_221_, 0, v_gate_197_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*1, v___x_220_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___x_221_);
lean_ctor_set(v___x_216_, 0, v___x_219_);
v___x_223_ = v___x_216_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_221_);
v___x_223_ = v_reuseFailAlloc_255_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v_res_224_; lean_object* v_ref_225_; lean_object* v_aig_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_254_; 
lean_inc_ref(v_inst_184_);
lean_inc_ref(v_inst_183_);
v_res_224_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_183_, v_inst_184_, v_aig_213_, v___x_223_);
v_ref_225_ = lean_ctor_get(v_res_224_, 1);
v_aig_226_ = lean_ctor_get(v_res_224_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v_res_224_);
if (v_isSharedCheck_254_ == 0)
{
v___x_228_ = v_res_224_;
v_isShared_229_ = v_isSharedCheck_254_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_ref_225_);
lean_inc(v_aig_226_);
lean_dec(v_res_224_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_254_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v_gate_230_; uint8_t v_invert_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_253_; 
v_gate_230_ = lean_ctor_get(v_ref_214_, 0);
v_invert_231_ = lean_ctor_get_uint8(v_ref_214_, sizeof(void*)*1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_ref_214_);
if (v_isSharedCheck_253_ == 0)
{
v___x_233_ = v_ref_214_;
v_isShared_234_ = v_isSharedCheck_253_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_gate_230_);
lean_dec(v_ref_214_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_253_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_gate_235_; uint8_t v_invert_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_252_; 
v_gate_235_ = lean_ctor_get(v_ref_225_, 0);
v_invert_236_ = lean_ctor_get_uint8(v_ref_225_, sizeof(void*)*1);
v_isSharedCheck_252_ = !lean_is_exclusive(v_ref_225_);
if (v_isSharedCheck_252_ == 0)
{
v___x_238_ = v_ref_225_;
v_isShared_239_ = v_isSharedCheck_252_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_gate_235_);
lean_dec(v_ref_225_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_252_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
uint8_t v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_bool_xor(v___x_203_, v_invert_231_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v_gate_230_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_gate_230_);
v___x_242_ = v_reuseFailAlloc_251_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
uint8_t v___x_243_; lean_object* v___x_245_; 
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*1, v___x_240_);
v___x_243_ = lean_bool_xor(v___x_203_, v_invert_236_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v_gate_235_);
v___x_245_ = v___x_233_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_gate_235_);
v___x_245_ = v_reuseFailAlloc_250_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_247_; 
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v___x_243_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v___x_245_);
lean_ctor_set(v___x_228_, 0, v___x_242_);
v___x_247_ = v___x_228_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_245_);
v___x_247_ = v_reuseFailAlloc_249_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; 
v___x_248_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_183_, v_inst_184_, v_aig_226_, v___x_247_);
return v___x_248_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached(lean_object* v_00_u03b1_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_aig_266_, lean_object* v_input_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_Sat_AIG_mkBEqCached___redArg(v_inst_264_, v_inst_265_, v_aig_266_, v_input_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached___redArg(lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_aig_271_, lean_object* v_input_272_){
_start:
{
lean_object* v_lhs_273_; lean_object* v_rhs_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_323_; 
v_lhs_273_ = lean_ctor_get(v_input_272_, 0);
v_rhs_274_ = lean_ctor_get(v_input_272_, 1);
v_isSharedCheck_323_ = !lean_is_exclusive(v_input_272_);
if (v_isSharedCheck_323_ == 0)
{
v___x_276_ = v_input_272_;
v_isShared_277_ = v_isSharedCheck_323_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_rhs_274_);
lean_inc(v_lhs_273_);
lean_dec(v_input_272_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_323_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v_gate_278_; uint8_t v_invert_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_322_; 
v_gate_278_ = lean_ctor_get(v_lhs_273_, 0);
v_invert_279_ = lean_ctor_get_uint8(v_lhs_273_, sizeof(void*)*1);
v_isSharedCheck_322_ = !lean_is_exclusive(v_lhs_273_);
if (v_isSharedCheck_322_ == 0)
{
v___x_281_ = v_lhs_273_;
v_isShared_282_ = v_isSharedCheck_322_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_gate_278_);
lean_dec(v_lhs_273_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_322_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v_gate_283_; uint8_t v_invert_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_321_; 
v_gate_283_ = lean_ctor_get(v_rhs_274_, 0);
v_invert_284_ = lean_ctor_get_uint8(v_rhs_274_, sizeof(void*)*1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_rhs_274_);
if (v_isSharedCheck_321_ == 0)
{
v___x_286_ = v_rhs_274_;
v_isShared_287_ = v_isSharedCheck_321_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_gate_283_);
lean_dec(v_rhs_274_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_321_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
uint8_t v___x_288_; uint8_t v___x_289_; uint8_t v___x_290_; lean_object* v___x_292_; 
v___x_288_ = 0;
v___x_289_ = 1;
v___x_290_ = lean_bool_xor(v___x_288_, v_invert_279_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v_gate_278_);
v___x_292_ = v___x_286_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_gate_278_);
v___x_292_ = v_reuseFailAlloc_320_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
uint8_t v___x_293_; lean_object* v___x_295_; 
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*1, v___x_290_);
v___x_293_ = lean_bool_xor(v___x_289_, v_invert_284_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v_gate_283_);
v___x_295_ = v___x_281_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_gate_283_);
v___x_295_ = v_reuseFailAlloc_319_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_297_; 
lean_ctor_set_uint8(v___x_295_, sizeof(void*)*1, v___x_293_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 1, v___x_295_);
lean_ctor_set(v___x_276_, 0, v___x_292_);
v___x_297_ = v___x_276_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_295_);
v___x_297_ = v_reuseFailAlloc_318_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v_res_298_; lean_object* v_ref_299_; lean_object* v_aig_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_317_; 
v_res_298_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_269_, v_inst_270_, v_aig_271_, v___x_297_);
v_ref_299_ = lean_ctor_get(v_res_298_, 1);
v_aig_300_ = lean_ctor_get(v_res_298_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v_res_298_);
if (v_isSharedCheck_317_ == 0)
{
v___x_302_ = v_res_298_;
v_isShared_303_ = v_isSharedCheck_317_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_ref_299_);
lean_inc(v_aig_300_);
lean_dec(v_res_298_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_317_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_gate_304_; uint8_t v_invert_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_316_; 
v_gate_304_ = lean_ctor_get(v_ref_299_, 0);
v_invert_305_ = lean_ctor_get_uint8(v_ref_299_, sizeof(void*)*1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_ref_299_);
if (v_isSharedCheck_316_ == 0)
{
v___x_307_ = v_ref_299_;
v_isShared_308_ = v_isSharedCheck_316_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_gate_304_);
lean_dec(v_ref_299_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_316_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
uint8_t v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_bool_xor(v___x_289_, v_invert_305_);
if (v_isShared_308_ == 0)
{
v___x_311_ = v___x_307_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_gate_304_);
v___x_311_ = v_reuseFailAlloc_315_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; 
lean_ctor_set_uint8(v___x_311_, sizeof(void*)*1, v___x_309_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_311_);
v___x_313_ = v___x_302_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_aig_300_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_311_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached(lean_object* v_00_u03b1_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_aig_327_, lean_object* v_input_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Std_Sat_AIG_mkImpCached___redArg(v_inst_325_, v_inst_326_, v_aig_327_, v_input_328_);
return v___x_329_;
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
