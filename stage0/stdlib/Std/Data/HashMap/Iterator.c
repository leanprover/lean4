// Lean compiler output
// Module: Std.Data.HashMap.Iterator
// Imports: public import Std.Data.DHashMap.Iterator public import Std.Data.HashMap.Basic public import Std.Data.HashMap.Raw import Init.Data.Iterators.Combinators.FilterMap
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysIter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysIter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesIter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesIter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_iter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_iter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keysIter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keysIter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keysIter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_valuesIter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_valuesIter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_valuesIter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_iter___redArg(lean_object* v_m_1_){
_start:
{
lean_object* v_buckets_2_; lean_object* v___x_4_; uint8_t v_isShared_5_; uint8_t v_isSharedCheck_12_; 
v_buckets_2_ = lean_ctor_get(v_m_1_, 1);
v_isSharedCheck_12_ = !lean_is_exclusive(v_m_1_);
if (v_isSharedCheck_12_ == 0)
{
lean_object* v_unused_13_; 
v_unused_13_ = lean_ctor_get(v_m_1_, 0);
lean_dec(v_unused_13_);
v___x_4_ = v_m_1_;
v_isShared_5_ = v_isSharedCheck_12_;
goto v_resetjp_3_;
}
else
{
lean_inc(v_buckets_2_);
lean_dec(v_m_1_);
v___x_4_ = lean_box(0);
v_isShared_5_ = v_isSharedCheck_12_;
goto v_resetjp_3_;
}
v_resetjp_3_:
{
lean_object* v___x_6_; lean_object* v___x_8_; 
v___x_6_ = lean_unsigned_to_nat(0u);
if (v_isShared_5_ == 0)
{
lean_ctor_set(v___x_4_, 1, v___x_6_);
lean_ctor_set(v___x_4_, 0, v_buckets_2_);
v___x_8_ = v___x_4_;
goto v_reusejp_7_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_11_, 0, v_buckets_2_);
lean_ctor_set(v_reuseFailAlloc_11_, 1, v___x_6_);
v___x_8_ = v_reuseFailAlloc_11_;
goto v_reusejp_7_;
}
v_reusejp_7_:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_box(0);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_8_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_iter(lean_object* v_00_u03b1_14_, lean_object* v_00_u03b2_15_, lean_object* v_m_16_){
_start:
{
lean_object* v_buckets_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_27_; 
v_buckets_17_ = lean_ctor_get(v_m_16_, 1);
v_isSharedCheck_27_ = !lean_is_exclusive(v_m_16_);
if (v_isSharedCheck_27_ == 0)
{
lean_object* v_unused_28_; 
v_unused_28_ = lean_ctor_get(v_m_16_, 0);
lean_dec(v_unused_28_);
v___x_19_ = v_m_16_;
v_isShared_20_ = v_isSharedCheck_27_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_buckets_17_);
lean_dec(v_m_16_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_27_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; lean_object* v___x_23_; 
v___x_21_ = lean_unsigned_to_nat(0u);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 1, v___x_21_);
lean_ctor_set(v___x_19_, 0, v_buckets_17_);
v___x_23_ = v___x_19_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_buckets_17_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v___x_21_);
v___x_23_ = v_reuseFailAlloc_26_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_box(0);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_23_);
lean_ctor_set(v___x_25_, 1, v___x_24_);
return v___x_25_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysIter___redArg(lean_object* v_m_29_){
_start:
{
lean_object* v_buckets_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_40_; 
v_buckets_30_ = lean_ctor_get(v_m_29_, 1);
v_isSharedCheck_40_ = !lean_is_exclusive(v_m_29_);
if (v_isSharedCheck_40_ == 0)
{
lean_object* v_unused_41_; 
v_unused_41_ = lean_ctor_get(v_m_29_, 0);
lean_dec(v_unused_41_);
v___x_32_ = v_m_29_;
v_isShared_33_ = v_isSharedCheck_40_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_buckets_30_);
lean_dec(v_m_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_40_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_34_ = lean_unsigned_to_nat(0u);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 1, v___x_34_);
lean_ctor_set(v___x_32_, 0, v_buckets_30_);
v___x_36_ = v___x_32_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_buckets_30_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v___x_34_);
v___x_36_ = v_reuseFailAlloc_39_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_box(0);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_36_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysIter(lean_object* v_00_u03b1_42_, lean_object* v_00_u03b2_43_, lean_object* v_m_44_){
_start:
{
lean_object* v_buckets_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_55_; 
v_buckets_45_ = lean_ctor_get(v_m_44_, 1);
v_isSharedCheck_55_ = !lean_is_exclusive(v_m_44_);
if (v_isSharedCheck_55_ == 0)
{
lean_object* v_unused_56_; 
v_unused_56_ = lean_ctor_get(v_m_44_, 0);
lean_dec(v_unused_56_);
v___x_47_ = v_m_44_;
v_isShared_48_ = v_isSharedCheck_55_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_buckets_45_);
lean_dec(v_m_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_55_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_51_; 
v___x_49_ = lean_unsigned_to_nat(0u);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 1, v___x_49_);
lean_ctor_set(v___x_47_, 0, v_buckets_45_);
v___x_51_ = v___x_47_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_buckets_45_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v___x_49_);
v___x_51_ = v_reuseFailAlloc_54_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_box(0);
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_51_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesIter___redArg(lean_object* v_m_57_){
_start:
{
lean_object* v_buckets_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_68_; 
v_buckets_58_ = lean_ctor_get(v_m_57_, 1);
v_isSharedCheck_68_ = !lean_is_exclusive(v_m_57_);
if (v_isSharedCheck_68_ == 0)
{
lean_object* v_unused_69_; 
v_unused_69_ = lean_ctor_get(v_m_57_, 0);
lean_dec(v_unused_69_);
v___x_60_ = v_m_57_;
v_isShared_61_ = v_isSharedCheck_68_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_buckets_58_);
lean_dec(v_m_57_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_68_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_62_ = lean_unsigned_to_nat(0u);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___x_62_);
lean_ctor_set(v___x_60_, 0, v_buckets_58_);
v___x_64_ = v___x_60_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_buckets_58_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v___x_62_);
v___x_64_ = v_reuseFailAlloc_67_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_box(0);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesIter(lean_object* v_00_u03b1_70_, lean_object* v_00_u03b2_71_, lean_object* v_m_72_){
_start:
{
lean_object* v_buckets_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_83_; 
v_buckets_73_ = lean_ctor_get(v_m_72_, 1);
v_isSharedCheck_83_ = !lean_is_exclusive(v_m_72_);
if (v_isSharedCheck_83_ == 0)
{
lean_object* v_unused_84_; 
v_unused_84_ = lean_ctor_get(v_m_72_, 0);
lean_dec(v_unused_84_);
v___x_75_ = v_m_72_;
v_isShared_76_ = v_isSharedCheck_83_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_buckets_73_);
lean_dec(v_m_72_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_83_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_77_ = lean_unsigned_to_nat(0u);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_77_);
lean_ctor_set(v___x_75_, 0, v_buckets_73_);
v___x_79_ = v___x_75_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_buckets_73_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v___x_77_);
v___x_79_ = v_reuseFailAlloc_82_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_box(0);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_79_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
return v___x_81_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_iter___redArg(lean_object* v_m_85_){
_start:
{
lean_object* v_buckets_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_96_; 
v_buckets_86_ = lean_ctor_get(v_m_85_, 1);
v_isSharedCheck_96_ = !lean_is_exclusive(v_m_85_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; 
v_unused_97_ = lean_ctor_get(v_m_85_, 0);
lean_dec(v_unused_97_);
v___x_88_ = v_m_85_;
v_isShared_89_ = v_isSharedCheck_96_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_buckets_86_);
lean_dec(v_m_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_96_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_90_ = lean_unsigned_to_nat(0u);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 1, v___x_90_);
lean_ctor_set(v___x_88_, 0, v_buckets_86_);
v___x_92_ = v___x_88_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_buckets_86_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___x_90_);
v___x_92_ = v_reuseFailAlloc_95_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_box(0);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_iter(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_m_102_){
_start:
{
lean_object* v_buckets_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_113_; 
v_buckets_103_ = lean_ctor_get(v_m_102_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_m_102_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v_m_102_, 0);
lean_dec(v_unused_114_);
v___x_105_ = v_m_102_;
v_isShared_106_ = v_isSharedCheck_113_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_buckets_103_);
lean_dec(v_m_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_113_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = lean_unsigned_to_nat(0u);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v___x_107_);
lean_ctor_set(v___x_105_, 0, v_buckets_103_);
v___x_109_ = v___x_105_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_buckets_103_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_107_);
v___x_109_ = v_reuseFailAlloc_112_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_box(0);
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
return v___x_111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_iter___boxed(lean_object* v_00_u03b1_115_, lean_object* v_00_u03b2_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_m_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Std_HashMap_iter(v_00_u03b1_115_, v_00_u03b2_116_, v_inst_117_, v_inst_118_, v_m_119_);
lean_dec_ref(v_inst_118_);
lean_dec_ref(v_inst_117_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysIter___redArg(lean_object* v_m_121_){
_start:
{
lean_object* v_buckets_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_132_; 
v_buckets_122_ = lean_ctor_get(v_m_121_, 1);
v_isSharedCheck_132_ = !lean_is_exclusive(v_m_121_);
if (v_isSharedCheck_132_ == 0)
{
lean_object* v_unused_133_; 
v_unused_133_ = lean_ctor_get(v_m_121_, 0);
lean_dec(v_unused_133_);
v___x_124_ = v_m_121_;
v_isShared_125_ = v_isSharedCheck_132_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_buckets_122_);
lean_dec(v_m_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_132_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_unsigned_to_nat(0u);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v___x_126_);
lean_ctor_set(v___x_124_, 0, v_buckets_122_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_buckets_122_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_126_);
v___x_128_ = v_reuseFailAlloc_131_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_box(0);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysIter(lean_object* v_00_u03b1_134_, lean_object* v_00_u03b2_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_m_138_){
_start:
{
lean_object* v_buckets_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_149_; 
v_buckets_139_ = lean_ctor_get(v_m_138_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_m_138_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; 
v_unused_150_ = lean_ctor_get(v_m_138_, 0);
lean_dec(v_unused_150_);
v___x_141_ = v_m_138_;
v_isShared_142_ = v_isSharedCheck_149_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_buckets_139_);
lean_dec(v_m_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_149_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_143_ = lean_unsigned_to_nat(0u);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v___x_143_);
lean_ctor_set(v___x_141_, 0, v_buckets_139_);
v___x_145_ = v___x_141_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_buckets_139_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_143_);
v___x_145_ = v_reuseFailAlloc_148_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_box(0);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysIter___boxed(lean_object* v_00_u03b1_151_, lean_object* v_00_u03b2_152_, lean_object* v_inst_153_, lean_object* v_inst_154_, lean_object* v_m_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_HashMap_keysIter(v_00_u03b1_151_, v_00_u03b2_152_, v_inst_153_, v_inst_154_, v_m_155_);
lean_dec_ref(v_inst_154_);
lean_dec_ref(v_inst_153_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesIter___redArg(lean_object* v_m_157_){
_start:
{
lean_object* v_buckets_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_168_; 
v_buckets_158_ = lean_ctor_get(v_m_157_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_m_157_);
if (v_isSharedCheck_168_ == 0)
{
lean_object* v_unused_169_; 
v_unused_169_ = lean_ctor_get(v_m_157_, 0);
lean_dec(v_unused_169_);
v___x_160_ = v_m_157_;
v_isShared_161_ = v_isSharedCheck_168_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_buckets_158_);
lean_dec(v_m_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_168_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_unsigned_to_nat(0u);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_162_);
lean_ctor_set(v___x_160_, 0, v_buckets_158_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_buckets_158_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_162_);
v___x_164_ = v_reuseFailAlloc_167_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_box(0);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesIter(lean_object* v_00_u03b1_170_, lean_object* v_00_u03b2_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_m_174_){
_start:
{
lean_object* v_buckets_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_185_; 
v_buckets_175_ = lean_ctor_get(v_m_174_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_m_174_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v_m_174_, 0);
lean_dec(v_unused_186_);
v___x_177_ = v_m_174_;
v_isShared_178_ = v_isSharedCheck_185_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_buckets_175_);
lean_dec(v_m_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_185_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_unsigned_to_nat(0u);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___x_179_);
lean_ctor_set(v___x_177_, 0, v_buckets_175_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_buckets_175_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_179_);
v___x_181_ = v_reuseFailAlloc_184_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_box(0);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesIter___boxed(lean_object* v_00_u03b1_187_, lean_object* v_00_u03b2_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_m_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_HashMap_valuesIter(v_00_u03b1_187_, v_00_u03b2_188_, v_inst_189_, v_inst_190_, v_m_191_);
lean_dec_ref(v_inst_190_);
lean_dec_ref(v_inst_189_);
return v_res_192_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Iterator(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Raw(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashMap_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DHashMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_HashMap_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DHashMap_Iterator(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Raw(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashMap_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_HashMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_HashMap_Iterator(builtin);
}
#ifdef __cplusplus
}
#endif
