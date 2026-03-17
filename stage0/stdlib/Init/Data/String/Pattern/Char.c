// Lean compiler output
// Module: Init.Data.String.Pattern.Char
// Imports: public import Init.Data.String.Pattern.Pred
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
lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar(uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object*);
static const lean_closure_object l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___closed__0 = (const lean_object*)&l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq(uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar(uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcher(uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcher___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0(uint32_t v_c_1_, lean_object* v_s_2_){
_start:
{
lean_object* v_str_3_; lean_object* v_startInclusive_4_; lean_object* v_endExclusive_5_; lean_object* v___x_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
v_str_3_ = lean_ctor_get(v_s_2_, 0);
v_startInclusive_4_ = lean_ctor_get(v_s_2_, 1);
v_endExclusive_5_ = lean_ctor_get(v_s_2_, 2);
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_nat_sub(v_endExclusive_5_, v_startInclusive_4_);
v___x_8_ = lean_nat_dec_eq(v___x_6_, v___x_7_);
lean_dec(v___x_7_);
if (v___x_8_ == 0)
{
uint32_t v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_string_utf8_get_fast(v_str_3_, v_startInclusive_4_);
v___x_10_ = lean_uint32_dec_eq(v___x_9_, v_c_1_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_string_utf8_next_fast(v_str_3_, v_startInclusive_4_);
v___x_13_ = lean_nat_sub(v___x_12_, v_startInclusive_4_);
v___x_14_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
else
{
lean_object* v___x_15_; 
v___x_15_ = lean_box(0);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0___boxed(lean_object* v_c_16_, lean_object* v_s_17_){
_start:
{
uint32_t v_c_boxed_18_; lean_object* v_res_19_; 
v_c_boxed_18_ = lean_unbox_uint32(v_c_16_);
lean_dec(v_c_16_);
v_res_19_ = l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0(v_c_boxed_18_, v_s_17_);
lean_dec_ref(v_s_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1(uint32_t v_c_20_, lean_object* v_s_21_, lean_object* v_h_22_){
_start:
{
lean_object* v_str_23_; lean_object* v_startInclusive_24_; uint32_t v___x_25_; uint8_t v___x_26_; 
v_str_23_ = lean_ctor_get(v_s_21_, 0);
v_startInclusive_24_ = lean_ctor_get(v_s_21_, 1);
v___x_25_ = lean_string_utf8_get_fast(v_str_23_, v_startInclusive_24_);
v___x_26_ = lean_uint32_dec_eq(v___x_25_, v_c_20_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; 
v___x_27_ = lean_box(0);
return v___x_27_;
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_string_utf8_next_fast(v_str_23_, v_startInclusive_24_);
v___x_29_ = lean_nat_sub(v___x_28_, v_startInclusive_24_);
v___x_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1___boxed(lean_object* v_c_31_, lean_object* v_s_32_, lean_object* v_h_33_){
_start:
{
uint32_t v_c_boxed_34_; lean_object* v_res_35_; 
v_c_boxed_34_ = lean_unbox_uint32(v_c_31_);
lean_dec(v_c_31_);
v_res_35_ = l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1(v_c_boxed_34_, v_s_32_, v_h_33_);
lean_dec_ref(v_s_32_);
return v_res_35_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2(uint32_t v_c_36_, lean_object* v_s_37_){
_start:
{
lean_object* v_str_38_; lean_object* v_startInclusive_39_; lean_object* v_endExclusive_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v_str_38_ = lean_ctor_get(v_s_37_, 0);
v_startInclusive_39_ = lean_ctor_get(v_s_37_, 1);
v_endExclusive_40_ = lean_ctor_get(v_s_37_, 2);
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_nat_sub(v_endExclusive_40_, v_startInclusive_39_);
v___x_43_ = lean_nat_dec_eq(v___x_41_, v___x_42_);
lean_dec(v___x_42_);
if (v___x_43_ == 0)
{
uint32_t v___x_44_; uint8_t v___x_45_; 
v___x_44_ = lean_string_utf8_get_fast(v_str_38_, v_startInclusive_39_);
v___x_45_ = lean_uint32_dec_eq(v___x_44_, v_c_36_);
return v___x_45_;
}
else
{
uint8_t v___x_46_; 
v___x_46_ = 0;
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2___boxed(lean_object* v_c_47_, lean_object* v_s_48_){
_start:
{
uint32_t v_c_boxed_49_; uint8_t v_res_50_; lean_object* v_r_51_; 
v_c_boxed_49_ = lean_unbox_uint32(v_c_47_);
lean_dec(v_c_47_);
v_res_50_ = l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2(v_c_boxed_49_, v_s_48_);
lean_dec_ref(v_s_48_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar(uint32_t v_c_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___f_56_; lean_object* v___x_57_; lean_object* v___f_58_; lean_object* v___x_59_; 
v___x_53_ = lean_box_uint32(v_c_52_);
v___f_54_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0___boxed), 2, 1);
lean_closure_set(v___f_54_, 0, v___x_53_);
v___x_55_ = lean_box_uint32(v_c_52_);
v___f_56_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1___boxed), 3, 1);
lean_closure_set(v___f_56_, 0, v___x_55_);
v___x_57_ = lean_box_uint32(v_c_52_);
v___f_58_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2___boxed), 2, 1);
lean_closure_set(v___f_58_, 0, v___x_57_);
v___x_59_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_59_, 0, v___f_54_);
lean_ctor_set(v___x_59_, 1, v___f_56_);
lean_ctor_set(v___x_59_, 2, v___f_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___boxed(lean_object* v_c_60_){
_start:
{
uint32_t v_c_boxed_61_; lean_object* v_res_62_; 
v_c_boxed_61_ = lean_unbox_uint32(v_c_60_);
lean_dec(v_c_60_);
v_res_62_ = l_String_Slice_Pattern_Char_instForwardPatternChar(v_c_boxed_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0(lean_object* v_s_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_unsigned_to_nat(0u);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object* v_s_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0(v_s_65_);
lean_dec_ref(v_s_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq(uint32_t v_c_68_){
_start:
{
lean_object* v___f_69_; 
v___f_69_ = ((lean_object*)(l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___closed__0));
return v___f_69_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___boxed(lean_object* v_c_70_){
_start:
{
uint32_t v_c_boxed_71_; lean_object* v_res_72_; 
v_c_boxed_71_ = lean_unbox_uint32(v_c_70_);
lean_dec(v_c_70_);
v_res_72_ = l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq(v_c_boxed_71_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0(uint32_t v_c_73_, lean_object* v_s_74_){
_start:
{
lean_object* v_str_75_; lean_object* v_startInclusive_76_; lean_object* v_endExclusive_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v_str_75_ = lean_ctor_get(v_s_74_, 0);
v_startInclusive_76_ = lean_ctor_get(v_s_74_, 1);
v_endExclusive_77_ = lean_ctor_get(v_s_74_, 2);
v___x_78_ = lean_nat_sub(v_endExclusive_77_, v_startInclusive_76_);
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_nat_dec_eq(v___x_78_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint32_t v___x_85_; uint8_t v___x_86_; 
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_sub(v___x_78_, v___x_81_);
lean_dec(v___x_78_);
v___x_83_ = l_String_Slice_posLE(v_s_74_, v___x_82_);
v___x_84_ = lean_nat_add(v_startInclusive_76_, v___x_83_);
v___x_85_ = lean_string_utf8_get_fast(v_str_75_, v___x_84_);
lean_dec(v___x_84_);
v___x_86_ = lean_uint32_dec_eq(v___x_85_, v_c_73_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; 
lean_dec(v___x_83_);
v___x_87_ = lean_box(0);
return v___x_87_;
}
else
{
lean_object* v___x_88_; 
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_83_);
return v___x_88_;
}
}
else
{
lean_object* v___x_89_; 
lean_dec(v___x_78_);
v___x_89_ = lean_box(0);
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0___boxed(lean_object* v_c_90_, lean_object* v_s_91_){
_start:
{
uint32_t v_c_boxed_92_; lean_object* v_res_93_; 
v_c_boxed_92_ = lean_unbox_uint32(v_c_90_);
lean_dec(v_c_90_);
v_res_93_ = l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0(v_c_boxed_92_, v_s_91_);
lean_dec_ref(v_s_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1(uint32_t v_c_94_, lean_object* v_s_95_, lean_object* v_h_96_){
_start:
{
lean_object* v_str_97_; lean_object* v_startInclusive_98_; lean_object* v_endExclusive_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint32_t v___x_105_; uint8_t v___x_106_; 
v_str_97_ = lean_ctor_get(v_s_95_, 0);
v_startInclusive_98_ = lean_ctor_get(v_s_95_, 1);
v_endExclusive_99_ = lean_ctor_get(v_s_95_, 2);
v___x_100_ = lean_nat_sub(v_endExclusive_99_, v_startInclusive_98_);
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_sub(v___x_100_, v___x_101_);
lean_dec(v___x_100_);
v___x_103_ = l_String_Slice_posLE(v_s_95_, v___x_102_);
v___x_104_ = lean_nat_add(v_startInclusive_98_, v___x_103_);
v___x_105_ = lean_string_utf8_get_fast(v_str_97_, v___x_104_);
lean_dec(v___x_104_);
v___x_106_ = lean_uint32_dec_eq(v___x_105_, v_c_94_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
lean_dec(v___x_103_);
v___x_107_ = lean_box(0);
return v___x_107_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_103_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1___boxed(lean_object* v_c_109_, lean_object* v_s_110_, lean_object* v_h_111_){
_start:
{
uint32_t v_c_boxed_112_; lean_object* v_res_113_; 
v_c_boxed_112_ = lean_unbox_uint32(v_c_109_);
lean_dec(v_c_109_);
v_res_113_ = l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1(v_c_boxed_112_, v_s_110_, v_h_111_);
lean_dec_ref(v_s_110_);
return v_res_113_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2(uint32_t v_c_114_, lean_object* v_s_115_){
_start:
{
lean_object* v_str_116_; lean_object* v_startInclusive_117_; lean_object* v_endExclusive_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_str_116_ = lean_ctor_get(v_s_115_, 0);
v_startInclusive_117_ = lean_ctor_get(v_s_115_, 1);
v_endExclusive_118_ = lean_ctor_get(v_s_115_, 2);
v___x_119_ = lean_nat_sub(v_endExclusive_118_, v_startInclusive_117_);
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_nat_dec_eq(v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint32_t v___x_126_; uint8_t v___x_127_; 
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_nat_sub(v___x_119_, v___x_122_);
lean_dec(v___x_119_);
v___x_124_ = l_String_Slice_posLE(v_s_115_, v___x_123_);
v___x_125_ = lean_nat_add(v_startInclusive_117_, v___x_124_);
lean_dec(v___x_124_);
v___x_126_ = lean_string_utf8_get_fast(v_str_116_, v___x_125_);
lean_dec(v___x_125_);
v___x_127_ = lean_uint32_dec_eq(v___x_126_, v_c_114_);
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
lean_dec(v___x_119_);
v___x_128_ = 0;
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2___boxed(lean_object* v_c_129_, lean_object* v_s_130_){
_start:
{
uint32_t v_c_boxed_131_; uint8_t v_res_132_; lean_object* v_r_133_; 
v_c_boxed_131_ = lean_unbox_uint32(v_c_129_);
lean_dec(v_c_129_);
v_res_132_ = l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2(v_c_boxed_131_, v_s_130_);
lean_dec_ref(v_s_130_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar(uint32_t v_c_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___f_136_; lean_object* v___x_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___f_140_; lean_object* v___x_141_; 
v___x_135_ = lean_box_uint32(v_c_134_);
v___f_136_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0___boxed), 2, 1);
lean_closure_set(v___f_136_, 0, v___x_135_);
v___x_137_ = lean_box_uint32(v_c_134_);
v___f_138_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1___boxed), 3, 1);
lean_closure_set(v___f_138_, 0, v___x_137_);
v___x_139_ = lean_box_uint32(v_c_134_);
v___f_140_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2___boxed), 2, 1);
lean_closure_set(v___f_140_, 0, v___x_139_);
v___x_141_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_141_, 0, v___f_136_);
lean_ctor_set(v___x_141_, 1, v___f_138_);
lean_ctor_set(v___x_141_, 2, v___f_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___boxed(lean_object* v_c_142_){
_start:
{
uint32_t v_c_boxed_143_; lean_object* v_res_144_; 
v_c_boxed_143_ = lean_unbox_uint32(v_c_142_);
lean_dec(v_c_142_);
v_res_144_ = l_String_Slice_Pattern_Char_instBackwardPatternChar(v_c_boxed_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcher(uint32_t v_c_145_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_box_uint32(v_c_145_);
v___x_147_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_147_, 0, lean_box(0));
lean_closure_set(v___x_147_, 1, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcher___boxed(lean_object* v_c_148_){
_start:
{
uint32_t v_c_boxed_149_; lean_object* v_res_150_; 
v_c_boxed_149_ = lean_unbox_uint32(v_c_148_);
lean_dec(v_c_148_);
v_res_150_ = l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcher(v_c_boxed_149_);
return v_res_150_;
}
}
lean_object* runtime_initialize_Init_Data_String_Pattern_Pred(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Pattern_Char(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Pattern_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Pattern_Char(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Pattern_Pred(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Pattern_Char(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Pattern_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Pattern_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Pattern_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Pattern_Char(builtin);
}
#ifdef __cplusplus
}
#endif
