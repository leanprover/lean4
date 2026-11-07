// Lean compiler output
// Module: Init.Data.String.Pattern.Memcmp
// Imports: public import Init.Data.String.Basic public import Init.Data.Ord.Basic import Init.Data.Ord.UInt import Init.Data.String.Lemmas.Order import Init.Omega
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_lt(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStrCompare_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStrCompare_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStrCompare_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStrCompare_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_memcmp_compare(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStrCompare___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_memcmp_lt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStrLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSliceCompare___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSliceCompare___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSliceCompare(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSliceCompare___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSliceLt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSliceLt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSliceLt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSliceLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStrCompare_go___redArg(lean_object* v_lhs_1_, lean_object* v_rhs_2_, lean_object* v_lstart_3_, lean_object* v_rstart_4_, lean_object* v_len_5_, lean_object* v_curr_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_nat_dec_lt(v_curr_6_, v_len_5_);
if (v___x_7_ == 0)
{
uint8_t v___x_8_; 
lean_dec(v_curr_6_);
v___x_8_ = 1;
return v___x_8_;
}
else
{
lean_object* v___x_9_; uint8_t v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; uint8_t v___x_13_; 
v___x_9_ = lean_nat_add(v_lstart_3_, v_curr_6_);
v___x_10_ = lean_string_get_byte_fast(v_lhs_1_, v___x_9_);
v___x_11_ = lean_nat_add(v_rstart_4_, v_curr_6_);
v___x_12_ = lean_string_get_byte_fast(v_rhs_2_, v___x_11_);
v___x_13_ = lean_uint8_dec_lt(v___x_10_, v___x_12_);
if (v___x_13_ == 0)
{
uint8_t v___x_14_; 
v___x_14_ = lean_uint8_dec_eq(v___x_10_, v___x_12_);
if (v___x_14_ == 0)
{
uint8_t v___x_15_; 
lean_dec(v_curr_6_);
v___x_15_ = 2;
return v___x_15_;
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_nat_add(v_curr_6_, v___x_16_);
lean_dec(v_curr_6_);
v_curr_6_ = v___x_17_;
goto _start;
}
}
else
{
uint8_t v___x_19_; 
lean_dec(v_curr_6_);
v___x_19_ = 0;
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStrCompare_go___redArg___boxed(lean_object* v_lhs_20_, lean_object* v_rhs_21_, lean_object* v_lstart_22_, lean_object* v_rstart_23_, lean_object* v_len_24_, lean_object* v_curr_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStrCompare_go___redArg(v_lhs_20_, v_rhs_21_, v_lstart_22_, v_rstart_23_, v_len_24_, v_curr_25_);
lean_dec(v_len_24_);
lean_dec(v_rstart_23_);
lean_dec(v_lstart_22_);
lean_dec_ref(v_rhs_21_);
lean_dec_ref(v_lhs_20_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStrCompare_go(lean_object* v_lhs_28_, lean_object* v_rhs_29_, lean_object* v_lstart_30_, lean_object* v_rstart_31_, lean_object* v_len_32_, lean_object* v_h1_33_, lean_object* v_h2_34_, lean_object* v_curr_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStrCompare_go___redArg(v_lhs_28_, v_rhs_29_, v_lstart_30_, v_rstart_31_, v_len_32_, v_curr_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStrCompare_go___boxed(lean_object* v_lhs_37_, lean_object* v_rhs_38_, lean_object* v_lstart_39_, lean_object* v_rstart_40_, lean_object* v_len_41_, lean_object* v_h1_42_, lean_object* v_h2_43_, lean_object* v_curr_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStrCompare_go(v_lhs_37_, v_rhs_38_, v_lstart_39_, v_rstart_40_, v_len_41_, v_h1_42_, v_h2_43_, v_curr_44_);
lean_dec(v_len_41_);
lean_dec(v_rstart_40_);
lean_dec(v_lstart_39_);
lean_dec_ref(v_rhs_38_);
lean_dec_ref(v_lhs_37_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStrCompare___boxed(lean_object* v_lhs_54_, lean_object* v_rhs_55_, lean_object* v_lstart_56_, lean_object* v_rstart_57_, lean_object* v_len_58_, lean_object* v_h1_59_, lean_object* v_h2_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = lean_string_memcmp_compare(v_lhs_54_, v_rhs_55_, v_lstart_56_, v_rstart_57_, v_len_58_);
lean_dec(v_len_58_);
lean_dec(v_rstart_57_);
lean_dec(v_lstart_56_);
lean_dec_ref(v_rhs_55_);
lean_dec_ref(v_lhs_54_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStr___boxed(lean_object* v_lhs_70_, lean_object* v_rhs_71_, lean_object* v_lstart_72_, lean_object* v_rstart_73_, lean_object* v_len_74_, lean_object* v_h1_75_, lean_object* v_h2_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = lean_string_memcmp(v_lhs_70_, v_rhs_71_, v_lstart_72_, v_rstart_73_, v_len_74_);
lean_dec(v_len_74_);
lean_dec(v_rstart_73_);
lean_dec(v_lstart_72_);
lean_dec_ref(v_rhs_71_);
lean_dec_ref(v_lhs_70_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStrLt___boxed(lean_object* v_lhs_86_, lean_object* v_rhs_87_, lean_object* v_lstart_88_, lean_object* v_rstart_89_, lean_object* v_len_90_, lean_object* v_h1_91_, lean_object* v_h2_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = lean_string_memcmp_lt(v_lhs_86_, v_rhs_87_, v_lstart_88_, v_rstart_89_, v_len_90_);
lean_dec(v_len_90_);
lean_dec(v_rstart_89_);
lean_dec(v_lstart_88_);
lean_dec_ref(v_rhs_87_);
lean_dec_ref(v_lhs_86_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSliceCompare___redArg(lean_object* v_lhs_95_, lean_object* v_rhs_96_, lean_object* v_lstart_97_, lean_object* v_rstart_98_, lean_object* v_len_99_){
_start:
{
lean_object* v_str_100_; lean_object* v_startInclusive_101_; lean_object* v_str_102_; lean_object* v_startInclusive_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v_str_100_ = lean_ctor_get(v_lhs_95_, 0);
v_startInclusive_101_ = lean_ctor_get(v_lhs_95_, 1);
v_str_102_ = lean_ctor_get(v_rhs_96_, 0);
v_startInclusive_103_ = lean_ctor_get(v_rhs_96_, 1);
v___x_104_ = lean_nat_add(v_startInclusive_101_, v_lstart_97_);
v___x_105_ = lean_nat_add(v_startInclusive_103_, v_rstart_98_);
v___x_106_ = lean_string_memcmp_compare(v_str_100_, v_str_102_, v___x_104_, v___x_105_, v_len_99_);
lean_dec(v___x_105_);
lean_dec(v___x_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSliceCompare___redArg___boxed(lean_object* v_lhs_107_, lean_object* v_rhs_108_, lean_object* v_lstart_109_, lean_object* v_rstart_110_, lean_object* v_len_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_String_Slice_Pattern_Internal_memcmpSliceCompare___redArg(v_lhs_107_, v_rhs_108_, v_lstart_109_, v_rstart_110_, v_len_111_);
lean_dec(v_len_111_);
lean_dec(v_rstart_110_);
lean_dec(v_lstart_109_);
lean_dec_ref(v_rhs_108_);
lean_dec_ref(v_lhs_107_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSliceCompare(lean_object* v_lhs_114_, lean_object* v_rhs_115_, lean_object* v_lstart_116_, lean_object* v_rstart_117_, lean_object* v_len_118_, lean_object* v_h1_119_, lean_object* v_h2_120_){
_start:
{
lean_object* v_str_121_; lean_object* v_startInclusive_122_; lean_object* v_str_123_; lean_object* v_startInclusive_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_str_121_ = lean_ctor_get(v_lhs_114_, 0);
v_startInclusive_122_ = lean_ctor_get(v_lhs_114_, 1);
v_str_123_ = lean_ctor_get(v_rhs_115_, 0);
v_startInclusive_124_ = lean_ctor_get(v_rhs_115_, 1);
v___x_125_ = lean_nat_add(v_startInclusive_122_, v_lstart_116_);
v___x_126_ = lean_nat_add(v_startInclusive_124_, v_rstart_117_);
v___x_127_ = lean_string_memcmp_compare(v_str_121_, v_str_123_, v___x_125_, v___x_126_, v_len_118_);
lean_dec(v___x_126_);
lean_dec(v___x_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSliceCompare___boxed(lean_object* v_lhs_128_, lean_object* v_rhs_129_, lean_object* v_lstart_130_, lean_object* v_rstart_131_, lean_object* v_len_132_, lean_object* v_h1_133_, lean_object* v_h2_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_String_Slice_Pattern_Internal_memcmpSliceCompare(v_lhs_128_, v_rhs_129_, v_lstart_130_, v_rstart_131_, v_len_132_, v_h1_133_, v_h2_134_);
lean_dec(v_len_132_);
lean_dec(v_rstart_131_);
lean_dec(v_lstart_130_);
lean_dec_ref(v_rhs_129_);
lean_dec_ref(v_lhs_128_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice___redArg(lean_object* v_lhs_137_, lean_object* v_rhs_138_, lean_object* v_lstart_139_, lean_object* v_rstart_140_, lean_object* v_len_141_){
_start:
{
lean_object* v_str_142_; lean_object* v_startInclusive_143_; lean_object* v_str_144_; lean_object* v_startInclusive_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v_str_142_ = lean_ctor_get(v_lhs_137_, 0);
v_startInclusive_143_ = lean_ctor_get(v_lhs_137_, 1);
v_str_144_ = lean_ctor_get(v_rhs_138_, 0);
v_startInclusive_145_ = lean_ctor_get(v_rhs_138_, 1);
v___x_146_ = lean_nat_add(v_startInclusive_143_, v_lstart_139_);
v___x_147_ = lean_nat_add(v_startInclusive_145_, v_rstart_140_);
v___x_148_ = lean_string_memcmp(v_str_142_, v_str_144_, v___x_146_, v___x_147_, v_len_141_);
lean_dec(v___x_147_);
lean_dec(v___x_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___redArg___boxed(lean_object* v_lhs_149_, lean_object* v_rhs_150_, lean_object* v_lstart_151_, lean_object* v_rstart_152_, lean_object* v_len_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_String_Slice_Pattern_Internal_memcmpSlice___redArg(v_lhs_149_, v_rhs_150_, v_lstart_151_, v_rstart_152_, v_len_153_);
lean_dec(v_len_153_);
lean_dec(v_rstart_152_);
lean_dec(v_lstart_151_);
lean_dec_ref(v_rhs_150_);
lean_dec_ref(v_lhs_149_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice(lean_object* v_lhs_156_, lean_object* v_rhs_157_, lean_object* v_lstart_158_, lean_object* v_rstart_159_, lean_object* v_len_160_, lean_object* v_h1_161_, lean_object* v_h2_162_){
_start:
{
lean_object* v_str_163_; lean_object* v_startInclusive_164_; lean_object* v_str_165_; lean_object* v_startInclusive_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_str_163_ = lean_ctor_get(v_lhs_156_, 0);
v_startInclusive_164_ = lean_ctor_get(v_lhs_156_, 1);
v_str_165_ = lean_ctor_get(v_rhs_157_, 0);
v_startInclusive_166_ = lean_ctor_get(v_rhs_157_, 1);
v___x_167_ = lean_nat_add(v_startInclusive_164_, v_lstart_158_);
v___x_168_ = lean_nat_add(v_startInclusive_166_, v_rstart_159_);
v___x_169_ = lean_string_memcmp(v_str_163_, v_str_165_, v___x_167_, v___x_168_, v_len_160_);
lean_dec(v___x_168_);
lean_dec(v___x_167_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___boxed(lean_object* v_lhs_170_, lean_object* v_rhs_171_, lean_object* v_lstart_172_, lean_object* v_rstart_173_, lean_object* v_len_174_, lean_object* v_h1_175_, lean_object* v_h2_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_String_Slice_Pattern_Internal_memcmpSlice(v_lhs_170_, v_rhs_171_, v_lstart_172_, v_rstart_173_, v_len_174_, v_h1_175_, v_h2_176_);
lean_dec(v_len_174_);
lean_dec(v_rstart_173_);
lean_dec(v_lstart_172_);
lean_dec_ref(v_rhs_171_);
lean_dec_ref(v_lhs_170_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSliceLt___redArg(lean_object* v_lhs_179_, lean_object* v_rhs_180_, lean_object* v_lstart_181_, lean_object* v_rstart_182_, lean_object* v_len_183_){
_start:
{
lean_object* v_str_184_; lean_object* v_startInclusive_185_; lean_object* v_str_186_; lean_object* v_startInclusive_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_str_184_ = lean_ctor_get(v_lhs_179_, 0);
v_startInclusive_185_ = lean_ctor_get(v_lhs_179_, 1);
v_str_186_ = lean_ctor_get(v_rhs_180_, 0);
v_startInclusive_187_ = lean_ctor_get(v_rhs_180_, 1);
v___x_188_ = lean_nat_add(v_startInclusive_185_, v_lstart_181_);
v___x_189_ = lean_nat_add(v_startInclusive_187_, v_rstart_182_);
v___x_190_ = lean_string_memcmp_lt(v_str_184_, v_str_186_, v___x_188_, v___x_189_, v_len_183_);
lean_dec(v___x_189_);
lean_dec(v___x_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSliceLt___redArg___boxed(lean_object* v_lhs_191_, lean_object* v_rhs_192_, lean_object* v_lstart_193_, lean_object* v_rstart_194_, lean_object* v_len_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_String_Slice_Pattern_Internal_memcmpSliceLt___redArg(v_lhs_191_, v_rhs_192_, v_lstart_193_, v_rstart_194_, v_len_195_);
lean_dec(v_len_195_);
lean_dec(v_rstart_194_);
lean_dec(v_lstart_193_);
lean_dec_ref(v_rhs_192_);
lean_dec_ref(v_lhs_191_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSliceLt(lean_object* v_lhs_198_, lean_object* v_rhs_199_, lean_object* v_lstart_200_, lean_object* v_rstart_201_, lean_object* v_len_202_, lean_object* v_h1_203_, lean_object* v_h2_204_){
_start:
{
lean_object* v_str_205_; lean_object* v_startInclusive_206_; lean_object* v_str_207_; lean_object* v_startInclusive_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_str_205_ = lean_ctor_get(v_lhs_198_, 0);
v_startInclusive_206_ = lean_ctor_get(v_lhs_198_, 1);
v_str_207_ = lean_ctor_get(v_rhs_199_, 0);
v_startInclusive_208_ = lean_ctor_get(v_rhs_199_, 1);
v___x_209_ = lean_nat_add(v_startInclusive_206_, v_lstart_200_);
v___x_210_ = lean_nat_add(v_startInclusive_208_, v_rstart_201_);
v___x_211_ = lean_string_memcmp_lt(v_str_205_, v_str_207_, v___x_209_, v___x_210_, v_len_202_);
lean_dec(v___x_210_);
lean_dec(v___x_209_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSliceLt___boxed(lean_object* v_lhs_212_, lean_object* v_rhs_213_, lean_object* v_lstart_214_, lean_object* v_rstart_215_, lean_object* v_len_216_, lean_object* v_h1_217_, lean_object* v_h2_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = l_String_Slice_Pattern_Internal_memcmpSliceLt(v_lhs_212_, v_rhs_213_, v_lstart_214_, v_rstart_215_, v_len_216_, v_h1_217_, v_h2_218_);
lean_dec(v_len_216_);
lean_dec(v_rstart_215_);
lean_dec(v_lstart_214_);
lean_dec_ref(v_rhs_213_);
lean_dec_ref(v_lhs_212_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Pattern_Memcmp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Pattern_Memcmp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Pattern_Memcmp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Pattern_Memcmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Pattern_Memcmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Pattern_Memcmp(builtin);
}
#ifdef __cplusplus
}
#endif
