// Lean compiler output
// Module: Init.Data.Char.Basic
// Imports: public import Init.Data.UInt.BasicAux import Init.Data.Nat.Div.Basic
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
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_instLT;
LEAN_EXPORT lean_object* l_Char_instLE;
LEAN_EXPORT uint8_t l_Char_instDecidableLt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_instDecidableLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Char_instDecidableLe(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_instDecidableLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_toNat(uint32_t);
LEAN_EXPORT lean_object* l_Char_toNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Char_toUInt8(uint32_t);
LEAN_EXPORT lean_object* l_Char_toUInt8___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Char_ofUInt8(uint8_t);
LEAN_EXPORT lean_object* l_Char_ofUInt8___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Char_instInhabited;
LEAN_EXPORT uint8_t l_Char_isWhitespace(uint32_t);
LEAN_EXPORT lean_object* l_Char_isWhitespace___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Char_isUpper(uint32_t);
LEAN_EXPORT lean_object* l_Char_isUpper___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Char_isLower(uint32_t);
LEAN_EXPORT lean_object* l_Char_isLower___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Char_isAlpha(uint32_t);
LEAN_EXPORT lean_object* l_Char_isAlpha___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Char_isDigit(uint32_t);
LEAN_EXPORT lean_object* l_Char_isDigit___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Char_isHexDigit(uint32_t);
LEAN_EXPORT lean_object* l_Char_isHexDigit___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Char_isAlphanum(uint32_t);
LEAN_EXPORT lean_object* l_Char_isAlphanum___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Char_toLower(uint32_t);
LEAN_EXPORT lean_object* l_Char_toLower___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Char_toUpper(uint32_t);
LEAN_EXPORT lean_object* l_Char_toUpper___boxed(lean_object*);
static lean_object* _init_l_Char_instLT(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
static lean_object* _init_l_Char_instLE(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT uint8_t l_Char_instDecidableLt(uint32_t v_a_3_, uint32_t v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_uint32_dec_lt(v_a_3_, v_b_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Char_instDecidableLt___boxed(lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
uint32_t v_a_boxed_8_; uint32_t v_b_boxed_9_; uint8_t v_res_10_; lean_object* v_r_11_; 
v_a_boxed_8_ = lean_unbox_uint32(v_a_6_);
lean_dec(v_a_6_);
v_b_boxed_9_ = lean_unbox_uint32(v_b_7_);
lean_dec(v_b_7_);
v_res_10_ = l_Char_instDecidableLt(v_a_boxed_8_, v_b_boxed_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l_Char_instDecidableLe(uint32_t v_a_12_, uint32_t v_b_13_){
_start:
{
uint8_t v___x_14_; 
v___x_14_ = lean_uint32_dec_le(v_a_12_, v_b_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Char_instDecidableLe___boxed(lean_object* v_a_15_, lean_object* v_b_16_){
_start:
{
uint32_t v_a_boxed_17_; uint32_t v_b_boxed_18_; uint8_t v_res_19_; lean_object* v_r_20_; 
v_a_boxed_17_ = lean_unbox_uint32(v_a_15_);
lean_dec(v_a_15_);
v_b_boxed_18_ = lean_unbox_uint32(v_b_16_);
lean_dec(v_b_16_);
v_res_19_ = l_Char_instDecidableLe(v_a_boxed_17_, v_b_boxed_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l_Char_toNat(uint32_t v_c_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_uint32_to_nat(v_c_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Char_toNat___boxed(lean_object* v_c_23_){
_start:
{
uint32_t v_c_boxed_24_; lean_object* v_res_25_; 
v_c_boxed_24_ = lean_unbox_uint32(v_c_23_);
lean_dec(v_c_23_);
v_res_25_ = l_Char_toNat(v_c_boxed_24_);
return v_res_25_;
}
}
LEAN_EXPORT uint8_t l_Char_toUInt8(uint32_t v_c_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = lean_uint32_to_uint8(v_c_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Char_toUInt8___boxed(lean_object* v_c_28_){
_start:
{
uint32_t v_c_boxed_29_; uint8_t v_res_30_; lean_object* v_r_31_; 
v_c_boxed_29_ = lean_unbox_uint32(v_c_28_);
lean_dec(v_c_28_);
v_res_30_ = l_Char_toUInt8(v_c_boxed_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT uint32_t l_Char_ofUInt8(uint8_t v_n_32_){
_start:
{
uint32_t v___x_33_; 
v___x_33_ = lean_uint8_to_uint32(v_n_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Char_ofUInt8___boxed(lean_object* v_n_34_){
_start:
{
uint8_t v_n_boxed_35_; uint32_t v_res_36_; lean_object* v_r_37_; 
v_n_boxed_35_ = lean_unbox(v_n_34_);
v_res_36_ = l_Char_ofUInt8(v_n_boxed_35_);
v_r_37_ = lean_box_uint32(v_res_36_);
return v_r_37_;
}
}
static uint32_t _init_l_Char_instInhabited(void){
_start:
{
uint32_t v___x_38_; 
v___x_38_ = 65;
return v___x_38_;
}
}
LEAN_EXPORT uint8_t l_Char_isWhitespace(uint32_t v_c_39_){
_start:
{
uint32_t v___x_40_; uint8_t v___x_41_; 
v___x_40_ = 32;
v___x_41_ = lean_uint32_dec_eq(v_c_39_, v___x_40_);
if (v___x_41_ == 0)
{
uint32_t v___x_42_; uint8_t v___x_43_; 
v___x_42_ = 9;
v___x_43_ = lean_uint32_dec_eq(v_c_39_, v___x_42_);
if (v___x_43_ == 0)
{
uint32_t v___x_44_; uint8_t v___x_45_; 
v___x_44_ = 13;
v___x_45_ = lean_uint32_dec_eq(v_c_39_, v___x_44_);
if (v___x_45_ == 0)
{
uint32_t v___x_46_; uint8_t v___x_47_; 
v___x_46_ = 10;
v___x_47_ = lean_uint32_dec_eq(v_c_39_, v___x_46_);
return v___x_47_;
}
else
{
return v___x_45_;
}
}
else
{
return v___x_43_;
}
}
else
{
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l_Char_isWhitespace___boxed(lean_object* v_c_48_){
_start:
{
uint32_t v_c_boxed_49_; uint8_t v_res_50_; lean_object* v_r_51_; 
v_c_boxed_49_ = lean_unbox_uint32(v_c_48_);
lean_dec(v_c_48_);
v_res_50_ = l_Char_isWhitespace(v_c_boxed_49_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
LEAN_EXPORT uint8_t l_Char_isUpper(uint32_t v_c_52_){
_start:
{
uint32_t v___x_53_; uint8_t v___x_54_; 
v___x_53_ = 65;
v___x_54_ = lean_uint32_dec_le(v___x_53_, v_c_52_);
if (v___x_54_ == 0)
{
return v___x_54_;
}
else
{
uint32_t v___x_55_; uint8_t v___x_56_; 
v___x_55_ = 90;
v___x_56_ = lean_uint32_dec_le(v_c_52_, v___x_55_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l_Char_isUpper___boxed(lean_object* v_c_57_){
_start:
{
uint32_t v_c_boxed_58_; uint8_t v_res_59_; lean_object* v_r_60_; 
v_c_boxed_58_ = lean_unbox_uint32(v_c_57_);
lean_dec(v_c_57_);
v_res_59_ = l_Char_isUpper(v_c_boxed_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t l_Char_isLower(uint32_t v_c_61_){
_start:
{
uint32_t v___x_62_; uint8_t v___x_63_; 
v___x_62_ = 97;
v___x_63_ = lean_uint32_dec_le(v___x_62_, v_c_61_);
if (v___x_63_ == 0)
{
return v___x_63_;
}
else
{
uint32_t v___x_64_; uint8_t v___x_65_; 
v___x_64_ = 122;
v___x_65_ = lean_uint32_dec_le(v_c_61_, v___x_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_Char_isLower___boxed(lean_object* v_c_66_){
_start:
{
uint32_t v_c_boxed_67_; uint8_t v_res_68_; lean_object* v_r_69_; 
v_c_boxed_67_ = lean_unbox_uint32(v_c_66_);
lean_dec(v_c_66_);
v_res_68_ = l_Char_isLower(v_c_boxed_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_Char_isAlpha(uint32_t v_c_70_){
_start:
{
uint8_t v___y_72_; uint32_t v___x_77_; uint8_t v___x_78_; 
v___x_77_ = 65;
v___x_78_ = lean_uint32_dec_le(v___x_77_, v_c_70_);
if (v___x_78_ == 0)
{
v___y_72_ = v___x_78_;
goto v___jp_71_;
}
else
{
uint32_t v___x_79_; uint8_t v___x_80_; 
v___x_79_ = 90;
v___x_80_ = lean_uint32_dec_le(v_c_70_, v___x_79_);
v___y_72_ = v___x_80_;
goto v___jp_71_;
}
v___jp_71_:
{
if (v___y_72_ == 0)
{
uint32_t v___x_73_; uint8_t v___x_74_; 
v___x_73_ = 97;
v___x_74_ = lean_uint32_dec_le(v___x_73_, v_c_70_);
if (v___x_74_ == 0)
{
return v___x_74_;
}
else
{
uint32_t v___x_75_; uint8_t v___x_76_; 
v___x_75_ = 122;
v___x_76_ = lean_uint32_dec_le(v_c_70_, v___x_75_);
return v___x_76_;
}
}
else
{
return v___y_72_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isAlpha___boxed(lean_object* v_c_81_){
_start:
{
uint32_t v_c_boxed_82_; uint8_t v_res_83_; lean_object* v_r_84_; 
v_c_boxed_82_ = lean_unbox_uint32(v_c_81_);
lean_dec(v_c_81_);
v_res_83_ = l_Char_isAlpha(v_c_boxed_82_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint8_t l_Char_isDigit(uint32_t v_c_85_){
_start:
{
uint32_t v___x_86_; uint8_t v___x_87_; 
v___x_86_ = 48;
v___x_87_ = lean_uint32_dec_le(v___x_86_, v_c_85_);
if (v___x_87_ == 0)
{
return v___x_87_;
}
else
{
uint32_t v___x_88_; uint8_t v___x_89_; 
v___x_88_ = 57;
v___x_89_ = lean_uint32_dec_le(v_c_85_, v___x_88_);
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* l_Char_isDigit___boxed(lean_object* v_c_90_){
_start:
{
uint32_t v_c_boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v_c_boxed_91_ = lean_unbox_uint32(v_c_90_);
lean_dec(v_c_90_);
v_res_92_ = l_Char_isDigit(v_c_boxed_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l_Char_isHexDigit(uint32_t v_c_94_){
_start:
{
uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_105_ = 48;
v___x_106_ = lean_uint32_dec_le(v___x_105_, v_c_94_);
if (v___x_106_ == 0)
{
goto v___jp_100_;
}
else
{
uint32_t v___x_107_; uint8_t v___x_108_; 
v___x_107_ = 57;
v___x_108_ = lean_uint32_dec_le(v_c_94_, v___x_107_);
if (v___x_108_ == 0)
{
goto v___jp_100_;
}
else
{
return v___x_108_;
}
}
v___jp_95_:
{
uint32_t v___x_96_; uint8_t v___x_97_; 
v___x_96_ = 65;
v___x_97_ = lean_uint32_dec_le(v___x_96_, v_c_94_);
if (v___x_97_ == 0)
{
return v___x_97_;
}
else
{
uint32_t v___x_98_; uint8_t v___x_99_; 
v___x_98_ = 70;
v___x_99_ = lean_uint32_dec_le(v_c_94_, v___x_98_);
return v___x_99_;
}
}
v___jp_100_:
{
uint32_t v___x_101_; uint8_t v___x_102_; 
v___x_101_ = 97;
v___x_102_ = lean_uint32_dec_le(v___x_101_, v_c_94_);
if (v___x_102_ == 0)
{
goto v___jp_95_;
}
else
{
uint32_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = 102;
v___x_104_ = lean_uint32_dec_le(v_c_94_, v___x_103_);
if (v___x_104_ == 0)
{
goto v___jp_95_;
}
else
{
return v___x_104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isHexDigit___boxed(lean_object* v_c_109_){
_start:
{
uint32_t v_c_boxed_110_; uint8_t v_res_111_; lean_object* v_r_112_; 
v_c_boxed_110_ = lean_unbox_uint32(v_c_109_);
lean_dec(v_c_109_);
v_res_111_ = l_Char_isHexDigit(v_c_boxed_110_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint8_t l_Char_isAlphanum(uint32_t v_c_113_){
_start:
{
uint8_t v___y_120_; uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 65;
v___x_126_ = lean_uint32_dec_le(v___x_125_, v_c_113_);
if (v___x_126_ == 0)
{
v___y_120_ = v___x_126_;
goto v___jp_119_;
}
else
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 90;
v___x_128_ = lean_uint32_dec_le(v_c_113_, v___x_127_);
v___y_120_ = v___x_128_;
goto v___jp_119_;
}
v___jp_114_:
{
uint32_t v___x_115_; uint8_t v___x_116_; 
v___x_115_ = 48;
v___x_116_ = lean_uint32_dec_le(v___x_115_, v_c_113_);
if (v___x_116_ == 0)
{
return v___x_116_;
}
else
{
uint32_t v___x_117_; uint8_t v___x_118_; 
v___x_117_ = 57;
v___x_118_ = lean_uint32_dec_le(v_c_113_, v___x_117_);
return v___x_118_;
}
}
v___jp_119_:
{
if (v___y_120_ == 0)
{
uint32_t v___x_121_; uint8_t v___x_122_; 
v___x_121_ = 97;
v___x_122_ = lean_uint32_dec_le(v___x_121_, v_c_113_);
if (v___x_122_ == 0)
{
goto v___jp_114_;
}
else
{
uint32_t v___x_123_; uint8_t v___x_124_; 
v___x_123_ = 122;
v___x_124_ = lean_uint32_dec_le(v_c_113_, v___x_123_);
if (v___x_124_ == 0)
{
goto v___jp_114_;
}
else
{
return v___x_124_;
}
}
}
else
{
return v___y_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isAlphanum___boxed(lean_object* v_c_129_){
_start:
{
uint32_t v_c_boxed_130_; uint8_t v_res_131_; lean_object* v_r_132_; 
v_c_boxed_130_ = lean_unbox_uint32(v_c_129_);
lean_dec(v_c_129_);
v_res_131_ = l_Char_isAlphanum(v_c_boxed_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT uint32_t l_Char_toLower(uint32_t v_c_133_){
_start:
{
uint8_t v___y_135_; uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 65;
v___x_139_ = lean_uint32_dec_le(v___x_138_, v_c_133_);
if (v___x_139_ == 0)
{
v___y_135_ = v___x_139_;
goto v___jp_134_;
}
else
{
uint32_t v___x_140_; uint8_t v___x_141_; 
v___x_140_ = 90;
v___x_141_ = lean_uint32_dec_le(v_c_133_, v___x_140_);
v___y_135_ = v___x_141_;
goto v___jp_134_;
}
v___jp_134_:
{
if (v___y_135_ == 0)
{
return v_c_133_;
}
else
{
uint32_t v___x_136_; uint32_t v___x_137_; 
v___x_136_ = 32;
v___x_137_ = lean_uint32_add(v_c_133_, v___x_136_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_toLower___boxed(lean_object* v_c_142_){
_start:
{
uint32_t v_c_boxed_143_; uint32_t v_res_144_; lean_object* v_r_145_; 
v_c_boxed_143_ = lean_unbox_uint32(v_c_142_);
lean_dec(v_c_142_);
v_res_144_ = l_Char_toLower(v_c_boxed_143_);
v_r_145_ = lean_box_uint32(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT uint32_t l_Char_toUpper(uint32_t v_c_146_){
_start:
{
uint8_t v___y_148_; uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 97;
v___x_152_ = lean_uint32_dec_le(v___x_151_, v_c_146_);
if (v___x_152_ == 0)
{
v___y_148_ = v___x_152_;
goto v___jp_147_;
}
else
{
uint32_t v___x_153_; uint8_t v___x_154_; 
v___x_153_ = 122;
v___x_154_ = lean_uint32_dec_le(v_c_146_, v___x_153_);
v___y_148_ = v___x_154_;
goto v___jp_147_;
}
v___jp_147_:
{
if (v___y_148_ == 0)
{
return v_c_146_;
}
else
{
uint32_t v___x_149_; uint32_t v___x_150_; 
v___x_149_ = 4294967264;
v___x_150_ = lean_uint32_add(v_c_146_, v___x_149_);
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_toUpper___boxed(lean_object* v_c_155_){
_start:
{
uint32_t v_c_boxed_156_; uint32_t v_res_157_; lean_object* v_r_158_; 
v_c_boxed_156_ = lean_unbox_uint32(v_c_155_);
lean_dec(v_c_155_);
v_res_157_ = l_Char_toUpper(v_c_boxed_156_);
v_r_158_ = lean_box_uint32(v_res_157_);
return v_r_158_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Char_instLT = _init_l_Char_instLT();
lean_mark_persistent(l_Char_instLT);
l_Char_instLE = _init_l_Char_instLE();
lean_mark_persistent(l_Char_instLE);
l_Char_instInhabited = _init_l_Char_instInhabited();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Char_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Char_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
