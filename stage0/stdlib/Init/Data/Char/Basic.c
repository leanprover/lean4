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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
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
uint8_t v___y_41_; uint32_t v___x_46_; uint8_t v___x_47_; 
v___x_46_ = 32;
v___x_47_ = lean_uint32_dec_eq(v_c_39_, v___x_46_);
if (v___x_47_ == 0)
{
uint32_t v___x_48_; uint8_t v___x_49_; 
v___x_48_ = 9;
v___x_49_ = lean_uint32_dec_eq(v_c_39_, v___x_48_);
v___y_41_ = v___x_49_;
goto v___jp_40_;
}
else
{
v___y_41_ = v___x_47_;
goto v___jp_40_;
}
v___jp_40_:
{
if (v___y_41_ == 0)
{
uint32_t v___x_42_; uint8_t v___x_43_; 
v___x_42_ = 13;
v___x_43_ = lean_uint32_dec_eq(v_c_39_, v___x_42_);
if (v___x_43_ == 0)
{
uint32_t v___x_44_; uint8_t v___x_45_; 
v___x_44_ = 10;
v___x_45_ = lean_uint32_dec_eq(v_c_39_, v___x_44_);
return v___x_45_;
}
else
{
return v___x_43_;
}
}
else
{
return v___y_41_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isWhitespace___boxed(lean_object* v_c_50_){
_start:
{
uint32_t v_c_boxed_51_; uint8_t v_res_52_; lean_object* v_r_53_; 
v_c_boxed_51_ = lean_unbox_uint32(v_c_50_);
lean_dec(v_c_50_);
v_res_52_ = l_Char_isWhitespace(v_c_boxed_51_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT uint8_t l_Char_isUpper(uint32_t v_c_54_){
_start:
{
uint32_t v___x_55_; uint8_t v___x_56_; 
v___x_55_ = 65;
v___x_56_ = lean_uint32_dec_le(v___x_55_, v_c_54_);
if (v___x_56_ == 0)
{
return v___x_56_;
}
else
{
uint32_t v___x_57_; uint8_t v___x_58_; 
v___x_57_ = 90;
v___x_58_ = lean_uint32_dec_le(v_c_54_, v___x_57_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l_Char_isUpper___boxed(lean_object* v_c_59_){
_start:
{
uint32_t v_c_boxed_60_; uint8_t v_res_61_; lean_object* v_r_62_; 
v_c_boxed_60_ = lean_unbox_uint32(v_c_59_);
lean_dec(v_c_59_);
v_res_61_ = l_Char_isUpper(v_c_boxed_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT uint8_t l_Char_isLower(uint32_t v_c_63_){
_start:
{
uint32_t v___x_64_; uint8_t v___x_65_; 
v___x_64_ = 97;
v___x_65_ = lean_uint32_dec_le(v___x_64_, v_c_63_);
if (v___x_65_ == 0)
{
return v___x_65_;
}
else
{
uint32_t v___x_66_; uint8_t v___x_67_; 
v___x_66_ = 122;
v___x_67_ = lean_uint32_dec_le(v_c_63_, v___x_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Char_isLower___boxed(lean_object* v_c_68_){
_start:
{
uint32_t v_c_boxed_69_; uint8_t v_res_70_; lean_object* v_r_71_; 
v_c_boxed_69_ = lean_unbox_uint32(v_c_68_);
lean_dec(v_c_68_);
v_res_70_ = l_Char_isLower(v_c_boxed_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint8_t l_Char_isAlpha(uint32_t v_c_72_){
_start:
{
uint32_t v___x_78_; uint8_t v___x_79_; 
v___x_78_ = 65;
v___x_79_ = lean_uint32_dec_le(v___x_78_, v_c_72_);
if (v___x_79_ == 0)
{
goto v___jp_73_;
}
else
{
uint32_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 90;
v___x_81_ = lean_uint32_dec_le(v_c_72_, v___x_80_);
if (v___x_81_ == 0)
{
goto v___jp_73_;
}
else
{
return v___x_81_;
}
}
v___jp_73_:
{
uint32_t v___x_74_; uint8_t v___x_75_; 
v___x_74_ = 97;
v___x_75_ = lean_uint32_dec_le(v___x_74_, v_c_72_);
if (v___x_75_ == 0)
{
return v___x_75_;
}
else
{
uint32_t v___x_76_; uint8_t v___x_77_; 
v___x_76_ = 122;
v___x_77_ = lean_uint32_dec_le(v_c_72_, v___x_76_);
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isAlpha___boxed(lean_object* v_c_82_){
_start:
{
uint32_t v_c_boxed_83_; uint8_t v_res_84_; lean_object* v_r_85_; 
v_c_boxed_83_ = lean_unbox_uint32(v_c_82_);
lean_dec(v_c_82_);
v_res_84_ = l_Char_isAlpha(v_c_boxed_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT uint8_t l_Char_isDigit(uint32_t v_c_86_){
_start:
{
uint32_t v___x_87_; uint8_t v___x_88_; 
v___x_87_ = 48;
v___x_88_ = lean_uint32_dec_le(v___x_87_, v_c_86_);
if (v___x_88_ == 0)
{
return v___x_88_;
}
else
{
uint32_t v___x_89_; uint8_t v___x_90_; 
v___x_89_ = 57;
v___x_90_ = lean_uint32_dec_le(v_c_86_, v___x_89_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l_Char_isDigit___boxed(lean_object* v_c_91_){
_start:
{
uint32_t v_c_boxed_92_; uint8_t v_res_93_; lean_object* v_r_94_; 
v_c_boxed_92_ = lean_unbox_uint32(v_c_91_);
lean_dec(v_c_91_);
v_res_93_ = l_Char_isDigit(v_c_boxed_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT uint8_t l_Char_isHexDigit(uint32_t v_c_95_){
_start:
{
uint8_t v___y_97_; uint8_t v___y_103_; uint32_t v___x_108_; uint8_t v___x_109_; 
v___x_108_ = 48;
v___x_109_ = lean_uint32_dec_le(v___x_108_, v_c_95_);
if (v___x_109_ == 0)
{
v___y_103_ = v___x_109_;
goto v___jp_102_;
}
else
{
uint32_t v___x_110_; uint8_t v___x_111_; 
v___x_110_ = 57;
v___x_111_ = lean_uint32_dec_le(v_c_95_, v___x_110_);
v___y_103_ = v___x_111_;
goto v___jp_102_;
}
v___jp_96_:
{
if (v___y_97_ == 0)
{
uint32_t v___x_98_; uint8_t v___x_99_; 
v___x_98_ = 65;
v___x_99_ = lean_uint32_dec_le(v___x_98_, v_c_95_);
if (v___x_99_ == 0)
{
return v___x_99_;
}
else
{
uint32_t v___x_100_; uint8_t v___x_101_; 
v___x_100_ = 70;
v___x_101_ = lean_uint32_dec_le(v_c_95_, v___x_100_);
return v___x_101_;
}
}
else
{
return v___y_97_;
}
}
v___jp_102_:
{
if (v___y_103_ == 0)
{
uint32_t v___x_104_; uint8_t v___x_105_; 
v___x_104_ = 97;
v___x_105_ = lean_uint32_dec_le(v___x_104_, v_c_95_);
if (v___x_105_ == 0)
{
v___y_97_ = v___x_105_;
goto v___jp_96_;
}
else
{
uint32_t v___x_106_; uint8_t v___x_107_; 
v___x_106_ = 102;
v___x_107_ = lean_uint32_dec_le(v_c_95_, v___x_106_);
v___y_97_ = v___x_107_;
goto v___jp_96_;
}
}
else
{
return v___y_103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isHexDigit___boxed(lean_object* v_c_112_){
_start:
{
uint32_t v_c_boxed_113_; uint8_t v_res_114_; lean_object* v_r_115_; 
v_c_boxed_113_ = lean_unbox_uint32(v_c_112_);
lean_dec(v_c_112_);
v_res_114_ = l_Char_isHexDigit(v_c_boxed_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t l_Char_isAlphanum(uint32_t v_c_116_){
_start:
{
uint8_t v___y_118_; uint32_t v___x_128_; uint8_t v___x_129_; 
v___x_128_ = 65;
v___x_129_ = lean_uint32_dec_le(v___x_128_, v_c_116_);
if (v___x_129_ == 0)
{
goto v___jp_123_;
}
else
{
uint32_t v___x_130_; uint8_t v___x_131_; 
v___x_130_ = 90;
v___x_131_ = lean_uint32_dec_le(v_c_116_, v___x_130_);
if (v___x_131_ == 0)
{
goto v___jp_123_;
}
else
{
return v___x_131_;
}
}
v___jp_117_:
{
if (v___y_118_ == 0)
{
uint32_t v___x_119_; uint8_t v___x_120_; 
v___x_119_ = 48;
v___x_120_ = lean_uint32_dec_le(v___x_119_, v_c_116_);
if (v___x_120_ == 0)
{
return v___x_120_;
}
else
{
uint32_t v___x_121_; uint8_t v___x_122_; 
v___x_121_ = 57;
v___x_122_ = lean_uint32_dec_le(v_c_116_, v___x_121_);
return v___x_122_;
}
}
else
{
return v___y_118_;
}
}
v___jp_123_:
{
uint32_t v___x_124_; uint8_t v___x_125_; 
v___x_124_ = 97;
v___x_125_ = lean_uint32_dec_le(v___x_124_, v_c_116_);
if (v___x_125_ == 0)
{
v___y_118_ = v___x_125_;
goto v___jp_117_;
}
else
{
uint32_t v___x_126_; uint8_t v___x_127_; 
v___x_126_ = 122;
v___x_127_ = lean_uint32_dec_le(v_c_116_, v___x_126_);
v___y_118_ = v___x_127_;
goto v___jp_117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isAlphanum___boxed(lean_object* v_c_132_){
_start:
{
uint32_t v_c_boxed_133_; uint8_t v_res_134_; lean_object* v_r_135_; 
v_c_boxed_133_ = lean_unbox_uint32(v_c_132_);
lean_dec(v_c_132_);
v_res_134_ = l_Char_isAlphanum(v_c_boxed_133_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT uint32_t l_Char_toLower(uint32_t v_c_136_){
_start:
{
uint32_t v___x_137_; uint8_t v___x_138_; 
v___x_137_ = 65;
v___x_138_ = lean_uint32_dec_le(v___x_137_, v_c_136_);
if (v___x_138_ == 0)
{
return v_c_136_;
}
else
{
uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = 90;
v___x_140_ = lean_uint32_dec_le(v_c_136_, v___x_139_);
if (v___x_140_ == 0)
{
return v_c_136_;
}
else
{
uint32_t v___x_141_; uint32_t v___x_142_; 
v___x_141_ = 32;
v___x_142_ = lean_uint32_add(v_c_136_, v___x_141_);
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_toLower___boxed(lean_object* v_c_143_){
_start:
{
uint32_t v_c_boxed_144_; uint32_t v_res_145_; lean_object* v_r_146_; 
v_c_boxed_144_ = lean_unbox_uint32(v_c_143_);
lean_dec(v_c_143_);
v_res_145_ = l_Char_toLower(v_c_boxed_144_);
v_r_146_ = lean_box_uint32(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT uint32_t l_Char_toUpper(uint32_t v_c_147_){
_start:
{
uint32_t v___x_148_; uint8_t v___x_149_; 
v___x_148_ = 97;
v___x_149_ = lean_uint32_dec_le(v___x_148_, v_c_147_);
if (v___x_149_ == 0)
{
return v_c_147_;
}
else
{
uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_150_ = 122;
v___x_151_ = lean_uint32_dec_le(v_c_147_, v___x_150_);
if (v___x_151_ == 0)
{
return v_c_147_;
}
else
{
uint32_t v___x_152_; uint32_t v___x_153_; 
v___x_152_ = 4294967264;
v___x_153_ = lean_uint32_add(v_c_147_, v___x_152_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_toUpper___boxed(lean_object* v_c_154_){
_start:
{
uint32_t v_c_boxed_155_; uint32_t v_res_156_; lean_object* v_r_157_; 
v_c_boxed_155_ = lean_unbox_uint32(v_c_154_);
lean_dec(v_c_154_);
v_res_156_ = l_Char_toUpper(v_c_boxed_155_);
v_r_157_ = lean_box_uint32(v_res_156_);
return v_r_157_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
