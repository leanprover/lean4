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
uint32_t v___x_76_; uint8_t v___x_77_; 
v___x_76_ = 65;
v___x_77_ = lean_uint32_dec_le(v___x_76_, v_c_70_);
if (v___x_77_ == 0)
{
goto v___jp_71_;
}
else
{
uint32_t v___x_78_; uint8_t v___x_79_; 
v___x_78_ = 90;
v___x_79_ = lean_uint32_dec_le(v_c_70_, v___x_78_);
if (v___x_79_ == 0)
{
goto v___jp_71_;
}
else
{
return v___x_79_;
}
}
v___jp_71_:
{
uint32_t v___x_72_; uint8_t v___x_73_; 
v___x_72_ = 97;
v___x_73_ = lean_uint32_dec_le(v___x_72_, v_c_70_);
if (v___x_73_ == 0)
{
return v___x_73_;
}
else
{
uint32_t v___x_74_; uint8_t v___x_75_; 
v___x_74_ = 122;
v___x_75_ = lean_uint32_dec_le(v_c_70_, v___x_74_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isAlpha___boxed(lean_object* v_c_80_){
_start:
{
uint32_t v_c_boxed_81_; uint8_t v_res_82_; lean_object* v_r_83_; 
v_c_boxed_81_ = lean_unbox_uint32(v_c_80_);
lean_dec(v_c_80_);
v_res_82_ = l_Char_isAlpha(v_c_boxed_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l_Char_isDigit(uint32_t v_c_84_){
_start:
{
uint32_t v___x_85_; uint8_t v___x_86_; 
v___x_85_ = 48;
v___x_86_ = lean_uint32_dec_le(v___x_85_, v_c_84_);
if (v___x_86_ == 0)
{
return v___x_86_;
}
else
{
uint32_t v___x_87_; uint8_t v___x_88_; 
v___x_87_ = 57;
v___x_88_ = lean_uint32_dec_le(v_c_84_, v___x_87_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Char_isDigit___boxed(lean_object* v_c_89_){
_start:
{
uint32_t v_c_boxed_90_; uint8_t v_res_91_; lean_object* v_r_92_; 
v_c_boxed_90_ = lean_unbox_uint32(v_c_89_);
lean_dec(v_c_89_);
v_res_91_ = l_Char_isDigit(v_c_boxed_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT uint8_t l_Char_isHexDigit(uint32_t v_c_93_){
_start:
{
uint32_t v___x_104_; uint8_t v___x_105_; 
v___x_104_ = 48;
v___x_105_ = lean_uint32_dec_le(v___x_104_, v_c_93_);
if (v___x_105_ == 0)
{
goto v___jp_99_;
}
else
{
uint32_t v___x_106_; uint8_t v___x_107_; 
v___x_106_ = 57;
v___x_107_ = lean_uint32_dec_le(v_c_93_, v___x_106_);
if (v___x_107_ == 0)
{
goto v___jp_99_;
}
else
{
return v___x_107_;
}
}
v___jp_94_:
{
uint32_t v___x_95_; uint8_t v___x_96_; 
v___x_95_ = 65;
v___x_96_ = lean_uint32_dec_le(v___x_95_, v_c_93_);
if (v___x_96_ == 0)
{
return v___x_96_;
}
else
{
uint32_t v___x_97_; uint8_t v___x_98_; 
v___x_97_ = 70;
v___x_98_ = lean_uint32_dec_le(v_c_93_, v___x_97_);
return v___x_98_;
}
}
v___jp_99_:
{
uint32_t v___x_100_; uint8_t v___x_101_; 
v___x_100_ = 97;
v___x_101_ = lean_uint32_dec_le(v___x_100_, v_c_93_);
if (v___x_101_ == 0)
{
goto v___jp_94_;
}
else
{
uint32_t v___x_102_; uint8_t v___x_103_; 
v___x_102_ = 102;
v___x_103_ = lean_uint32_dec_le(v_c_93_, v___x_102_);
if (v___x_103_ == 0)
{
goto v___jp_94_;
}
else
{
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isHexDigit___boxed(lean_object* v_c_108_){
_start:
{
uint32_t v_c_boxed_109_; uint8_t v_res_110_; lean_object* v_r_111_; 
v_c_boxed_109_ = lean_unbox_uint32(v_c_108_);
lean_dec(v_c_108_);
v_res_110_ = l_Char_isHexDigit(v_c_boxed_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT uint8_t l_Char_isAlphanum(uint32_t v_c_112_){
_start:
{
uint32_t v___x_123_; uint8_t v___x_124_; 
v___x_123_ = 65;
v___x_124_ = lean_uint32_dec_le(v___x_123_, v_c_112_);
if (v___x_124_ == 0)
{
goto v___jp_118_;
}
else
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 90;
v___x_126_ = lean_uint32_dec_le(v_c_112_, v___x_125_);
if (v___x_126_ == 0)
{
goto v___jp_118_;
}
else
{
return v___x_126_;
}
}
v___jp_113_:
{
uint32_t v___x_114_; uint8_t v___x_115_; 
v___x_114_ = 48;
v___x_115_ = lean_uint32_dec_le(v___x_114_, v_c_112_);
if (v___x_115_ == 0)
{
return v___x_115_;
}
else
{
uint32_t v___x_116_; uint8_t v___x_117_; 
v___x_116_ = 57;
v___x_117_ = lean_uint32_dec_le(v_c_112_, v___x_116_);
return v___x_117_;
}
}
v___jp_118_:
{
uint32_t v___x_119_; uint8_t v___x_120_; 
v___x_119_ = 97;
v___x_120_ = lean_uint32_dec_le(v___x_119_, v_c_112_);
if (v___x_120_ == 0)
{
goto v___jp_113_;
}
else
{
uint32_t v___x_121_; uint8_t v___x_122_; 
v___x_121_ = 122;
v___x_122_ = lean_uint32_dec_le(v_c_112_, v___x_121_);
if (v___x_122_ == 0)
{
goto v___jp_113_;
}
else
{
return v___x_122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isAlphanum___boxed(lean_object* v_c_127_){
_start:
{
uint32_t v_c_boxed_128_; uint8_t v_res_129_; lean_object* v_r_130_; 
v_c_boxed_128_ = lean_unbox_uint32(v_c_127_);
lean_dec(v_c_127_);
v_res_129_ = l_Char_isAlphanum(v_c_boxed_128_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT uint32_t l_Char_toLower(uint32_t v_c_131_){
_start:
{
uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 65;
v___x_133_ = lean_uint32_dec_le(v___x_132_, v_c_131_);
if (v___x_133_ == 0)
{
return v_c_131_;
}
else
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 90;
v___x_135_ = lean_uint32_dec_le(v_c_131_, v___x_134_);
if (v___x_135_ == 0)
{
return v_c_131_;
}
else
{
uint32_t v___x_136_; uint32_t v___x_137_; 
v___x_136_ = 32;
v___x_137_ = lean_uint32_add(v_c_131_, v___x_136_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_toLower___boxed(lean_object* v_c_138_){
_start:
{
uint32_t v_c_boxed_139_; uint32_t v_res_140_; lean_object* v_r_141_; 
v_c_boxed_139_ = lean_unbox_uint32(v_c_138_);
lean_dec(v_c_138_);
v_res_140_ = l_Char_toLower(v_c_boxed_139_);
v_r_141_ = lean_box_uint32(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT uint32_t l_Char_toUpper(uint32_t v_c_142_){
_start:
{
uint32_t v___x_143_; uint8_t v___x_144_; 
v___x_143_ = 97;
v___x_144_ = lean_uint32_dec_le(v___x_143_, v_c_142_);
if (v___x_144_ == 0)
{
return v_c_142_;
}
else
{
uint32_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = 122;
v___x_146_ = lean_uint32_dec_le(v_c_142_, v___x_145_);
if (v___x_146_ == 0)
{
return v_c_142_;
}
else
{
uint32_t v___x_147_; uint32_t v___x_148_; 
v___x_147_ = 4294967264;
v___x_148_ = lean_uint32_add(v_c_142_, v___x_147_);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_toUpper___boxed(lean_object* v_c_149_){
_start:
{
uint32_t v_c_boxed_150_; uint32_t v_res_151_; lean_object* v_r_152_; 
v_c_boxed_150_ = lean_unbox_uint32(v_c_149_);
lean_dec(v_c_149_);
v_res_151_ = l_Char_toUpper(v_c_boxed_150_);
v_r_152_ = lean_box_uint32(v_res_151_);
return v_r_152_;
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
