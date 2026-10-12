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
uint8_t l_Char_instDecidableLt(uint32_t v_a_3_, uint32_t v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_uint32_dec_lt(v_a_3_, v_b_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l_Char_instDecidableLt_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_3_ = stack[0].m_num;
uint32_t v_b_4_ = stack[1].m_num;
uint8_t v_res_6_;
v_res_6_ = l_Char_instDecidableLt(v_a_3_, v_b_4_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Char_instDecidableLt___boxed(lean_object* v_a_7_, lean_object* v_b_8_){
_start:
{
uint32_t v_a_boxed_9_; uint32_t v_b_boxed_10_; uint8_t v_res_11_; lean_object* v_r_12_; 
v_a_boxed_9_ = lean_unbox_uint32(v_a_7_);
lean_dec(v_a_7_);
v_b_boxed_10_ = lean_unbox_uint32(v_b_8_);
lean_dec(v_b_8_);
v_res_11_ = l_Char_instDecidableLt(v_a_boxed_9_, v_b_boxed_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
uint8_t l_Char_instDecidableLe(uint32_t v_a_13_, uint32_t v_b_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = lean_uint32_dec_le(v_a_13_, v_b_14_);
return v___x_15_;
}
}
LEAN_EXPORT void l_Char_instDecidableLe_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_13_ = stack[0].m_num;
uint32_t v_b_14_ = stack[1].m_num;
uint8_t v_res_16_;
v_res_16_ = l_Char_instDecidableLe(v_a_13_, v_b_14_);
stack->m_num = v_res_16_;
}
LEAN_EXPORT lean_object* l_Char_instDecidableLe___boxed(lean_object* v_a_17_, lean_object* v_b_18_){
_start:
{
uint32_t v_a_boxed_19_; uint32_t v_b_boxed_20_; uint8_t v_res_21_; lean_object* v_r_22_; 
v_a_boxed_19_ = lean_unbox_uint32(v_a_17_);
lean_dec(v_a_17_);
v_b_boxed_20_ = lean_unbox_uint32(v_b_18_);
lean_dec(v_b_18_);
v_res_21_ = l_Char_instDecidableLe(v_a_boxed_19_, v_b_boxed_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
lean_object* l_Char_toNat(uint32_t v_c_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_uint32_to_nat(v_c_23_);
return v___x_24_;
}
}
LEAN_EXPORT void l_Char_toNat_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_23_ = stack[0].m_num;
lean_object* v_res_25_;
v_res_25_ = l_Char_toNat(v_c_23_);
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l_Char_toNat___boxed(lean_object* v_c_26_){
_start:
{
uint32_t v_c_boxed_27_; lean_object* v_res_28_; 
v_c_boxed_27_ = lean_unbox_uint32(v_c_26_);
lean_dec(v_c_26_);
v_res_28_ = l_Char_toNat(v_c_boxed_27_);
return v_res_28_;
}
}
uint8_t l_Char_toUInt8(uint32_t v_c_29_){
_start:
{
uint8_t v___x_30_; 
v___x_30_ = lean_uint32_to_uint8(v_c_29_);
return v___x_30_;
}
}
LEAN_EXPORT void l_Char_toUInt8_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_29_ = stack[0].m_num;
uint8_t v_res_31_;
v_res_31_ = l_Char_toUInt8(v_c_29_);
stack->m_num = v_res_31_;
}
LEAN_EXPORT lean_object* l_Char_toUInt8___boxed(lean_object* v_c_32_){
_start:
{
uint32_t v_c_boxed_33_; uint8_t v_res_34_; lean_object* v_r_35_; 
v_c_boxed_33_ = lean_unbox_uint32(v_c_32_);
lean_dec(v_c_32_);
v_res_34_ = l_Char_toUInt8(v_c_boxed_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
uint32_t l_Char_ofUInt8(uint8_t v_n_36_){
_start:
{
uint32_t v___x_37_; 
v___x_37_ = lean_uint8_to_uint32(v_n_36_);
return v___x_37_;
}
}
LEAN_EXPORT void l_Char_ofUInt8_0interp(lean_interpreter_value* stack)
{
uint8_t v_n_36_ = stack[0].m_num;
uint32_t v_res_38_;
v_res_38_ = l_Char_ofUInt8(v_n_36_);
stack->m_num = v_res_38_;
}
LEAN_EXPORT lean_object* l_Char_ofUInt8___boxed(lean_object* v_n_39_){
_start:
{
uint8_t v_n_boxed_40_; uint32_t v_res_41_; lean_object* v_r_42_; 
v_n_boxed_40_ = lean_unbox(v_n_39_);
v_res_41_ = l_Char_ofUInt8(v_n_boxed_40_);
v_r_42_ = lean_box_uint32(v_res_41_);
return v_r_42_;
}
}
static uint32_t _init_l_Char_instInhabited(void){
_start:
{
uint32_t v___x_43_; 
v___x_43_ = 65;
return v___x_43_;
}
}
uint8_t l_Char_isWhitespace(uint32_t v_c_44_){
_start:
{
uint32_t v___x_45_; uint8_t v___x_46_; 
v___x_45_ = 32;
v___x_46_ = lean_uint32_dec_eq(v_c_44_, v___x_45_);
if (v___x_46_ == 0)
{
uint32_t v___x_47_; uint8_t v___x_48_; 
v___x_47_ = 9;
v___x_48_ = lean_uint32_dec_eq(v_c_44_, v___x_47_);
if (v___x_48_ == 0)
{
uint32_t v___x_49_; uint8_t v___x_50_; 
v___x_49_ = 13;
v___x_50_ = lean_uint32_dec_eq(v_c_44_, v___x_49_);
if (v___x_50_ == 0)
{
uint32_t v___x_51_; uint8_t v___x_52_; 
v___x_51_ = 10;
v___x_52_ = lean_uint32_dec_eq(v_c_44_, v___x_51_);
return v___x_52_;
}
else
{
return v___x_50_;
}
}
else
{
return v___x_48_;
}
}
else
{
return v___x_46_;
}
}
}
LEAN_EXPORT void l_Char_isWhitespace_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_44_ = stack[0].m_num;
uint8_t v_res_53_;
v_res_53_ = l_Char_isWhitespace(v_c_44_);
stack->m_num = v_res_53_;
}
LEAN_EXPORT lean_object* l_Char_isWhitespace___boxed(lean_object* v_c_54_){
_start:
{
uint32_t v_c_boxed_55_; uint8_t v_res_56_; lean_object* v_r_57_; 
v_c_boxed_55_ = lean_unbox_uint32(v_c_54_);
lean_dec(v_c_54_);
v_res_56_ = l_Char_isWhitespace(v_c_boxed_55_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
uint8_t l_Char_isUpper(uint32_t v_c_58_){
_start:
{
uint32_t v___x_59_; uint8_t v___x_60_; 
v___x_59_ = 65;
v___x_60_ = lean_uint32_dec_le(v___x_59_, v_c_58_);
if (v___x_60_ == 0)
{
return v___x_60_;
}
else
{
uint32_t v___x_61_; uint8_t v___x_62_; 
v___x_61_ = 90;
v___x_62_ = lean_uint32_dec_le(v_c_58_, v___x_61_);
return v___x_62_;
}
}
}
LEAN_EXPORT void l_Char_isUpper_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_58_ = stack[0].m_num;
uint8_t v_res_63_;
v_res_63_ = l_Char_isUpper(v_c_58_);
stack->m_num = v_res_63_;
}
LEAN_EXPORT lean_object* l_Char_isUpper___boxed(lean_object* v_c_64_){
_start:
{
uint32_t v_c_boxed_65_; uint8_t v_res_66_; lean_object* v_r_67_; 
v_c_boxed_65_ = lean_unbox_uint32(v_c_64_);
lean_dec(v_c_64_);
v_res_66_ = l_Char_isUpper(v_c_boxed_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
uint8_t l_Char_isLower(uint32_t v_c_68_){
_start:
{
uint32_t v___x_69_; uint8_t v___x_70_; 
v___x_69_ = 97;
v___x_70_ = lean_uint32_dec_le(v___x_69_, v_c_68_);
if (v___x_70_ == 0)
{
return v___x_70_;
}
else
{
uint32_t v___x_71_; uint8_t v___x_72_; 
v___x_71_ = 122;
v___x_72_ = lean_uint32_dec_le(v_c_68_, v___x_71_);
return v___x_72_;
}
}
}
LEAN_EXPORT void l_Char_isLower_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_68_ = stack[0].m_num;
uint8_t v_res_73_;
v_res_73_ = l_Char_isLower(v_c_68_);
stack->m_num = v_res_73_;
}
LEAN_EXPORT lean_object* l_Char_isLower___boxed(lean_object* v_c_74_){
_start:
{
uint32_t v_c_boxed_75_; uint8_t v_res_76_; lean_object* v_r_77_; 
v_c_boxed_75_ = lean_unbox_uint32(v_c_74_);
lean_dec(v_c_74_);
v_res_76_ = l_Char_isLower(v_c_boxed_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
uint8_t l_Char_isAlpha(uint32_t v_c_78_){
_start:
{
uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 65;
v___x_85_ = lean_uint32_dec_le(v___x_84_, v_c_78_);
if (v___x_85_ == 0)
{
goto v___jp_79_;
}
else
{
uint32_t v___x_86_; uint8_t v___x_87_; 
v___x_86_ = 90;
v___x_87_ = lean_uint32_dec_le(v_c_78_, v___x_86_);
if (v___x_87_ == 0)
{
goto v___jp_79_;
}
else
{
return v___x_87_;
}
}
v___jp_79_:
{
uint32_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 97;
v___x_81_ = lean_uint32_dec_le(v___x_80_, v_c_78_);
if (v___x_81_ == 0)
{
return v___x_81_;
}
else
{
uint32_t v___x_82_; uint8_t v___x_83_; 
v___x_82_ = 122;
v___x_83_ = lean_uint32_dec_le(v_c_78_, v___x_82_);
return v___x_83_;
}
}
}
}
LEAN_EXPORT void l_Char_isAlpha_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_78_ = stack[0].m_num;
uint8_t v_res_88_;
v_res_88_ = l_Char_isAlpha(v_c_78_);
stack->m_num = v_res_88_;
}
LEAN_EXPORT lean_object* l_Char_isAlpha___boxed(lean_object* v_c_89_){
_start:
{
uint32_t v_c_boxed_90_; uint8_t v_res_91_; lean_object* v_r_92_; 
v_c_boxed_90_ = lean_unbox_uint32(v_c_89_);
lean_dec(v_c_89_);
v_res_91_ = l_Char_isAlpha(v_c_boxed_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
uint8_t l_Char_isDigit(uint32_t v_c_93_){
_start:
{
uint32_t v___x_94_; uint8_t v___x_95_; 
v___x_94_ = 48;
v___x_95_ = lean_uint32_dec_le(v___x_94_, v_c_93_);
if (v___x_95_ == 0)
{
return v___x_95_;
}
else
{
uint32_t v___x_96_; uint8_t v___x_97_; 
v___x_96_ = 57;
v___x_97_ = lean_uint32_dec_le(v_c_93_, v___x_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT void l_Char_isDigit_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_93_ = stack[0].m_num;
uint8_t v_res_98_;
v_res_98_ = l_Char_isDigit(v_c_93_);
stack->m_num = v_res_98_;
}
LEAN_EXPORT lean_object* l_Char_isDigit___boxed(lean_object* v_c_99_){
_start:
{
uint32_t v_c_boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v_c_boxed_100_ = lean_unbox_uint32(v_c_99_);
lean_dec(v_c_99_);
v_res_101_ = l_Char_isDigit(v_c_boxed_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
uint8_t l_Char_isHexDigit(uint32_t v_c_103_){
_start:
{
uint32_t v___x_114_; uint8_t v___x_115_; 
v___x_114_ = 48;
v___x_115_ = lean_uint32_dec_le(v___x_114_, v_c_103_);
if (v___x_115_ == 0)
{
goto v___jp_109_;
}
else
{
uint32_t v___x_116_; uint8_t v___x_117_; 
v___x_116_ = 57;
v___x_117_ = lean_uint32_dec_le(v_c_103_, v___x_116_);
if (v___x_117_ == 0)
{
goto v___jp_109_;
}
else
{
return v___x_117_;
}
}
v___jp_104_:
{
uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_105_ = 65;
v___x_106_ = lean_uint32_dec_le(v___x_105_, v_c_103_);
if (v___x_106_ == 0)
{
return v___x_106_;
}
else
{
uint32_t v___x_107_; uint8_t v___x_108_; 
v___x_107_ = 70;
v___x_108_ = lean_uint32_dec_le(v_c_103_, v___x_107_);
return v___x_108_;
}
}
v___jp_109_:
{
uint32_t v___x_110_; uint8_t v___x_111_; 
v___x_110_ = 97;
v___x_111_ = lean_uint32_dec_le(v___x_110_, v_c_103_);
if (v___x_111_ == 0)
{
goto v___jp_104_;
}
else
{
uint32_t v___x_112_; uint8_t v___x_113_; 
v___x_112_ = 102;
v___x_113_ = lean_uint32_dec_le(v_c_103_, v___x_112_);
if (v___x_113_ == 0)
{
goto v___jp_104_;
}
else
{
return v___x_113_;
}
}
}
}
}
LEAN_EXPORT void l_Char_isHexDigit_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_103_ = stack[0].m_num;
uint8_t v_res_118_;
v_res_118_ = l_Char_isHexDigit(v_c_103_);
stack->m_num = v_res_118_;
}
LEAN_EXPORT lean_object* l_Char_isHexDigit___boxed(lean_object* v_c_119_){
_start:
{
uint32_t v_c_boxed_120_; uint8_t v_res_121_; lean_object* v_r_122_; 
v_c_boxed_120_ = lean_unbox_uint32(v_c_119_);
lean_dec(v_c_119_);
v_res_121_ = l_Char_isHexDigit(v_c_boxed_120_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
uint8_t l_Char_isAlphanum(uint32_t v_c_123_){
_start:
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 65;
v___x_135_ = lean_uint32_dec_le(v___x_134_, v_c_123_);
if (v___x_135_ == 0)
{
goto v___jp_129_;
}
else
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 90;
v___x_137_ = lean_uint32_dec_le(v_c_123_, v___x_136_);
if (v___x_137_ == 0)
{
goto v___jp_129_;
}
else
{
return v___x_137_;
}
}
v___jp_124_:
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 48;
v___x_126_ = lean_uint32_dec_le(v___x_125_, v_c_123_);
if (v___x_126_ == 0)
{
return v___x_126_;
}
else
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 57;
v___x_128_ = lean_uint32_dec_le(v_c_123_, v___x_127_);
return v___x_128_;
}
}
v___jp_129_:
{
uint32_t v___x_130_; uint8_t v___x_131_; 
v___x_130_ = 97;
v___x_131_ = lean_uint32_dec_le(v___x_130_, v_c_123_);
if (v___x_131_ == 0)
{
goto v___jp_124_;
}
else
{
uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 122;
v___x_133_ = lean_uint32_dec_le(v_c_123_, v___x_132_);
if (v___x_133_ == 0)
{
goto v___jp_124_;
}
else
{
return v___x_133_;
}
}
}
}
}
LEAN_EXPORT void l_Char_isAlphanum_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_123_ = stack[0].m_num;
uint8_t v_res_138_;
v_res_138_ = l_Char_isAlphanum(v_c_123_);
stack->m_num = v_res_138_;
}
LEAN_EXPORT lean_object* l_Char_isAlphanum___boxed(lean_object* v_c_139_){
_start:
{
uint32_t v_c_boxed_140_; uint8_t v_res_141_; lean_object* v_r_142_; 
v_c_boxed_140_ = lean_unbox_uint32(v_c_139_);
lean_dec(v_c_139_);
v_res_141_ = l_Char_isAlphanum(v_c_boxed_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
uint32_t l_Char_toLower(uint32_t v_c_143_){
_start:
{
uint32_t v___x_144_; uint8_t v___x_145_; 
v___x_144_ = 65;
v___x_145_ = lean_uint32_dec_le(v___x_144_, v_c_143_);
if (v___x_145_ == 0)
{
return v_c_143_;
}
else
{
uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_146_ = 90;
v___x_147_ = lean_uint32_dec_le(v_c_143_, v___x_146_);
if (v___x_147_ == 0)
{
return v_c_143_;
}
else
{
uint32_t v___x_148_; uint32_t v___x_149_; 
v___x_148_ = 32;
v___x_149_ = lean_uint32_add(v_c_143_, v___x_148_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT void l_Char_toLower_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_143_ = stack[0].m_num;
uint32_t v_res_150_;
v_res_150_ = l_Char_toLower(v_c_143_);
stack->m_num = v_res_150_;
}
LEAN_EXPORT lean_object* l_Char_toLower___boxed(lean_object* v_c_151_){
_start:
{
uint32_t v_c_boxed_152_; uint32_t v_res_153_; lean_object* v_r_154_; 
v_c_boxed_152_ = lean_unbox_uint32(v_c_151_);
lean_dec(v_c_151_);
v_res_153_ = l_Char_toLower(v_c_boxed_152_);
v_r_154_ = lean_box_uint32(v_res_153_);
return v_r_154_;
}
}
uint32_t l_Char_toUpper(uint32_t v_c_155_){
_start:
{
uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 97;
v___x_157_ = lean_uint32_dec_le(v___x_156_, v_c_155_);
if (v___x_157_ == 0)
{
return v_c_155_;
}
else
{
uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_158_ = 122;
v___x_159_ = lean_uint32_dec_le(v_c_155_, v___x_158_);
if (v___x_159_ == 0)
{
return v_c_155_;
}
else
{
uint32_t v___x_160_; uint32_t v___x_161_; 
v___x_160_ = 4294967264;
v___x_161_ = lean_uint32_add(v_c_155_, v___x_160_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT void l_Char_toUpper_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_155_ = stack[0].m_num;
uint32_t v_res_162_;
v_res_162_ = l_Char_toUpper(v_c_155_);
stack->m_num = v_res_162_;
}
LEAN_EXPORT lean_object* l_Char_toUpper___boxed(lean_object* v_c_163_){
_start:
{
uint32_t v_c_boxed_164_; uint32_t v_res_165_; lean_object* v_r_166_; 
v_c_boxed_164_ = lean_unbox_uint32(v_c_163_);
lean_dec(v_c_163_);
v_res_165_ = l_Char_toUpper(v_c_boxed_164_);
v_r_166_ = lean_box_uint32(v_res_165_);
return v_r_166_;
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
