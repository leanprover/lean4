// Lean compiler output
// Module: Lake.Util.String
// Imports: public import Init.Data.ToString.Basic import Init.Data.UInt.Lemmas import Init.Data.String.Basic import Init.Data.Nat.Fold import Init.Data.String.Length
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
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
uint32_t lean_uint8_to_uint32(uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_land(uint64_t, uint64_t);
uint8_t lean_uint64_to_uint8(uint64_t);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpadAscii_spec__0(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpadAscii_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_lpadAscii___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_lpadAscii___closed__0 = (const lean_object*)&l_Lake_lpadAscii___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_lpadAscii(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_lpadAscii___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rpadAscii(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rpadAscii___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_zpad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_zpad___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_isHex(lean_object*);
LEAN_EXPORT lean_object* l_Lake_isHex___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Util_String_0__Lake_lowerHexByte(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Util_String_0__Lake_lowerHexByte___boxed(lean_object*);
LEAN_EXPORT uint32_t l___private_Lake_Util_String_0__Lake_lowerHexChar(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Util_String_0__Lake_lowerHexChar___boxed(lean_object*);
static lean_once_cell_t l_Lake_lowerHexUInt64___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_lowerHexUInt64___closed__0;
static lean_once_cell_t l_Lake_lowerHexUInt64___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_lowerHexUInt64___closed__1;
LEAN_EXPORT lean_object* l_Lake_lowerHexUInt64(uint64_t);
LEAN_EXPORT lean_object* l_Lake_lowerHexUInt64___boxed(lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpadAscii_spec__0(uint32_t v_c_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_2_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_dec(v_x_2_);
return v_x_3_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_x_2_, v_one_6_);
lean_dec(v_x_2_);
v___x_8_ = lean_string_push(v_x_3_, v_c_1_);
v_x_2_ = v_n_7_;
v_x_3_ = v___x_8_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpadAscii_spec__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1_ = stack[0].m_num;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v_x_3_ = stack[2].m_obj;
lean_object* v_res_10_;
v_res_10_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpadAscii_spec__0(v_c_1_, v_x_2_, v_x_3_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpadAscii_spec__0___boxed(lean_object* v_c_11_, lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
uint32_t v_c_boxed_14_; lean_object* v_res_15_; 
v_c_boxed_14_ = lean_unbox_uint32(v_c_11_);
lean_dec(v_c_11_);
v_res_15_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpadAscii_spec__0(v_c_boxed_14_, v_x_12_, v_x_13_);
return v_res_15_;
}
}
lean_object* l_Lake_lpadAscii(lean_object* v_s_17_, uint32_t v_c_18_, lean_object* v_len_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_20_ = ((lean_object*)(l_Lake_lpadAscii___closed__0));
v___x_21_ = lean_string_utf8_byte_size(v_s_17_);
v___x_22_ = lean_nat_sub(v_len_19_, v___x_21_);
v___x_23_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpadAscii_spec__0(v_c_18_, v___x_22_, v___x_20_);
v___x_24_ = lean_string_append(v___x_23_, v_s_17_);
return v___x_24_;
}
}
LEAN_EXPORT void l_Lake_lpadAscii_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_17_ = stack[0].m_obj;
uint32_t v_c_18_ = stack[1].m_num;
lean_object* v_len_19_ = stack[2].m_obj;
lean_object* v_res_25_;
v_res_25_ = l_Lake_lpadAscii(v_s_17_, v_c_18_, v_len_19_);
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lake_lpadAscii___boxed(lean_object* v_s_26_, lean_object* v_c_27_, lean_object* v_len_28_){
_start:
{
uint32_t v_c_boxed_29_; lean_object* v_res_30_; 
v_c_boxed_29_ = lean_unbox_uint32(v_c_27_);
lean_dec(v_c_27_);
v_res_30_ = l_Lake_lpadAscii(v_s_26_, v_c_boxed_29_, v_len_28_);
lean_dec(v_len_28_);
lean_dec_ref(v_s_26_);
return v_res_30_;
}
}
lean_object* l_Lake_rpadAscii(lean_object* v_s_31_, uint32_t v_c_32_, lean_object* v_len_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_string_utf8_byte_size(v_s_31_);
v___x_35_ = lean_nat_sub(v_len_33_, v___x_34_);
v___x_36_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpadAscii_spec__0(v_c_32_, v___x_35_, v_s_31_);
return v___x_36_;
}
}
LEAN_EXPORT void l_Lake_rpadAscii_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_31_ = stack[0].m_obj;
uint32_t v_c_32_ = stack[1].m_num;
lean_object* v_len_33_ = stack[2].m_obj;
lean_object* v_res_37_;
v_res_37_ = l_Lake_rpadAscii(v_s_31_, v_c_32_, v_len_33_);
stack->m_obj
 = v_res_37_;
}
LEAN_EXPORT lean_object* l_Lake_rpadAscii___boxed(lean_object* v_s_38_, lean_object* v_c_39_, lean_object* v_len_40_){
_start:
{
uint32_t v_c_boxed_41_; lean_object* v_res_42_; 
v_c_boxed_41_ = lean_unbox_uint32(v_c_39_);
lean_dec(v_c_39_);
v_res_42_ = l_Lake_rpadAscii(v_s_38_, v_c_boxed_41_, v_len_40_);
lean_dec(v_len_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_zpad(lean_object* v_n_43_, lean_object* v_len_44_){
_start:
{
lean_object* v___x_45_; uint32_t v___x_46_; lean_object* v___x_47_; 
v___x_45_ = l_Nat_reprFast(v_n_43_);
v___x_46_ = 48;
v___x_47_ = l_Lake_lpadAscii(v___x_45_, v___x_46_, v_len_44_);
lean_dec_ref(v___x_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_zpad___boxed(lean_object* v_n_48_, lean_object* v_len_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lake_zpad(v_n_48_, v_len_49_);
lean_dec(v_len_49_);
return v_res_50_;
}
}
uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(lean_object* v_s_51_, lean_object* v_n_52_, lean_object* v_i_53_){
_start:
{
lean_object* v_zero_54_; uint8_t v_isZero_55_; 
v_zero_54_ = lean_unsigned_to_nat(0u);
v_isZero_55_ = lean_nat_dec_eq(v_i_53_, v_zero_54_);
if (v_isZero_55_ == 1)
{
lean_dec(v_i_53_);
return v_isZero_55_;
}
else
{
lean_object* v_one_56_; lean_object* v_n_57_; uint8_t v___y_59_; lean_object* v___x_61_; uint8_t v_c_62_; uint8_t v___x_63_; uint8_t v___x_64_; 
v_one_56_ = lean_unsigned_to_nat(1u);
v_n_57_ = lean_nat_sub(v_i_53_, v_one_56_);
v___x_61_ = lean_nat_sub(v_n_52_, v_i_53_);
lean_dec(v_i_53_);
v_c_62_ = lean_string_get_byte_fast(v_s_51_, v___x_61_);
v___x_63_ = 57;
v___x_64_ = lean_uint8_dec_le(v_c_62_, v___x_63_);
if (v___x_64_ == 0)
{
uint8_t v___x_65_; uint8_t v___x_66_; 
v___x_65_ = 102;
v___x_66_ = lean_uint8_dec_le(v_c_62_, v___x_65_);
if (v___x_66_ == 0)
{
uint8_t v___x_67_; uint8_t v___x_68_; 
v___x_67_ = 70;
v___x_68_ = lean_uint8_dec_le(v_c_62_, v___x_67_);
if (v___x_68_ == 0)
{
lean_dec(v_n_57_);
return v___x_68_;
}
else
{
uint8_t v___x_69_; uint8_t v___x_70_; 
v___x_69_ = 65;
v___x_70_ = lean_uint8_dec_le(v___x_69_, v_c_62_);
v___y_59_ = v___x_70_;
goto v___jp_58_;
}
}
else
{
uint8_t v___x_71_; uint8_t v___x_72_; 
v___x_71_ = 97;
v___x_72_ = lean_uint8_dec_le(v___x_71_, v_c_62_);
v___y_59_ = v___x_72_;
goto v___jp_58_;
}
}
else
{
uint8_t v___x_73_; uint8_t v___x_74_; 
v___x_73_ = 48;
v___x_74_ = lean_uint8_dec_le(v___x_73_, v_c_62_);
v___y_59_ = v___x_74_;
goto v___jp_58_;
}
v___jp_58_:
{
if (v___y_59_ == 0)
{
lean_dec(v_n_57_);
return v___y_59_;
}
else
{
v_i_53_ = v_n_57_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_51_ = stack[0].m_obj;
lean_object* v_n_52_ = stack[1].m_obj;
lean_object* v_i_53_ = stack[2].m_obj;
uint8_t v_res_75_;
v_res_75_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(v_s_51_, v_n_52_, v_i_53_);
stack->m_num = v_res_75_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg___boxed(lean_object* v_s_76_, lean_object* v_n_77_, lean_object* v_i_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(v_s_76_, v_n_77_, v_i_78_);
lean_dec(v_n_77_);
lean_dec_ref(v_s_76_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
uint8_t l_Lake_isHex(lean_object* v_s_81_){
_start:
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = lean_string_utf8_byte_size(v_s_81_);
v___x_83_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(v_s_81_, v___x_82_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT void l_Lake_isHex_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_81_ = stack[0].m_obj;
uint8_t v_res_84_;
v_res_84_ = l_Lake_isHex(v_s_81_);
stack->m_num = v_res_84_;
}
LEAN_EXPORT lean_object* l_Lake_isHex___boxed(lean_object* v_s_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Lake_isHex(v_s_85_);
lean_dec_ref(v_s_85_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0(lean_object* v_s_88_, lean_object* v_n_89_, lean_object* v_i_90_, lean_object* v_a_91_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(v_s_88_, v_n_89_, v_i_90_);
return v___x_92_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_88_ = stack[0].m_obj;
lean_object* v_n_89_ = stack[1].m_obj;
lean_object* v_i_90_ = stack[2].m_obj;
uint8_t v_res_93_;
v_res_93_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0(v_s_88_, v_n_89_, v_i_90_, lean_box(0));
stack->m_num = v_res_93_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___boxed(lean_object* v_s_94_, lean_object* v_n_95_, lean_object* v_i_96_, lean_object* v_a_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0(v_s_94_, v_n_95_, v_i_96_, v_a_97_);
lean_dec(v_n_95_);
lean_dec_ref(v_s_94_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
uint8_t l___private_Lake_Util_String_0__Lake_lowerHexByte(uint8_t v_n_100_){
_start:
{
uint8_t v___x_101_; uint8_t v___x_102_; 
v___x_101_ = 9;
v___x_102_ = lean_uint8_dec_le(v_n_100_, v___x_101_);
if (v___x_102_ == 0)
{
uint8_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = 87;
v___x_104_ = lean_uint8_add(v_n_100_, v___x_103_);
return v___x_104_;
}
else
{
uint8_t v___x_105_; uint8_t v___x_106_; 
v___x_105_ = 48;
v___x_106_ = lean_uint8_add(v_n_100_, v___x_105_);
return v___x_106_;
}
}
}
LEAN_EXPORT void l___private_Lake_Util_String_0__Lake_lowerHexByte_0interp(lean_interpreter_value* stack)
{
uint8_t v_n_100_ = stack[0].m_num;
uint8_t v_res_107_;
v_res_107_ = l___private_Lake_Util_String_0__Lake_lowerHexByte(v_n_100_);
stack->m_num = v_res_107_;
}
LEAN_EXPORT lean_object* l___private_Lake_Util_String_0__Lake_lowerHexByte___boxed(lean_object* v_n_108_){
_start:
{
uint8_t v_n_boxed_109_; uint8_t v_res_110_; lean_object* v_r_111_; 
v_n_boxed_109_ = lean_unbox(v_n_108_);
v_res_110_ = l___private_Lake_Util_String_0__Lake_lowerHexByte(v_n_boxed_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
uint32_t l___private_Lake_Util_String_0__Lake_lowerHexChar(uint8_t v_n_112_){
_start:
{
uint8_t v___x_113_; uint32_t v___x_114_; 
v___x_113_ = l___private_Lake_Util_String_0__Lake_lowerHexByte(v_n_112_);
v___x_114_ = lean_uint8_to_uint32(v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT void l___private_Lake_Util_String_0__Lake_lowerHexChar_0interp(lean_interpreter_value* stack)
{
uint8_t v_n_112_ = stack[0].m_num;
uint32_t v_res_115_;
v_res_115_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v_n_112_);
stack->m_num = v_res_115_;
}
LEAN_EXPORT lean_object* l___private_Lake_Util_String_0__Lake_lowerHexChar___boxed(lean_object* v_n_116_){
_start:
{
uint8_t v_n_boxed_117_; uint32_t v_res_118_; lean_object* v_r_119_; 
v_n_boxed_117_ = lean_unbox(v_n_116_);
v_res_118_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v_n_boxed_117_);
v_r_119_ = lean_box_uint32(v_res_118_);
return v_r_119_;
}
}
static lean_object* _init_l_Lake_lowerHexUInt64___closed__0(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(16u);
v___x_121_ = lean_mk_empty_byte_array(v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lake_lowerHexUInt64___closed__1(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_obj_once(&l_Lake_lowerHexUInt64___closed__0, &l_Lake_lowerHexUInt64___closed__0_once, _init_l_Lake_lowerHexUInt64___closed__0);
v___x_123_ = lean_string_from_utf8_unchecked(v___x_122_);
return v___x_123_;
}
}
lean_object* l_Lake_lowerHexUInt64(uint64_t v_n_124_){
_start:
{
lean_object* v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v___x_129_; uint8_t v___x_130_; uint32_t v___x_131_; lean_object* v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint8_t v___x_136_; uint32_t v___x_137_; lean_object* v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; uint8_t v___x_142_; uint32_t v___x_143_; lean_object* v___x_144_; uint64_t v___x_145_; uint64_t v___x_146_; uint64_t v___x_147_; uint8_t v___x_148_; uint32_t v___x_149_; lean_object* v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; uint64_t v___x_153_; uint8_t v___x_154_; uint32_t v___x_155_; lean_object* v___x_156_; uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v___x_159_; uint8_t v___x_160_; uint32_t v___x_161_; lean_object* v___x_162_; uint64_t v___x_163_; uint64_t v___x_164_; uint64_t v___x_165_; uint8_t v___x_166_; uint32_t v___x_167_; lean_object* v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v___x_171_; uint8_t v___x_172_; uint32_t v___x_173_; lean_object* v___x_174_; uint64_t v___x_175_; uint64_t v___x_176_; uint64_t v___x_177_; uint8_t v___x_178_; uint32_t v___x_179_; lean_object* v___x_180_; uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v___x_183_; uint8_t v___x_184_; uint32_t v___x_185_; lean_object* v___x_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v___x_189_; uint8_t v___x_190_; uint32_t v___x_191_; lean_object* v___x_192_; uint64_t v___x_193_; uint64_t v___x_194_; uint64_t v___x_195_; uint8_t v___x_196_; uint32_t v___x_197_; lean_object* v___x_198_; uint64_t v___x_199_; uint64_t v___x_200_; uint64_t v___x_201_; uint8_t v___x_202_; uint32_t v___x_203_; lean_object* v___x_204_; uint64_t v___x_205_; uint64_t v___x_206_; uint64_t v___x_207_; uint8_t v___x_208_; uint32_t v___x_209_; lean_object* v___x_210_; uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint8_t v___x_214_; uint32_t v___x_215_; lean_object* v___x_216_; uint64_t v___x_217_; uint8_t v___x_218_; uint32_t v___x_219_; lean_object* v___x_220_; 
v___x_125_ = lean_obj_once(&l_Lake_lowerHexUInt64___closed__1, &l_Lake_lowerHexUInt64___closed__1_once, _init_l_Lake_lowerHexUInt64___closed__1);
v___x_126_ = 60ULL;
v___x_127_ = lean_uint64_shift_right(v_n_124_, v___x_126_);
v___x_128_ = 15ULL;
v___x_129_ = lean_uint64_land(v___x_127_, v___x_128_);
v___x_130_ = lean_uint64_to_uint8(v___x_129_);
v___x_131_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_130_);
v___x_132_ = lean_string_push(v___x_125_, v___x_131_);
v___x_133_ = 56ULL;
v___x_134_ = lean_uint64_shift_right(v_n_124_, v___x_133_);
v___x_135_ = lean_uint64_land(v___x_134_, v___x_128_);
v___x_136_ = lean_uint64_to_uint8(v___x_135_);
v___x_137_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_136_);
v___x_138_ = lean_string_push(v___x_132_, v___x_137_);
v___x_139_ = 52ULL;
v___x_140_ = lean_uint64_shift_right(v_n_124_, v___x_139_);
v___x_141_ = lean_uint64_land(v___x_140_, v___x_128_);
v___x_142_ = lean_uint64_to_uint8(v___x_141_);
v___x_143_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_142_);
v___x_144_ = lean_string_push(v___x_138_, v___x_143_);
v___x_145_ = 48ULL;
v___x_146_ = lean_uint64_shift_right(v_n_124_, v___x_145_);
v___x_147_ = lean_uint64_land(v___x_146_, v___x_128_);
v___x_148_ = lean_uint64_to_uint8(v___x_147_);
v___x_149_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_148_);
v___x_150_ = lean_string_push(v___x_144_, v___x_149_);
v___x_151_ = 44ULL;
v___x_152_ = lean_uint64_shift_right(v_n_124_, v___x_151_);
v___x_153_ = lean_uint64_land(v___x_152_, v___x_128_);
v___x_154_ = lean_uint64_to_uint8(v___x_153_);
v___x_155_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_154_);
v___x_156_ = lean_string_push(v___x_150_, v___x_155_);
v___x_157_ = 40ULL;
v___x_158_ = lean_uint64_shift_right(v_n_124_, v___x_157_);
v___x_159_ = lean_uint64_land(v___x_158_, v___x_128_);
v___x_160_ = lean_uint64_to_uint8(v___x_159_);
v___x_161_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_160_);
v___x_162_ = lean_string_push(v___x_156_, v___x_161_);
v___x_163_ = 36ULL;
v___x_164_ = lean_uint64_shift_right(v_n_124_, v___x_163_);
v___x_165_ = lean_uint64_land(v___x_164_, v___x_128_);
v___x_166_ = lean_uint64_to_uint8(v___x_165_);
v___x_167_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_166_);
v___x_168_ = lean_string_push(v___x_162_, v___x_167_);
v___x_169_ = 32ULL;
v___x_170_ = lean_uint64_shift_right(v_n_124_, v___x_169_);
v___x_171_ = lean_uint64_land(v___x_170_, v___x_128_);
v___x_172_ = lean_uint64_to_uint8(v___x_171_);
v___x_173_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_172_);
v___x_174_ = lean_string_push(v___x_168_, v___x_173_);
v___x_175_ = 28ULL;
v___x_176_ = lean_uint64_shift_right(v_n_124_, v___x_175_);
v___x_177_ = lean_uint64_land(v___x_176_, v___x_128_);
v___x_178_ = lean_uint64_to_uint8(v___x_177_);
v___x_179_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_178_);
v___x_180_ = lean_string_push(v___x_174_, v___x_179_);
v___x_181_ = 24ULL;
v___x_182_ = lean_uint64_shift_right(v_n_124_, v___x_181_);
v___x_183_ = lean_uint64_land(v___x_182_, v___x_128_);
v___x_184_ = lean_uint64_to_uint8(v___x_183_);
v___x_185_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_184_);
v___x_186_ = lean_string_push(v___x_180_, v___x_185_);
v___x_187_ = 20ULL;
v___x_188_ = lean_uint64_shift_right(v_n_124_, v___x_187_);
v___x_189_ = lean_uint64_land(v___x_188_, v___x_128_);
v___x_190_ = lean_uint64_to_uint8(v___x_189_);
v___x_191_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_190_);
v___x_192_ = lean_string_push(v___x_186_, v___x_191_);
v___x_193_ = 16ULL;
v___x_194_ = lean_uint64_shift_right(v_n_124_, v___x_193_);
v___x_195_ = lean_uint64_land(v___x_194_, v___x_128_);
v___x_196_ = lean_uint64_to_uint8(v___x_195_);
v___x_197_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_196_);
v___x_198_ = lean_string_push(v___x_192_, v___x_197_);
v___x_199_ = 12ULL;
v___x_200_ = lean_uint64_shift_right(v_n_124_, v___x_199_);
v___x_201_ = lean_uint64_land(v___x_200_, v___x_128_);
v___x_202_ = lean_uint64_to_uint8(v___x_201_);
v___x_203_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_202_);
v___x_204_ = lean_string_push(v___x_198_, v___x_203_);
v___x_205_ = 8ULL;
v___x_206_ = lean_uint64_shift_right(v_n_124_, v___x_205_);
v___x_207_ = lean_uint64_land(v___x_206_, v___x_128_);
v___x_208_ = lean_uint64_to_uint8(v___x_207_);
v___x_209_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_208_);
v___x_210_ = lean_string_push(v___x_204_, v___x_209_);
v___x_211_ = 4ULL;
v___x_212_ = lean_uint64_shift_right(v_n_124_, v___x_211_);
v___x_213_ = lean_uint64_land(v___x_212_, v___x_128_);
v___x_214_ = lean_uint64_to_uint8(v___x_213_);
v___x_215_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_214_);
v___x_216_ = lean_string_push(v___x_210_, v___x_215_);
v___x_217_ = lean_uint64_land(v_n_124_, v___x_128_);
v___x_218_ = lean_uint64_to_uint8(v___x_217_);
v___x_219_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_218_);
v___x_220_ = lean_string_push(v___x_216_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT void l_Lake_lowerHexUInt64_0interp(lean_interpreter_value* stack)
{
uint64_t v_n_124_ = stack[0].m_num;
lean_object* v_res_221_;
v_res_221_ = l_Lake_lowerHexUInt64(v_n_124_);
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l_Lake_lowerHexUInt64___boxed(lean_object* v_n_222_){
_start:
{
uint64_t v_n_boxed_223_; lean_object* v_res_224_; 
v_n_boxed_223_ = lean_unbox_uint64(v_n_222_);
lean_dec_ref(v_n_222_);
v_res_224_ = l_Lake_lowerHexUInt64(v_n_boxed_223_);
return v_res_224_;
}
}
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Fold(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_String(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_String(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Fold(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_String(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_String(builtin);
}
#ifdef __cplusplus
}
#endif
