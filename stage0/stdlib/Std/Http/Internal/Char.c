// Lean compiler output
// Module: Std.Http.Internal.Char
// Imports: public import Init.Data.Char public import Init.Data.String.Basic public import Init.Data.Int.Basic public import Init.Grind
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
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_uint8_dec_lt(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAscii(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAscii___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAsciiByte(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAsciiByte___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isDigitByte(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isDigitByte___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAlphaByte(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAlphaByte___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_tchar(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_tchar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_vchar(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_vchar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_qdtext(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_qdtext___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_quotedPairChar(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_quotedPairChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_quotedStringChar(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_quotedStringChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_fieldVchar(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldVchar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_fieldContent(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldContent___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_ctext(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ctext___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_etagc(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_etagc___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_ows(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ows___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_bws(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_bws___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_rws(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_rws___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_obsText(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_obsText___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_reasonPhraseChar(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_reasonPhraseChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isHexDigit(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigit___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isHexDigitByte(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigitByte___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAlphaNum(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAlphaNum___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAsciiAlphaNumChar(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAsciiAlphaNumChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isValidSchemeChar(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidSchemeChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isValidDomainNameChar(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidDomainNameChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUnreserved(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUnreserved___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isSubDelims(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isSubDelims___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isPChar(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isPChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryChar(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isFragmentChar(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isFragmentChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUserInfoChar(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUserInfoChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryDataChar(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryDataChar___boxed(lean_object*);
uint8_t l_Std_Http_Internal_Char_isAscii(uint32_t v_c_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; uint8_t v___x_4_; 
v___x_2_ = lean_uint32_to_nat(v_c_1_);
v___x_3_ = lean_unsigned_to_nat(128u);
v___x_4_ = lean_nat_dec_lt(v___x_2_, v___x_3_);
lean_dec(v___x_2_);
return v___x_4_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isAscii_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1_ = stack[0].m_num;
uint8_t v_res_5_;
v_res_5_ = l_Std_Http_Internal_Char_isAscii(v_c_1_);
stack->m_num = v_res_5_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAscii___boxed(lean_object* v_c_6_){
_start:
{
uint32_t v_c_boxed_7_; uint8_t v_res_8_; lean_object* v_r_9_; 
v_c_boxed_7_ = lean_unbox_uint32(v_c_6_);
lean_dec(v_c_6_);
v_res_8_ = l_Std_Http_Internal_Char_isAscii(v_c_boxed_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
uint8_t l_Std_Http_Internal_Char_isAsciiByte(uint8_t v_c_10_){
_start:
{
uint8_t v___x_11_; uint8_t v___x_12_; 
v___x_11_ = 128;
v___x_12_ = lean_uint8_dec_lt(v_c_10_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isAsciiByte_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_10_ = stack[0].m_num;
uint8_t v_res_13_;
v_res_13_ = l_Std_Http_Internal_Char_isAsciiByte(v_c_10_);
stack->m_num = v_res_13_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAsciiByte___boxed(lean_object* v_c_14_){
_start:
{
uint8_t v_c_boxed_15_; uint8_t v_res_16_; lean_object* v_r_17_; 
v_c_boxed_15_ = lean_unbox(v_c_14_);
v_res_16_ = l_Std_Http_Internal_Char_isAsciiByte(v_c_boxed_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
uint8_t l_Std_Http_Internal_Char_isDigitByte(uint8_t v_c_18_){
_start:
{
uint8_t v___x_19_; uint8_t v___x_20_; 
v___x_19_ = 48;
v___x_20_ = lean_uint8_dec_le(v___x_19_, v_c_18_);
if (v___x_20_ == 0)
{
return v___x_20_;
}
else
{
uint8_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = 57;
v___x_22_ = lean_uint8_dec_le(v_c_18_, v___x_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isDigitByte_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_18_ = stack[0].m_num;
uint8_t v_res_23_;
v_res_23_ = l_Std_Http_Internal_Char_isDigitByte(v_c_18_);
stack->m_num = v_res_23_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isDigitByte___boxed(lean_object* v_c_24_){
_start:
{
uint8_t v_c_boxed_25_; uint8_t v_res_26_; lean_object* v_r_27_; 
v_c_boxed_25_ = lean_unbox(v_c_24_);
v_res_26_ = l_Std_Http_Internal_Char_isDigitByte(v_c_boxed_25_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
uint8_t l_Std_Http_Internal_Char_isAlphaByte(uint8_t v_c_28_){
_start:
{
uint8_t v___x_34_; uint8_t v___x_35_; 
v___x_34_ = 65;
v___x_35_ = lean_uint8_dec_le(v___x_34_, v_c_28_);
if (v___x_35_ == 0)
{
goto v___jp_29_;
}
else
{
uint8_t v___x_36_; uint8_t v___x_37_; 
v___x_36_ = 90;
v___x_37_ = lean_uint8_dec_le(v_c_28_, v___x_36_);
if (v___x_37_ == 0)
{
goto v___jp_29_;
}
else
{
return v___x_37_;
}
}
v___jp_29_:
{
uint8_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 97;
v___x_31_ = lean_uint8_dec_le(v___x_30_, v_c_28_);
if (v___x_31_ == 0)
{
return v___x_31_;
}
else
{
uint8_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 122;
v___x_33_ = lean_uint8_dec_le(v_c_28_, v___x_32_);
return v___x_33_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isAlphaByte_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_28_ = stack[0].m_num;
uint8_t v_res_38_;
v_res_38_ = l_Std_Http_Internal_Char_isAlphaByte(v_c_28_);
stack->m_num = v_res_38_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAlphaByte___boxed(lean_object* v_c_39_){
_start:
{
uint8_t v_c_boxed_40_; uint8_t v_res_41_; lean_object* v_r_42_; 
v_c_boxed_40_ = lean_unbox(v_c_39_);
v_res_41_ = l_Std_Http_Internal_Char_isAlphaByte(v_c_boxed_40_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
uint8_t l_Std_Http_Internal_Char_tchar(uint32_t v_c_43_){
_start:
{
uint32_t v___x_54_; uint8_t v___x_55_; 
v___x_54_ = 33;
v___x_55_ = lean_uint32_dec_eq(v_c_43_, v___x_54_);
if (v___x_55_ == 0)
{
uint32_t v___x_56_; uint8_t v___x_57_; 
v___x_56_ = 35;
v___x_57_ = lean_uint32_dec_eq(v_c_43_, v___x_56_);
if (v___x_57_ == 0)
{
uint32_t v___x_58_; uint8_t v___x_59_; 
v___x_58_ = 36;
v___x_59_ = lean_uint32_dec_eq(v_c_43_, v___x_58_);
if (v___x_59_ == 0)
{
uint32_t v___x_60_; uint8_t v___x_61_; 
v___x_60_ = 37;
v___x_61_ = lean_uint32_dec_eq(v_c_43_, v___x_60_);
if (v___x_61_ == 0)
{
uint32_t v___x_62_; uint8_t v___x_63_; 
v___x_62_ = 38;
v___x_63_ = lean_uint32_dec_eq(v_c_43_, v___x_62_);
if (v___x_63_ == 0)
{
uint32_t v___x_64_; uint8_t v___x_65_; 
v___x_64_ = 39;
v___x_65_ = lean_uint32_dec_eq(v_c_43_, v___x_64_);
if (v___x_65_ == 0)
{
uint32_t v___x_66_; uint8_t v___x_67_; 
v___x_66_ = 42;
v___x_67_ = lean_uint32_dec_eq(v_c_43_, v___x_66_);
if (v___x_67_ == 0)
{
uint32_t v___x_68_; uint8_t v___x_69_; 
v___x_68_ = 43;
v___x_69_ = lean_uint32_dec_eq(v_c_43_, v___x_68_);
if (v___x_69_ == 0)
{
uint32_t v___x_70_; uint8_t v___x_71_; 
v___x_70_ = 45;
v___x_71_ = lean_uint32_dec_eq(v_c_43_, v___x_70_);
if (v___x_71_ == 0)
{
uint32_t v___x_72_; uint8_t v___x_73_; 
v___x_72_ = 46;
v___x_73_ = lean_uint32_dec_eq(v_c_43_, v___x_72_);
if (v___x_73_ == 0)
{
uint32_t v___x_74_; uint8_t v___x_75_; 
v___x_74_ = 94;
v___x_75_ = lean_uint32_dec_eq(v_c_43_, v___x_74_);
if (v___x_75_ == 0)
{
uint32_t v___x_76_; uint8_t v___x_77_; 
v___x_76_ = 95;
v___x_77_ = lean_uint32_dec_eq(v_c_43_, v___x_76_);
if (v___x_77_ == 0)
{
uint32_t v___x_78_; uint8_t v___x_79_; 
v___x_78_ = 96;
v___x_79_ = lean_uint32_dec_eq(v_c_43_, v___x_78_);
if (v___x_79_ == 0)
{
uint32_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 124;
v___x_81_ = lean_uint32_dec_eq(v_c_43_, v___x_80_);
if (v___x_81_ == 0)
{
uint32_t v___x_82_; uint8_t v___x_83_; 
v___x_82_ = 126;
v___x_83_ = lean_uint32_dec_eq(v_c_43_, v___x_82_);
if (v___x_83_ == 0)
{
uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 48;
v___x_85_ = lean_uint32_dec_le(v___x_84_, v_c_43_);
if (v___x_85_ == 0)
{
goto v___jp_49_;
}
else
{
uint32_t v___x_86_; uint8_t v___x_87_; 
v___x_86_ = 57;
v___x_87_ = lean_uint32_dec_le(v_c_43_, v___x_86_);
if (v___x_87_ == 0)
{
goto v___jp_49_;
}
else
{
return v___x_87_;
}
}
}
else
{
return v___x_83_;
}
}
else
{
return v___x_81_;
}
}
else
{
return v___x_79_;
}
}
else
{
return v___x_77_;
}
}
else
{
return v___x_75_;
}
}
else
{
return v___x_73_;
}
}
else
{
return v___x_71_;
}
}
else
{
return v___x_69_;
}
}
else
{
return v___x_67_;
}
}
else
{
return v___x_65_;
}
}
else
{
return v___x_63_;
}
}
else
{
return v___x_61_;
}
}
else
{
return v___x_59_;
}
}
else
{
return v___x_57_;
}
}
else
{
return v___x_55_;
}
v___jp_44_:
{
uint32_t v___x_45_; uint8_t v___x_46_; 
v___x_45_ = 97;
v___x_46_ = lean_uint32_dec_le(v___x_45_, v_c_43_);
if (v___x_46_ == 0)
{
return v___x_46_;
}
else
{
uint32_t v___x_47_; uint8_t v___x_48_; 
v___x_47_ = 122;
v___x_48_ = lean_uint32_dec_le(v_c_43_, v___x_47_);
return v___x_48_;
}
}
v___jp_49_:
{
uint32_t v___x_50_; uint8_t v___x_51_; 
v___x_50_ = 65;
v___x_51_ = lean_uint32_dec_le(v___x_50_, v_c_43_);
if (v___x_51_ == 0)
{
goto v___jp_44_;
}
else
{
uint32_t v___x_52_; uint8_t v___x_53_; 
v___x_52_ = 90;
v___x_53_ = lean_uint32_dec_le(v_c_43_, v___x_52_);
if (v___x_53_ == 0)
{
goto v___jp_44_;
}
else
{
return v___x_53_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_tchar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_43_ = stack[0].m_num;
uint8_t v_res_88_;
v_res_88_ = l_Std_Http_Internal_Char_tchar(v_c_43_);
stack->m_num = v_res_88_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_tchar___boxed(lean_object* v_c_89_){
_start:
{
uint32_t v_c_boxed_90_; uint8_t v_res_91_; lean_object* v_r_92_; 
v_c_boxed_90_ = lean_unbox_uint32(v_c_89_);
lean_dec(v_c_89_);
v_res_91_ = l_Std_Http_Internal_Char_tchar(v_c_boxed_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
uint8_t l_Std_Http_Internal_Char_vchar(uint32_t v_c_93_){
_start:
{
uint32_t v___x_94_; uint8_t v___x_95_; 
v___x_94_ = 33;
v___x_95_ = lean_uint32_dec_le(v___x_94_, v_c_93_);
if (v___x_95_ == 0)
{
return v___x_95_;
}
else
{
uint32_t v___x_96_; uint8_t v___x_97_; 
v___x_96_ = 126;
v___x_97_ = lean_uint32_dec_le(v_c_93_, v___x_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_vchar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_93_ = stack[0].m_num;
uint8_t v_res_98_;
v_res_98_ = l_Std_Http_Internal_Char_vchar(v_c_93_);
stack->m_num = v_res_98_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_vchar___boxed(lean_object* v_c_99_){
_start:
{
uint32_t v_c_boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v_c_boxed_100_ = lean_unbox_uint32(v_c_99_);
lean_dec(v_c_99_);
v_res_101_ = l_Std_Http_Internal_Char_vchar(v_c_boxed_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
uint8_t l_Std_Http_Internal_Char_qdtext(uint32_t v_c_103_){
_start:
{
uint32_t v___x_109_; uint8_t v___x_110_; 
v___x_109_ = 9;
v___x_110_ = lean_uint32_dec_eq(v_c_103_, v___x_109_);
if (v___x_110_ == 0)
{
uint32_t v___x_111_; uint8_t v___x_112_; 
v___x_111_ = 32;
v___x_112_ = lean_uint32_dec_eq(v_c_103_, v___x_111_);
if (v___x_112_ == 0)
{
uint32_t v___x_113_; uint8_t v___x_114_; 
v___x_113_ = 33;
v___x_114_ = lean_uint32_dec_eq(v_c_103_, v___x_113_);
if (v___x_114_ == 0)
{
uint32_t v___x_115_; uint8_t v___x_116_; 
v___x_115_ = 35;
v___x_116_ = lean_uint32_dec_le(v___x_115_, v_c_103_);
if (v___x_116_ == 0)
{
goto v___jp_104_;
}
else
{
uint32_t v___x_117_; uint8_t v___x_118_; 
v___x_117_ = 91;
v___x_118_ = lean_uint32_dec_le(v_c_103_, v___x_117_);
if (v___x_118_ == 0)
{
goto v___jp_104_;
}
else
{
return v___x_118_;
}
}
}
else
{
return v___x_114_;
}
}
else
{
return v___x_112_;
}
}
else
{
return v___x_110_;
}
v___jp_104_:
{
uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_105_ = 93;
v___x_106_ = lean_uint32_dec_le(v___x_105_, v_c_103_);
if (v___x_106_ == 0)
{
return v___x_106_;
}
else
{
uint32_t v___x_107_; uint8_t v___x_108_; 
v___x_107_ = 126;
v___x_108_ = lean_uint32_dec_le(v_c_103_, v___x_107_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_qdtext_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_103_ = stack[0].m_num;
uint8_t v_res_119_;
v_res_119_ = l_Std_Http_Internal_Char_qdtext(v_c_103_);
stack->m_num = v_res_119_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_qdtext___boxed(lean_object* v_c_120_){
_start:
{
uint32_t v_c_boxed_121_; uint8_t v_res_122_; lean_object* v_r_123_; 
v_c_boxed_121_ = lean_unbox_uint32(v_c_120_);
lean_dec(v_c_120_);
v_res_122_ = l_Std_Http_Internal_Char_qdtext(v_c_boxed_121_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
uint8_t l_Std_Http_Internal_Char_quotedPairChar(uint32_t v_c_124_){
_start:
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 9;
v___x_126_ = lean_uint32_dec_eq(v_c_124_, v___x_125_);
if (v___x_126_ == 0)
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 32;
v___x_128_ = lean_uint32_dec_eq(v_c_124_, v___x_127_);
if (v___x_128_ == 0)
{
uint32_t v___x_129_; uint8_t v___x_130_; 
v___x_129_ = 33;
v___x_130_ = lean_uint32_dec_le(v___x_129_, v_c_124_);
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
uint32_t v___x_131_; uint8_t v___x_132_; 
v___x_131_ = 126;
v___x_132_ = lean_uint32_dec_le(v_c_124_, v___x_131_);
return v___x_132_;
}
}
else
{
return v___x_128_;
}
}
else
{
return v___x_126_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_quotedPairChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_124_ = stack[0].m_num;
uint8_t v_res_133_;
v_res_133_ = l_Std_Http_Internal_Char_quotedPairChar(v_c_124_);
stack->m_num = v_res_133_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_quotedPairChar___boxed(lean_object* v_c_134_){
_start:
{
uint32_t v_c_boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v_c_boxed_135_ = lean_unbox_uint32(v_c_134_);
lean_dec(v_c_134_);
v_res_136_ = l_Std_Http_Internal_Char_quotedPairChar(v_c_boxed_135_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
uint8_t l_Std_Http_Internal_Char_quotedStringChar(uint32_t v_c_138_){
_start:
{
uint32_t v___x_153_; uint8_t v___x_154_; 
v___x_153_ = 9;
v___x_154_ = lean_uint32_dec_eq(v_c_138_, v___x_153_);
if (v___x_154_ == 0)
{
uint32_t v___x_155_; uint8_t v___x_156_; 
v___x_155_ = 32;
v___x_156_ = lean_uint32_dec_eq(v_c_138_, v___x_155_);
if (v___x_156_ == 0)
{
uint32_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 33;
v___x_158_ = lean_uint32_dec_eq(v_c_138_, v___x_157_);
if (v___x_158_ == 0)
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 35;
v___x_160_ = lean_uint32_dec_le(v___x_159_, v_c_138_);
if (v___x_160_ == 0)
{
goto v___jp_148_;
}
else
{
uint32_t v___x_161_; uint8_t v___x_162_; 
v___x_161_ = 91;
v___x_162_ = lean_uint32_dec_le(v_c_138_, v___x_161_);
if (v___x_162_ == 0)
{
goto v___jp_148_;
}
else
{
return v___x_162_;
}
}
}
else
{
return v___x_158_;
}
}
else
{
return v___x_156_;
}
}
else
{
return v___x_154_;
}
v___jp_139_:
{
uint32_t v___x_140_; uint8_t v___x_141_; 
v___x_140_ = 9;
v___x_141_ = lean_uint32_dec_eq(v_c_138_, v___x_140_);
if (v___x_141_ == 0)
{
uint32_t v___x_142_; uint8_t v___x_143_; 
v___x_142_ = 32;
v___x_143_ = lean_uint32_dec_eq(v_c_138_, v___x_142_);
if (v___x_143_ == 0)
{
uint32_t v___x_144_; uint8_t v___x_145_; 
v___x_144_ = 33;
v___x_145_ = lean_uint32_dec_le(v___x_144_, v_c_138_);
if (v___x_145_ == 0)
{
return v___x_145_;
}
else
{
uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_146_ = 126;
v___x_147_ = lean_uint32_dec_le(v_c_138_, v___x_146_);
return v___x_147_;
}
}
else
{
return v___x_143_;
}
}
else
{
return v___x_141_;
}
}
v___jp_148_:
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 93;
v___x_150_ = lean_uint32_dec_le(v___x_149_, v_c_138_);
if (v___x_150_ == 0)
{
goto v___jp_139_;
}
else
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 126;
v___x_152_ = lean_uint32_dec_le(v_c_138_, v___x_151_);
if (v___x_152_ == 0)
{
goto v___jp_139_;
}
else
{
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_quotedStringChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_138_ = stack[0].m_num;
uint8_t v_res_163_;
v_res_163_ = l_Std_Http_Internal_Char_quotedStringChar(v_c_138_);
stack->m_num = v_res_163_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_quotedStringChar___boxed(lean_object* v_c_164_){
_start:
{
uint32_t v_c_boxed_165_; uint8_t v_res_166_; lean_object* v_r_167_; 
v_c_boxed_165_ = lean_unbox_uint32(v_c_164_);
lean_dec(v_c_164_);
v_res_166_ = l_Std_Http_Internal_Char_quotedStringChar(v_c_boxed_165_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg(uint32_t v_c_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_, lean_object* v_h__3_171_, lean_object* v_h__4_172_){
_start:
{
uint32_t v___x_173_; uint8_t v___x_174_; 
v___x_173_ = 9;
v___x_174_ = lean_uint32_dec_eq(v_c_168_, v___x_173_);
if (v___x_174_ == 0)
{
uint32_t v___x_175_; uint8_t v___x_176_; 
lean_dec(v_h__1_169_);
v___x_175_ = 32;
v___x_176_ = lean_uint32_dec_eq(v_c_168_, v___x_175_);
if (v___x_176_ == 0)
{
uint32_t v___x_177_; uint8_t v___x_178_; 
lean_dec(v_h__2_170_);
v___x_177_ = 33;
v___x_178_ = lean_uint32_dec_eq(v_c_168_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_h__3_171_);
v___x_179_ = lean_box_uint32(v_c_168_);
v___x_180_ = lean_apply_4(v_h__4_172_, v___x_179_, lean_box(0), lean_box(0), lean_box(0));
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_h__4_172_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_apply_1(v_h__3_171_, v___x_181_);
return v___x_182_;
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_h__4_172_);
lean_dec(v_h__3_171_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_apply_1(v_h__2_170_, v___x_183_);
return v___x_184_;
}
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_h__4_172_);
lean_dec(v_h__3_171_);
lean_dec(v_h__2_170_);
v___x_185_ = lean_box(0);
v___x_186_ = lean_apply_1(v_h__1_169_, v___x_185_);
return v___x_186_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_168_ = stack[0].m_num;
lean_object* v_h__1_169_ = stack[1].m_obj;
lean_object* v_h__2_170_ = stack[2].m_obj;
lean_object* v_h__3_171_ = stack[3].m_obj;
lean_object* v_h__4_172_ = stack[4].m_obj;
lean_object* v_res_187_;
v_res_187_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg(v_c_168_, v_h__1_169_, v_h__2_170_, v_h__3_171_, v_h__4_172_);
stack->m_obj
 = v_res_187_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg___boxed(lean_object* v_c_188_, lean_object* v_h__1_189_, lean_object* v_h__2_190_, lean_object* v_h__3_191_, lean_object* v_h__4_192_){
_start:
{
uint32_t v_c_73__boxed_193_; lean_object* v_res_194_; 
v_c_73__boxed_193_ = lean_unbox_uint32(v_c_188_);
lean_dec(v_c_188_);
v_res_194_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg(v_c_73__boxed_193_, v_h__1_189_, v_h__2_190_, v_h__3_191_, v_h__4_192_);
return v_res_194_;
}
}
lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(lean_object* v_motive_195_, uint32_t v_c_196_, lean_object* v_h__1_197_, lean_object* v_h__2_198_, lean_object* v_h__3_199_, lean_object* v_h__4_200_){
_start:
{
uint32_t v___x_201_; uint8_t v___x_202_; 
v___x_201_ = 9;
v___x_202_ = lean_uint32_dec_eq(v_c_196_, v___x_201_);
if (v___x_202_ == 0)
{
uint32_t v___x_203_; uint8_t v___x_204_; 
lean_dec(v_h__1_197_);
v___x_203_ = 32;
v___x_204_ = lean_uint32_dec_eq(v_c_196_, v___x_203_);
if (v___x_204_ == 0)
{
uint32_t v___x_205_; uint8_t v___x_206_; 
lean_dec(v_h__2_198_);
v___x_205_ = 33;
v___x_206_ = lean_uint32_dec_eq(v_c_196_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v_h__3_199_);
v___x_207_ = lean_box_uint32(v_c_196_);
v___x_208_ = lean_apply_4(v_h__4_200_, v___x_207_, lean_box(0), lean_box(0), lean_box(0));
return v___x_208_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec(v_h__4_200_);
v___x_209_ = lean_box(0);
v___x_210_ = lean_apply_1(v_h__3_199_, v___x_209_);
return v___x_210_;
}
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_h__4_200_);
lean_dec(v_h__3_199_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_apply_1(v_h__2_198_, v___x_211_);
return v___x_212_;
}
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v_h__4_200_);
lean_dec(v_h__3_199_);
lean_dec(v_h__2_198_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_apply_1(v_h__1_197_, v___x_213_);
return v___x_214_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_196_ = stack[1].m_num;
lean_object* v_h__1_197_ = stack[2].m_obj;
lean_object* v_h__2_198_ = stack[3].m_obj;
lean_object* v_h__3_199_ = stack[4].m_obj;
lean_object* v_h__4_200_ = stack[5].m_obj;
lean_object* v_res_215_;
v_res_215_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(lean_box(0), v_c_196_, v_h__1_197_, v_h__2_198_, v_h__3_199_, v_h__4_200_);
stack->m_obj
 = v_res_215_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___boxed(lean_object* v_motive_216_, lean_object* v_c_217_, lean_object* v_h__1_218_, lean_object* v_h__2_219_, lean_object* v_h__3_220_, lean_object* v_h__4_221_){
_start:
{
uint32_t v_c_120__boxed_222_; lean_object* v_res_223_; 
v_c_120__boxed_222_ = lean_unbox_uint32(v_c_217_);
lean_dec(v_c_217_);
v_res_223_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(v_motive_216_, v_c_120__boxed_222_, v_h__1_218_, v_h__2_219_, v_h__3_220_, v_h__4_221_);
return v_res_223_;
}
}
lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(uint32_t v_c_224_, lean_object* v_h__1_225_, lean_object* v_h__2_226_, lean_object* v_h__3_227_){
_start:
{
uint32_t v___x_228_; uint8_t v___x_229_; 
v___x_228_ = 9;
v___x_229_ = lean_uint32_dec_eq(v_c_224_, v___x_228_);
if (v___x_229_ == 0)
{
uint32_t v___x_230_; uint8_t v___x_231_; 
lean_dec(v_h__1_225_);
v___x_230_ = 32;
v___x_231_ = lean_uint32_dec_eq(v_c_224_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v_h__2_226_);
v___x_232_ = lean_box_uint32(v_c_224_);
v___x_233_ = lean_apply_3(v_h__3_227_, v___x_232_, lean_box(0), lean_box(0));
return v___x_233_;
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec(v_h__3_227_);
v___x_234_ = lean_box(0);
v___x_235_ = lean_apply_1(v_h__2_226_, v___x_234_);
return v___x_235_;
}
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v_h__3_227_);
lean_dec(v_h__2_226_);
v___x_236_ = lean_box(0);
v___x_237_ = lean_apply_1(v_h__1_225_, v___x_236_);
return v___x_237_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_224_ = stack[0].m_num;
lean_object* v_h__1_225_ = stack[1].m_obj;
lean_object* v_h__2_226_ = stack[2].m_obj;
lean_object* v_h__3_227_ = stack[3].m_obj;
lean_object* v_res_238_;
v_res_238_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(v_c_224_, v_h__1_225_, v_h__2_226_, v_h__3_227_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg___boxed(lean_object* v_c_239_, lean_object* v_h__1_240_, lean_object* v_h__2_241_, lean_object* v_h__3_242_){
_start:
{
uint32_t v_c_51__boxed_243_; lean_object* v_res_244_; 
v_c_51__boxed_243_ = lean_unbox_uint32(v_c_239_);
lean_dec(v_c_239_);
v_res_244_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(v_c_51__boxed_243_, v_h__1_240_, v_h__2_241_, v_h__3_242_);
return v_res_244_;
}
}
lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(lean_object* v_motive_245_, uint32_t v_c_246_, lean_object* v_h__1_247_, lean_object* v_h__2_248_, lean_object* v_h__3_249_){
_start:
{
uint32_t v___x_250_; uint8_t v___x_251_; 
v___x_250_ = 9;
v___x_251_ = lean_uint32_dec_eq(v_c_246_, v___x_250_);
if (v___x_251_ == 0)
{
uint32_t v___x_252_; uint8_t v___x_253_; 
lean_dec(v_h__1_247_);
v___x_252_ = 32;
v___x_253_ = lean_uint32_dec_eq(v_c_246_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v_h__2_248_);
v___x_254_ = lean_box_uint32(v_c_246_);
v___x_255_ = lean_apply_3(v_h__3_249_, v___x_254_, lean_box(0), lean_box(0));
return v___x_255_;
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec(v_h__3_249_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_apply_1(v_h__2_248_, v___x_256_);
return v___x_257_;
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec(v_h__3_249_);
lean_dec(v_h__2_248_);
v___x_258_ = lean_box(0);
v___x_259_ = lean_apply_1(v_h__1_247_, v___x_258_);
return v___x_259_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_246_ = stack[1].m_num;
lean_object* v_h__1_247_ = stack[2].m_obj;
lean_object* v_h__2_248_ = stack[3].m_obj;
lean_object* v_h__3_249_ = stack[4].m_obj;
lean_object* v_res_260_;
v_res_260_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(lean_box(0), v_c_246_, v_h__1_247_, v_h__2_248_, v_h__3_249_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___boxed(lean_object* v_motive_261_, lean_object* v_c_262_, lean_object* v_h__1_263_, lean_object* v_h__2_264_, lean_object* v_h__3_265_){
_start:
{
uint32_t v_c_86__boxed_266_; lean_object* v_res_267_; 
v_c_86__boxed_266_ = lean_unbox_uint32(v_c_262_);
lean_dec(v_c_262_);
v_res_267_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(v_motive_261_, v_c_86__boxed_266_, v_h__1_263_, v_h__2_264_, v_h__3_265_);
return v_res_267_;
}
}
uint8_t l_Std_Http_Internal_Char_fieldVchar(uint32_t v_c_268_){
_start:
{
uint32_t v___x_269_; uint8_t v___x_270_; 
v___x_269_ = 33;
v___x_270_ = lean_uint32_dec_le(v___x_269_, v_c_268_);
if (v___x_270_ == 0)
{
return v___x_270_;
}
else
{
uint32_t v___x_271_; uint8_t v___x_272_; 
v___x_271_ = 126;
v___x_272_ = lean_uint32_dec_le(v_c_268_, v___x_271_);
return v___x_272_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_fieldVchar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_268_ = stack[0].m_num;
uint8_t v_res_273_;
v_res_273_ = l_Std_Http_Internal_Char_fieldVchar(v_c_268_);
stack->m_num = v_res_273_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldVchar___boxed(lean_object* v_c_274_){
_start:
{
uint32_t v_c_boxed_275_; uint8_t v_res_276_; lean_object* v_r_277_; 
v_c_boxed_275_ = lean_unbox_uint32(v_c_274_);
lean_dec(v_c_274_);
v_res_276_ = l_Std_Http_Internal_Char_fieldVchar(v_c_boxed_275_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
uint8_t l_Std_Http_Internal_Char_fieldContent(uint32_t v_c_278_){
_start:
{
uint32_t v___x_284_; uint8_t v___x_285_; 
v___x_284_ = 33;
v___x_285_ = lean_uint32_dec_le(v___x_284_, v_c_278_);
if (v___x_285_ == 0)
{
goto v___jp_279_;
}
else
{
uint32_t v___x_286_; uint8_t v___x_287_; 
v___x_286_ = 126;
v___x_287_ = lean_uint32_dec_le(v_c_278_, v___x_286_);
if (v___x_287_ == 0)
{
goto v___jp_279_;
}
else
{
return v___x_287_;
}
}
v___jp_279_:
{
uint32_t v___x_280_; uint8_t v___x_281_; 
v___x_280_ = 32;
v___x_281_ = lean_uint32_dec_eq(v_c_278_, v___x_280_);
if (v___x_281_ == 0)
{
uint32_t v___x_282_; uint8_t v___x_283_; 
v___x_282_ = 9;
v___x_283_ = lean_uint32_dec_eq(v_c_278_, v___x_282_);
return v___x_283_;
}
else
{
return v___x_281_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_fieldContent_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_278_ = stack[0].m_num;
uint8_t v_res_288_;
v_res_288_ = l_Std_Http_Internal_Char_fieldContent(v_c_278_);
stack->m_num = v_res_288_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldContent___boxed(lean_object* v_c_289_){
_start:
{
uint32_t v_c_boxed_290_; uint8_t v_res_291_; lean_object* v_r_292_; 
v_c_boxed_290_ = lean_unbox_uint32(v_c_289_);
lean_dec(v_c_289_);
v_res_291_ = l_Std_Http_Internal_Char_fieldContent(v_c_boxed_290_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
uint8_t l_Std_Http_Internal_Char_ctext(uint32_t v_c_293_){
_start:
{
uint32_t v___x_304_; uint8_t v___x_305_; 
v___x_304_ = 9;
v___x_305_ = lean_uint32_dec_eq(v_c_293_, v___x_304_);
if (v___x_305_ == 0)
{
uint32_t v___x_306_; uint8_t v___x_307_; 
v___x_306_ = 32;
v___x_307_ = lean_uint32_dec_eq(v_c_293_, v___x_306_);
if (v___x_307_ == 0)
{
uint32_t v___x_308_; uint8_t v___x_309_; 
v___x_308_ = 33;
v___x_309_ = lean_uint32_dec_le(v___x_308_, v_c_293_);
if (v___x_309_ == 0)
{
goto v___jp_299_;
}
else
{
uint32_t v___x_310_; uint8_t v___x_311_; 
v___x_310_ = 39;
v___x_311_ = lean_uint32_dec_le(v_c_293_, v___x_310_);
if (v___x_311_ == 0)
{
goto v___jp_299_;
}
else
{
return v___x_311_;
}
}
}
else
{
return v___x_307_;
}
}
else
{
return v___x_305_;
}
v___jp_294_:
{
uint32_t v___x_295_; uint8_t v___x_296_; 
v___x_295_ = 93;
v___x_296_ = lean_uint32_dec_le(v___x_295_, v_c_293_);
if (v___x_296_ == 0)
{
return v___x_296_;
}
else
{
uint32_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = 126;
v___x_298_ = lean_uint32_dec_le(v_c_293_, v___x_297_);
return v___x_298_;
}
}
v___jp_299_:
{
uint32_t v___x_300_; uint8_t v___x_301_; 
v___x_300_ = 42;
v___x_301_ = lean_uint32_dec_le(v___x_300_, v_c_293_);
if (v___x_301_ == 0)
{
goto v___jp_294_;
}
else
{
uint32_t v___x_302_; uint8_t v___x_303_; 
v___x_302_ = 91;
v___x_303_ = lean_uint32_dec_le(v_c_293_, v___x_302_);
if (v___x_303_ == 0)
{
goto v___jp_294_;
}
else
{
return v___x_303_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_ctext_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_293_ = stack[0].m_num;
uint8_t v_res_312_;
v_res_312_ = l_Std_Http_Internal_Char_ctext(v_c_293_);
stack->m_num = v_res_312_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ctext___boxed(lean_object* v_c_313_){
_start:
{
uint32_t v_c_boxed_314_; uint8_t v_res_315_; lean_object* v_r_316_; 
v_c_boxed_314_ = lean_unbox_uint32(v_c_313_);
lean_dec(v_c_313_);
v_res_315_ = l_Std_Http_Internal_Char_ctext(v_c_boxed_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
uint8_t l_Std_Http_Internal_Char_etagc(uint32_t v_c_317_){
_start:
{
uint32_t v___x_318_; uint8_t v___x_319_; 
v___x_318_ = 33;
v___x_319_ = lean_uint32_dec_eq(v_c_317_, v___x_318_);
if (v___x_319_ == 0)
{
uint32_t v___x_320_; uint8_t v___x_321_; 
v___x_320_ = 35;
v___x_321_ = lean_uint32_dec_le(v___x_320_, v_c_317_);
if (v___x_321_ == 0)
{
return v___x_321_;
}
else
{
uint32_t v___x_322_; uint8_t v___x_323_; 
v___x_322_ = 126;
v___x_323_ = lean_uint32_dec_le(v_c_317_, v___x_322_);
return v___x_323_;
}
}
else
{
return v___x_319_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_etagc_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_317_ = stack[0].m_num;
uint8_t v_res_324_;
v_res_324_ = l_Std_Http_Internal_Char_etagc(v_c_317_);
stack->m_num = v_res_324_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_etagc___boxed(lean_object* v_c_325_){
_start:
{
uint32_t v_c_boxed_326_; uint8_t v_res_327_; lean_object* v_r_328_; 
v_c_boxed_326_ = lean_unbox_uint32(v_c_325_);
lean_dec(v_c_325_);
v_res_327_ = l_Std_Http_Internal_Char_etagc(v_c_boxed_326_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
uint8_t l_Std_Http_Internal_Char_ows(uint32_t v_c_329_){
_start:
{
uint32_t v___x_330_; uint8_t v___x_331_; 
v___x_330_ = 32;
v___x_331_ = lean_uint32_dec_eq(v_c_329_, v___x_330_);
if (v___x_331_ == 0)
{
uint32_t v___x_332_; uint8_t v___x_333_; 
v___x_332_ = 9;
v___x_333_ = lean_uint32_dec_eq(v_c_329_, v___x_332_);
return v___x_333_;
}
else
{
return v___x_331_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_ows_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_329_ = stack[0].m_num;
uint8_t v_res_334_;
v_res_334_ = l_Std_Http_Internal_Char_ows(v_c_329_);
stack->m_num = v_res_334_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ows___boxed(lean_object* v_c_335_){
_start:
{
uint32_t v_c_boxed_336_; uint8_t v_res_337_; lean_object* v_r_338_; 
v_c_boxed_336_ = lean_unbox_uint32(v_c_335_);
lean_dec(v_c_335_);
v_res_337_ = l_Std_Http_Internal_Char_ows(v_c_boxed_336_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
uint8_t l_Std_Http_Internal_Char_bws(uint32_t v_c_339_){
_start:
{
uint32_t v___x_340_; uint8_t v___x_341_; 
v___x_340_ = 32;
v___x_341_ = lean_uint32_dec_eq(v_c_339_, v___x_340_);
if (v___x_341_ == 0)
{
uint32_t v___x_342_; uint8_t v___x_343_; 
v___x_342_ = 9;
v___x_343_ = lean_uint32_dec_eq(v_c_339_, v___x_342_);
return v___x_343_;
}
else
{
return v___x_341_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_bws_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_339_ = stack[0].m_num;
uint8_t v_res_344_;
v_res_344_ = l_Std_Http_Internal_Char_bws(v_c_339_);
stack->m_num = v_res_344_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_bws___boxed(lean_object* v_c_345_){
_start:
{
uint32_t v_c_boxed_346_; uint8_t v_res_347_; lean_object* v_r_348_; 
v_c_boxed_346_ = lean_unbox_uint32(v_c_345_);
lean_dec(v_c_345_);
v_res_347_ = l_Std_Http_Internal_Char_bws(v_c_boxed_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
uint8_t l_Std_Http_Internal_Char_rws(uint32_t v_c_349_){
_start:
{
uint32_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = 32;
v___x_351_ = lean_uint32_dec_eq(v_c_349_, v___x_350_);
if (v___x_351_ == 0)
{
uint32_t v___x_352_; uint8_t v___x_353_; 
v___x_352_ = 9;
v___x_353_ = lean_uint32_dec_eq(v_c_349_, v___x_352_);
return v___x_353_;
}
else
{
return v___x_351_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_rws_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_349_ = stack[0].m_num;
uint8_t v_res_354_;
v_res_354_ = l_Std_Http_Internal_Char_rws(v_c_349_);
stack->m_num = v_res_354_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_rws___boxed(lean_object* v_c_355_){
_start:
{
uint32_t v_c_boxed_356_; uint8_t v_res_357_; lean_object* v_r_358_; 
v_c_boxed_356_ = lean_unbox_uint32(v_c_355_);
lean_dec(v_c_355_);
v_res_357_ = l_Std_Http_Internal_Char_rws(v_c_boxed_356_);
v_r_358_ = lean_box(v_res_357_);
return v_r_358_;
}
}
uint8_t l_Std_Http_Internal_Char_obsText(uint32_t v_c_359_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_360_ = lean_unsigned_to_nat(128u);
v___x_361_ = lean_uint32_to_nat(v_c_359_);
v___x_362_ = lean_nat_dec_le(v___x_360_, v___x_361_);
lean_dec(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_obsText_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_359_ = stack[0].m_num;
uint8_t v_res_363_;
v_res_363_ = l_Std_Http_Internal_Char_obsText(v_c_359_);
stack->m_num = v_res_363_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_obsText___boxed(lean_object* v_c_364_){
_start:
{
uint32_t v_c_boxed_365_; uint8_t v_res_366_; lean_object* v_r_367_; 
v_c_boxed_365_ = lean_unbox_uint32(v_c_364_);
lean_dec(v_c_364_);
v_res_366_ = l_Std_Http_Internal_Char_obsText(v_c_boxed_365_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
uint8_t l_Std_Http_Internal_Char_reasonPhraseChar(uint32_t v_c_368_){
_start:
{
uint32_t v___x_369_; uint8_t v___x_370_; 
v___x_369_ = 9;
v___x_370_ = lean_uint32_dec_eq(v_c_368_, v___x_369_);
if (v___x_370_ == 0)
{
uint32_t v___x_371_; uint8_t v___x_372_; 
v___x_371_ = 32;
v___x_372_ = lean_uint32_dec_eq(v_c_368_, v___x_371_);
if (v___x_372_ == 0)
{
uint32_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 33;
v___x_374_ = lean_uint32_dec_le(v___x_373_, v_c_368_);
if (v___x_374_ == 0)
{
return v___x_374_;
}
else
{
uint32_t v___x_375_; uint8_t v___x_376_; 
v___x_375_ = 126;
v___x_376_ = lean_uint32_dec_le(v_c_368_, v___x_375_);
return v___x_376_;
}
}
else
{
return v___x_372_;
}
}
else
{
return v___x_370_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_reasonPhraseChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_368_ = stack[0].m_num;
uint8_t v_res_377_;
v_res_377_ = l_Std_Http_Internal_Char_reasonPhraseChar(v_c_368_);
stack->m_num = v_res_377_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_reasonPhraseChar___boxed(lean_object* v_c_378_){
_start:
{
uint32_t v_c_boxed_379_; uint8_t v_res_380_; lean_object* v_r_381_; 
v_c_boxed_379_ = lean_unbox_uint32(v_c_378_);
lean_dec(v_c_378_);
v_res_380_ = l_Std_Http_Internal_Char_reasonPhraseChar(v_c_boxed_379_);
v_r_381_ = lean_box(v_res_380_);
return v_r_381_;
}
}
uint8_t l_Std_Http_Internal_Char_isHexDigit(uint32_t v_c_382_){
_start:
{
uint32_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = 97;
v___x_384_ = lean_uint32_dec_eq(v_c_382_, v___x_383_);
if (v___x_384_ == 0)
{
uint32_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 98;
v___x_386_ = lean_uint32_dec_eq(v_c_382_, v___x_385_);
if (v___x_386_ == 0)
{
uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 99;
v___x_388_ = lean_uint32_dec_eq(v_c_382_, v___x_387_);
if (v___x_388_ == 0)
{
uint32_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 100;
v___x_390_ = lean_uint32_dec_eq(v_c_382_, v___x_389_);
if (v___x_390_ == 0)
{
uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 101;
v___x_392_ = lean_uint32_dec_eq(v_c_382_, v___x_391_);
if (v___x_392_ == 0)
{
uint32_t v___x_393_; uint8_t v___x_394_; 
v___x_393_ = 102;
v___x_394_ = lean_uint32_dec_eq(v_c_382_, v___x_393_);
if (v___x_394_ == 0)
{
uint32_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = 65;
v___x_396_ = lean_uint32_dec_eq(v_c_382_, v___x_395_);
if (v___x_396_ == 0)
{
uint32_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 66;
v___x_398_ = lean_uint32_dec_eq(v_c_382_, v___x_397_);
if (v___x_398_ == 0)
{
uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_399_ = 67;
v___x_400_ = lean_uint32_dec_eq(v_c_382_, v___x_399_);
if (v___x_400_ == 0)
{
uint32_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = 68;
v___x_402_ = lean_uint32_dec_eq(v_c_382_, v___x_401_);
if (v___x_402_ == 0)
{
uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 69;
v___x_404_ = lean_uint32_dec_eq(v_c_382_, v___x_403_);
if (v___x_404_ == 0)
{
uint32_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 70;
v___x_406_ = lean_uint32_dec_eq(v_c_382_, v___x_405_);
if (v___x_406_ == 0)
{
uint32_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = 48;
v___x_408_ = lean_uint32_dec_le(v___x_407_, v_c_382_);
if (v___x_408_ == 0)
{
return v___x_408_;
}
else
{
uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 57;
v___x_410_ = lean_uint32_dec_le(v_c_382_, v___x_409_);
return v___x_410_;
}
}
else
{
return v___x_406_;
}
}
else
{
return v___x_404_;
}
}
else
{
return v___x_402_;
}
}
else
{
return v___x_400_;
}
}
else
{
return v___x_398_;
}
}
else
{
return v___x_396_;
}
}
else
{
return v___x_394_;
}
}
else
{
return v___x_392_;
}
}
else
{
return v___x_390_;
}
}
else
{
return v___x_388_;
}
}
else
{
return v___x_386_;
}
}
else
{
return v___x_384_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isHexDigit_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_382_ = stack[0].m_num;
uint8_t v_res_411_;
v_res_411_ = l_Std_Http_Internal_Char_isHexDigit(v_c_382_);
stack->m_num = v_res_411_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigit___boxed(lean_object* v_c_412_){
_start:
{
uint32_t v_c_boxed_413_; uint8_t v_res_414_; lean_object* v_r_415_; 
v_c_boxed_413_ = lean_unbox_uint32(v_c_412_);
lean_dec(v_c_412_);
v_res_414_ = l_Std_Http_Internal_Char_isHexDigit(v_c_boxed_413_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
uint8_t l_Std_Http_Internal_Char_isHexDigitByte(uint8_t v_c_416_){
_start:
{
uint8_t v___x_427_; uint8_t v___x_428_; 
v___x_427_ = 48;
v___x_428_ = lean_uint8_dec_le(v___x_427_, v_c_416_);
if (v___x_428_ == 0)
{
goto v___jp_422_;
}
else
{
uint8_t v___x_429_; uint8_t v___x_430_; 
v___x_429_ = 57;
v___x_430_ = lean_uint8_dec_le(v_c_416_, v___x_429_);
if (v___x_430_ == 0)
{
goto v___jp_422_;
}
else
{
return v___x_430_;
}
}
v___jp_417_:
{
uint8_t v___x_418_; uint8_t v___x_419_; 
v___x_418_ = 65;
v___x_419_ = lean_uint8_dec_le(v___x_418_, v_c_416_);
if (v___x_419_ == 0)
{
return v___x_419_;
}
else
{
uint8_t v___x_420_; uint8_t v___x_421_; 
v___x_420_ = 70;
v___x_421_ = lean_uint8_dec_le(v_c_416_, v___x_420_);
return v___x_421_;
}
}
v___jp_422_:
{
uint8_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 97;
v___x_424_ = lean_uint8_dec_le(v___x_423_, v_c_416_);
if (v___x_424_ == 0)
{
goto v___jp_417_;
}
else
{
uint8_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 102;
v___x_426_ = lean_uint8_dec_le(v_c_416_, v___x_425_);
if (v___x_426_ == 0)
{
goto v___jp_417_;
}
else
{
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isHexDigitByte_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_416_ = stack[0].m_num;
uint8_t v_res_431_;
v_res_431_ = l_Std_Http_Internal_Char_isHexDigitByte(v_c_416_);
stack->m_num = v_res_431_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigitByte___boxed(lean_object* v_c_432_){
_start:
{
uint8_t v_c_boxed_433_; uint8_t v_res_434_; lean_object* v_r_435_; 
v_c_boxed_433_ = lean_unbox(v_c_432_);
v_res_434_ = l_Std_Http_Internal_Char_isHexDigitByte(v_c_boxed_433_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
uint8_t l_Std_Http_Internal_Char_isAlphaNum(uint8_t v_c_436_){
_start:
{
uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = 48;
v___x_448_ = lean_uint8_dec_le(v___x_447_, v_c_436_);
if (v___x_448_ == 0)
{
goto v___jp_442_;
}
else
{
uint8_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = 57;
v___x_450_ = lean_uint8_dec_le(v_c_436_, v___x_449_);
if (v___x_450_ == 0)
{
goto v___jp_442_;
}
else
{
return v___x_450_;
}
}
v___jp_437_:
{
uint8_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = 65;
v___x_439_ = lean_uint8_dec_le(v___x_438_, v_c_436_);
if (v___x_439_ == 0)
{
return v___x_439_;
}
else
{
uint8_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = 90;
v___x_441_ = lean_uint8_dec_le(v_c_436_, v___x_440_);
return v___x_441_;
}
}
v___jp_442_:
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 97;
v___x_444_ = lean_uint8_dec_le(v___x_443_, v_c_436_);
if (v___x_444_ == 0)
{
goto v___jp_437_;
}
else
{
uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = 122;
v___x_446_ = lean_uint8_dec_le(v_c_436_, v___x_445_);
if (v___x_446_ == 0)
{
goto v___jp_437_;
}
else
{
return v___x_446_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isAlphaNum_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_436_ = stack[0].m_num;
uint8_t v_res_451_;
v_res_451_ = l_Std_Http_Internal_Char_isAlphaNum(v_c_436_);
stack->m_num = v_res_451_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAlphaNum___boxed(lean_object* v_c_452_){
_start:
{
uint8_t v_c_boxed_453_; uint8_t v_res_454_; lean_object* v_r_455_; 
v_c_boxed_453_ = lean_unbox(v_c_452_);
v_res_454_ = l_Std_Http_Internal_Char_isAlphaNum(v_c_boxed_453_);
v_r_455_ = lean_box(v_res_454_);
return v_r_455_;
}
}
uint8_t l_Std_Http_Internal_Char_isAsciiAlphaNumChar(uint32_t v_c_456_){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_467_ = lean_uint32_to_nat(v_c_456_);
v___x_468_ = lean_unsigned_to_nat(128u);
v___x_469_ = lean_nat_dec_lt(v___x_467_, v___x_468_);
lean_dec(v___x_467_);
if (v___x_469_ == 0)
{
return v___x_469_;
}
else
{
uint32_t v___x_470_; uint8_t v___x_471_; 
v___x_470_ = 48;
v___x_471_ = lean_uint32_dec_le(v___x_470_, v_c_456_);
if (v___x_471_ == 0)
{
goto v___jp_462_;
}
else
{
uint32_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = 57;
v___x_473_ = lean_uint32_dec_le(v_c_456_, v___x_472_);
if (v___x_473_ == 0)
{
goto v___jp_462_;
}
else
{
return v___x_473_;
}
}
}
v___jp_457_:
{
uint32_t v___x_458_; uint8_t v___x_459_; 
v___x_458_ = 97;
v___x_459_ = lean_uint32_dec_le(v___x_458_, v_c_456_);
if (v___x_459_ == 0)
{
return v___x_459_;
}
else
{
uint32_t v___x_460_; uint8_t v___x_461_; 
v___x_460_ = 122;
v___x_461_ = lean_uint32_dec_le(v_c_456_, v___x_460_);
return v___x_461_;
}
}
v___jp_462_:
{
uint32_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = 65;
v___x_464_ = lean_uint32_dec_le(v___x_463_, v_c_456_);
if (v___x_464_ == 0)
{
goto v___jp_457_;
}
else
{
uint32_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = 90;
v___x_466_ = lean_uint32_dec_le(v_c_456_, v___x_465_);
if (v___x_466_ == 0)
{
goto v___jp_457_;
}
else
{
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isAsciiAlphaNumChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_456_ = stack[0].m_num;
uint8_t v_res_474_;
v_res_474_ = l_Std_Http_Internal_Char_isAsciiAlphaNumChar(v_c_456_);
stack->m_num = v_res_474_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAsciiAlphaNumChar___boxed(lean_object* v_c_475_){
_start:
{
uint32_t v_c_boxed_476_; uint8_t v_res_477_; lean_object* v_r_478_; 
v_c_boxed_476_ = lean_unbox_uint32(v_c_475_);
lean_dec(v_c_475_);
v_res_477_ = l_Std_Http_Internal_Char_isAsciiAlphaNumChar(v_c_boxed_476_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
uint8_t l_Std_Http_Internal_Char_isValidSchemeChar(uint32_t v_c_479_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_497_ = lean_uint32_to_nat(v_c_479_);
v___x_498_ = lean_unsigned_to_nat(128u);
v___x_499_ = lean_nat_dec_lt(v___x_497_, v___x_498_);
lean_dec(v___x_497_);
if (v___x_499_ == 0)
{
goto v___jp_480_;
}
else
{
uint32_t v___x_500_; uint8_t v___x_501_; 
v___x_500_ = 48;
v___x_501_ = lean_uint32_dec_le(v___x_500_, v_c_479_);
if (v___x_501_ == 0)
{
goto v___jp_492_;
}
else
{
uint32_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = 57;
v___x_503_ = lean_uint32_dec_le(v_c_479_, v___x_502_);
if (v___x_503_ == 0)
{
goto v___jp_492_;
}
else
{
return v___x_503_;
}
}
}
v___jp_480_:
{
uint32_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = 43;
v___x_482_ = lean_uint32_dec_eq(v_c_479_, v___x_481_);
if (v___x_482_ == 0)
{
uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 45;
v___x_484_ = lean_uint32_dec_eq(v_c_479_, v___x_483_);
if (v___x_484_ == 0)
{
uint32_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = 46;
v___x_486_ = lean_uint32_dec_eq(v_c_479_, v___x_485_);
return v___x_486_;
}
else
{
return v___x_484_;
}
}
else
{
return v___x_482_;
}
}
v___jp_487_:
{
uint32_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = 97;
v___x_489_ = lean_uint32_dec_le(v___x_488_, v_c_479_);
if (v___x_489_ == 0)
{
goto v___jp_480_;
}
else
{
uint32_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = 122;
v___x_491_ = lean_uint32_dec_le(v_c_479_, v___x_490_);
if (v___x_491_ == 0)
{
goto v___jp_480_;
}
else
{
return v___x_491_;
}
}
}
v___jp_492_:
{
uint32_t v___x_493_; uint8_t v___x_494_; 
v___x_493_ = 65;
v___x_494_ = lean_uint32_dec_le(v___x_493_, v_c_479_);
if (v___x_494_ == 0)
{
goto v___jp_487_;
}
else
{
uint32_t v___x_495_; uint8_t v___x_496_; 
v___x_495_ = 90;
v___x_496_ = lean_uint32_dec_le(v_c_479_, v___x_495_);
if (v___x_496_ == 0)
{
goto v___jp_487_;
}
else
{
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isValidSchemeChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_479_ = stack[0].m_num;
uint8_t v_res_504_;
v_res_504_ = l_Std_Http_Internal_Char_isValidSchemeChar(v_c_479_);
stack->m_num = v_res_504_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidSchemeChar___boxed(lean_object* v_c_505_){
_start:
{
uint32_t v_c_boxed_506_; uint8_t v_res_507_; lean_object* v_r_508_; 
v_c_boxed_506_ = lean_unbox_uint32(v_c_505_);
lean_dec(v_c_505_);
v_res_507_ = l_Std_Http_Internal_Char_isValidSchemeChar(v_c_boxed_506_);
v_r_508_ = lean_box(v_res_507_);
return v_r_508_;
}
}
uint8_t l_Std_Http_Internal_Char_isValidDomainNameChar(uint32_t v_c_509_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_525_ = lean_uint32_to_nat(v_c_509_);
v___x_526_ = lean_unsigned_to_nat(128u);
v___x_527_ = lean_nat_dec_lt(v___x_525_, v___x_526_);
lean_dec(v___x_525_);
if (v___x_527_ == 0)
{
goto v___jp_510_;
}
else
{
uint32_t v___x_528_; uint8_t v___x_529_; 
v___x_528_ = 48;
v___x_529_ = lean_uint32_dec_le(v___x_528_, v_c_509_);
if (v___x_529_ == 0)
{
goto v___jp_520_;
}
else
{
uint32_t v___x_530_; uint8_t v___x_531_; 
v___x_530_ = 57;
v___x_531_ = lean_uint32_dec_le(v_c_509_, v___x_530_);
if (v___x_531_ == 0)
{
goto v___jp_520_;
}
else
{
return v___x_531_;
}
}
}
v___jp_510_:
{
uint32_t v___x_511_; uint8_t v___x_512_; 
v___x_511_ = 45;
v___x_512_ = lean_uint32_dec_eq(v_c_509_, v___x_511_);
if (v___x_512_ == 0)
{
uint32_t v___x_513_; uint8_t v___x_514_; 
v___x_513_ = 46;
v___x_514_ = lean_uint32_dec_eq(v_c_509_, v___x_513_);
return v___x_514_;
}
else
{
return v___x_512_;
}
}
v___jp_515_:
{
uint32_t v___x_516_; uint8_t v___x_517_; 
v___x_516_ = 97;
v___x_517_ = lean_uint32_dec_le(v___x_516_, v_c_509_);
if (v___x_517_ == 0)
{
goto v___jp_510_;
}
else
{
uint32_t v___x_518_; uint8_t v___x_519_; 
v___x_518_ = 122;
v___x_519_ = lean_uint32_dec_le(v_c_509_, v___x_518_);
if (v___x_519_ == 0)
{
goto v___jp_510_;
}
else
{
return v___x_519_;
}
}
}
v___jp_520_:
{
uint32_t v___x_521_; uint8_t v___x_522_; 
v___x_521_ = 65;
v___x_522_ = lean_uint32_dec_le(v___x_521_, v_c_509_);
if (v___x_522_ == 0)
{
goto v___jp_515_;
}
else
{
uint32_t v___x_523_; uint8_t v___x_524_; 
v___x_523_ = 90;
v___x_524_ = lean_uint32_dec_le(v_c_509_, v___x_523_);
if (v___x_524_ == 0)
{
goto v___jp_515_;
}
else
{
return v___x_524_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isValidDomainNameChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_509_ = stack[0].m_num;
uint8_t v_res_532_;
v_res_532_ = l_Std_Http_Internal_Char_isValidDomainNameChar(v_c_509_);
stack->m_num = v_res_532_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidDomainNameChar___boxed(lean_object* v_c_533_){
_start:
{
uint32_t v_c_boxed_534_; uint8_t v_res_535_; lean_object* v_r_536_; 
v_c_boxed_534_ = lean_unbox_uint32(v_c_533_);
lean_dec(v_c_533_);
v_res_535_ = l_Std_Http_Internal_Char_isValidDomainNameChar(v_c_boxed_534_);
v_r_536_ = lean_box(v_res_535_);
return v_r_536_;
}
}
uint8_t l_Std_Http_Internal_Char_isUnreserved(uint8_t v_c_537_){
_start:
{
uint8_t v___x_557_; uint8_t v___x_558_; 
v___x_557_ = 48;
v___x_558_ = lean_uint8_dec_le(v___x_557_, v_c_537_);
if (v___x_558_ == 0)
{
goto v___jp_552_;
}
else
{
uint8_t v___x_559_; uint8_t v___x_560_; 
v___x_559_ = 57;
v___x_560_ = lean_uint8_dec_le(v_c_537_, v___x_559_);
if (v___x_560_ == 0)
{
goto v___jp_552_;
}
else
{
return v___x_560_;
}
}
v___jp_538_:
{
uint8_t v___x_539_; uint8_t v___x_540_; 
v___x_539_ = 45;
v___x_540_ = lean_uint8_dec_eq(v_c_537_, v___x_539_);
if (v___x_540_ == 0)
{
uint8_t v___x_541_; uint8_t v___x_542_; 
v___x_541_ = 46;
v___x_542_ = lean_uint8_dec_eq(v_c_537_, v___x_541_);
if (v___x_542_ == 0)
{
uint8_t v___x_543_; uint8_t v___x_544_; 
v___x_543_ = 95;
v___x_544_ = lean_uint8_dec_eq(v_c_537_, v___x_543_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; uint8_t v___x_546_; 
v___x_545_ = 126;
v___x_546_ = lean_uint8_dec_eq(v_c_537_, v___x_545_);
return v___x_546_;
}
else
{
return v___x_544_;
}
}
else
{
return v___x_542_;
}
}
else
{
return v___x_540_;
}
}
v___jp_547_:
{
uint8_t v___x_548_; uint8_t v___x_549_; 
v___x_548_ = 65;
v___x_549_ = lean_uint8_dec_le(v___x_548_, v_c_537_);
if (v___x_549_ == 0)
{
goto v___jp_538_;
}
else
{
uint8_t v___x_550_; uint8_t v___x_551_; 
v___x_550_ = 90;
v___x_551_ = lean_uint8_dec_le(v_c_537_, v___x_550_);
if (v___x_551_ == 0)
{
goto v___jp_538_;
}
else
{
return v___x_551_;
}
}
}
v___jp_552_:
{
uint8_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = 97;
v___x_554_ = lean_uint8_dec_le(v___x_553_, v_c_537_);
if (v___x_554_ == 0)
{
goto v___jp_547_;
}
else
{
uint8_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = 122;
v___x_556_ = lean_uint8_dec_le(v_c_537_, v___x_555_);
if (v___x_556_ == 0)
{
goto v___jp_547_;
}
else
{
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isUnreserved_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_537_ = stack[0].m_num;
uint8_t v_res_561_;
v_res_561_ = l_Std_Http_Internal_Char_isUnreserved(v_c_537_);
stack->m_num = v_res_561_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUnreserved___boxed(lean_object* v_c_562_){
_start:
{
uint8_t v_c_boxed_563_; uint8_t v_res_564_; lean_object* v_r_565_; 
v_c_boxed_563_ = lean_unbox(v_c_562_);
v_res_564_ = l_Std_Http_Internal_Char_isUnreserved(v_c_boxed_563_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
uint8_t l_Std_Http_Internal_Char_isSubDelims(uint8_t v_c_566_){
_start:
{
uint8_t v___x_567_; uint8_t v___x_568_; 
v___x_567_ = 33;
v___x_568_ = lean_uint8_dec_eq(v_c_566_, v___x_567_);
if (v___x_568_ == 0)
{
uint8_t v___x_569_; uint8_t v___x_570_; 
v___x_569_ = 36;
v___x_570_ = lean_uint8_dec_eq(v_c_566_, v___x_569_);
if (v___x_570_ == 0)
{
uint8_t v___x_571_; uint8_t v___x_572_; 
v___x_571_ = 38;
v___x_572_ = lean_uint8_dec_eq(v_c_566_, v___x_571_);
if (v___x_572_ == 0)
{
uint8_t v___x_573_; uint8_t v___x_574_; 
v___x_573_ = 39;
v___x_574_ = lean_uint8_dec_eq(v_c_566_, v___x_573_);
if (v___x_574_ == 0)
{
uint8_t v___x_575_; uint8_t v___x_576_; 
v___x_575_ = 40;
v___x_576_ = lean_uint8_dec_eq(v_c_566_, v___x_575_);
if (v___x_576_ == 0)
{
uint8_t v___x_577_; uint8_t v___x_578_; 
v___x_577_ = 41;
v___x_578_ = lean_uint8_dec_eq(v_c_566_, v___x_577_);
if (v___x_578_ == 0)
{
uint8_t v___x_579_; uint8_t v___x_580_; 
v___x_579_ = 42;
v___x_580_ = lean_uint8_dec_eq(v_c_566_, v___x_579_);
if (v___x_580_ == 0)
{
uint8_t v___x_581_; uint8_t v___x_582_; 
v___x_581_ = 43;
v___x_582_ = lean_uint8_dec_eq(v_c_566_, v___x_581_);
if (v___x_582_ == 0)
{
uint8_t v___x_583_; uint8_t v___x_584_; 
v___x_583_ = 44;
v___x_584_ = lean_uint8_dec_eq(v_c_566_, v___x_583_);
if (v___x_584_ == 0)
{
uint8_t v___x_585_; uint8_t v___x_586_; 
v___x_585_ = 59;
v___x_586_ = lean_uint8_dec_eq(v_c_566_, v___x_585_);
if (v___x_586_ == 0)
{
uint8_t v___x_587_; uint8_t v___x_588_; 
v___x_587_ = 61;
v___x_588_ = lean_uint8_dec_eq(v_c_566_, v___x_587_);
return v___x_588_;
}
else
{
return v___x_586_;
}
}
else
{
return v___x_584_;
}
}
else
{
return v___x_582_;
}
}
else
{
return v___x_580_;
}
}
else
{
return v___x_578_;
}
}
else
{
return v___x_576_;
}
}
else
{
return v___x_574_;
}
}
else
{
return v___x_572_;
}
}
else
{
return v___x_570_;
}
}
else
{
return v___x_568_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isSubDelims_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_566_ = stack[0].m_num;
uint8_t v_res_589_;
v_res_589_ = l_Std_Http_Internal_Char_isSubDelims(v_c_566_);
stack->m_num = v_res_589_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isSubDelims___boxed(lean_object* v_c_590_){
_start:
{
uint8_t v_c_boxed_591_; uint8_t v_res_592_; lean_object* v_r_593_; 
v_c_boxed_591_ = lean_unbox(v_c_590_);
v_res_592_ = l_Std_Http_Internal_Char_isSubDelims(v_c_boxed_591_);
v_r_593_ = lean_box(v_res_592_);
return v_r_593_;
}
}
uint8_t l_Std_Http_Internal_Char_isPChar(uint8_t v_c_594_){
_start:
{
uint8_t v___x_640_; uint8_t v___x_641_; 
v___x_640_ = 48;
v___x_641_ = lean_uint8_dec_le(v___x_640_, v_c_594_);
if (v___x_641_ == 0)
{
goto v___jp_635_;
}
else
{
uint8_t v___x_642_; uint8_t v___x_643_; 
v___x_642_ = 57;
v___x_643_ = lean_uint8_dec_le(v_c_594_, v___x_642_);
if (v___x_643_ == 0)
{
goto v___jp_635_;
}
else
{
return v___x_643_;
}
}
v___jp_595_:
{
uint8_t v___x_596_; uint8_t v___x_597_; 
v___x_596_ = 45;
v___x_597_ = lean_uint8_dec_eq(v_c_594_, v___x_596_);
if (v___x_597_ == 0)
{
uint8_t v___x_598_; uint8_t v___x_599_; 
v___x_598_ = 46;
v___x_599_ = lean_uint8_dec_eq(v_c_594_, v___x_598_);
if (v___x_599_ == 0)
{
uint8_t v___x_600_; uint8_t v___x_601_; 
v___x_600_ = 95;
v___x_601_ = lean_uint8_dec_eq(v_c_594_, v___x_600_);
if (v___x_601_ == 0)
{
uint8_t v___x_602_; uint8_t v___x_603_; 
v___x_602_ = 126;
v___x_603_ = lean_uint8_dec_eq(v_c_594_, v___x_602_);
if (v___x_603_ == 0)
{
uint8_t v___x_604_; uint8_t v___x_605_; 
v___x_604_ = 33;
v___x_605_ = lean_uint8_dec_eq(v_c_594_, v___x_604_);
if (v___x_605_ == 0)
{
uint8_t v___x_606_; uint8_t v___x_607_; 
v___x_606_ = 36;
v___x_607_ = lean_uint8_dec_eq(v_c_594_, v___x_606_);
if (v___x_607_ == 0)
{
uint8_t v___x_608_; uint8_t v___x_609_; 
v___x_608_ = 38;
v___x_609_ = lean_uint8_dec_eq(v_c_594_, v___x_608_);
if (v___x_609_ == 0)
{
uint8_t v___x_610_; uint8_t v___x_611_; 
v___x_610_ = 39;
v___x_611_ = lean_uint8_dec_eq(v_c_594_, v___x_610_);
if (v___x_611_ == 0)
{
uint8_t v___x_612_; uint8_t v___x_613_; 
v___x_612_ = 40;
v___x_613_ = lean_uint8_dec_eq(v_c_594_, v___x_612_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; uint8_t v___x_615_; 
v___x_614_ = 41;
v___x_615_ = lean_uint8_dec_eq(v_c_594_, v___x_614_);
if (v___x_615_ == 0)
{
uint8_t v___x_616_; uint8_t v___x_617_; 
v___x_616_ = 42;
v___x_617_ = lean_uint8_dec_eq(v_c_594_, v___x_616_);
if (v___x_617_ == 0)
{
uint8_t v___x_618_; uint8_t v___x_619_; 
v___x_618_ = 43;
v___x_619_ = lean_uint8_dec_eq(v_c_594_, v___x_618_);
if (v___x_619_ == 0)
{
uint8_t v___x_620_; uint8_t v___x_621_; 
v___x_620_ = 44;
v___x_621_ = lean_uint8_dec_eq(v_c_594_, v___x_620_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; uint8_t v___x_623_; 
v___x_622_ = 59;
v___x_623_ = lean_uint8_dec_eq(v_c_594_, v___x_622_);
if (v___x_623_ == 0)
{
uint8_t v___x_624_; uint8_t v___x_625_; 
v___x_624_ = 61;
v___x_625_ = lean_uint8_dec_eq(v_c_594_, v___x_624_);
if (v___x_625_ == 0)
{
uint8_t v___x_626_; uint8_t v___x_627_; 
v___x_626_ = 58;
v___x_627_ = lean_uint8_dec_eq(v_c_594_, v___x_626_);
if (v___x_627_ == 0)
{
uint8_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = 64;
v___x_629_ = lean_uint8_dec_eq(v_c_594_, v___x_628_);
return v___x_629_;
}
else
{
return v___x_627_;
}
}
else
{
return v___x_625_;
}
}
else
{
return v___x_623_;
}
}
else
{
return v___x_621_;
}
}
else
{
return v___x_619_;
}
}
else
{
return v___x_617_;
}
}
else
{
return v___x_615_;
}
}
else
{
return v___x_613_;
}
}
else
{
return v___x_611_;
}
}
else
{
return v___x_609_;
}
}
else
{
return v___x_607_;
}
}
else
{
return v___x_605_;
}
}
else
{
return v___x_603_;
}
}
else
{
return v___x_601_;
}
}
else
{
return v___x_599_;
}
}
else
{
return v___x_597_;
}
}
v___jp_630_:
{
uint8_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = 65;
v___x_632_ = lean_uint8_dec_le(v___x_631_, v_c_594_);
if (v___x_632_ == 0)
{
goto v___jp_595_;
}
else
{
uint8_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = 90;
v___x_634_ = lean_uint8_dec_le(v_c_594_, v___x_633_);
if (v___x_634_ == 0)
{
goto v___jp_595_;
}
else
{
return v___x_634_;
}
}
}
v___jp_635_:
{
uint8_t v___x_636_; uint8_t v___x_637_; 
v___x_636_ = 97;
v___x_637_ = lean_uint8_dec_le(v___x_636_, v_c_594_);
if (v___x_637_ == 0)
{
goto v___jp_630_;
}
else
{
uint8_t v___x_638_; uint8_t v___x_639_; 
v___x_638_ = 122;
v___x_639_ = lean_uint8_dec_le(v_c_594_, v___x_638_);
if (v___x_639_ == 0)
{
goto v___jp_630_;
}
else
{
return v___x_639_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isPChar_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_594_ = stack[0].m_num;
uint8_t v_res_644_;
v_res_644_ = l_Std_Http_Internal_Char_isPChar(v_c_594_);
stack->m_num = v_res_644_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isPChar___boxed(lean_object* v_c_645_){
_start:
{
uint8_t v_c_boxed_646_; uint8_t v_res_647_; lean_object* v_r_648_; 
v_c_boxed_646_ = lean_unbox(v_c_645_);
v_res_647_ = l_Std_Http_Internal_Char_isPChar(v_c_boxed_646_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
uint8_t l_Std_Http_Internal_Char_isQueryChar(uint8_t v_c_649_){
_start:
{
uint8_t v___x_699_; uint8_t v___x_700_; 
v___x_699_ = 48;
v___x_700_ = lean_uint8_dec_le(v___x_699_, v_c_649_);
if (v___x_700_ == 0)
{
goto v___jp_694_;
}
else
{
uint8_t v___x_701_; uint8_t v___x_702_; 
v___x_701_ = 57;
v___x_702_ = lean_uint8_dec_le(v_c_649_, v___x_701_);
if (v___x_702_ == 0)
{
goto v___jp_694_;
}
else
{
return v___x_702_;
}
}
v___jp_650_:
{
uint8_t v___x_651_; uint8_t v___x_652_; 
v___x_651_ = 45;
v___x_652_ = lean_uint8_dec_eq(v_c_649_, v___x_651_);
if (v___x_652_ == 0)
{
uint8_t v___x_653_; uint8_t v___x_654_; 
v___x_653_ = 46;
v___x_654_ = lean_uint8_dec_eq(v_c_649_, v___x_653_);
if (v___x_654_ == 0)
{
uint8_t v___x_655_; uint8_t v___x_656_; 
v___x_655_ = 95;
v___x_656_ = lean_uint8_dec_eq(v_c_649_, v___x_655_);
if (v___x_656_ == 0)
{
uint8_t v___x_657_; uint8_t v___x_658_; 
v___x_657_ = 126;
v___x_658_ = lean_uint8_dec_eq(v_c_649_, v___x_657_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; uint8_t v___x_660_; 
v___x_659_ = 33;
v___x_660_ = lean_uint8_dec_eq(v_c_649_, v___x_659_);
if (v___x_660_ == 0)
{
uint8_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = 36;
v___x_662_ = lean_uint8_dec_eq(v_c_649_, v___x_661_);
if (v___x_662_ == 0)
{
uint8_t v___x_663_; uint8_t v___x_664_; 
v___x_663_ = 38;
v___x_664_ = lean_uint8_dec_eq(v_c_649_, v___x_663_);
if (v___x_664_ == 0)
{
uint8_t v___x_665_; uint8_t v___x_666_; 
v___x_665_ = 39;
v___x_666_ = lean_uint8_dec_eq(v_c_649_, v___x_665_);
if (v___x_666_ == 0)
{
uint8_t v___x_667_; uint8_t v___x_668_; 
v___x_667_ = 40;
v___x_668_ = lean_uint8_dec_eq(v_c_649_, v___x_667_);
if (v___x_668_ == 0)
{
uint8_t v___x_669_; uint8_t v___x_670_; 
v___x_669_ = 41;
v___x_670_ = lean_uint8_dec_eq(v_c_649_, v___x_669_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; uint8_t v___x_672_; 
v___x_671_ = 42;
v___x_672_ = lean_uint8_dec_eq(v_c_649_, v___x_671_);
if (v___x_672_ == 0)
{
uint8_t v___x_673_; uint8_t v___x_674_; 
v___x_673_ = 43;
v___x_674_ = lean_uint8_dec_eq(v_c_649_, v___x_673_);
if (v___x_674_ == 0)
{
uint8_t v___x_675_; uint8_t v___x_676_; 
v___x_675_ = 44;
v___x_676_ = lean_uint8_dec_eq(v_c_649_, v___x_675_);
if (v___x_676_ == 0)
{
uint8_t v___x_677_; uint8_t v___x_678_; 
v___x_677_ = 59;
v___x_678_ = lean_uint8_dec_eq(v_c_649_, v___x_677_);
if (v___x_678_ == 0)
{
uint8_t v___x_679_; uint8_t v___x_680_; 
v___x_679_ = 61;
v___x_680_ = lean_uint8_dec_eq(v_c_649_, v___x_679_);
if (v___x_680_ == 0)
{
uint8_t v___x_681_; uint8_t v___x_682_; 
v___x_681_ = 58;
v___x_682_ = lean_uint8_dec_eq(v_c_649_, v___x_681_);
if (v___x_682_ == 0)
{
uint8_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = 64;
v___x_684_ = lean_uint8_dec_eq(v_c_649_, v___x_683_);
if (v___x_684_ == 0)
{
uint8_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = 47;
v___x_686_ = lean_uint8_dec_eq(v_c_649_, v___x_685_);
if (v___x_686_ == 0)
{
uint8_t v___x_687_; uint8_t v___x_688_; 
v___x_687_ = 63;
v___x_688_ = lean_uint8_dec_eq(v_c_649_, v___x_687_);
return v___x_688_;
}
else
{
return v___x_686_;
}
}
else
{
return v___x_684_;
}
}
else
{
return v___x_682_;
}
}
else
{
return v___x_680_;
}
}
else
{
return v___x_678_;
}
}
else
{
return v___x_676_;
}
}
else
{
return v___x_674_;
}
}
else
{
return v___x_672_;
}
}
else
{
return v___x_670_;
}
}
else
{
return v___x_668_;
}
}
else
{
return v___x_666_;
}
}
else
{
return v___x_664_;
}
}
else
{
return v___x_662_;
}
}
else
{
return v___x_660_;
}
}
else
{
return v___x_658_;
}
}
else
{
return v___x_656_;
}
}
else
{
return v___x_654_;
}
}
else
{
return v___x_652_;
}
}
v___jp_689_:
{
uint8_t v___x_690_; uint8_t v___x_691_; 
v___x_690_ = 65;
v___x_691_ = lean_uint8_dec_le(v___x_690_, v_c_649_);
if (v___x_691_ == 0)
{
goto v___jp_650_;
}
else
{
uint8_t v___x_692_; uint8_t v___x_693_; 
v___x_692_ = 90;
v___x_693_ = lean_uint8_dec_le(v_c_649_, v___x_692_);
if (v___x_693_ == 0)
{
goto v___jp_650_;
}
else
{
return v___x_693_;
}
}
}
v___jp_694_:
{
uint8_t v___x_695_; uint8_t v___x_696_; 
v___x_695_ = 97;
v___x_696_ = lean_uint8_dec_le(v___x_695_, v_c_649_);
if (v___x_696_ == 0)
{
goto v___jp_689_;
}
else
{
uint8_t v___x_697_; uint8_t v___x_698_; 
v___x_697_ = 122;
v___x_698_ = lean_uint8_dec_le(v_c_649_, v___x_697_);
if (v___x_698_ == 0)
{
goto v___jp_689_;
}
else
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isQueryChar_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_649_ = stack[0].m_num;
uint8_t v_res_703_;
v_res_703_ = l_Std_Http_Internal_Char_isQueryChar(v_c_649_);
stack->m_num = v_res_703_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryChar___boxed(lean_object* v_c_704_){
_start:
{
uint8_t v_c_boxed_705_; uint8_t v_res_706_; lean_object* v_r_707_; 
v_c_boxed_705_ = lean_unbox(v_c_704_);
v_res_706_ = l_Std_Http_Internal_Char_isQueryChar(v_c_boxed_705_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
uint8_t l_Std_Http_Internal_Char_isFragmentChar(uint8_t v_c_708_){
_start:
{
uint8_t v___x_758_; uint8_t v___x_759_; 
v___x_758_ = 48;
v___x_759_ = lean_uint8_dec_le(v___x_758_, v_c_708_);
if (v___x_759_ == 0)
{
goto v___jp_753_;
}
else
{
uint8_t v___x_760_; uint8_t v___x_761_; 
v___x_760_ = 57;
v___x_761_ = lean_uint8_dec_le(v_c_708_, v___x_760_);
if (v___x_761_ == 0)
{
goto v___jp_753_;
}
else
{
return v___x_761_;
}
}
v___jp_709_:
{
uint8_t v___x_710_; uint8_t v___x_711_; 
v___x_710_ = 45;
v___x_711_ = lean_uint8_dec_eq(v_c_708_, v___x_710_);
if (v___x_711_ == 0)
{
uint8_t v___x_712_; uint8_t v___x_713_; 
v___x_712_ = 46;
v___x_713_ = lean_uint8_dec_eq(v_c_708_, v___x_712_);
if (v___x_713_ == 0)
{
uint8_t v___x_714_; uint8_t v___x_715_; 
v___x_714_ = 95;
v___x_715_ = lean_uint8_dec_eq(v_c_708_, v___x_714_);
if (v___x_715_ == 0)
{
uint8_t v___x_716_; uint8_t v___x_717_; 
v___x_716_ = 126;
v___x_717_ = lean_uint8_dec_eq(v_c_708_, v___x_716_);
if (v___x_717_ == 0)
{
uint8_t v___x_718_; uint8_t v___x_719_; 
v___x_718_ = 33;
v___x_719_ = lean_uint8_dec_eq(v_c_708_, v___x_718_);
if (v___x_719_ == 0)
{
uint8_t v___x_720_; uint8_t v___x_721_; 
v___x_720_ = 36;
v___x_721_ = lean_uint8_dec_eq(v_c_708_, v___x_720_);
if (v___x_721_ == 0)
{
uint8_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = 38;
v___x_723_ = lean_uint8_dec_eq(v_c_708_, v___x_722_);
if (v___x_723_ == 0)
{
uint8_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = 39;
v___x_725_ = lean_uint8_dec_eq(v_c_708_, v___x_724_);
if (v___x_725_ == 0)
{
uint8_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 40;
v___x_727_ = lean_uint8_dec_eq(v_c_708_, v___x_726_);
if (v___x_727_ == 0)
{
uint8_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 41;
v___x_729_ = lean_uint8_dec_eq(v_c_708_, v___x_728_);
if (v___x_729_ == 0)
{
uint8_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = 42;
v___x_731_ = lean_uint8_dec_eq(v_c_708_, v___x_730_);
if (v___x_731_ == 0)
{
uint8_t v___x_732_; uint8_t v___x_733_; 
v___x_732_ = 43;
v___x_733_ = lean_uint8_dec_eq(v_c_708_, v___x_732_);
if (v___x_733_ == 0)
{
uint8_t v___x_734_; uint8_t v___x_735_; 
v___x_734_ = 44;
v___x_735_ = lean_uint8_dec_eq(v_c_708_, v___x_734_);
if (v___x_735_ == 0)
{
uint8_t v___x_736_; uint8_t v___x_737_; 
v___x_736_ = 59;
v___x_737_ = lean_uint8_dec_eq(v_c_708_, v___x_736_);
if (v___x_737_ == 0)
{
uint8_t v___x_738_; uint8_t v___x_739_; 
v___x_738_ = 61;
v___x_739_ = lean_uint8_dec_eq(v_c_708_, v___x_738_);
if (v___x_739_ == 0)
{
uint8_t v___x_740_; uint8_t v___x_741_; 
v___x_740_ = 58;
v___x_741_ = lean_uint8_dec_eq(v_c_708_, v___x_740_);
if (v___x_741_ == 0)
{
uint8_t v___x_742_; uint8_t v___x_743_; 
v___x_742_ = 64;
v___x_743_ = lean_uint8_dec_eq(v_c_708_, v___x_742_);
if (v___x_743_ == 0)
{
uint8_t v___x_744_; uint8_t v___x_745_; 
v___x_744_ = 47;
v___x_745_ = lean_uint8_dec_eq(v_c_708_, v___x_744_);
if (v___x_745_ == 0)
{
uint8_t v___x_746_; uint8_t v___x_747_; 
v___x_746_ = 63;
v___x_747_ = lean_uint8_dec_eq(v_c_708_, v___x_746_);
return v___x_747_;
}
else
{
return v___x_745_;
}
}
else
{
return v___x_743_;
}
}
else
{
return v___x_741_;
}
}
else
{
return v___x_739_;
}
}
else
{
return v___x_737_;
}
}
else
{
return v___x_735_;
}
}
else
{
return v___x_733_;
}
}
else
{
return v___x_731_;
}
}
else
{
return v___x_729_;
}
}
else
{
return v___x_727_;
}
}
else
{
return v___x_725_;
}
}
else
{
return v___x_723_;
}
}
else
{
return v___x_721_;
}
}
else
{
return v___x_719_;
}
}
else
{
return v___x_717_;
}
}
else
{
return v___x_715_;
}
}
else
{
return v___x_713_;
}
}
else
{
return v___x_711_;
}
}
v___jp_748_:
{
uint8_t v___x_749_; uint8_t v___x_750_; 
v___x_749_ = 65;
v___x_750_ = lean_uint8_dec_le(v___x_749_, v_c_708_);
if (v___x_750_ == 0)
{
goto v___jp_709_;
}
else
{
uint8_t v___x_751_; uint8_t v___x_752_; 
v___x_751_ = 90;
v___x_752_ = lean_uint8_dec_le(v_c_708_, v___x_751_);
if (v___x_752_ == 0)
{
goto v___jp_709_;
}
else
{
return v___x_752_;
}
}
}
v___jp_753_:
{
uint8_t v___x_754_; uint8_t v___x_755_; 
v___x_754_ = 97;
v___x_755_ = lean_uint8_dec_le(v___x_754_, v_c_708_);
if (v___x_755_ == 0)
{
goto v___jp_748_;
}
else
{
uint8_t v___x_756_; uint8_t v___x_757_; 
v___x_756_ = 122;
v___x_757_ = lean_uint8_dec_le(v_c_708_, v___x_756_);
if (v___x_757_ == 0)
{
goto v___jp_748_;
}
else
{
return v___x_757_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isFragmentChar_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_708_ = stack[0].m_num;
uint8_t v_res_762_;
v_res_762_ = l_Std_Http_Internal_Char_isFragmentChar(v_c_708_);
stack->m_num = v_res_762_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isFragmentChar___boxed(lean_object* v_c_763_){
_start:
{
uint8_t v_c_boxed_764_; uint8_t v_res_765_; lean_object* v_r_766_; 
v_c_boxed_764_ = lean_unbox(v_c_763_);
v_res_765_ = l_Std_Http_Internal_Char_isFragmentChar(v_c_boxed_764_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
uint8_t l_Std_Http_Internal_Char_isUserInfoChar(uint8_t v_c_767_){
_start:
{
uint8_t v___x_811_; uint8_t v___x_812_; 
v___x_811_ = 48;
v___x_812_ = lean_uint8_dec_le(v___x_811_, v_c_767_);
if (v___x_812_ == 0)
{
goto v___jp_806_;
}
else
{
uint8_t v___x_813_; uint8_t v___x_814_; 
v___x_813_ = 57;
v___x_814_ = lean_uint8_dec_le(v_c_767_, v___x_813_);
if (v___x_814_ == 0)
{
goto v___jp_806_;
}
else
{
return v___x_814_;
}
}
v___jp_768_:
{
uint8_t v___x_769_; uint8_t v___x_770_; 
v___x_769_ = 45;
v___x_770_ = lean_uint8_dec_eq(v_c_767_, v___x_769_);
if (v___x_770_ == 0)
{
uint8_t v___x_771_; uint8_t v___x_772_; 
v___x_771_ = 46;
v___x_772_ = lean_uint8_dec_eq(v_c_767_, v___x_771_);
if (v___x_772_ == 0)
{
uint8_t v___x_773_; uint8_t v___x_774_; 
v___x_773_ = 95;
v___x_774_ = lean_uint8_dec_eq(v_c_767_, v___x_773_);
if (v___x_774_ == 0)
{
uint8_t v___x_775_; uint8_t v___x_776_; 
v___x_775_ = 126;
v___x_776_ = lean_uint8_dec_eq(v_c_767_, v___x_775_);
if (v___x_776_ == 0)
{
uint8_t v___x_777_; uint8_t v___x_778_; 
v___x_777_ = 33;
v___x_778_ = lean_uint8_dec_eq(v_c_767_, v___x_777_);
if (v___x_778_ == 0)
{
uint8_t v___x_779_; uint8_t v___x_780_; 
v___x_779_ = 36;
v___x_780_ = lean_uint8_dec_eq(v_c_767_, v___x_779_);
if (v___x_780_ == 0)
{
uint8_t v___x_781_; uint8_t v___x_782_; 
v___x_781_ = 38;
v___x_782_ = lean_uint8_dec_eq(v_c_767_, v___x_781_);
if (v___x_782_ == 0)
{
uint8_t v___x_783_; uint8_t v___x_784_; 
v___x_783_ = 39;
v___x_784_ = lean_uint8_dec_eq(v_c_767_, v___x_783_);
if (v___x_784_ == 0)
{
uint8_t v___x_785_; uint8_t v___x_786_; 
v___x_785_ = 40;
v___x_786_ = lean_uint8_dec_eq(v_c_767_, v___x_785_);
if (v___x_786_ == 0)
{
uint8_t v___x_787_; uint8_t v___x_788_; 
v___x_787_ = 41;
v___x_788_ = lean_uint8_dec_eq(v_c_767_, v___x_787_);
if (v___x_788_ == 0)
{
uint8_t v___x_789_; uint8_t v___x_790_; 
v___x_789_ = 42;
v___x_790_ = lean_uint8_dec_eq(v_c_767_, v___x_789_);
if (v___x_790_ == 0)
{
uint8_t v___x_791_; uint8_t v___x_792_; 
v___x_791_ = 43;
v___x_792_ = lean_uint8_dec_eq(v_c_767_, v___x_791_);
if (v___x_792_ == 0)
{
uint8_t v___x_793_; uint8_t v___x_794_; 
v___x_793_ = 44;
v___x_794_ = lean_uint8_dec_eq(v_c_767_, v___x_793_);
if (v___x_794_ == 0)
{
uint8_t v___x_795_; uint8_t v___x_796_; 
v___x_795_ = 59;
v___x_796_ = lean_uint8_dec_eq(v_c_767_, v___x_795_);
if (v___x_796_ == 0)
{
uint8_t v___x_797_; uint8_t v___x_798_; 
v___x_797_ = 61;
v___x_798_ = lean_uint8_dec_eq(v_c_767_, v___x_797_);
if (v___x_798_ == 0)
{
uint8_t v___x_799_; uint8_t v___x_800_; 
v___x_799_ = 58;
v___x_800_ = lean_uint8_dec_eq(v_c_767_, v___x_799_);
return v___x_800_;
}
else
{
return v___x_798_;
}
}
else
{
return v___x_796_;
}
}
else
{
return v___x_794_;
}
}
else
{
return v___x_792_;
}
}
else
{
return v___x_790_;
}
}
else
{
return v___x_788_;
}
}
else
{
return v___x_786_;
}
}
else
{
return v___x_784_;
}
}
else
{
return v___x_782_;
}
}
else
{
return v___x_780_;
}
}
else
{
return v___x_778_;
}
}
else
{
return v___x_776_;
}
}
else
{
return v___x_774_;
}
}
else
{
return v___x_772_;
}
}
else
{
return v___x_770_;
}
}
v___jp_801_:
{
uint8_t v___x_802_; uint8_t v___x_803_; 
v___x_802_ = 65;
v___x_803_ = lean_uint8_dec_le(v___x_802_, v_c_767_);
if (v___x_803_ == 0)
{
goto v___jp_768_;
}
else
{
uint8_t v___x_804_; uint8_t v___x_805_; 
v___x_804_ = 90;
v___x_805_ = lean_uint8_dec_le(v_c_767_, v___x_804_);
if (v___x_805_ == 0)
{
goto v___jp_768_;
}
else
{
return v___x_805_;
}
}
}
v___jp_806_:
{
uint8_t v___x_807_; uint8_t v___x_808_; 
v___x_807_ = 97;
v___x_808_ = lean_uint8_dec_le(v___x_807_, v_c_767_);
if (v___x_808_ == 0)
{
goto v___jp_801_;
}
else
{
uint8_t v___x_809_; uint8_t v___x_810_; 
v___x_809_ = 122;
v___x_810_ = lean_uint8_dec_le(v_c_767_, v___x_809_);
if (v___x_810_ == 0)
{
goto v___jp_801_;
}
else
{
return v___x_810_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isUserInfoChar_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_767_ = stack[0].m_num;
uint8_t v_res_815_;
v_res_815_ = l_Std_Http_Internal_Char_isUserInfoChar(v_c_767_);
stack->m_num = v_res_815_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUserInfoChar___boxed(lean_object* v_c_816_){
_start:
{
uint8_t v_c_boxed_817_; uint8_t v_res_818_; lean_object* v_r_819_; 
v_c_boxed_817_ = lean_unbox(v_c_816_);
v_res_818_ = l_Std_Http_Internal_Char_isUserInfoChar(v_c_boxed_817_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
uint8_t l_Std_Http_Internal_Char_isQueryDataChar(uint8_t v_c_820_){
_start:
{
uint8_t v___x_877_; uint8_t v___x_878_; 
v___x_877_ = 48;
v___x_878_ = lean_uint8_dec_le(v___x_877_, v_c_820_);
if (v___x_878_ == 0)
{
goto v___jp_872_;
}
else
{
uint8_t v___x_879_; uint8_t v___x_880_; 
v___x_879_ = 57;
v___x_880_ = lean_uint8_dec_le(v_c_820_, v___x_879_);
if (v___x_880_ == 0)
{
goto v___jp_872_;
}
else
{
goto v___jp_821_;
}
}
v___jp_821_:
{
uint8_t v___x_822_; uint8_t v___x_823_; 
v___x_822_ = 38;
v___x_823_ = lean_uint8_dec_eq(v_c_820_, v___x_822_);
if (v___x_823_ == 0)
{
uint8_t v___x_824_; uint8_t v___x_825_; 
v___x_824_ = 61;
v___x_825_ = lean_uint8_dec_eq(v_c_820_, v___x_824_);
if (v___x_825_ == 0)
{
uint8_t v___x_826_; 
v___x_826_ = 1;
return v___x_826_;
}
else
{
return v___x_823_;
}
}
else
{
uint8_t v___x_827_; 
v___x_827_ = 0;
return v___x_827_;
}
}
v___jp_828_:
{
uint8_t v___x_829_; uint8_t v___x_830_; 
v___x_829_ = 45;
v___x_830_ = lean_uint8_dec_eq(v_c_820_, v___x_829_);
if (v___x_830_ == 0)
{
uint8_t v___x_831_; uint8_t v___x_832_; 
v___x_831_ = 46;
v___x_832_ = lean_uint8_dec_eq(v_c_820_, v___x_831_);
if (v___x_832_ == 0)
{
uint8_t v___x_833_; uint8_t v___x_834_; 
v___x_833_ = 95;
v___x_834_ = lean_uint8_dec_eq(v_c_820_, v___x_833_);
if (v___x_834_ == 0)
{
uint8_t v___x_835_; uint8_t v___x_836_; 
v___x_835_ = 126;
v___x_836_ = lean_uint8_dec_eq(v_c_820_, v___x_835_);
if (v___x_836_ == 0)
{
uint8_t v___x_837_; uint8_t v___x_838_; 
v___x_837_ = 33;
v___x_838_ = lean_uint8_dec_eq(v_c_820_, v___x_837_);
if (v___x_838_ == 0)
{
uint8_t v___x_839_; uint8_t v___x_840_; 
v___x_839_ = 36;
v___x_840_ = lean_uint8_dec_eq(v_c_820_, v___x_839_);
if (v___x_840_ == 0)
{
uint8_t v___x_841_; uint8_t v___x_842_; 
v___x_841_ = 38;
v___x_842_ = lean_uint8_dec_eq(v_c_820_, v___x_841_);
if (v___x_842_ == 0)
{
uint8_t v___x_843_; uint8_t v___x_844_; 
v___x_843_ = 39;
v___x_844_ = lean_uint8_dec_eq(v_c_820_, v___x_843_);
if (v___x_844_ == 0)
{
uint8_t v___x_845_; uint8_t v___x_846_; 
v___x_845_ = 40;
v___x_846_ = lean_uint8_dec_eq(v_c_820_, v___x_845_);
if (v___x_846_ == 0)
{
uint8_t v___x_847_; uint8_t v___x_848_; 
v___x_847_ = 41;
v___x_848_ = lean_uint8_dec_eq(v_c_820_, v___x_847_);
if (v___x_848_ == 0)
{
uint8_t v___x_849_; uint8_t v___x_850_; 
v___x_849_ = 42;
v___x_850_ = lean_uint8_dec_eq(v_c_820_, v___x_849_);
if (v___x_850_ == 0)
{
uint8_t v___x_851_; uint8_t v___x_852_; 
v___x_851_ = 43;
v___x_852_ = lean_uint8_dec_eq(v_c_820_, v___x_851_);
if (v___x_852_ == 0)
{
uint8_t v___x_853_; uint8_t v___x_854_; 
v___x_853_ = 44;
v___x_854_ = lean_uint8_dec_eq(v_c_820_, v___x_853_);
if (v___x_854_ == 0)
{
uint8_t v___x_855_; uint8_t v___x_856_; 
v___x_855_ = 59;
v___x_856_ = lean_uint8_dec_eq(v_c_820_, v___x_855_);
if (v___x_856_ == 0)
{
uint8_t v___x_857_; uint8_t v___x_858_; 
v___x_857_ = 61;
v___x_858_ = lean_uint8_dec_eq(v_c_820_, v___x_857_);
if (v___x_858_ == 0)
{
uint8_t v___x_859_; uint8_t v___x_860_; 
v___x_859_ = 58;
v___x_860_ = lean_uint8_dec_eq(v_c_820_, v___x_859_);
if (v___x_860_ == 0)
{
uint8_t v___x_861_; uint8_t v___x_862_; 
v___x_861_ = 64;
v___x_862_ = lean_uint8_dec_eq(v_c_820_, v___x_861_);
if (v___x_862_ == 0)
{
uint8_t v___x_863_; uint8_t v___x_864_; 
v___x_863_ = 47;
v___x_864_ = lean_uint8_dec_eq(v_c_820_, v___x_863_);
if (v___x_864_ == 0)
{
uint8_t v___x_865_; uint8_t v___x_866_; 
v___x_865_ = 63;
v___x_866_ = lean_uint8_dec_eq(v_c_820_, v___x_865_);
if (v___x_866_ == 0)
{
return v___x_866_;
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
else
{
goto v___jp_821_;
}
}
v___jp_867_:
{
uint8_t v___x_868_; uint8_t v___x_869_; 
v___x_868_ = 65;
v___x_869_ = lean_uint8_dec_le(v___x_868_, v_c_820_);
if (v___x_869_ == 0)
{
goto v___jp_828_;
}
else
{
uint8_t v___x_870_; uint8_t v___x_871_; 
v___x_870_ = 90;
v___x_871_ = lean_uint8_dec_le(v_c_820_, v___x_870_);
if (v___x_871_ == 0)
{
goto v___jp_828_;
}
else
{
goto v___jp_821_;
}
}
}
v___jp_872_:
{
uint8_t v___x_873_; uint8_t v___x_874_; 
v___x_873_ = 97;
v___x_874_ = lean_uint8_dec_le(v___x_873_, v_c_820_);
if (v___x_874_ == 0)
{
goto v___jp_867_;
}
else
{
uint8_t v___x_875_; uint8_t v___x_876_; 
v___x_875_ = 122;
v___x_876_ = lean_uint8_dec_le(v_c_820_, v___x_875_);
if (v___x_876_ == 0)
{
goto v___jp_867_;
}
else
{
goto v___jp_821_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Char_isQueryDataChar_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_820_ = stack[0].m_num;
uint8_t v_res_881_;
v_res_881_ = l_Std_Http_Internal_Char_isQueryDataChar(v_c_820_);
stack->m_num = v_res_881_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryDataChar___boxed(lean_object* v_c_882_){
_start:
{
uint8_t v_c_boxed_883_; uint8_t v_res_884_; lean_object* v_r_885_; 
v_c_boxed_883_ = lean_unbox(v_c_882_);
v_res_884_ = l_Std_Http_Internal_Char_isQueryDataChar(v_c_boxed_883_);
v_r_885_ = lean_box(v_res_884_);
return v_r_885_;
}
}
lean_object* runtime_initialize_Init_Data_Char(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Internal_Char(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Internal_Char(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Char(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Internal_Char(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Internal_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Internal_Char(builtin);
}
#ifdef __cplusplus
}
#endif
