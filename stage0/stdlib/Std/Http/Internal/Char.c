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
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAscii(uint32_t v_c_1_){
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAscii___boxed(lean_object* v_c_5_){
_start:
{
uint32_t v_c_boxed_6_; uint8_t v_res_7_; lean_object* v_r_8_; 
v_c_boxed_6_ = lean_unbox_uint32(v_c_5_);
lean_dec(v_c_5_);
v_res_7_ = l_Std_Http_Internal_Char_isAscii(v_c_boxed_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAsciiByte(uint8_t v_c_9_){
_start:
{
uint8_t v___x_10_; uint8_t v___x_11_; 
v___x_10_ = 128;
v___x_11_ = lean_uint8_dec_lt(v_c_9_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAsciiByte___boxed(lean_object* v_c_12_){
_start:
{
uint8_t v_c_boxed_13_; uint8_t v_res_14_; lean_object* v_r_15_; 
v_c_boxed_13_ = lean_unbox(v_c_12_);
v_res_14_ = l_Std_Http_Internal_Char_isAsciiByte(v_c_boxed_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isDigitByte(uint8_t v_c_16_){
_start:
{
uint8_t v___x_17_; uint8_t v___x_18_; 
v___x_17_ = 48;
v___x_18_ = lean_uint8_dec_le(v___x_17_, v_c_16_);
if (v___x_18_ == 0)
{
return v___x_18_;
}
else
{
uint8_t v___x_19_; uint8_t v___x_20_; 
v___x_19_ = 57;
v___x_20_ = lean_uint8_dec_le(v_c_16_, v___x_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isDigitByte___boxed(lean_object* v_c_21_){
_start:
{
uint8_t v_c_boxed_22_; uint8_t v_res_23_; lean_object* v_r_24_; 
v_c_boxed_22_ = lean_unbox(v_c_21_);
v_res_23_ = l_Std_Http_Internal_Char_isDigitByte(v_c_boxed_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAlphaByte(uint8_t v_c_25_){
_start:
{
uint8_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 65;
v___x_32_ = lean_uint8_dec_le(v___x_31_, v_c_25_);
if (v___x_32_ == 0)
{
goto v___jp_26_;
}
else
{
uint8_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = 90;
v___x_34_ = lean_uint8_dec_le(v_c_25_, v___x_33_);
if (v___x_34_ == 0)
{
goto v___jp_26_;
}
else
{
return v___x_34_;
}
}
v___jp_26_:
{
uint8_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 97;
v___x_28_ = lean_uint8_dec_le(v___x_27_, v_c_25_);
if (v___x_28_ == 0)
{
return v___x_28_;
}
else
{
uint8_t v___x_29_; uint8_t v___x_30_; 
v___x_29_ = 122;
v___x_30_ = lean_uint8_dec_le(v_c_25_, v___x_29_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAlphaByte___boxed(lean_object* v_c_35_){
_start:
{
uint8_t v_c_boxed_36_; uint8_t v_res_37_; lean_object* v_r_38_; 
v_c_boxed_36_ = lean_unbox(v_c_35_);
v_res_37_ = l_Std_Http_Internal_Char_isAlphaByte(v_c_boxed_36_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_tchar(uint32_t v_c_39_){
_start:
{
uint8_t v___y_41_; uint32_t v___x_51_; uint8_t v___x_52_; 
v___x_51_ = 33;
v___x_52_ = lean_uint32_dec_eq(v_c_39_, v___x_51_);
if (v___x_52_ == 0)
{
uint32_t v___x_53_; uint8_t v___x_54_; 
v___x_53_ = 35;
v___x_54_ = lean_uint32_dec_eq(v_c_39_, v___x_53_);
if (v___x_54_ == 0)
{
uint32_t v___x_55_; uint8_t v___x_56_; 
v___x_55_ = 36;
v___x_56_ = lean_uint32_dec_eq(v_c_39_, v___x_55_);
if (v___x_56_ == 0)
{
uint32_t v___x_57_; uint8_t v___x_58_; 
v___x_57_ = 37;
v___x_58_ = lean_uint32_dec_eq(v_c_39_, v___x_57_);
if (v___x_58_ == 0)
{
uint32_t v___x_59_; uint8_t v___x_60_; 
v___x_59_ = 38;
v___x_60_ = lean_uint32_dec_eq(v_c_39_, v___x_59_);
if (v___x_60_ == 0)
{
uint32_t v___x_61_; uint8_t v___x_62_; 
v___x_61_ = 39;
v___x_62_ = lean_uint32_dec_eq(v_c_39_, v___x_61_);
if (v___x_62_ == 0)
{
uint32_t v___x_63_; uint8_t v___x_64_; 
v___x_63_ = 42;
v___x_64_ = lean_uint32_dec_eq(v_c_39_, v___x_63_);
if (v___x_64_ == 0)
{
uint32_t v___x_65_; uint8_t v___x_66_; 
v___x_65_ = 43;
v___x_66_ = lean_uint32_dec_eq(v_c_39_, v___x_65_);
if (v___x_66_ == 0)
{
uint32_t v___x_67_; uint8_t v___x_68_; 
v___x_67_ = 45;
v___x_68_ = lean_uint32_dec_eq(v_c_39_, v___x_67_);
if (v___x_68_ == 0)
{
uint32_t v___x_69_; uint8_t v___x_70_; 
v___x_69_ = 46;
v___x_70_ = lean_uint32_dec_eq(v_c_39_, v___x_69_);
if (v___x_70_ == 0)
{
uint32_t v___x_71_; uint8_t v___x_72_; 
v___x_71_ = 94;
v___x_72_ = lean_uint32_dec_eq(v_c_39_, v___x_71_);
if (v___x_72_ == 0)
{
uint32_t v___x_73_; uint8_t v___x_74_; 
v___x_73_ = 95;
v___x_74_ = lean_uint32_dec_eq(v_c_39_, v___x_73_);
if (v___x_74_ == 0)
{
uint32_t v___x_75_; uint8_t v___x_76_; 
v___x_75_ = 96;
v___x_76_ = lean_uint32_dec_eq(v_c_39_, v___x_75_);
if (v___x_76_ == 0)
{
uint32_t v___x_77_; uint8_t v___x_78_; 
v___x_77_ = 124;
v___x_78_ = lean_uint32_dec_eq(v_c_39_, v___x_77_);
if (v___x_78_ == 0)
{
uint32_t v___x_79_; uint8_t v___x_80_; 
v___x_79_ = 126;
v___x_80_ = lean_uint32_dec_eq(v_c_39_, v___x_79_);
if (v___x_80_ == 0)
{
uint32_t v___x_81_; uint8_t v___x_82_; 
v___x_81_ = 48;
v___x_82_ = lean_uint32_dec_le(v___x_81_, v_c_39_);
if (v___x_82_ == 0)
{
goto v___jp_46_;
}
else
{
uint32_t v___x_83_; uint8_t v___x_84_; 
v___x_83_ = 57;
v___x_84_ = lean_uint32_dec_le(v_c_39_, v___x_83_);
if (v___x_84_ == 0)
{
goto v___jp_46_;
}
else
{
return v___x_84_;
}
}
}
else
{
return v___x_80_;
}
}
else
{
return v___x_78_;
}
}
else
{
return v___x_76_;
}
}
else
{
return v___x_74_;
}
}
else
{
return v___x_72_;
}
}
else
{
return v___x_70_;
}
}
else
{
return v___x_68_;
}
}
else
{
return v___x_66_;
}
}
else
{
return v___x_64_;
}
}
else
{
return v___x_62_;
}
}
else
{
return v___x_60_;
}
}
else
{
return v___x_58_;
}
}
else
{
return v___x_56_;
}
}
else
{
return v___x_54_;
}
}
else
{
return v___x_52_;
}
v___jp_40_:
{
if (v___y_41_ == 0)
{
uint32_t v___x_42_; uint8_t v___x_43_; 
v___x_42_ = 97;
v___x_43_ = lean_uint32_dec_le(v___x_42_, v_c_39_);
if (v___x_43_ == 0)
{
return v___x_43_;
}
else
{
uint32_t v___x_44_; uint8_t v___x_45_; 
v___x_44_ = 122;
v___x_45_ = lean_uint32_dec_le(v_c_39_, v___x_44_);
return v___x_45_;
}
}
else
{
return v___y_41_;
}
}
v___jp_46_:
{
uint32_t v___x_47_; uint8_t v___x_48_; 
v___x_47_ = 65;
v___x_48_ = lean_uint32_dec_le(v___x_47_, v_c_39_);
if (v___x_48_ == 0)
{
v___y_41_ = v___x_48_;
goto v___jp_40_;
}
else
{
uint32_t v___x_49_; uint8_t v___x_50_; 
v___x_49_ = 90;
v___x_50_ = lean_uint32_dec_le(v_c_39_, v___x_49_);
v___y_41_ = v___x_50_;
goto v___jp_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_tchar___boxed(lean_object* v_c_85_){
_start:
{
uint32_t v_c_boxed_86_; uint8_t v_res_87_; lean_object* v_r_88_; 
v_c_boxed_86_ = lean_unbox_uint32(v_c_85_);
lean_dec(v_c_85_);
v_res_87_ = l_Std_Http_Internal_Char_tchar(v_c_boxed_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_vchar(uint32_t v_c_89_){
_start:
{
uint32_t v___x_90_; uint8_t v___x_91_; 
v___x_90_ = 33;
v___x_91_ = lean_uint32_dec_le(v___x_90_, v_c_89_);
if (v___x_91_ == 0)
{
return v___x_91_;
}
else
{
uint32_t v___x_92_; uint8_t v___x_93_; 
v___x_92_ = 126;
v___x_93_ = lean_uint32_dec_le(v_c_89_, v___x_92_);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_vchar___boxed(lean_object* v_c_94_){
_start:
{
uint32_t v_c_boxed_95_; uint8_t v_res_96_; lean_object* v_r_97_; 
v_c_boxed_95_ = lean_unbox_uint32(v_c_94_);
lean_dec(v_c_94_);
v_res_96_ = l_Std_Http_Internal_Char_vchar(v_c_boxed_95_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_qdtext(uint32_t v_c_98_){
_start:
{
uint8_t v___y_100_; uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_105_ = 9;
v___x_106_ = lean_uint32_dec_eq(v_c_98_, v___x_105_);
if (v___x_106_ == 0)
{
uint32_t v___x_107_; uint8_t v___x_108_; 
v___x_107_ = 32;
v___x_108_ = lean_uint32_dec_eq(v_c_98_, v___x_107_);
if (v___x_108_ == 0)
{
uint32_t v___x_109_; uint8_t v___x_110_; 
v___x_109_ = 33;
v___x_110_ = lean_uint32_dec_eq(v_c_98_, v___x_109_);
if (v___x_110_ == 0)
{
uint32_t v___x_111_; uint8_t v___x_112_; 
v___x_111_ = 35;
v___x_112_ = lean_uint32_dec_le(v___x_111_, v_c_98_);
if (v___x_112_ == 0)
{
v___y_100_ = v___x_112_;
goto v___jp_99_;
}
else
{
uint32_t v___x_113_; uint8_t v___x_114_; 
v___x_113_ = 91;
v___x_114_ = lean_uint32_dec_le(v_c_98_, v___x_113_);
v___y_100_ = v___x_114_;
goto v___jp_99_;
}
}
else
{
return v___x_110_;
}
}
else
{
return v___x_108_;
}
}
else
{
return v___x_106_;
}
v___jp_99_:
{
if (v___y_100_ == 0)
{
uint32_t v___x_101_; uint8_t v___x_102_; 
v___x_101_ = 93;
v___x_102_ = lean_uint32_dec_le(v___x_101_, v_c_98_);
if (v___x_102_ == 0)
{
return v___x_102_;
}
else
{
uint32_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = 126;
v___x_104_ = lean_uint32_dec_le(v_c_98_, v___x_103_);
return v___x_104_;
}
}
else
{
return v___y_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_qdtext___boxed(lean_object* v_c_115_){
_start:
{
uint32_t v_c_boxed_116_; uint8_t v_res_117_; lean_object* v_r_118_; 
v_c_boxed_116_ = lean_unbox_uint32(v_c_115_);
lean_dec(v_c_115_);
v_res_117_ = l_Std_Http_Internal_Char_qdtext(v_c_boxed_116_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_quotedPairChar(uint32_t v_c_119_){
_start:
{
uint32_t v___x_120_; uint8_t v___x_121_; 
v___x_120_ = 9;
v___x_121_ = lean_uint32_dec_eq(v_c_119_, v___x_120_);
if (v___x_121_ == 0)
{
uint32_t v___x_122_; uint8_t v___x_123_; 
v___x_122_ = 32;
v___x_123_ = lean_uint32_dec_eq(v_c_119_, v___x_122_);
if (v___x_123_ == 0)
{
uint32_t v___x_124_; uint8_t v___x_125_; 
v___x_124_ = 33;
v___x_125_ = lean_uint32_dec_le(v___x_124_, v_c_119_);
if (v___x_125_ == 0)
{
return v___x_125_;
}
else
{
uint32_t v___x_126_; uint8_t v___x_127_; 
v___x_126_ = 126;
v___x_127_ = lean_uint32_dec_le(v_c_119_, v___x_126_);
return v___x_127_;
}
}
else
{
return v___x_123_;
}
}
else
{
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_quotedPairChar___boxed(lean_object* v_c_128_){
_start:
{
uint32_t v_c_boxed_129_; uint8_t v_res_130_; lean_object* v_r_131_; 
v_c_boxed_129_ = lean_unbox_uint32(v_c_128_);
lean_dec(v_c_128_);
v_res_130_ = l_Std_Http_Internal_Char_quotedPairChar(v_c_boxed_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_quotedStringChar(uint32_t v_c_132_){
_start:
{
uint32_t v___x_133_; uint8_t v___x_134_; 
v___x_133_ = 9;
v___x_134_ = lean_uint32_dec_eq(v_c_132_, v___x_133_);
if (v___x_134_ == 0)
{
uint32_t v___x_135_; uint8_t v___x_136_; 
v___x_135_ = 32;
v___x_136_ = lean_uint32_dec_eq(v_c_132_, v___x_135_);
if (v___x_136_ == 0)
{
uint32_t v___x_137_; uint8_t v___y_139_; uint8_t v___y_140_; uint8_t v___y_143_; uint8_t v___x_148_; 
v___x_137_ = 33;
v___x_148_ = lean_uint32_dec_eq(v_c_132_, v___x_137_);
if (v___x_148_ == 0)
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 35;
v___x_150_ = lean_uint32_dec_le(v___x_149_, v_c_132_);
if (v___x_150_ == 0)
{
v___y_143_ = v___x_150_;
goto v___jp_142_;
}
else
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 91;
v___x_152_ = lean_uint32_dec_le(v_c_132_, v___x_151_);
v___y_143_ = v___x_152_;
goto v___jp_142_;
}
}
else
{
return v___x_148_;
}
v___jp_138_:
{
if (v___y_140_ == 0)
{
if (v___x_134_ == 0)
{
if (v___x_136_ == 0)
{
uint8_t v___x_141_; 
v___x_141_ = lean_uint32_dec_le(v___x_137_, v_c_132_);
if (v___x_141_ == 0)
{
return v___x_141_;
}
else
{
return v___y_139_;
}
}
else
{
return v___x_136_;
}
}
else
{
return v___x_134_;
}
}
else
{
return v___y_140_;
}
}
v___jp_142_:
{
if (v___y_143_ == 0)
{
uint32_t v___x_144_; uint8_t v___x_145_; uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_144_ = 93;
v___x_145_ = lean_uint32_dec_le(v___x_144_, v_c_132_);
v___x_146_ = 126;
v___x_147_ = lean_uint32_dec_le(v_c_132_, v___x_146_);
if (v___x_145_ == 0)
{
v___y_139_ = v___x_147_;
v___y_140_ = v___x_145_;
goto v___jp_138_;
}
else
{
v___y_139_ = v___x_147_;
v___y_140_ = v___x_147_;
goto v___jp_138_;
}
}
else
{
return v___y_143_;
}
}
}
else
{
return v___x_136_;
}
}
else
{
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_quotedStringChar___boxed(lean_object* v_c_153_){
_start:
{
uint32_t v_c_boxed_154_; uint8_t v_res_155_; lean_object* v_r_156_; 
v_c_boxed_154_ = lean_unbox_uint32(v_c_153_);
lean_dec(v_c_153_);
v_res_155_ = l_Std_Http_Internal_Char_quotedStringChar(v_c_boxed_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg(uint32_t v_c_157_, lean_object* v_h__1_158_, lean_object* v_h__2_159_, lean_object* v_h__3_160_, lean_object* v_h__4_161_){
_start:
{
uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 9;
v___x_163_ = lean_uint32_dec_eq(v_c_157_, v___x_162_);
if (v___x_163_ == 0)
{
uint32_t v___x_164_; uint8_t v___x_165_; 
lean_dec(v_h__1_158_);
v___x_164_ = 32;
v___x_165_ = lean_uint32_dec_eq(v_c_157_, v___x_164_);
if (v___x_165_ == 0)
{
uint32_t v___x_166_; uint8_t v___x_167_; 
lean_dec(v_h__2_159_);
v___x_166_ = 33;
v___x_167_ = lean_uint32_dec_eq(v_c_157_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v_h__3_160_);
v___x_168_ = lean_box_uint32(v_c_157_);
v___x_169_ = lean_apply_4(v_h__4_161_, v___x_168_, lean_box(0), lean_box(0), lean_box(0));
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; 
lean_dec(v_h__4_161_);
v___x_170_ = lean_box(0);
v___x_171_ = lean_apply_1(v_h__3_160_, v___x_170_);
return v___x_171_;
}
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec(v_h__4_161_);
lean_dec(v_h__3_160_);
v___x_172_ = lean_box(0);
v___x_173_ = lean_apply_1(v_h__2_159_, v___x_172_);
return v___x_173_;
}
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v_h__4_161_);
lean_dec(v_h__3_160_);
lean_dec(v_h__2_159_);
v___x_174_ = lean_box(0);
v___x_175_ = lean_apply_1(v_h__1_158_, v___x_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg___boxed(lean_object* v_c_176_, lean_object* v_h__1_177_, lean_object* v_h__2_178_, lean_object* v_h__3_179_, lean_object* v_h__4_180_){
_start:
{
uint32_t v_c_73__boxed_181_; lean_object* v_res_182_; 
v_c_73__boxed_181_ = lean_unbox_uint32(v_c_176_);
lean_dec(v_c_176_);
v_res_182_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg(v_c_73__boxed_181_, v_h__1_177_, v_h__2_178_, v_h__3_179_, v_h__4_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(lean_object* v_motive_183_, uint32_t v_c_184_, lean_object* v_h__1_185_, lean_object* v_h__2_186_, lean_object* v_h__3_187_, lean_object* v_h__4_188_){
_start:
{
uint32_t v___x_189_; uint8_t v___x_190_; 
v___x_189_ = 9;
v___x_190_ = lean_uint32_dec_eq(v_c_184_, v___x_189_);
if (v___x_190_ == 0)
{
uint32_t v___x_191_; uint8_t v___x_192_; 
lean_dec(v_h__1_185_);
v___x_191_ = 32;
v___x_192_ = lean_uint32_dec_eq(v_c_184_, v___x_191_);
if (v___x_192_ == 0)
{
uint32_t v___x_193_; uint8_t v___x_194_; 
lean_dec(v_h__2_186_);
v___x_193_ = 33;
v___x_194_ = lean_uint32_dec_eq(v_c_184_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v_h__3_187_);
v___x_195_ = lean_box_uint32(v_c_184_);
v___x_196_ = lean_apply_4(v_h__4_188_, v___x_195_, lean_box(0), lean_box(0), lean_box(0));
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_h__4_188_);
v___x_197_ = lean_box(0);
v___x_198_ = lean_apply_1(v_h__3_187_, v___x_197_);
return v___x_198_;
}
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v_h__4_188_);
lean_dec(v_h__3_187_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_apply_1(v_h__2_186_, v___x_199_);
return v___x_200_;
}
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v_h__4_188_);
lean_dec(v_h__3_187_);
lean_dec(v_h__2_186_);
v___x_201_ = lean_box(0);
v___x_202_ = lean_apply_1(v_h__1_185_, v___x_201_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___boxed(lean_object* v_motive_203_, lean_object* v_c_204_, lean_object* v_h__1_205_, lean_object* v_h__2_206_, lean_object* v_h__3_207_, lean_object* v_h__4_208_){
_start:
{
uint32_t v_c_104__boxed_209_; lean_object* v_res_210_; 
v_c_104__boxed_209_ = lean_unbox_uint32(v_c_204_);
lean_dec(v_c_204_);
v_res_210_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(v_motive_203_, v_c_104__boxed_209_, v_h__1_205_, v_h__2_206_, v_h__3_207_, v_h__4_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(uint32_t v_c_211_, lean_object* v_h__1_212_, lean_object* v_h__2_213_, lean_object* v_h__3_214_){
_start:
{
uint32_t v___x_215_; uint8_t v___x_216_; 
v___x_215_ = 9;
v___x_216_ = lean_uint32_dec_eq(v_c_211_, v___x_215_);
if (v___x_216_ == 0)
{
uint32_t v___x_217_; uint8_t v___x_218_; 
lean_dec(v_h__1_212_);
v___x_217_ = 32;
v___x_218_ = lean_uint32_dec_eq(v_c_211_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v_h__2_213_);
v___x_219_ = lean_box_uint32(v_c_211_);
v___x_220_ = lean_apply_3(v_h__3_214_, v___x_219_, lean_box(0), lean_box(0));
return v___x_220_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v_h__3_214_);
v___x_221_ = lean_box(0);
v___x_222_ = lean_apply_1(v_h__2_213_, v___x_221_);
return v___x_222_;
}
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec(v_h__3_214_);
lean_dec(v_h__2_213_);
v___x_223_ = lean_box(0);
v___x_224_ = lean_apply_1(v_h__1_212_, v___x_223_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg___boxed(lean_object* v_c_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_, lean_object* v_h__3_228_){
_start:
{
uint32_t v_c_51__boxed_229_; lean_object* v_res_230_; 
v_c_51__boxed_229_ = lean_unbox_uint32(v_c_225_);
lean_dec(v_c_225_);
v_res_230_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(v_c_51__boxed_229_, v_h__1_226_, v_h__2_227_, v_h__3_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(lean_object* v_motive_231_, uint32_t v_c_232_, lean_object* v_h__1_233_, lean_object* v_h__2_234_, lean_object* v_h__3_235_){
_start:
{
uint32_t v___x_236_; uint8_t v___x_237_; 
v___x_236_ = 9;
v___x_237_ = lean_uint32_dec_eq(v_c_232_, v___x_236_);
if (v___x_237_ == 0)
{
uint32_t v___x_238_; uint8_t v___x_239_; 
lean_dec(v_h__1_233_);
v___x_238_ = 32;
v___x_239_ = lean_uint32_dec_eq(v_c_232_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v_h__2_234_);
v___x_240_ = lean_box_uint32(v_c_232_);
v___x_241_ = lean_apply_3(v_h__3_235_, v___x_240_, lean_box(0), lean_box(0));
return v___x_241_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_h__3_235_);
v___x_242_ = lean_box(0);
v___x_243_ = lean_apply_1(v_h__2_234_, v___x_242_);
return v___x_243_;
}
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_h__3_235_);
lean_dec(v_h__2_234_);
v___x_244_ = lean_box(0);
v___x_245_ = lean_apply_1(v_h__1_233_, v___x_244_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___boxed(lean_object* v_motive_246_, lean_object* v_c_247_, lean_object* v_h__1_248_, lean_object* v_h__2_249_, lean_object* v_h__3_250_){
_start:
{
uint32_t v_c_74__boxed_251_; lean_object* v_res_252_; 
v_c_74__boxed_251_ = lean_unbox_uint32(v_c_247_);
lean_dec(v_c_247_);
v_res_252_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(v_motive_246_, v_c_74__boxed_251_, v_h__1_248_, v_h__2_249_, v_h__3_250_);
return v_res_252_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_fieldVchar(uint32_t v_c_253_){
_start:
{
uint32_t v___x_254_; uint8_t v___x_255_; 
v___x_254_ = 33;
v___x_255_ = lean_uint32_dec_le(v___x_254_, v_c_253_);
if (v___x_255_ == 0)
{
return v___x_255_;
}
else
{
uint32_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = 126;
v___x_257_ = lean_uint32_dec_le(v_c_253_, v___x_256_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldVchar___boxed(lean_object* v_c_258_){
_start:
{
uint32_t v_c_boxed_259_; uint8_t v_res_260_; lean_object* v_r_261_; 
v_c_boxed_259_ = lean_unbox_uint32(v_c_258_);
lean_dec(v_c_258_);
v_res_260_ = l_Std_Http_Internal_Char_fieldVchar(v_c_boxed_259_);
v_r_261_ = lean_box(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_fieldContent(uint32_t v_c_262_){
_start:
{
uint8_t v___y_264_; uint32_t v___x_269_; uint8_t v___x_270_; 
v___x_269_ = 33;
v___x_270_ = lean_uint32_dec_le(v___x_269_, v_c_262_);
if (v___x_270_ == 0)
{
v___y_264_ = v___x_270_;
goto v___jp_263_;
}
else
{
uint32_t v___x_271_; uint8_t v___x_272_; 
v___x_271_ = 126;
v___x_272_ = lean_uint32_dec_le(v_c_262_, v___x_271_);
v___y_264_ = v___x_272_;
goto v___jp_263_;
}
v___jp_263_:
{
if (v___y_264_ == 0)
{
uint32_t v___x_265_; uint8_t v___x_266_; 
v___x_265_ = 32;
v___x_266_ = lean_uint32_dec_eq(v_c_262_, v___x_265_);
if (v___x_266_ == 0)
{
uint32_t v___x_267_; uint8_t v___x_268_; 
v___x_267_ = 9;
v___x_268_ = lean_uint32_dec_eq(v_c_262_, v___x_267_);
return v___x_268_;
}
else
{
return v___x_266_;
}
}
else
{
return v___y_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldContent___boxed(lean_object* v_c_273_){
_start:
{
uint32_t v_c_boxed_274_; uint8_t v_res_275_; lean_object* v_r_276_; 
v_c_boxed_274_ = lean_unbox_uint32(v_c_273_);
lean_dec(v_c_273_);
v_res_275_ = l_Std_Http_Internal_Char_fieldContent(v_c_boxed_274_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_ctext(uint32_t v_c_277_){
_start:
{
uint8_t v___y_279_; uint8_t v___y_285_; uint32_t v___x_290_; uint8_t v___x_291_; 
v___x_290_ = 9;
v___x_291_ = lean_uint32_dec_eq(v_c_277_, v___x_290_);
if (v___x_291_ == 0)
{
uint32_t v___x_292_; uint8_t v___x_293_; 
v___x_292_ = 32;
v___x_293_ = lean_uint32_dec_eq(v_c_277_, v___x_292_);
if (v___x_293_ == 0)
{
uint32_t v___x_294_; uint8_t v___x_295_; 
v___x_294_ = 33;
v___x_295_ = lean_uint32_dec_le(v___x_294_, v_c_277_);
if (v___x_295_ == 0)
{
v___y_285_ = v___x_295_;
goto v___jp_284_;
}
else
{
uint32_t v___x_296_; uint8_t v___x_297_; 
v___x_296_ = 39;
v___x_297_ = lean_uint32_dec_le(v_c_277_, v___x_296_);
v___y_285_ = v___x_297_;
goto v___jp_284_;
}
}
else
{
return v___x_293_;
}
}
else
{
return v___x_291_;
}
v___jp_278_:
{
if (v___y_279_ == 0)
{
uint32_t v___x_280_; uint8_t v___x_281_; 
v___x_280_ = 93;
v___x_281_ = lean_uint32_dec_le(v___x_280_, v_c_277_);
if (v___x_281_ == 0)
{
return v___x_281_;
}
else
{
uint32_t v___x_282_; uint8_t v___x_283_; 
v___x_282_ = 126;
v___x_283_ = lean_uint32_dec_le(v_c_277_, v___x_282_);
return v___x_283_;
}
}
else
{
return v___y_279_;
}
}
v___jp_284_:
{
if (v___y_285_ == 0)
{
uint32_t v___x_286_; uint8_t v___x_287_; 
v___x_286_ = 42;
v___x_287_ = lean_uint32_dec_le(v___x_286_, v_c_277_);
if (v___x_287_ == 0)
{
v___y_279_ = v___x_287_;
goto v___jp_278_;
}
else
{
uint32_t v___x_288_; uint8_t v___x_289_; 
v___x_288_ = 91;
v___x_289_ = lean_uint32_dec_le(v_c_277_, v___x_288_);
v___y_279_ = v___x_289_;
goto v___jp_278_;
}
}
else
{
return v___y_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ctext___boxed(lean_object* v_c_298_){
_start:
{
uint32_t v_c_boxed_299_; uint8_t v_res_300_; lean_object* v_r_301_; 
v_c_boxed_299_ = lean_unbox_uint32(v_c_298_);
lean_dec(v_c_298_);
v_res_300_ = l_Std_Http_Internal_Char_ctext(v_c_boxed_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_etagc(uint32_t v_c_302_){
_start:
{
uint32_t v___x_303_; uint8_t v___x_304_; 
v___x_303_ = 33;
v___x_304_ = lean_uint32_dec_eq(v_c_302_, v___x_303_);
if (v___x_304_ == 0)
{
uint32_t v___x_305_; uint8_t v___x_306_; 
v___x_305_ = 35;
v___x_306_ = lean_uint32_dec_le(v___x_305_, v_c_302_);
if (v___x_306_ == 0)
{
return v___x_306_;
}
else
{
uint32_t v___x_307_; uint8_t v___x_308_; 
v___x_307_ = 126;
v___x_308_ = lean_uint32_dec_le(v_c_302_, v___x_307_);
return v___x_308_;
}
}
else
{
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_etagc___boxed(lean_object* v_c_309_){
_start:
{
uint32_t v_c_boxed_310_; uint8_t v_res_311_; lean_object* v_r_312_; 
v_c_boxed_310_ = lean_unbox_uint32(v_c_309_);
lean_dec(v_c_309_);
v_res_311_ = l_Std_Http_Internal_Char_etagc(v_c_boxed_310_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_ows(uint32_t v_c_313_){
_start:
{
uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = 32;
v___x_315_ = lean_uint32_dec_eq(v_c_313_, v___x_314_);
if (v___x_315_ == 0)
{
uint32_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 9;
v___x_317_ = lean_uint32_dec_eq(v_c_313_, v___x_316_);
return v___x_317_;
}
else
{
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ows___boxed(lean_object* v_c_318_){
_start:
{
uint32_t v_c_boxed_319_; uint8_t v_res_320_; lean_object* v_r_321_; 
v_c_boxed_319_ = lean_unbox_uint32(v_c_318_);
lean_dec(v_c_318_);
v_res_320_ = l_Std_Http_Internal_Char_ows(v_c_boxed_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_bws(uint32_t v_c_322_){
_start:
{
uint32_t v___x_323_; uint8_t v___x_324_; 
v___x_323_ = 32;
v___x_324_ = lean_uint32_dec_eq(v_c_322_, v___x_323_);
if (v___x_324_ == 0)
{
uint32_t v___x_325_; uint8_t v___x_326_; 
v___x_325_ = 9;
v___x_326_ = lean_uint32_dec_eq(v_c_322_, v___x_325_);
return v___x_326_;
}
else
{
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_bws___boxed(lean_object* v_c_327_){
_start:
{
uint32_t v_c_boxed_328_; uint8_t v_res_329_; lean_object* v_r_330_; 
v_c_boxed_328_ = lean_unbox_uint32(v_c_327_);
lean_dec(v_c_327_);
v_res_329_ = l_Std_Http_Internal_Char_bws(v_c_boxed_328_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_rws(uint32_t v_c_331_){
_start:
{
uint32_t v___x_332_; uint8_t v___x_333_; 
v___x_332_ = 32;
v___x_333_ = lean_uint32_dec_eq(v_c_331_, v___x_332_);
if (v___x_333_ == 0)
{
uint32_t v___x_334_; uint8_t v___x_335_; 
v___x_334_ = 9;
v___x_335_ = lean_uint32_dec_eq(v_c_331_, v___x_334_);
return v___x_335_;
}
else
{
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_rws___boxed(lean_object* v_c_336_){
_start:
{
uint32_t v_c_boxed_337_; uint8_t v_res_338_; lean_object* v_r_339_; 
v_c_boxed_337_ = lean_unbox_uint32(v_c_336_);
lean_dec(v_c_336_);
v_res_338_ = l_Std_Http_Internal_Char_rws(v_c_boxed_337_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_obsText(uint32_t v_c_340_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_341_ = lean_unsigned_to_nat(128u);
v___x_342_ = lean_uint32_to_nat(v_c_340_);
v___x_343_ = lean_nat_dec_le(v___x_341_, v___x_342_);
lean_dec(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_obsText___boxed(lean_object* v_c_344_){
_start:
{
uint32_t v_c_boxed_345_; uint8_t v_res_346_; lean_object* v_r_347_; 
v_c_boxed_345_ = lean_unbox_uint32(v_c_344_);
lean_dec(v_c_344_);
v_res_346_ = l_Std_Http_Internal_Char_obsText(v_c_boxed_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_reasonPhraseChar(uint32_t v_c_348_){
_start:
{
uint32_t v___x_349_; uint8_t v___x_350_; 
v___x_349_ = 9;
v___x_350_ = lean_uint32_dec_eq(v_c_348_, v___x_349_);
if (v___x_350_ == 0)
{
uint32_t v___x_351_; uint8_t v___x_352_; 
v___x_351_ = 32;
v___x_352_ = lean_uint32_dec_eq(v_c_348_, v___x_351_);
if (v___x_352_ == 0)
{
uint32_t v___x_353_; uint8_t v___x_354_; 
v___x_353_ = 33;
v___x_354_ = lean_uint32_dec_le(v___x_353_, v_c_348_);
if (v___x_354_ == 0)
{
return v___x_354_;
}
else
{
uint32_t v___x_355_; uint8_t v___x_356_; 
v___x_355_ = 126;
v___x_356_ = lean_uint32_dec_le(v_c_348_, v___x_355_);
return v___x_356_;
}
}
else
{
return v___x_352_;
}
}
else
{
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_reasonPhraseChar___boxed(lean_object* v_c_357_){
_start:
{
uint32_t v_c_boxed_358_; uint8_t v_res_359_; lean_object* v_r_360_; 
v_c_boxed_358_ = lean_unbox_uint32(v_c_357_);
lean_dec(v_c_357_);
v_res_359_ = l_Std_Http_Internal_Char_reasonPhraseChar(v_c_boxed_358_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isHexDigit(uint32_t v_c_361_){
_start:
{
uint32_t v___x_362_; uint8_t v___x_363_; 
v___x_362_ = 97;
v___x_363_ = lean_uint32_dec_eq(v_c_361_, v___x_362_);
if (v___x_363_ == 0)
{
uint32_t v___x_364_; uint8_t v___x_365_; 
v___x_364_ = 98;
v___x_365_ = lean_uint32_dec_eq(v_c_361_, v___x_364_);
if (v___x_365_ == 0)
{
uint32_t v___x_366_; uint8_t v___x_367_; 
v___x_366_ = 99;
v___x_367_ = lean_uint32_dec_eq(v_c_361_, v___x_366_);
if (v___x_367_ == 0)
{
uint32_t v___x_368_; uint8_t v___x_369_; 
v___x_368_ = 100;
v___x_369_ = lean_uint32_dec_eq(v_c_361_, v___x_368_);
if (v___x_369_ == 0)
{
uint32_t v___x_370_; uint8_t v___x_371_; 
v___x_370_ = 101;
v___x_371_ = lean_uint32_dec_eq(v_c_361_, v___x_370_);
if (v___x_371_ == 0)
{
uint32_t v___x_372_; uint8_t v___x_373_; 
v___x_372_ = 102;
v___x_373_ = lean_uint32_dec_eq(v_c_361_, v___x_372_);
if (v___x_373_ == 0)
{
uint32_t v___x_374_; uint8_t v___x_375_; 
v___x_374_ = 65;
v___x_375_ = lean_uint32_dec_eq(v_c_361_, v___x_374_);
if (v___x_375_ == 0)
{
uint32_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = 66;
v___x_377_ = lean_uint32_dec_eq(v_c_361_, v___x_376_);
if (v___x_377_ == 0)
{
uint32_t v___x_378_; uint8_t v___x_379_; 
v___x_378_ = 67;
v___x_379_ = lean_uint32_dec_eq(v_c_361_, v___x_378_);
if (v___x_379_ == 0)
{
uint32_t v___x_380_; uint8_t v___x_381_; 
v___x_380_ = 68;
v___x_381_ = lean_uint32_dec_eq(v_c_361_, v___x_380_);
if (v___x_381_ == 0)
{
uint32_t v___x_382_; uint8_t v___x_383_; 
v___x_382_ = 69;
v___x_383_ = lean_uint32_dec_eq(v_c_361_, v___x_382_);
if (v___x_383_ == 0)
{
uint32_t v___x_384_; uint8_t v___x_385_; 
v___x_384_ = 70;
v___x_385_ = lean_uint32_dec_eq(v_c_361_, v___x_384_);
if (v___x_385_ == 0)
{
uint32_t v___x_386_; uint8_t v___x_387_; 
v___x_386_ = 48;
v___x_387_ = lean_uint32_dec_le(v___x_386_, v_c_361_);
if (v___x_387_ == 0)
{
return v___x_387_;
}
else
{
uint32_t v___x_388_; uint8_t v___x_389_; 
v___x_388_ = 57;
v___x_389_ = lean_uint32_dec_le(v_c_361_, v___x_388_);
return v___x_389_;
}
}
else
{
return v___x_385_;
}
}
else
{
return v___x_383_;
}
}
else
{
return v___x_381_;
}
}
else
{
return v___x_379_;
}
}
else
{
return v___x_377_;
}
}
else
{
return v___x_375_;
}
}
else
{
return v___x_373_;
}
}
else
{
return v___x_371_;
}
}
else
{
return v___x_369_;
}
}
else
{
return v___x_367_;
}
}
else
{
return v___x_365_;
}
}
else
{
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigit___boxed(lean_object* v_c_390_){
_start:
{
uint32_t v_c_boxed_391_; uint8_t v_res_392_; lean_object* v_r_393_; 
v_c_boxed_391_ = lean_unbox_uint32(v_c_390_);
lean_dec(v_c_390_);
v_res_392_ = l_Std_Http_Internal_Char_isHexDigit(v_c_boxed_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isHexDigitByte(uint8_t v_c_394_){
_start:
{
uint8_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 48;
v___x_406_ = lean_uint8_dec_le(v___x_405_, v_c_394_);
if (v___x_406_ == 0)
{
goto v___jp_400_;
}
else
{
uint8_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = 57;
v___x_408_ = lean_uint8_dec_le(v_c_394_, v___x_407_);
if (v___x_408_ == 0)
{
goto v___jp_400_;
}
else
{
return v___x_408_;
}
}
v___jp_395_:
{
uint8_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 65;
v___x_397_ = lean_uint8_dec_le(v___x_396_, v_c_394_);
if (v___x_397_ == 0)
{
return v___x_397_;
}
else
{
uint8_t v___x_398_; uint8_t v___x_399_; 
v___x_398_ = 70;
v___x_399_ = lean_uint8_dec_le(v_c_394_, v___x_398_);
return v___x_399_;
}
}
v___jp_400_:
{
uint8_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = 97;
v___x_402_ = lean_uint8_dec_le(v___x_401_, v_c_394_);
if (v___x_402_ == 0)
{
goto v___jp_395_;
}
else
{
uint8_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 102;
v___x_404_ = lean_uint8_dec_le(v_c_394_, v___x_403_);
if (v___x_404_ == 0)
{
goto v___jp_395_;
}
else
{
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigitByte___boxed(lean_object* v_c_409_){
_start:
{
uint8_t v_c_boxed_410_; uint8_t v_res_411_; lean_object* v_r_412_; 
v_c_boxed_410_ = lean_unbox(v_c_409_);
v_res_411_ = l_Std_Http_Internal_Char_isHexDigitByte(v_c_boxed_410_);
v_r_412_ = lean_box(v_res_411_);
return v_r_412_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAlphaNum(uint8_t v_c_413_){
_start:
{
uint8_t v___x_424_; uint8_t v___x_425_; 
v___x_424_ = 48;
v___x_425_ = lean_uint8_dec_le(v___x_424_, v_c_413_);
if (v___x_425_ == 0)
{
goto v___jp_419_;
}
else
{
uint8_t v___x_426_; uint8_t v___x_427_; 
v___x_426_ = 57;
v___x_427_ = lean_uint8_dec_le(v_c_413_, v___x_426_);
if (v___x_427_ == 0)
{
goto v___jp_419_;
}
else
{
return v___x_427_;
}
}
v___jp_414_:
{
uint8_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 65;
v___x_416_ = lean_uint8_dec_le(v___x_415_, v_c_413_);
if (v___x_416_ == 0)
{
return v___x_416_;
}
else
{
uint8_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = 90;
v___x_418_ = lean_uint8_dec_le(v_c_413_, v___x_417_);
return v___x_418_;
}
}
v___jp_419_:
{
uint8_t v___x_420_; uint8_t v___x_421_; 
v___x_420_ = 97;
v___x_421_ = lean_uint8_dec_le(v___x_420_, v_c_413_);
if (v___x_421_ == 0)
{
goto v___jp_414_;
}
else
{
uint8_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = 122;
v___x_423_ = lean_uint8_dec_le(v_c_413_, v___x_422_);
if (v___x_423_ == 0)
{
goto v___jp_414_;
}
else
{
return v___x_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAlphaNum___boxed(lean_object* v_c_428_){
_start:
{
uint8_t v_c_boxed_429_; uint8_t v_res_430_; lean_object* v_r_431_; 
v_c_boxed_429_ = lean_unbox(v_c_428_);
v_res_430_ = l_Std_Http_Internal_Char_isAlphaNum(v_c_boxed_429_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAsciiAlphaNumChar(uint32_t v_c_432_){
_start:
{
uint8_t v___y_434_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_444_ = lean_uint32_to_nat(v_c_432_);
v___x_445_ = lean_unsigned_to_nat(128u);
v___x_446_ = lean_nat_dec_lt(v___x_444_, v___x_445_);
lean_dec(v___x_444_);
if (v___x_446_ == 0)
{
return v___x_446_;
}
else
{
uint32_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = 48;
v___x_448_ = lean_uint32_dec_le(v___x_447_, v_c_432_);
if (v___x_448_ == 0)
{
goto v___jp_439_;
}
else
{
uint32_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = 57;
v___x_450_ = lean_uint32_dec_le(v_c_432_, v___x_449_);
if (v___x_450_ == 0)
{
goto v___jp_439_;
}
else
{
return v___x_450_;
}
}
}
v___jp_433_:
{
if (v___y_434_ == 0)
{
uint32_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = 97;
v___x_436_ = lean_uint32_dec_le(v___x_435_, v_c_432_);
if (v___x_436_ == 0)
{
return v___x_436_;
}
else
{
uint32_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = 122;
v___x_438_ = lean_uint32_dec_le(v_c_432_, v___x_437_);
return v___x_438_;
}
}
else
{
return v___y_434_;
}
}
v___jp_439_:
{
uint32_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = 65;
v___x_441_ = lean_uint32_dec_le(v___x_440_, v_c_432_);
if (v___x_441_ == 0)
{
v___y_434_ = v___x_441_;
goto v___jp_433_;
}
else
{
uint32_t v___x_442_; uint8_t v___x_443_; 
v___x_442_ = 90;
v___x_443_ = lean_uint32_dec_le(v_c_432_, v___x_442_);
v___y_434_ = v___x_443_;
goto v___jp_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAsciiAlphaNumChar___boxed(lean_object* v_c_451_){
_start:
{
uint32_t v_c_boxed_452_; uint8_t v_res_453_; lean_object* v_r_454_; 
v_c_boxed_452_ = lean_unbox_uint32(v_c_451_);
lean_dec(v_c_451_);
v_res_453_ = l_Std_Http_Internal_Char_isAsciiAlphaNumChar(v_c_boxed_452_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isValidSchemeChar(uint32_t v_c_455_){
_start:
{
uint8_t v___y_464_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_474_ = lean_uint32_to_nat(v_c_455_);
v___x_475_ = lean_unsigned_to_nat(128u);
v___x_476_ = lean_nat_dec_lt(v___x_474_, v___x_475_);
lean_dec(v___x_474_);
if (v___x_476_ == 0)
{
goto v___jp_456_;
}
else
{
uint32_t v___x_477_; uint8_t v___x_478_; 
v___x_477_ = 48;
v___x_478_ = lean_uint32_dec_le(v___x_477_, v_c_455_);
if (v___x_478_ == 0)
{
goto v___jp_469_;
}
else
{
uint32_t v___x_479_; uint8_t v___x_480_; 
v___x_479_ = 57;
v___x_480_ = lean_uint32_dec_le(v_c_455_, v___x_479_);
if (v___x_480_ == 0)
{
goto v___jp_469_;
}
else
{
return v___x_480_;
}
}
}
v___jp_456_:
{
uint32_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = 43;
v___x_458_ = lean_uint32_dec_eq(v_c_455_, v___x_457_);
if (v___x_458_ == 0)
{
uint32_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = 45;
v___x_460_ = lean_uint32_dec_eq(v_c_455_, v___x_459_);
if (v___x_460_ == 0)
{
uint32_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 46;
v___x_462_ = lean_uint32_dec_eq(v_c_455_, v___x_461_);
return v___x_462_;
}
else
{
return v___x_460_;
}
}
else
{
return v___x_458_;
}
}
v___jp_463_:
{
if (v___y_464_ == 0)
{
uint32_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = 97;
v___x_466_ = lean_uint32_dec_le(v___x_465_, v_c_455_);
if (v___x_466_ == 0)
{
goto v___jp_456_;
}
else
{
uint32_t v___x_467_; uint8_t v___x_468_; 
v___x_467_ = 122;
v___x_468_ = lean_uint32_dec_le(v_c_455_, v___x_467_);
if (v___x_468_ == 0)
{
goto v___jp_456_;
}
else
{
return v___x_468_;
}
}
}
else
{
return v___y_464_;
}
}
v___jp_469_:
{
uint32_t v___x_470_; uint8_t v___x_471_; 
v___x_470_ = 65;
v___x_471_ = lean_uint32_dec_le(v___x_470_, v_c_455_);
if (v___x_471_ == 0)
{
v___y_464_ = v___x_471_;
goto v___jp_463_;
}
else
{
uint32_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = 90;
v___x_473_ = lean_uint32_dec_le(v_c_455_, v___x_472_);
v___y_464_ = v___x_473_;
goto v___jp_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidSchemeChar___boxed(lean_object* v_c_481_){
_start:
{
uint32_t v_c_boxed_482_; uint8_t v_res_483_; lean_object* v_r_484_; 
v_c_boxed_482_ = lean_unbox_uint32(v_c_481_);
lean_dec(v_c_481_);
v_res_483_ = l_Std_Http_Internal_Char_isValidSchemeChar(v_c_boxed_482_);
v_r_484_ = lean_box(v_res_483_);
return v_r_484_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isValidDomainNameChar(uint32_t v_c_485_){
_start:
{
uint8_t v___y_492_; lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_502_ = lean_uint32_to_nat(v_c_485_);
v___x_503_ = lean_unsigned_to_nat(128u);
v___x_504_ = lean_nat_dec_lt(v___x_502_, v___x_503_);
lean_dec(v___x_502_);
if (v___x_504_ == 0)
{
goto v___jp_486_;
}
else
{
uint32_t v___x_505_; uint8_t v___x_506_; 
v___x_505_ = 48;
v___x_506_ = lean_uint32_dec_le(v___x_505_, v_c_485_);
if (v___x_506_ == 0)
{
goto v___jp_497_;
}
else
{
uint32_t v___x_507_; uint8_t v___x_508_; 
v___x_507_ = 57;
v___x_508_ = lean_uint32_dec_le(v_c_485_, v___x_507_);
if (v___x_508_ == 0)
{
goto v___jp_497_;
}
else
{
return v___x_508_;
}
}
}
v___jp_486_:
{
uint32_t v___x_487_; uint8_t v___x_488_; 
v___x_487_ = 45;
v___x_488_ = lean_uint32_dec_eq(v_c_485_, v___x_487_);
if (v___x_488_ == 0)
{
uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_489_ = 46;
v___x_490_ = lean_uint32_dec_eq(v_c_485_, v___x_489_);
return v___x_490_;
}
else
{
return v___x_488_;
}
}
v___jp_491_:
{
if (v___y_492_ == 0)
{
uint32_t v___x_493_; uint8_t v___x_494_; 
v___x_493_ = 97;
v___x_494_ = lean_uint32_dec_le(v___x_493_, v_c_485_);
if (v___x_494_ == 0)
{
goto v___jp_486_;
}
else
{
uint32_t v___x_495_; uint8_t v___x_496_; 
v___x_495_ = 122;
v___x_496_ = lean_uint32_dec_le(v_c_485_, v___x_495_);
if (v___x_496_ == 0)
{
goto v___jp_486_;
}
else
{
return v___x_496_;
}
}
}
else
{
return v___y_492_;
}
}
v___jp_497_:
{
uint32_t v___x_498_; uint8_t v___x_499_; 
v___x_498_ = 65;
v___x_499_ = lean_uint32_dec_le(v___x_498_, v_c_485_);
if (v___x_499_ == 0)
{
v___y_492_ = v___x_499_;
goto v___jp_491_;
}
else
{
uint32_t v___x_500_; uint8_t v___x_501_; 
v___x_500_ = 90;
v___x_501_ = lean_uint32_dec_le(v_c_485_, v___x_500_);
v___y_492_ = v___x_501_;
goto v___jp_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidDomainNameChar___boxed(lean_object* v_c_509_){
_start:
{
uint32_t v_c_boxed_510_; uint8_t v_res_511_; lean_object* v_r_512_; 
v_c_boxed_510_ = lean_unbox_uint32(v_c_509_);
lean_dec(v_c_509_);
v_res_511_ = l_Std_Http_Internal_Char_isValidDomainNameChar(v_c_boxed_510_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUnreserved(uint8_t v_c_513_){
_start:
{
uint8_t v___x_533_; uint8_t v___x_534_; 
v___x_533_ = 48;
v___x_534_ = lean_uint8_dec_le(v___x_533_, v_c_513_);
if (v___x_534_ == 0)
{
goto v___jp_528_;
}
else
{
uint8_t v___x_535_; uint8_t v___x_536_; 
v___x_535_ = 57;
v___x_536_ = lean_uint8_dec_le(v_c_513_, v___x_535_);
if (v___x_536_ == 0)
{
goto v___jp_528_;
}
else
{
return v___x_536_;
}
}
v___jp_514_:
{
uint8_t v___x_515_; uint8_t v___x_516_; 
v___x_515_ = 45;
v___x_516_ = lean_uint8_dec_eq(v_c_513_, v___x_515_);
if (v___x_516_ == 0)
{
uint8_t v___x_517_; uint8_t v___x_518_; 
v___x_517_ = 46;
v___x_518_ = lean_uint8_dec_eq(v_c_513_, v___x_517_);
if (v___x_518_ == 0)
{
uint8_t v___x_519_; uint8_t v___x_520_; 
v___x_519_ = 95;
v___x_520_ = lean_uint8_dec_eq(v_c_513_, v___x_519_);
if (v___x_520_ == 0)
{
uint8_t v___x_521_; uint8_t v___x_522_; 
v___x_521_ = 126;
v___x_522_ = lean_uint8_dec_eq(v_c_513_, v___x_521_);
return v___x_522_;
}
else
{
return v___x_520_;
}
}
else
{
return v___x_518_;
}
}
else
{
return v___x_516_;
}
}
v___jp_523_:
{
uint8_t v___x_524_; uint8_t v___x_525_; 
v___x_524_ = 65;
v___x_525_ = lean_uint8_dec_le(v___x_524_, v_c_513_);
if (v___x_525_ == 0)
{
goto v___jp_514_;
}
else
{
uint8_t v___x_526_; uint8_t v___x_527_; 
v___x_526_ = 90;
v___x_527_ = lean_uint8_dec_le(v_c_513_, v___x_526_);
if (v___x_527_ == 0)
{
goto v___jp_514_;
}
else
{
return v___x_527_;
}
}
}
v___jp_528_:
{
uint8_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = 97;
v___x_530_ = lean_uint8_dec_le(v___x_529_, v_c_513_);
if (v___x_530_ == 0)
{
goto v___jp_523_;
}
else
{
uint8_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 122;
v___x_532_ = lean_uint8_dec_le(v_c_513_, v___x_531_);
if (v___x_532_ == 0)
{
goto v___jp_523_;
}
else
{
return v___x_532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUnreserved___boxed(lean_object* v_c_537_){
_start:
{
uint8_t v_c_boxed_538_; uint8_t v_res_539_; lean_object* v_r_540_; 
v_c_boxed_538_ = lean_unbox(v_c_537_);
v_res_539_ = l_Std_Http_Internal_Char_isUnreserved(v_c_boxed_538_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isSubDelims(uint8_t v_c_541_){
_start:
{
uint8_t v___x_542_; uint8_t v___x_543_; 
v___x_542_ = 33;
v___x_543_ = lean_uint8_dec_eq(v_c_541_, v___x_542_);
if (v___x_543_ == 0)
{
uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = 36;
v___x_545_ = lean_uint8_dec_eq(v_c_541_, v___x_544_);
if (v___x_545_ == 0)
{
uint8_t v___x_546_; uint8_t v___x_547_; 
v___x_546_ = 38;
v___x_547_ = lean_uint8_dec_eq(v_c_541_, v___x_546_);
if (v___x_547_ == 0)
{
uint8_t v___x_548_; uint8_t v___x_549_; 
v___x_548_ = 39;
v___x_549_ = lean_uint8_dec_eq(v_c_541_, v___x_548_);
if (v___x_549_ == 0)
{
uint8_t v___x_550_; uint8_t v___x_551_; 
v___x_550_ = 40;
v___x_551_ = lean_uint8_dec_eq(v_c_541_, v___x_550_);
if (v___x_551_ == 0)
{
uint8_t v___x_552_; uint8_t v___x_553_; 
v___x_552_ = 41;
v___x_553_ = lean_uint8_dec_eq(v_c_541_, v___x_552_);
if (v___x_553_ == 0)
{
uint8_t v___x_554_; uint8_t v___x_555_; 
v___x_554_ = 42;
v___x_555_ = lean_uint8_dec_eq(v_c_541_, v___x_554_);
if (v___x_555_ == 0)
{
uint8_t v___x_556_; uint8_t v___x_557_; 
v___x_556_ = 43;
v___x_557_ = lean_uint8_dec_eq(v_c_541_, v___x_556_);
if (v___x_557_ == 0)
{
uint8_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = 44;
v___x_559_ = lean_uint8_dec_eq(v_c_541_, v___x_558_);
if (v___x_559_ == 0)
{
uint8_t v___x_560_; uint8_t v___x_561_; 
v___x_560_ = 59;
v___x_561_ = lean_uint8_dec_eq(v_c_541_, v___x_560_);
if (v___x_561_ == 0)
{
uint8_t v___x_562_; uint8_t v___x_563_; 
v___x_562_ = 61;
v___x_563_ = lean_uint8_dec_eq(v_c_541_, v___x_562_);
return v___x_563_;
}
else
{
return v___x_561_;
}
}
else
{
return v___x_559_;
}
}
else
{
return v___x_557_;
}
}
else
{
return v___x_555_;
}
}
else
{
return v___x_553_;
}
}
else
{
return v___x_551_;
}
}
else
{
return v___x_549_;
}
}
else
{
return v___x_547_;
}
}
else
{
return v___x_545_;
}
}
else
{
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isSubDelims___boxed(lean_object* v_c_564_){
_start:
{
uint8_t v_c_boxed_565_; uint8_t v_res_566_; lean_object* v_r_567_; 
v_c_boxed_565_ = lean_unbox(v_c_564_);
v_res_566_ = l_Std_Http_Internal_Char_isSubDelims(v_c_boxed_565_);
v_r_567_ = lean_box(v_res_566_);
return v_r_567_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isPChar(uint8_t v_c_568_){
_start:
{
uint8_t v___x_614_; uint8_t v___x_615_; 
v___x_614_ = 48;
v___x_615_ = lean_uint8_dec_le(v___x_614_, v_c_568_);
if (v___x_615_ == 0)
{
goto v___jp_609_;
}
else
{
uint8_t v___x_616_; uint8_t v___x_617_; 
v___x_616_ = 57;
v___x_617_ = lean_uint8_dec_le(v_c_568_, v___x_616_);
if (v___x_617_ == 0)
{
goto v___jp_609_;
}
else
{
return v___x_617_;
}
}
v___jp_569_:
{
uint8_t v___x_570_; uint8_t v___x_571_; 
v___x_570_ = 45;
v___x_571_ = lean_uint8_dec_eq(v_c_568_, v___x_570_);
if (v___x_571_ == 0)
{
uint8_t v___x_572_; uint8_t v___x_573_; 
v___x_572_ = 46;
v___x_573_ = lean_uint8_dec_eq(v_c_568_, v___x_572_);
if (v___x_573_ == 0)
{
uint8_t v___x_574_; uint8_t v___x_575_; 
v___x_574_ = 95;
v___x_575_ = lean_uint8_dec_eq(v_c_568_, v___x_574_);
if (v___x_575_ == 0)
{
uint8_t v___x_576_; uint8_t v___x_577_; 
v___x_576_ = 126;
v___x_577_ = lean_uint8_dec_eq(v_c_568_, v___x_576_);
if (v___x_577_ == 0)
{
uint8_t v___x_578_; uint8_t v___x_579_; 
v___x_578_ = 33;
v___x_579_ = lean_uint8_dec_eq(v_c_568_, v___x_578_);
if (v___x_579_ == 0)
{
uint8_t v___x_580_; uint8_t v___x_581_; 
v___x_580_ = 36;
v___x_581_ = lean_uint8_dec_eq(v_c_568_, v___x_580_);
if (v___x_581_ == 0)
{
uint8_t v___x_582_; uint8_t v___x_583_; 
v___x_582_ = 38;
v___x_583_ = lean_uint8_dec_eq(v_c_568_, v___x_582_);
if (v___x_583_ == 0)
{
uint8_t v___x_584_; uint8_t v___x_585_; 
v___x_584_ = 39;
v___x_585_ = lean_uint8_dec_eq(v_c_568_, v___x_584_);
if (v___x_585_ == 0)
{
uint8_t v___x_586_; uint8_t v___x_587_; 
v___x_586_ = 40;
v___x_587_ = lean_uint8_dec_eq(v_c_568_, v___x_586_);
if (v___x_587_ == 0)
{
uint8_t v___x_588_; uint8_t v___x_589_; 
v___x_588_ = 41;
v___x_589_ = lean_uint8_dec_eq(v_c_568_, v___x_588_);
if (v___x_589_ == 0)
{
uint8_t v___x_590_; uint8_t v___x_591_; 
v___x_590_ = 42;
v___x_591_ = lean_uint8_dec_eq(v_c_568_, v___x_590_);
if (v___x_591_ == 0)
{
uint8_t v___x_592_; uint8_t v___x_593_; 
v___x_592_ = 43;
v___x_593_ = lean_uint8_dec_eq(v_c_568_, v___x_592_);
if (v___x_593_ == 0)
{
uint8_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = 44;
v___x_595_ = lean_uint8_dec_eq(v_c_568_, v___x_594_);
if (v___x_595_ == 0)
{
uint8_t v___x_596_; uint8_t v___x_597_; 
v___x_596_ = 59;
v___x_597_ = lean_uint8_dec_eq(v_c_568_, v___x_596_);
if (v___x_597_ == 0)
{
uint8_t v___x_598_; uint8_t v___x_599_; 
v___x_598_ = 61;
v___x_599_ = lean_uint8_dec_eq(v_c_568_, v___x_598_);
if (v___x_599_ == 0)
{
uint8_t v___x_600_; uint8_t v___x_601_; 
v___x_600_ = 58;
v___x_601_ = lean_uint8_dec_eq(v_c_568_, v___x_600_);
if (v___x_601_ == 0)
{
uint8_t v___x_602_; uint8_t v___x_603_; 
v___x_602_ = 64;
v___x_603_ = lean_uint8_dec_eq(v_c_568_, v___x_602_);
return v___x_603_;
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
else
{
return v___x_595_;
}
}
else
{
return v___x_593_;
}
}
else
{
return v___x_591_;
}
}
else
{
return v___x_589_;
}
}
else
{
return v___x_587_;
}
}
else
{
return v___x_585_;
}
}
else
{
return v___x_583_;
}
}
else
{
return v___x_581_;
}
}
else
{
return v___x_579_;
}
}
else
{
return v___x_577_;
}
}
else
{
return v___x_575_;
}
}
else
{
return v___x_573_;
}
}
else
{
return v___x_571_;
}
}
v___jp_604_:
{
uint8_t v___x_605_; uint8_t v___x_606_; 
v___x_605_ = 65;
v___x_606_ = lean_uint8_dec_le(v___x_605_, v_c_568_);
if (v___x_606_ == 0)
{
goto v___jp_569_;
}
else
{
uint8_t v___x_607_; uint8_t v___x_608_; 
v___x_607_ = 90;
v___x_608_ = lean_uint8_dec_le(v_c_568_, v___x_607_);
if (v___x_608_ == 0)
{
goto v___jp_569_;
}
else
{
return v___x_608_;
}
}
}
v___jp_609_:
{
uint8_t v___x_610_; uint8_t v___x_611_; 
v___x_610_ = 97;
v___x_611_ = lean_uint8_dec_le(v___x_610_, v_c_568_);
if (v___x_611_ == 0)
{
goto v___jp_604_;
}
else
{
uint8_t v___x_612_; uint8_t v___x_613_; 
v___x_612_ = 122;
v___x_613_ = lean_uint8_dec_le(v_c_568_, v___x_612_);
if (v___x_613_ == 0)
{
goto v___jp_604_;
}
else
{
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isPChar___boxed(lean_object* v_c_618_){
_start:
{
uint8_t v_c_boxed_619_; uint8_t v_res_620_; lean_object* v_r_621_; 
v_c_boxed_619_ = lean_unbox(v_c_618_);
v_res_620_ = l_Std_Http_Internal_Char_isPChar(v_c_boxed_619_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryChar(uint8_t v_c_622_){
_start:
{
uint8_t v___x_672_; uint8_t v___x_673_; 
v___x_672_ = 48;
v___x_673_ = lean_uint8_dec_le(v___x_672_, v_c_622_);
if (v___x_673_ == 0)
{
goto v___jp_667_;
}
else
{
uint8_t v___x_674_; uint8_t v___x_675_; 
v___x_674_ = 57;
v___x_675_ = lean_uint8_dec_le(v_c_622_, v___x_674_);
if (v___x_675_ == 0)
{
goto v___jp_667_;
}
else
{
return v___x_675_;
}
}
v___jp_623_:
{
uint8_t v___x_624_; uint8_t v___x_625_; 
v___x_624_ = 45;
v___x_625_ = lean_uint8_dec_eq(v_c_622_, v___x_624_);
if (v___x_625_ == 0)
{
uint8_t v___x_626_; uint8_t v___x_627_; 
v___x_626_ = 46;
v___x_627_ = lean_uint8_dec_eq(v_c_622_, v___x_626_);
if (v___x_627_ == 0)
{
uint8_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = 95;
v___x_629_ = lean_uint8_dec_eq(v_c_622_, v___x_628_);
if (v___x_629_ == 0)
{
uint8_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = 126;
v___x_631_ = lean_uint8_dec_eq(v_c_622_, v___x_630_);
if (v___x_631_ == 0)
{
uint8_t v___x_632_; uint8_t v___x_633_; 
v___x_632_ = 33;
v___x_633_ = lean_uint8_dec_eq(v_c_622_, v___x_632_);
if (v___x_633_ == 0)
{
uint8_t v___x_634_; uint8_t v___x_635_; 
v___x_634_ = 36;
v___x_635_ = lean_uint8_dec_eq(v_c_622_, v___x_634_);
if (v___x_635_ == 0)
{
uint8_t v___x_636_; uint8_t v___x_637_; 
v___x_636_ = 38;
v___x_637_ = lean_uint8_dec_eq(v_c_622_, v___x_636_);
if (v___x_637_ == 0)
{
uint8_t v___x_638_; uint8_t v___x_639_; 
v___x_638_ = 39;
v___x_639_ = lean_uint8_dec_eq(v_c_622_, v___x_638_);
if (v___x_639_ == 0)
{
uint8_t v___x_640_; uint8_t v___x_641_; 
v___x_640_ = 40;
v___x_641_ = lean_uint8_dec_eq(v_c_622_, v___x_640_);
if (v___x_641_ == 0)
{
uint8_t v___x_642_; uint8_t v___x_643_; 
v___x_642_ = 41;
v___x_643_ = lean_uint8_dec_eq(v_c_622_, v___x_642_);
if (v___x_643_ == 0)
{
uint8_t v___x_644_; uint8_t v___x_645_; 
v___x_644_ = 42;
v___x_645_ = lean_uint8_dec_eq(v_c_622_, v___x_644_);
if (v___x_645_ == 0)
{
uint8_t v___x_646_; uint8_t v___x_647_; 
v___x_646_ = 43;
v___x_647_ = lean_uint8_dec_eq(v_c_622_, v___x_646_);
if (v___x_647_ == 0)
{
uint8_t v___x_648_; uint8_t v___x_649_; 
v___x_648_ = 44;
v___x_649_ = lean_uint8_dec_eq(v_c_622_, v___x_648_);
if (v___x_649_ == 0)
{
uint8_t v___x_650_; uint8_t v___x_651_; 
v___x_650_ = 59;
v___x_651_ = lean_uint8_dec_eq(v_c_622_, v___x_650_);
if (v___x_651_ == 0)
{
uint8_t v___x_652_; uint8_t v___x_653_; 
v___x_652_ = 61;
v___x_653_ = lean_uint8_dec_eq(v_c_622_, v___x_652_);
if (v___x_653_ == 0)
{
uint8_t v___x_654_; uint8_t v___x_655_; 
v___x_654_ = 58;
v___x_655_ = lean_uint8_dec_eq(v_c_622_, v___x_654_);
if (v___x_655_ == 0)
{
uint8_t v___x_656_; uint8_t v___x_657_; 
v___x_656_ = 64;
v___x_657_ = lean_uint8_dec_eq(v_c_622_, v___x_656_);
if (v___x_657_ == 0)
{
uint8_t v___x_658_; uint8_t v___x_659_; 
v___x_658_ = 47;
v___x_659_ = lean_uint8_dec_eq(v_c_622_, v___x_658_);
if (v___x_659_ == 0)
{
uint8_t v___x_660_; uint8_t v___x_661_; 
v___x_660_ = 63;
v___x_661_ = lean_uint8_dec_eq(v_c_622_, v___x_660_);
return v___x_661_;
}
else
{
return v___x_659_;
}
}
else
{
return v___x_657_;
}
}
else
{
return v___x_655_;
}
}
else
{
return v___x_653_;
}
}
else
{
return v___x_651_;
}
}
else
{
return v___x_649_;
}
}
else
{
return v___x_647_;
}
}
else
{
return v___x_645_;
}
}
else
{
return v___x_643_;
}
}
else
{
return v___x_641_;
}
}
else
{
return v___x_639_;
}
}
else
{
return v___x_637_;
}
}
else
{
return v___x_635_;
}
}
else
{
return v___x_633_;
}
}
else
{
return v___x_631_;
}
}
else
{
return v___x_629_;
}
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
v___jp_662_:
{
uint8_t v___x_663_; uint8_t v___x_664_; 
v___x_663_ = 65;
v___x_664_ = lean_uint8_dec_le(v___x_663_, v_c_622_);
if (v___x_664_ == 0)
{
goto v___jp_623_;
}
else
{
uint8_t v___x_665_; uint8_t v___x_666_; 
v___x_665_ = 90;
v___x_666_ = lean_uint8_dec_le(v_c_622_, v___x_665_);
if (v___x_666_ == 0)
{
goto v___jp_623_;
}
else
{
return v___x_666_;
}
}
}
v___jp_667_:
{
uint8_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = 97;
v___x_669_ = lean_uint8_dec_le(v___x_668_, v_c_622_);
if (v___x_669_ == 0)
{
goto v___jp_662_;
}
else
{
uint8_t v___x_670_; uint8_t v___x_671_; 
v___x_670_ = 122;
v___x_671_ = lean_uint8_dec_le(v_c_622_, v___x_670_);
if (v___x_671_ == 0)
{
goto v___jp_662_;
}
else
{
return v___x_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryChar___boxed(lean_object* v_c_676_){
_start:
{
uint8_t v_c_boxed_677_; uint8_t v_res_678_; lean_object* v_r_679_; 
v_c_boxed_677_ = lean_unbox(v_c_676_);
v_res_678_ = l_Std_Http_Internal_Char_isQueryChar(v_c_boxed_677_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isFragmentChar(uint8_t v_c_680_){
_start:
{
uint8_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = 48;
v___x_731_ = lean_uint8_dec_le(v___x_730_, v_c_680_);
if (v___x_731_ == 0)
{
goto v___jp_725_;
}
else
{
uint8_t v___x_732_; uint8_t v___x_733_; 
v___x_732_ = 57;
v___x_733_ = lean_uint8_dec_le(v_c_680_, v___x_732_);
if (v___x_733_ == 0)
{
goto v___jp_725_;
}
else
{
return v___x_733_;
}
}
v___jp_681_:
{
uint8_t v___x_682_; uint8_t v___x_683_; 
v___x_682_ = 45;
v___x_683_ = lean_uint8_dec_eq(v_c_680_, v___x_682_);
if (v___x_683_ == 0)
{
uint8_t v___x_684_; uint8_t v___x_685_; 
v___x_684_ = 46;
v___x_685_ = lean_uint8_dec_eq(v_c_680_, v___x_684_);
if (v___x_685_ == 0)
{
uint8_t v___x_686_; uint8_t v___x_687_; 
v___x_686_ = 95;
v___x_687_ = lean_uint8_dec_eq(v_c_680_, v___x_686_);
if (v___x_687_ == 0)
{
uint8_t v___x_688_; uint8_t v___x_689_; 
v___x_688_ = 126;
v___x_689_ = lean_uint8_dec_eq(v_c_680_, v___x_688_);
if (v___x_689_ == 0)
{
uint8_t v___x_690_; uint8_t v___x_691_; 
v___x_690_ = 33;
v___x_691_ = lean_uint8_dec_eq(v_c_680_, v___x_690_);
if (v___x_691_ == 0)
{
uint8_t v___x_692_; uint8_t v___x_693_; 
v___x_692_ = 36;
v___x_693_ = lean_uint8_dec_eq(v_c_680_, v___x_692_);
if (v___x_693_ == 0)
{
uint8_t v___x_694_; uint8_t v___x_695_; 
v___x_694_ = 38;
v___x_695_ = lean_uint8_dec_eq(v_c_680_, v___x_694_);
if (v___x_695_ == 0)
{
uint8_t v___x_696_; uint8_t v___x_697_; 
v___x_696_ = 39;
v___x_697_ = lean_uint8_dec_eq(v_c_680_, v___x_696_);
if (v___x_697_ == 0)
{
uint8_t v___x_698_; uint8_t v___x_699_; 
v___x_698_ = 40;
v___x_699_ = lean_uint8_dec_eq(v_c_680_, v___x_698_);
if (v___x_699_ == 0)
{
uint8_t v___x_700_; uint8_t v___x_701_; 
v___x_700_ = 41;
v___x_701_ = lean_uint8_dec_eq(v_c_680_, v___x_700_);
if (v___x_701_ == 0)
{
uint8_t v___x_702_; uint8_t v___x_703_; 
v___x_702_ = 42;
v___x_703_ = lean_uint8_dec_eq(v_c_680_, v___x_702_);
if (v___x_703_ == 0)
{
uint8_t v___x_704_; uint8_t v___x_705_; 
v___x_704_ = 43;
v___x_705_ = lean_uint8_dec_eq(v_c_680_, v___x_704_);
if (v___x_705_ == 0)
{
uint8_t v___x_706_; uint8_t v___x_707_; 
v___x_706_ = 44;
v___x_707_ = lean_uint8_dec_eq(v_c_680_, v___x_706_);
if (v___x_707_ == 0)
{
uint8_t v___x_708_; uint8_t v___x_709_; 
v___x_708_ = 59;
v___x_709_ = lean_uint8_dec_eq(v_c_680_, v___x_708_);
if (v___x_709_ == 0)
{
uint8_t v___x_710_; uint8_t v___x_711_; 
v___x_710_ = 61;
v___x_711_ = lean_uint8_dec_eq(v_c_680_, v___x_710_);
if (v___x_711_ == 0)
{
uint8_t v___x_712_; uint8_t v___x_713_; 
v___x_712_ = 58;
v___x_713_ = lean_uint8_dec_eq(v_c_680_, v___x_712_);
if (v___x_713_ == 0)
{
uint8_t v___x_714_; uint8_t v___x_715_; 
v___x_714_ = 64;
v___x_715_ = lean_uint8_dec_eq(v_c_680_, v___x_714_);
if (v___x_715_ == 0)
{
uint8_t v___x_716_; uint8_t v___x_717_; 
v___x_716_ = 47;
v___x_717_ = lean_uint8_dec_eq(v_c_680_, v___x_716_);
if (v___x_717_ == 0)
{
uint8_t v___x_718_; uint8_t v___x_719_; 
v___x_718_ = 63;
v___x_719_ = lean_uint8_dec_eq(v_c_680_, v___x_718_);
return v___x_719_;
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
else
{
return v___x_709_;
}
}
else
{
return v___x_707_;
}
}
else
{
return v___x_705_;
}
}
else
{
return v___x_703_;
}
}
else
{
return v___x_701_;
}
}
else
{
return v___x_699_;
}
}
else
{
return v___x_697_;
}
}
else
{
return v___x_695_;
}
}
else
{
return v___x_693_;
}
}
else
{
return v___x_691_;
}
}
else
{
return v___x_689_;
}
}
else
{
return v___x_687_;
}
}
else
{
return v___x_685_;
}
}
else
{
return v___x_683_;
}
}
v___jp_720_:
{
uint8_t v___x_721_; uint8_t v___x_722_; 
v___x_721_ = 65;
v___x_722_ = lean_uint8_dec_le(v___x_721_, v_c_680_);
if (v___x_722_ == 0)
{
goto v___jp_681_;
}
else
{
uint8_t v___x_723_; uint8_t v___x_724_; 
v___x_723_ = 90;
v___x_724_ = lean_uint8_dec_le(v_c_680_, v___x_723_);
if (v___x_724_ == 0)
{
goto v___jp_681_;
}
else
{
return v___x_724_;
}
}
}
v___jp_725_:
{
uint8_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 97;
v___x_727_ = lean_uint8_dec_le(v___x_726_, v_c_680_);
if (v___x_727_ == 0)
{
goto v___jp_720_;
}
else
{
uint8_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 122;
v___x_729_ = lean_uint8_dec_le(v_c_680_, v___x_728_);
if (v___x_729_ == 0)
{
goto v___jp_720_;
}
else
{
return v___x_729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isFragmentChar___boxed(lean_object* v_c_734_){
_start:
{
uint8_t v_c_boxed_735_; uint8_t v_res_736_; lean_object* v_r_737_; 
v_c_boxed_735_ = lean_unbox(v_c_734_);
v_res_736_ = l_Std_Http_Internal_Char_isFragmentChar(v_c_boxed_735_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUserInfoChar(uint8_t v_c_738_){
_start:
{
uint8_t v___x_782_; uint8_t v___x_783_; 
v___x_782_ = 48;
v___x_783_ = lean_uint8_dec_le(v___x_782_, v_c_738_);
if (v___x_783_ == 0)
{
goto v___jp_777_;
}
else
{
uint8_t v___x_784_; uint8_t v___x_785_; 
v___x_784_ = 57;
v___x_785_ = lean_uint8_dec_le(v_c_738_, v___x_784_);
if (v___x_785_ == 0)
{
goto v___jp_777_;
}
else
{
return v___x_785_;
}
}
v___jp_739_:
{
uint8_t v___x_740_; uint8_t v___x_741_; 
v___x_740_ = 45;
v___x_741_ = lean_uint8_dec_eq(v_c_738_, v___x_740_);
if (v___x_741_ == 0)
{
uint8_t v___x_742_; uint8_t v___x_743_; 
v___x_742_ = 46;
v___x_743_ = lean_uint8_dec_eq(v_c_738_, v___x_742_);
if (v___x_743_ == 0)
{
uint8_t v___x_744_; uint8_t v___x_745_; 
v___x_744_ = 95;
v___x_745_ = lean_uint8_dec_eq(v_c_738_, v___x_744_);
if (v___x_745_ == 0)
{
uint8_t v___x_746_; uint8_t v___x_747_; 
v___x_746_ = 126;
v___x_747_ = lean_uint8_dec_eq(v_c_738_, v___x_746_);
if (v___x_747_ == 0)
{
uint8_t v___x_748_; uint8_t v___x_749_; 
v___x_748_ = 33;
v___x_749_ = lean_uint8_dec_eq(v_c_738_, v___x_748_);
if (v___x_749_ == 0)
{
uint8_t v___x_750_; uint8_t v___x_751_; 
v___x_750_ = 36;
v___x_751_ = lean_uint8_dec_eq(v_c_738_, v___x_750_);
if (v___x_751_ == 0)
{
uint8_t v___x_752_; uint8_t v___x_753_; 
v___x_752_ = 38;
v___x_753_ = lean_uint8_dec_eq(v_c_738_, v___x_752_);
if (v___x_753_ == 0)
{
uint8_t v___x_754_; uint8_t v___x_755_; 
v___x_754_ = 39;
v___x_755_ = lean_uint8_dec_eq(v_c_738_, v___x_754_);
if (v___x_755_ == 0)
{
uint8_t v___x_756_; uint8_t v___x_757_; 
v___x_756_ = 40;
v___x_757_ = lean_uint8_dec_eq(v_c_738_, v___x_756_);
if (v___x_757_ == 0)
{
uint8_t v___x_758_; uint8_t v___x_759_; 
v___x_758_ = 41;
v___x_759_ = lean_uint8_dec_eq(v_c_738_, v___x_758_);
if (v___x_759_ == 0)
{
uint8_t v___x_760_; uint8_t v___x_761_; 
v___x_760_ = 42;
v___x_761_ = lean_uint8_dec_eq(v_c_738_, v___x_760_);
if (v___x_761_ == 0)
{
uint8_t v___x_762_; uint8_t v___x_763_; 
v___x_762_ = 43;
v___x_763_ = lean_uint8_dec_eq(v_c_738_, v___x_762_);
if (v___x_763_ == 0)
{
uint8_t v___x_764_; uint8_t v___x_765_; 
v___x_764_ = 44;
v___x_765_ = lean_uint8_dec_eq(v_c_738_, v___x_764_);
if (v___x_765_ == 0)
{
uint8_t v___x_766_; uint8_t v___x_767_; 
v___x_766_ = 59;
v___x_767_ = lean_uint8_dec_eq(v_c_738_, v___x_766_);
if (v___x_767_ == 0)
{
uint8_t v___x_768_; uint8_t v___x_769_; 
v___x_768_ = 61;
v___x_769_ = lean_uint8_dec_eq(v_c_738_, v___x_768_);
if (v___x_769_ == 0)
{
uint8_t v___x_770_; uint8_t v___x_771_; 
v___x_770_ = 58;
v___x_771_ = lean_uint8_dec_eq(v_c_738_, v___x_770_);
return v___x_771_;
}
else
{
return v___x_769_;
}
}
else
{
return v___x_767_;
}
}
else
{
return v___x_765_;
}
}
else
{
return v___x_763_;
}
}
else
{
return v___x_761_;
}
}
else
{
return v___x_759_;
}
}
else
{
return v___x_757_;
}
}
else
{
return v___x_755_;
}
}
else
{
return v___x_753_;
}
}
else
{
return v___x_751_;
}
}
else
{
return v___x_749_;
}
}
else
{
return v___x_747_;
}
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
v___jp_772_:
{
uint8_t v___x_773_; uint8_t v___x_774_; 
v___x_773_ = 65;
v___x_774_ = lean_uint8_dec_le(v___x_773_, v_c_738_);
if (v___x_774_ == 0)
{
goto v___jp_739_;
}
else
{
uint8_t v___x_775_; uint8_t v___x_776_; 
v___x_775_ = 90;
v___x_776_ = lean_uint8_dec_le(v_c_738_, v___x_775_);
if (v___x_776_ == 0)
{
goto v___jp_739_;
}
else
{
return v___x_776_;
}
}
}
v___jp_777_:
{
uint8_t v___x_778_; uint8_t v___x_779_; 
v___x_778_ = 97;
v___x_779_ = lean_uint8_dec_le(v___x_778_, v_c_738_);
if (v___x_779_ == 0)
{
goto v___jp_772_;
}
else
{
uint8_t v___x_780_; uint8_t v___x_781_; 
v___x_780_ = 122;
v___x_781_ = lean_uint8_dec_le(v_c_738_, v___x_780_);
if (v___x_781_ == 0)
{
goto v___jp_772_;
}
else
{
return v___x_781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUserInfoChar___boxed(lean_object* v_c_786_){
_start:
{
uint8_t v_c_boxed_787_; uint8_t v_res_788_; lean_object* v_r_789_; 
v_c_boxed_787_ = lean_unbox(v_c_786_);
v_res_788_ = l_Std_Http_Internal_Char_isUserInfoChar(v_c_boxed_787_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryDataChar(uint8_t v_c_790_){
_start:
{
uint8_t v___x_847_; uint8_t v___x_848_; 
v___x_847_ = 48;
v___x_848_ = lean_uint8_dec_le(v___x_847_, v_c_790_);
if (v___x_848_ == 0)
{
goto v___jp_842_;
}
else
{
uint8_t v___x_849_; uint8_t v___x_850_; 
v___x_849_ = 57;
v___x_850_ = lean_uint8_dec_le(v_c_790_, v___x_849_);
if (v___x_850_ == 0)
{
goto v___jp_842_;
}
else
{
goto v___jp_791_;
}
}
v___jp_791_:
{
uint8_t v___x_792_; uint8_t v___x_793_; 
v___x_792_ = 38;
v___x_793_ = lean_uint8_dec_eq(v_c_790_, v___x_792_);
if (v___x_793_ == 0)
{
uint8_t v___x_794_; uint8_t v___x_795_; 
v___x_794_ = 61;
v___x_795_ = lean_uint8_dec_eq(v_c_790_, v___x_794_);
if (v___x_795_ == 0)
{
uint8_t v___x_796_; 
v___x_796_ = 1;
return v___x_796_;
}
else
{
return v___x_793_;
}
}
else
{
uint8_t v___x_797_; 
v___x_797_ = 0;
return v___x_797_;
}
}
v___jp_798_:
{
uint8_t v___x_799_; uint8_t v___x_800_; 
v___x_799_ = 45;
v___x_800_ = lean_uint8_dec_eq(v_c_790_, v___x_799_);
if (v___x_800_ == 0)
{
uint8_t v___x_801_; uint8_t v___x_802_; 
v___x_801_ = 46;
v___x_802_ = lean_uint8_dec_eq(v_c_790_, v___x_801_);
if (v___x_802_ == 0)
{
uint8_t v___x_803_; uint8_t v___x_804_; 
v___x_803_ = 95;
v___x_804_ = lean_uint8_dec_eq(v_c_790_, v___x_803_);
if (v___x_804_ == 0)
{
uint8_t v___x_805_; uint8_t v___x_806_; 
v___x_805_ = 126;
v___x_806_ = lean_uint8_dec_eq(v_c_790_, v___x_805_);
if (v___x_806_ == 0)
{
uint8_t v___x_807_; uint8_t v___x_808_; 
v___x_807_ = 33;
v___x_808_ = lean_uint8_dec_eq(v_c_790_, v___x_807_);
if (v___x_808_ == 0)
{
uint8_t v___x_809_; uint8_t v___x_810_; 
v___x_809_ = 36;
v___x_810_ = lean_uint8_dec_eq(v_c_790_, v___x_809_);
if (v___x_810_ == 0)
{
uint8_t v___x_811_; uint8_t v___x_812_; 
v___x_811_ = 38;
v___x_812_ = lean_uint8_dec_eq(v_c_790_, v___x_811_);
if (v___x_812_ == 0)
{
uint8_t v___x_813_; uint8_t v___x_814_; 
v___x_813_ = 39;
v___x_814_ = lean_uint8_dec_eq(v_c_790_, v___x_813_);
if (v___x_814_ == 0)
{
uint8_t v___x_815_; uint8_t v___x_816_; 
v___x_815_ = 40;
v___x_816_ = lean_uint8_dec_eq(v_c_790_, v___x_815_);
if (v___x_816_ == 0)
{
uint8_t v___x_817_; uint8_t v___x_818_; 
v___x_817_ = 41;
v___x_818_ = lean_uint8_dec_eq(v_c_790_, v___x_817_);
if (v___x_818_ == 0)
{
uint8_t v___x_819_; uint8_t v___x_820_; 
v___x_819_ = 42;
v___x_820_ = lean_uint8_dec_eq(v_c_790_, v___x_819_);
if (v___x_820_ == 0)
{
uint8_t v___x_821_; uint8_t v___x_822_; 
v___x_821_ = 43;
v___x_822_ = lean_uint8_dec_eq(v_c_790_, v___x_821_);
if (v___x_822_ == 0)
{
uint8_t v___x_823_; uint8_t v___x_824_; 
v___x_823_ = 44;
v___x_824_ = lean_uint8_dec_eq(v_c_790_, v___x_823_);
if (v___x_824_ == 0)
{
uint8_t v___x_825_; uint8_t v___x_826_; 
v___x_825_ = 59;
v___x_826_ = lean_uint8_dec_eq(v_c_790_, v___x_825_);
if (v___x_826_ == 0)
{
uint8_t v___x_827_; uint8_t v___x_828_; 
v___x_827_ = 61;
v___x_828_ = lean_uint8_dec_eq(v_c_790_, v___x_827_);
if (v___x_828_ == 0)
{
uint8_t v___x_829_; uint8_t v___x_830_; 
v___x_829_ = 58;
v___x_830_ = lean_uint8_dec_eq(v_c_790_, v___x_829_);
if (v___x_830_ == 0)
{
uint8_t v___x_831_; uint8_t v___x_832_; 
v___x_831_ = 64;
v___x_832_ = lean_uint8_dec_eq(v_c_790_, v___x_831_);
if (v___x_832_ == 0)
{
uint8_t v___x_833_; uint8_t v___x_834_; 
v___x_833_ = 47;
v___x_834_ = lean_uint8_dec_eq(v_c_790_, v___x_833_);
if (v___x_834_ == 0)
{
uint8_t v___x_835_; uint8_t v___x_836_; 
v___x_835_ = 63;
v___x_836_ = lean_uint8_dec_eq(v_c_790_, v___x_835_);
if (v___x_836_ == 0)
{
return v___x_836_;
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
v___jp_837_:
{
uint8_t v___x_838_; uint8_t v___x_839_; 
v___x_838_ = 65;
v___x_839_ = lean_uint8_dec_le(v___x_838_, v_c_790_);
if (v___x_839_ == 0)
{
goto v___jp_798_;
}
else
{
uint8_t v___x_840_; uint8_t v___x_841_; 
v___x_840_ = 90;
v___x_841_ = lean_uint8_dec_le(v_c_790_, v___x_840_);
if (v___x_841_ == 0)
{
goto v___jp_798_;
}
else
{
goto v___jp_791_;
}
}
}
v___jp_842_:
{
uint8_t v___x_843_; uint8_t v___x_844_; 
v___x_843_ = 97;
v___x_844_ = lean_uint8_dec_le(v___x_843_, v_c_790_);
if (v___x_844_ == 0)
{
goto v___jp_837_;
}
else
{
uint8_t v___x_845_; uint8_t v___x_846_; 
v___x_845_ = 122;
v___x_846_ = lean_uint8_dec_le(v_c_790_, v___x_845_);
if (v___x_846_ == 0)
{
goto v___jp_837_;
}
else
{
goto v___jp_791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryDataChar___boxed(lean_object* v_c_851_){
_start:
{
uint8_t v_c_boxed_852_; uint8_t v_res_853_; lean_object* v_r_854_; 
v_c_boxed_852_ = lean_unbox(v_c_851_);
v_res_853_ = l_Std_Http_Internal_Char_isQueryDataChar(v_c_boxed_852_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
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
