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
uint32_t v___x_50_; uint8_t v___x_51_; 
v___x_50_ = 33;
v___x_51_ = lean_uint32_dec_eq(v_c_39_, v___x_50_);
if (v___x_51_ == 0)
{
uint32_t v___x_52_; uint8_t v___x_53_; 
v___x_52_ = 35;
v___x_53_ = lean_uint32_dec_eq(v_c_39_, v___x_52_);
if (v___x_53_ == 0)
{
uint32_t v___x_54_; uint8_t v___x_55_; 
v___x_54_ = 36;
v___x_55_ = lean_uint32_dec_eq(v_c_39_, v___x_54_);
if (v___x_55_ == 0)
{
uint32_t v___x_56_; uint8_t v___x_57_; 
v___x_56_ = 37;
v___x_57_ = lean_uint32_dec_eq(v_c_39_, v___x_56_);
if (v___x_57_ == 0)
{
uint32_t v___x_58_; uint8_t v___x_59_; 
v___x_58_ = 38;
v___x_59_ = lean_uint32_dec_eq(v_c_39_, v___x_58_);
if (v___x_59_ == 0)
{
uint32_t v___x_60_; uint8_t v___x_61_; 
v___x_60_ = 39;
v___x_61_ = lean_uint32_dec_eq(v_c_39_, v___x_60_);
if (v___x_61_ == 0)
{
uint32_t v___x_62_; uint8_t v___x_63_; 
v___x_62_ = 42;
v___x_63_ = lean_uint32_dec_eq(v_c_39_, v___x_62_);
if (v___x_63_ == 0)
{
uint32_t v___x_64_; uint8_t v___x_65_; 
v___x_64_ = 43;
v___x_65_ = lean_uint32_dec_eq(v_c_39_, v___x_64_);
if (v___x_65_ == 0)
{
uint32_t v___x_66_; uint8_t v___x_67_; 
v___x_66_ = 45;
v___x_67_ = lean_uint32_dec_eq(v_c_39_, v___x_66_);
if (v___x_67_ == 0)
{
uint32_t v___x_68_; uint8_t v___x_69_; 
v___x_68_ = 46;
v___x_69_ = lean_uint32_dec_eq(v_c_39_, v___x_68_);
if (v___x_69_ == 0)
{
uint32_t v___x_70_; uint8_t v___x_71_; 
v___x_70_ = 94;
v___x_71_ = lean_uint32_dec_eq(v_c_39_, v___x_70_);
if (v___x_71_ == 0)
{
uint32_t v___x_72_; uint8_t v___x_73_; 
v___x_72_ = 95;
v___x_73_ = lean_uint32_dec_eq(v_c_39_, v___x_72_);
if (v___x_73_ == 0)
{
uint32_t v___x_74_; uint8_t v___x_75_; 
v___x_74_ = 96;
v___x_75_ = lean_uint32_dec_eq(v_c_39_, v___x_74_);
if (v___x_75_ == 0)
{
uint32_t v___x_76_; uint8_t v___x_77_; 
v___x_76_ = 124;
v___x_77_ = lean_uint32_dec_eq(v_c_39_, v___x_76_);
if (v___x_77_ == 0)
{
uint32_t v___x_78_; uint8_t v___x_79_; 
v___x_78_ = 126;
v___x_79_ = lean_uint32_dec_eq(v_c_39_, v___x_78_);
if (v___x_79_ == 0)
{
uint32_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 48;
v___x_81_ = lean_uint32_dec_le(v___x_80_, v_c_39_);
if (v___x_81_ == 0)
{
goto v___jp_45_;
}
else
{
uint32_t v___x_82_; uint8_t v___x_83_; 
v___x_82_ = 57;
v___x_83_ = lean_uint32_dec_le(v_c_39_, v___x_82_);
if (v___x_83_ == 0)
{
goto v___jp_45_;
}
else
{
return v___x_83_;
}
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
}
else
{
return v___x_53_;
}
}
else
{
return v___x_51_;
}
v___jp_40_:
{
uint32_t v___x_41_; uint8_t v___x_42_; 
v___x_41_ = 97;
v___x_42_ = lean_uint32_dec_le(v___x_41_, v_c_39_);
if (v___x_42_ == 0)
{
return v___x_42_;
}
else
{
uint32_t v___x_43_; uint8_t v___x_44_; 
v___x_43_ = 122;
v___x_44_ = lean_uint32_dec_le(v_c_39_, v___x_43_);
return v___x_44_;
}
}
v___jp_45_:
{
uint32_t v___x_46_; uint8_t v___x_47_; 
v___x_46_ = 65;
v___x_47_ = lean_uint32_dec_le(v___x_46_, v_c_39_);
if (v___x_47_ == 0)
{
goto v___jp_40_;
}
else
{
uint32_t v___x_48_; uint8_t v___x_49_; 
v___x_48_ = 90;
v___x_49_ = lean_uint32_dec_le(v_c_39_, v___x_48_);
if (v___x_49_ == 0)
{
goto v___jp_40_;
}
else
{
return v___x_49_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_tchar___boxed(lean_object* v_c_84_){
_start:
{
uint32_t v_c_boxed_85_; uint8_t v_res_86_; lean_object* v_r_87_; 
v_c_boxed_85_ = lean_unbox_uint32(v_c_84_);
lean_dec(v_c_84_);
v_res_86_ = l_Std_Http_Internal_Char_tchar(v_c_boxed_85_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_vchar(uint32_t v_c_88_){
_start:
{
uint32_t v___x_89_; uint8_t v___x_90_; 
v___x_89_ = 33;
v___x_90_ = lean_uint32_dec_le(v___x_89_, v_c_88_);
if (v___x_90_ == 0)
{
return v___x_90_;
}
else
{
uint32_t v___x_91_; uint8_t v___x_92_; 
v___x_91_ = 126;
v___x_92_ = lean_uint32_dec_le(v_c_88_, v___x_91_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_vchar___boxed(lean_object* v_c_93_){
_start:
{
uint32_t v_c_boxed_94_; uint8_t v_res_95_; lean_object* v_r_96_; 
v_c_boxed_94_ = lean_unbox_uint32(v_c_93_);
lean_dec(v_c_93_);
v_res_95_ = l_Std_Http_Internal_Char_vchar(v_c_boxed_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_qdtext(uint32_t v_c_97_){
_start:
{
uint32_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = 9;
v___x_104_ = lean_uint32_dec_eq(v_c_97_, v___x_103_);
if (v___x_104_ == 0)
{
uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_105_ = 32;
v___x_106_ = lean_uint32_dec_eq(v_c_97_, v___x_105_);
if (v___x_106_ == 0)
{
uint32_t v___x_107_; uint8_t v___x_108_; 
v___x_107_ = 33;
v___x_108_ = lean_uint32_dec_eq(v_c_97_, v___x_107_);
if (v___x_108_ == 0)
{
uint32_t v___x_109_; uint8_t v___x_110_; 
v___x_109_ = 35;
v___x_110_ = lean_uint32_dec_le(v___x_109_, v_c_97_);
if (v___x_110_ == 0)
{
goto v___jp_98_;
}
else
{
uint32_t v___x_111_; uint8_t v___x_112_; 
v___x_111_ = 91;
v___x_112_ = lean_uint32_dec_le(v_c_97_, v___x_111_);
if (v___x_112_ == 0)
{
goto v___jp_98_;
}
else
{
return v___x_112_;
}
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
}
else
{
return v___x_104_;
}
v___jp_98_:
{
uint32_t v___x_99_; uint8_t v___x_100_; 
v___x_99_ = 93;
v___x_100_ = lean_uint32_dec_le(v___x_99_, v_c_97_);
if (v___x_100_ == 0)
{
return v___x_100_;
}
else
{
uint32_t v___x_101_; uint8_t v___x_102_; 
v___x_101_ = 126;
v___x_102_ = lean_uint32_dec_le(v_c_97_, v___x_101_);
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_qdtext___boxed(lean_object* v_c_113_){
_start:
{
uint32_t v_c_boxed_114_; uint8_t v_res_115_; lean_object* v_r_116_; 
v_c_boxed_114_ = lean_unbox_uint32(v_c_113_);
lean_dec(v_c_113_);
v_res_115_ = l_Std_Http_Internal_Char_qdtext(v_c_boxed_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_quotedPairChar(uint32_t v_c_117_){
_start:
{
uint32_t v___x_118_; uint8_t v___x_119_; 
v___x_118_ = 9;
v___x_119_ = lean_uint32_dec_eq(v_c_117_, v___x_118_);
if (v___x_119_ == 0)
{
uint32_t v___x_120_; uint8_t v___x_121_; 
v___x_120_ = 32;
v___x_121_ = lean_uint32_dec_eq(v_c_117_, v___x_120_);
if (v___x_121_ == 0)
{
uint32_t v___x_122_; uint8_t v___x_123_; 
v___x_122_ = 33;
v___x_123_ = lean_uint32_dec_le(v___x_122_, v_c_117_);
if (v___x_123_ == 0)
{
return v___x_123_;
}
else
{
uint32_t v___x_124_; uint8_t v___x_125_; 
v___x_124_ = 126;
v___x_125_ = lean_uint32_dec_le(v_c_117_, v___x_124_);
return v___x_125_;
}
}
else
{
return v___x_121_;
}
}
else
{
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_quotedPairChar___boxed(lean_object* v_c_126_){
_start:
{
uint32_t v_c_boxed_127_; uint8_t v_res_128_; lean_object* v_r_129_; 
v_c_boxed_127_ = lean_unbox_uint32(v_c_126_);
lean_dec(v_c_126_);
v_res_128_ = l_Std_Http_Internal_Char_quotedPairChar(v_c_boxed_127_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_quotedStringChar(uint32_t v_c_130_){
_start:
{
uint32_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = 9;
v___x_146_ = lean_uint32_dec_eq(v_c_130_, v___x_145_);
if (v___x_146_ == 0)
{
uint32_t v___x_147_; uint8_t v___x_148_; 
v___x_147_ = 32;
v___x_148_ = lean_uint32_dec_eq(v_c_130_, v___x_147_);
if (v___x_148_ == 0)
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 33;
v___x_150_ = lean_uint32_dec_eq(v_c_130_, v___x_149_);
if (v___x_150_ == 0)
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 35;
v___x_152_ = lean_uint32_dec_le(v___x_151_, v_c_130_);
if (v___x_152_ == 0)
{
goto v___jp_140_;
}
else
{
uint32_t v___x_153_; uint8_t v___x_154_; 
v___x_153_ = 91;
v___x_154_ = lean_uint32_dec_le(v_c_130_, v___x_153_);
if (v___x_154_ == 0)
{
goto v___jp_140_;
}
else
{
return v___x_154_;
}
}
}
else
{
return v___x_150_;
}
}
else
{
return v___x_148_;
}
}
else
{
return v___x_146_;
}
v___jp_131_:
{
uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 9;
v___x_133_ = lean_uint32_dec_eq(v_c_130_, v___x_132_);
if (v___x_133_ == 0)
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 32;
v___x_135_ = lean_uint32_dec_eq(v_c_130_, v___x_134_);
if (v___x_135_ == 0)
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 33;
v___x_137_ = lean_uint32_dec_le(v___x_136_, v_c_130_);
if (v___x_137_ == 0)
{
return v___x_137_;
}
else
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 126;
v___x_139_ = lean_uint32_dec_le(v_c_130_, v___x_138_);
return v___x_139_;
}
}
else
{
return v___x_135_;
}
}
else
{
return v___x_133_;
}
}
v___jp_140_:
{
uint32_t v___x_141_; uint8_t v___x_142_; 
v___x_141_ = 93;
v___x_142_ = lean_uint32_dec_le(v___x_141_, v_c_130_);
if (v___x_142_ == 0)
{
goto v___jp_131_;
}
else
{
uint32_t v___x_143_; uint8_t v___x_144_; 
v___x_143_ = 126;
v___x_144_ = lean_uint32_dec_le(v_c_130_, v___x_143_);
if (v___x_144_ == 0)
{
goto v___jp_131_;
}
else
{
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_quotedStringChar___boxed(lean_object* v_c_155_){
_start:
{
uint32_t v_c_boxed_156_; uint8_t v_res_157_; lean_object* v_r_158_; 
v_c_boxed_156_ = lean_unbox_uint32(v_c_155_);
lean_dec(v_c_155_);
v_res_157_ = l_Std_Http_Internal_Char_quotedStringChar(v_c_boxed_156_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg(uint32_t v_c_159_, lean_object* v_h__1_160_, lean_object* v_h__2_161_, lean_object* v_h__3_162_, lean_object* v_h__4_163_){
_start:
{
uint32_t v___x_164_; uint8_t v___x_165_; 
v___x_164_ = 9;
v___x_165_ = lean_uint32_dec_eq(v_c_159_, v___x_164_);
if (v___x_165_ == 0)
{
uint32_t v___x_166_; uint8_t v___x_167_; 
lean_dec(v_h__1_160_);
v___x_166_ = 32;
v___x_167_ = lean_uint32_dec_eq(v_c_159_, v___x_166_);
if (v___x_167_ == 0)
{
uint32_t v___x_168_; uint8_t v___x_169_; 
lean_dec(v_h__2_161_);
v___x_168_ = 33;
v___x_169_ = lean_uint32_dec_eq(v_c_159_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; 
lean_dec(v_h__3_162_);
v___x_170_ = lean_box_uint32(v_c_159_);
v___x_171_ = lean_apply_4(v_h__4_163_, v___x_170_, lean_box(0), lean_box(0), lean_box(0));
return v___x_171_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec(v_h__4_163_);
v___x_172_ = lean_box(0);
v___x_173_ = lean_apply_1(v_h__3_162_, v___x_172_);
return v___x_173_;
}
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v_h__4_163_);
lean_dec(v_h__3_162_);
v___x_174_ = lean_box(0);
v___x_175_ = lean_apply_1(v_h__2_161_, v___x_174_);
return v___x_175_;
}
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec(v_h__4_163_);
lean_dec(v_h__3_162_);
lean_dec(v_h__2_161_);
v___x_176_ = lean_box(0);
v___x_177_ = lean_apply_1(v_h__1_160_, v___x_176_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg___boxed(lean_object* v_c_178_, lean_object* v_h__1_179_, lean_object* v_h__2_180_, lean_object* v_h__3_181_, lean_object* v_h__4_182_){
_start:
{
uint32_t v_c_73__boxed_183_; lean_object* v_res_184_; 
v_c_73__boxed_183_ = lean_unbox_uint32(v_c_178_);
lean_dec(v_c_178_);
v_res_184_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg(v_c_73__boxed_183_, v_h__1_179_, v_h__2_180_, v_h__3_181_, v_h__4_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(lean_object* v_motive_185_, uint32_t v_c_186_, lean_object* v_h__1_187_, lean_object* v_h__2_188_, lean_object* v_h__3_189_, lean_object* v_h__4_190_){
_start:
{
uint32_t v___x_191_; uint8_t v___x_192_; 
v___x_191_ = 9;
v___x_192_ = lean_uint32_dec_eq(v_c_186_, v___x_191_);
if (v___x_192_ == 0)
{
uint32_t v___x_193_; uint8_t v___x_194_; 
lean_dec(v_h__1_187_);
v___x_193_ = 32;
v___x_194_ = lean_uint32_dec_eq(v_c_186_, v___x_193_);
if (v___x_194_ == 0)
{
uint32_t v___x_195_; uint8_t v___x_196_; 
lean_dec(v_h__2_188_);
v___x_195_ = 33;
v___x_196_ = lean_uint32_dec_eq(v_c_186_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_h__3_189_);
v___x_197_ = lean_box_uint32(v_c_186_);
v___x_198_ = lean_apply_4(v_h__4_190_, v___x_197_, lean_box(0), lean_box(0), lean_box(0));
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v_h__4_190_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_apply_1(v_h__3_189_, v___x_199_);
return v___x_200_;
}
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v_h__4_190_);
lean_dec(v_h__3_189_);
v___x_201_ = lean_box(0);
v___x_202_ = lean_apply_1(v_h__2_188_, v___x_201_);
return v___x_202_;
}
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v_h__4_190_);
lean_dec(v_h__3_189_);
lean_dec(v_h__2_188_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_apply_1(v_h__1_187_, v___x_203_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___boxed(lean_object* v_motive_205_, lean_object* v_c_206_, lean_object* v_h__1_207_, lean_object* v_h__2_208_, lean_object* v_h__3_209_, lean_object* v_h__4_210_){
_start:
{
uint32_t v_c_104__boxed_211_; lean_object* v_res_212_; 
v_c_104__boxed_211_ = lean_unbox_uint32(v_c_206_);
lean_dec(v_c_206_);
v_res_212_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(v_motive_205_, v_c_104__boxed_211_, v_h__1_207_, v_h__2_208_, v_h__3_209_, v_h__4_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(uint32_t v_c_213_, lean_object* v_h__1_214_, lean_object* v_h__2_215_, lean_object* v_h__3_216_){
_start:
{
uint32_t v___x_217_; uint8_t v___x_218_; 
v___x_217_ = 9;
v___x_218_ = lean_uint32_dec_eq(v_c_213_, v___x_217_);
if (v___x_218_ == 0)
{
uint32_t v___x_219_; uint8_t v___x_220_; 
lean_dec(v_h__1_214_);
v___x_219_ = 32;
v___x_220_ = lean_uint32_dec_eq(v_c_213_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v_h__2_215_);
v___x_221_ = lean_box_uint32(v_c_213_);
v___x_222_ = lean_apply_3(v_h__3_216_, v___x_221_, lean_box(0), lean_box(0));
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec(v_h__3_216_);
v___x_223_ = lean_box(0);
v___x_224_ = lean_apply_1(v_h__2_215_, v___x_223_);
return v___x_224_;
}
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec(v_h__3_216_);
lean_dec(v_h__2_215_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_apply_1(v_h__1_214_, v___x_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg___boxed(lean_object* v_c_227_, lean_object* v_h__1_228_, lean_object* v_h__2_229_, lean_object* v_h__3_230_){
_start:
{
uint32_t v_c_51__boxed_231_; lean_object* v_res_232_; 
v_c_51__boxed_231_ = lean_unbox_uint32(v_c_227_);
lean_dec(v_c_227_);
v_res_232_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(v_c_51__boxed_231_, v_h__1_228_, v_h__2_229_, v_h__3_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(lean_object* v_motive_233_, uint32_t v_c_234_, lean_object* v_h__1_235_, lean_object* v_h__2_236_, lean_object* v_h__3_237_){
_start:
{
uint32_t v___x_238_; uint8_t v___x_239_; 
v___x_238_ = 9;
v___x_239_ = lean_uint32_dec_eq(v_c_234_, v___x_238_);
if (v___x_239_ == 0)
{
uint32_t v___x_240_; uint8_t v___x_241_; 
lean_dec(v_h__1_235_);
v___x_240_ = 32;
v___x_241_ = lean_uint32_dec_eq(v_c_234_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_h__2_236_);
v___x_242_ = lean_box_uint32(v_c_234_);
v___x_243_ = lean_apply_3(v_h__3_237_, v___x_242_, lean_box(0), lean_box(0));
return v___x_243_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_h__3_237_);
v___x_244_ = lean_box(0);
v___x_245_ = lean_apply_1(v_h__2_236_, v___x_244_);
return v___x_245_;
}
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v_h__3_237_);
lean_dec(v_h__2_236_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_apply_1(v_h__1_235_, v___x_246_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___boxed(lean_object* v_motive_248_, lean_object* v_c_249_, lean_object* v_h__1_250_, lean_object* v_h__2_251_, lean_object* v_h__3_252_){
_start:
{
uint32_t v_c_74__boxed_253_; lean_object* v_res_254_; 
v_c_74__boxed_253_ = lean_unbox_uint32(v_c_249_);
lean_dec(v_c_249_);
v_res_254_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(v_motive_248_, v_c_74__boxed_253_, v_h__1_250_, v_h__2_251_, v_h__3_252_);
return v_res_254_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_fieldVchar(uint32_t v_c_255_){
_start:
{
uint32_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = 33;
v___x_257_ = lean_uint32_dec_le(v___x_256_, v_c_255_);
if (v___x_257_ == 0)
{
return v___x_257_;
}
else
{
uint32_t v___x_258_; uint8_t v___x_259_; 
v___x_258_ = 126;
v___x_259_ = lean_uint32_dec_le(v_c_255_, v___x_258_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldVchar___boxed(lean_object* v_c_260_){
_start:
{
uint32_t v_c_boxed_261_; uint8_t v_res_262_; lean_object* v_r_263_; 
v_c_boxed_261_ = lean_unbox_uint32(v_c_260_);
lean_dec(v_c_260_);
v_res_262_ = l_Std_Http_Internal_Char_fieldVchar(v_c_boxed_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_fieldContent(uint32_t v_c_264_){
_start:
{
uint32_t v___x_270_; uint8_t v___x_271_; 
v___x_270_ = 33;
v___x_271_ = lean_uint32_dec_le(v___x_270_, v_c_264_);
if (v___x_271_ == 0)
{
goto v___jp_265_;
}
else
{
uint32_t v___x_272_; uint8_t v___x_273_; 
v___x_272_ = 126;
v___x_273_ = lean_uint32_dec_le(v_c_264_, v___x_272_);
if (v___x_273_ == 0)
{
goto v___jp_265_;
}
else
{
return v___x_273_;
}
}
v___jp_265_:
{
uint32_t v___x_266_; uint8_t v___x_267_; 
v___x_266_ = 32;
v___x_267_ = lean_uint32_dec_eq(v_c_264_, v___x_266_);
if (v___x_267_ == 0)
{
uint32_t v___x_268_; uint8_t v___x_269_; 
v___x_268_ = 9;
v___x_269_ = lean_uint32_dec_eq(v_c_264_, v___x_268_);
return v___x_269_;
}
else
{
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldContent___boxed(lean_object* v_c_274_){
_start:
{
uint32_t v_c_boxed_275_; uint8_t v_res_276_; lean_object* v_r_277_; 
v_c_boxed_275_ = lean_unbox_uint32(v_c_274_);
lean_dec(v_c_274_);
v_res_276_ = l_Std_Http_Internal_Char_fieldContent(v_c_boxed_275_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_ctext(uint32_t v_c_278_){
_start:
{
uint32_t v___x_289_; uint8_t v___x_290_; 
v___x_289_ = 9;
v___x_290_ = lean_uint32_dec_eq(v_c_278_, v___x_289_);
if (v___x_290_ == 0)
{
uint32_t v___x_291_; uint8_t v___x_292_; 
v___x_291_ = 32;
v___x_292_ = lean_uint32_dec_eq(v_c_278_, v___x_291_);
if (v___x_292_ == 0)
{
uint32_t v___x_293_; uint8_t v___x_294_; 
v___x_293_ = 33;
v___x_294_ = lean_uint32_dec_le(v___x_293_, v_c_278_);
if (v___x_294_ == 0)
{
goto v___jp_284_;
}
else
{
uint32_t v___x_295_; uint8_t v___x_296_; 
v___x_295_ = 39;
v___x_296_ = lean_uint32_dec_le(v_c_278_, v___x_295_);
if (v___x_296_ == 0)
{
goto v___jp_284_;
}
else
{
return v___x_296_;
}
}
}
else
{
return v___x_292_;
}
}
else
{
return v___x_290_;
}
v___jp_279_:
{
uint32_t v___x_280_; uint8_t v___x_281_; 
v___x_280_ = 93;
v___x_281_ = lean_uint32_dec_le(v___x_280_, v_c_278_);
if (v___x_281_ == 0)
{
return v___x_281_;
}
else
{
uint32_t v___x_282_; uint8_t v___x_283_; 
v___x_282_ = 126;
v___x_283_ = lean_uint32_dec_le(v_c_278_, v___x_282_);
return v___x_283_;
}
}
v___jp_284_:
{
uint32_t v___x_285_; uint8_t v___x_286_; 
v___x_285_ = 42;
v___x_286_ = lean_uint32_dec_le(v___x_285_, v_c_278_);
if (v___x_286_ == 0)
{
goto v___jp_279_;
}
else
{
uint32_t v___x_287_; uint8_t v___x_288_; 
v___x_287_ = 91;
v___x_288_ = lean_uint32_dec_le(v_c_278_, v___x_287_);
if (v___x_288_ == 0)
{
goto v___jp_279_;
}
else
{
return v___x_288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ctext___boxed(lean_object* v_c_297_){
_start:
{
uint32_t v_c_boxed_298_; uint8_t v_res_299_; lean_object* v_r_300_; 
v_c_boxed_298_ = lean_unbox_uint32(v_c_297_);
lean_dec(v_c_297_);
v_res_299_ = l_Std_Http_Internal_Char_ctext(v_c_boxed_298_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_etagc(uint32_t v_c_301_){
_start:
{
uint32_t v___x_302_; uint8_t v___x_303_; 
v___x_302_ = 33;
v___x_303_ = lean_uint32_dec_eq(v_c_301_, v___x_302_);
if (v___x_303_ == 0)
{
uint32_t v___x_304_; uint8_t v___x_305_; 
v___x_304_ = 35;
v___x_305_ = lean_uint32_dec_le(v___x_304_, v_c_301_);
if (v___x_305_ == 0)
{
return v___x_305_;
}
else
{
uint32_t v___x_306_; uint8_t v___x_307_; 
v___x_306_ = 126;
v___x_307_ = lean_uint32_dec_le(v_c_301_, v___x_306_);
return v___x_307_;
}
}
else
{
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_etagc___boxed(lean_object* v_c_308_){
_start:
{
uint32_t v_c_boxed_309_; uint8_t v_res_310_; lean_object* v_r_311_; 
v_c_boxed_309_ = lean_unbox_uint32(v_c_308_);
lean_dec(v_c_308_);
v_res_310_ = l_Std_Http_Internal_Char_etagc(v_c_boxed_309_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_ows(uint32_t v_c_312_){
_start:
{
uint32_t v___x_313_; uint8_t v___x_314_; 
v___x_313_ = 32;
v___x_314_ = lean_uint32_dec_eq(v_c_312_, v___x_313_);
if (v___x_314_ == 0)
{
uint32_t v___x_315_; uint8_t v___x_316_; 
v___x_315_ = 9;
v___x_316_ = lean_uint32_dec_eq(v_c_312_, v___x_315_);
return v___x_316_;
}
else
{
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ows___boxed(lean_object* v_c_317_){
_start:
{
uint32_t v_c_boxed_318_; uint8_t v_res_319_; lean_object* v_r_320_; 
v_c_boxed_318_ = lean_unbox_uint32(v_c_317_);
lean_dec(v_c_317_);
v_res_319_ = l_Std_Http_Internal_Char_ows(v_c_boxed_318_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_bws(uint32_t v_c_321_){
_start:
{
uint32_t v___x_322_; uint8_t v___x_323_; 
v___x_322_ = 32;
v___x_323_ = lean_uint32_dec_eq(v_c_321_, v___x_322_);
if (v___x_323_ == 0)
{
uint32_t v___x_324_; uint8_t v___x_325_; 
v___x_324_ = 9;
v___x_325_ = lean_uint32_dec_eq(v_c_321_, v___x_324_);
return v___x_325_;
}
else
{
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_bws___boxed(lean_object* v_c_326_){
_start:
{
uint32_t v_c_boxed_327_; uint8_t v_res_328_; lean_object* v_r_329_; 
v_c_boxed_327_ = lean_unbox_uint32(v_c_326_);
lean_dec(v_c_326_);
v_res_328_ = l_Std_Http_Internal_Char_bws(v_c_boxed_327_);
v_r_329_ = lean_box(v_res_328_);
return v_r_329_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_rws(uint32_t v_c_330_){
_start:
{
uint32_t v___x_331_; uint8_t v___x_332_; 
v___x_331_ = 32;
v___x_332_ = lean_uint32_dec_eq(v_c_330_, v___x_331_);
if (v___x_332_ == 0)
{
uint32_t v___x_333_; uint8_t v___x_334_; 
v___x_333_ = 9;
v___x_334_ = lean_uint32_dec_eq(v_c_330_, v___x_333_);
return v___x_334_;
}
else
{
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_rws___boxed(lean_object* v_c_335_){
_start:
{
uint32_t v_c_boxed_336_; uint8_t v_res_337_; lean_object* v_r_338_; 
v_c_boxed_336_ = lean_unbox_uint32(v_c_335_);
lean_dec(v_c_335_);
v_res_337_ = l_Std_Http_Internal_Char_rws(v_c_boxed_336_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_obsText(uint32_t v_c_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_340_ = lean_unsigned_to_nat(128u);
v___x_341_ = lean_uint32_to_nat(v_c_339_);
v___x_342_ = lean_nat_dec_le(v___x_340_, v___x_341_);
lean_dec(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_obsText___boxed(lean_object* v_c_343_){
_start:
{
uint32_t v_c_boxed_344_; uint8_t v_res_345_; lean_object* v_r_346_; 
v_c_boxed_344_ = lean_unbox_uint32(v_c_343_);
lean_dec(v_c_343_);
v_res_345_ = l_Std_Http_Internal_Char_obsText(v_c_boxed_344_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_reasonPhraseChar(uint32_t v_c_347_){
_start:
{
uint32_t v___x_348_; uint8_t v___x_349_; 
v___x_348_ = 9;
v___x_349_ = lean_uint32_dec_eq(v_c_347_, v___x_348_);
if (v___x_349_ == 0)
{
uint32_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = 32;
v___x_351_ = lean_uint32_dec_eq(v_c_347_, v___x_350_);
if (v___x_351_ == 0)
{
uint32_t v___x_352_; uint8_t v___x_353_; 
v___x_352_ = 33;
v___x_353_ = lean_uint32_dec_le(v___x_352_, v_c_347_);
if (v___x_353_ == 0)
{
return v___x_353_;
}
else
{
uint32_t v___x_354_; uint8_t v___x_355_; 
v___x_354_ = 126;
v___x_355_ = lean_uint32_dec_le(v_c_347_, v___x_354_);
return v___x_355_;
}
}
else
{
return v___x_351_;
}
}
else
{
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_reasonPhraseChar___boxed(lean_object* v_c_356_){
_start:
{
uint32_t v_c_boxed_357_; uint8_t v_res_358_; lean_object* v_r_359_; 
v_c_boxed_357_ = lean_unbox_uint32(v_c_356_);
lean_dec(v_c_356_);
v_res_358_ = l_Std_Http_Internal_Char_reasonPhraseChar(v_c_boxed_357_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isHexDigit(uint32_t v_c_360_){
_start:
{
uint32_t v___x_361_; uint8_t v___x_362_; 
v___x_361_ = 97;
v___x_362_ = lean_uint32_dec_eq(v_c_360_, v___x_361_);
if (v___x_362_ == 0)
{
uint32_t v___x_363_; uint8_t v___x_364_; 
v___x_363_ = 98;
v___x_364_ = lean_uint32_dec_eq(v_c_360_, v___x_363_);
if (v___x_364_ == 0)
{
uint32_t v___x_365_; uint8_t v___x_366_; 
v___x_365_ = 99;
v___x_366_ = lean_uint32_dec_eq(v_c_360_, v___x_365_);
if (v___x_366_ == 0)
{
uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = 100;
v___x_368_ = lean_uint32_dec_eq(v_c_360_, v___x_367_);
if (v___x_368_ == 0)
{
uint32_t v___x_369_; uint8_t v___x_370_; 
v___x_369_ = 101;
v___x_370_ = lean_uint32_dec_eq(v_c_360_, v___x_369_);
if (v___x_370_ == 0)
{
uint32_t v___x_371_; uint8_t v___x_372_; 
v___x_371_ = 102;
v___x_372_ = lean_uint32_dec_eq(v_c_360_, v___x_371_);
if (v___x_372_ == 0)
{
uint32_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 65;
v___x_374_ = lean_uint32_dec_eq(v_c_360_, v___x_373_);
if (v___x_374_ == 0)
{
uint32_t v___x_375_; uint8_t v___x_376_; 
v___x_375_ = 66;
v___x_376_ = lean_uint32_dec_eq(v_c_360_, v___x_375_);
if (v___x_376_ == 0)
{
uint32_t v___x_377_; uint8_t v___x_378_; 
v___x_377_ = 67;
v___x_378_ = lean_uint32_dec_eq(v_c_360_, v___x_377_);
if (v___x_378_ == 0)
{
uint32_t v___x_379_; uint8_t v___x_380_; 
v___x_379_ = 68;
v___x_380_ = lean_uint32_dec_eq(v_c_360_, v___x_379_);
if (v___x_380_ == 0)
{
uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = 69;
v___x_382_ = lean_uint32_dec_eq(v_c_360_, v___x_381_);
if (v___x_382_ == 0)
{
uint32_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = 70;
v___x_384_ = lean_uint32_dec_eq(v_c_360_, v___x_383_);
if (v___x_384_ == 0)
{
uint32_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 48;
v___x_386_ = lean_uint32_dec_le(v___x_385_, v_c_360_);
if (v___x_386_ == 0)
{
return v___x_386_;
}
else
{
uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 57;
v___x_388_ = lean_uint32_dec_le(v_c_360_, v___x_387_);
return v___x_388_;
}
}
else
{
return v___x_384_;
}
}
else
{
return v___x_382_;
}
}
else
{
return v___x_380_;
}
}
else
{
return v___x_378_;
}
}
else
{
return v___x_376_;
}
}
else
{
return v___x_374_;
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
else
{
return v___x_368_;
}
}
else
{
return v___x_366_;
}
}
else
{
return v___x_364_;
}
}
else
{
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigit___boxed(lean_object* v_c_389_){
_start:
{
uint32_t v_c_boxed_390_; uint8_t v_res_391_; lean_object* v_r_392_; 
v_c_boxed_390_ = lean_unbox_uint32(v_c_389_);
lean_dec(v_c_389_);
v_res_391_ = l_Std_Http_Internal_Char_isHexDigit(v_c_boxed_390_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isHexDigitByte(uint8_t v_c_393_){
_start:
{
uint8_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = 48;
v___x_405_ = lean_uint8_dec_le(v___x_404_, v_c_393_);
if (v___x_405_ == 0)
{
goto v___jp_399_;
}
else
{
uint8_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = 57;
v___x_407_ = lean_uint8_dec_le(v_c_393_, v___x_406_);
if (v___x_407_ == 0)
{
goto v___jp_399_;
}
else
{
return v___x_407_;
}
}
v___jp_394_:
{
uint8_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = 65;
v___x_396_ = lean_uint8_dec_le(v___x_395_, v_c_393_);
if (v___x_396_ == 0)
{
return v___x_396_;
}
else
{
uint8_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 70;
v___x_398_ = lean_uint8_dec_le(v_c_393_, v___x_397_);
return v___x_398_;
}
}
v___jp_399_:
{
uint8_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 97;
v___x_401_ = lean_uint8_dec_le(v___x_400_, v_c_393_);
if (v___x_401_ == 0)
{
goto v___jp_394_;
}
else
{
uint8_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 102;
v___x_403_ = lean_uint8_dec_le(v_c_393_, v___x_402_);
if (v___x_403_ == 0)
{
goto v___jp_394_;
}
else
{
return v___x_403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigitByte___boxed(lean_object* v_c_408_){
_start:
{
uint8_t v_c_boxed_409_; uint8_t v_res_410_; lean_object* v_r_411_; 
v_c_boxed_409_ = lean_unbox(v_c_408_);
v_res_410_ = l_Std_Http_Internal_Char_isHexDigitByte(v_c_boxed_409_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAlphaNum(uint8_t v_c_412_){
_start:
{
uint8_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 48;
v___x_424_ = lean_uint8_dec_le(v___x_423_, v_c_412_);
if (v___x_424_ == 0)
{
goto v___jp_418_;
}
else
{
uint8_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 57;
v___x_426_ = lean_uint8_dec_le(v_c_412_, v___x_425_);
if (v___x_426_ == 0)
{
goto v___jp_418_;
}
else
{
return v___x_426_;
}
}
v___jp_413_:
{
uint8_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = 65;
v___x_415_ = lean_uint8_dec_le(v___x_414_, v_c_412_);
if (v___x_415_ == 0)
{
return v___x_415_;
}
else
{
uint8_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = 90;
v___x_417_ = lean_uint8_dec_le(v_c_412_, v___x_416_);
return v___x_417_;
}
}
v___jp_418_:
{
uint8_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 97;
v___x_420_ = lean_uint8_dec_le(v___x_419_, v_c_412_);
if (v___x_420_ == 0)
{
goto v___jp_413_;
}
else
{
uint8_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 122;
v___x_422_ = lean_uint8_dec_le(v_c_412_, v___x_421_);
if (v___x_422_ == 0)
{
goto v___jp_413_;
}
else
{
return v___x_422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAlphaNum___boxed(lean_object* v_c_427_){
_start:
{
uint8_t v_c_boxed_428_; uint8_t v_res_429_; lean_object* v_r_430_; 
v_c_boxed_428_ = lean_unbox(v_c_427_);
v_res_429_ = l_Std_Http_Internal_Char_isAlphaNum(v_c_boxed_428_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAsciiAlphaNumChar(uint32_t v_c_431_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_442_ = lean_uint32_to_nat(v_c_431_);
v___x_443_ = lean_unsigned_to_nat(128u);
v___x_444_ = lean_nat_dec_lt(v___x_442_, v___x_443_);
lean_dec(v___x_442_);
if (v___x_444_ == 0)
{
return v___x_444_;
}
else
{
uint32_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = 48;
v___x_446_ = lean_uint32_dec_le(v___x_445_, v_c_431_);
if (v___x_446_ == 0)
{
goto v___jp_437_;
}
else
{
uint32_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = 57;
v___x_448_ = lean_uint32_dec_le(v_c_431_, v___x_447_);
if (v___x_448_ == 0)
{
goto v___jp_437_;
}
else
{
return v___x_448_;
}
}
}
v___jp_432_:
{
uint32_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = 97;
v___x_434_ = lean_uint32_dec_le(v___x_433_, v_c_431_);
if (v___x_434_ == 0)
{
return v___x_434_;
}
else
{
uint32_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = 122;
v___x_436_ = lean_uint32_dec_le(v_c_431_, v___x_435_);
return v___x_436_;
}
}
v___jp_437_:
{
uint32_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = 65;
v___x_439_ = lean_uint32_dec_le(v___x_438_, v_c_431_);
if (v___x_439_ == 0)
{
goto v___jp_432_;
}
else
{
uint32_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = 90;
v___x_441_ = lean_uint32_dec_le(v_c_431_, v___x_440_);
if (v___x_441_ == 0)
{
goto v___jp_432_;
}
else
{
return v___x_441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAsciiAlphaNumChar___boxed(lean_object* v_c_449_){
_start:
{
uint32_t v_c_boxed_450_; uint8_t v_res_451_; lean_object* v_r_452_; 
v_c_boxed_450_ = lean_unbox_uint32(v_c_449_);
lean_dec(v_c_449_);
v_res_451_ = l_Std_Http_Internal_Char_isAsciiAlphaNumChar(v_c_boxed_450_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isValidSchemeChar(uint32_t v_c_453_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_471_ = lean_uint32_to_nat(v_c_453_);
v___x_472_ = lean_unsigned_to_nat(128u);
v___x_473_ = lean_nat_dec_lt(v___x_471_, v___x_472_);
lean_dec(v___x_471_);
if (v___x_473_ == 0)
{
goto v___jp_454_;
}
else
{
uint32_t v___x_474_; uint8_t v___x_475_; 
v___x_474_ = 48;
v___x_475_ = lean_uint32_dec_le(v___x_474_, v_c_453_);
if (v___x_475_ == 0)
{
goto v___jp_466_;
}
else
{
uint32_t v___x_476_; uint8_t v___x_477_; 
v___x_476_ = 57;
v___x_477_ = lean_uint32_dec_le(v_c_453_, v___x_476_);
if (v___x_477_ == 0)
{
goto v___jp_466_;
}
else
{
return v___x_477_;
}
}
}
v___jp_454_:
{
uint32_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 43;
v___x_456_ = lean_uint32_dec_eq(v_c_453_, v___x_455_);
if (v___x_456_ == 0)
{
uint32_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = 45;
v___x_458_ = lean_uint32_dec_eq(v_c_453_, v___x_457_);
if (v___x_458_ == 0)
{
uint32_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = 46;
v___x_460_ = lean_uint32_dec_eq(v_c_453_, v___x_459_);
return v___x_460_;
}
else
{
return v___x_458_;
}
}
else
{
return v___x_456_;
}
}
v___jp_461_:
{
uint32_t v___x_462_; uint8_t v___x_463_; 
v___x_462_ = 97;
v___x_463_ = lean_uint32_dec_le(v___x_462_, v_c_453_);
if (v___x_463_ == 0)
{
goto v___jp_454_;
}
else
{
uint32_t v___x_464_; uint8_t v___x_465_; 
v___x_464_ = 122;
v___x_465_ = lean_uint32_dec_le(v_c_453_, v___x_464_);
if (v___x_465_ == 0)
{
goto v___jp_454_;
}
else
{
return v___x_465_;
}
}
}
v___jp_466_:
{
uint32_t v___x_467_; uint8_t v___x_468_; 
v___x_467_ = 65;
v___x_468_ = lean_uint32_dec_le(v___x_467_, v_c_453_);
if (v___x_468_ == 0)
{
goto v___jp_461_;
}
else
{
uint32_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = 90;
v___x_470_ = lean_uint32_dec_le(v_c_453_, v___x_469_);
if (v___x_470_ == 0)
{
goto v___jp_461_;
}
else
{
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidSchemeChar___boxed(lean_object* v_c_478_){
_start:
{
uint32_t v_c_boxed_479_; uint8_t v_res_480_; lean_object* v_r_481_; 
v_c_boxed_479_ = lean_unbox_uint32(v_c_478_);
lean_dec(v_c_478_);
v_res_480_ = l_Std_Http_Internal_Char_isValidSchemeChar(v_c_boxed_479_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isValidDomainNameChar(uint32_t v_c_482_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_498_ = lean_uint32_to_nat(v_c_482_);
v___x_499_ = lean_unsigned_to_nat(128u);
v___x_500_ = lean_nat_dec_lt(v___x_498_, v___x_499_);
lean_dec(v___x_498_);
if (v___x_500_ == 0)
{
goto v___jp_483_;
}
else
{
uint32_t v___x_501_; uint8_t v___x_502_; 
v___x_501_ = 48;
v___x_502_ = lean_uint32_dec_le(v___x_501_, v_c_482_);
if (v___x_502_ == 0)
{
goto v___jp_493_;
}
else
{
uint32_t v___x_503_; uint8_t v___x_504_; 
v___x_503_ = 57;
v___x_504_ = lean_uint32_dec_le(v_c_482_, v___x_503_);
if (v___x_504_ == 0)
{
goto v___jp_493_;
}
else
{
return v___x_504_;
}
}
}
v___jp_483_:
{
uint32_t v___x_484_; uint8_t v___x_485_; 
v___x_484_ = 45;
v___x_485_ = lean_uint32_dec_eq(v_c_482_, v___x_484_);
if (v___x_485_ == 0)
{
uint32_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = 46;
v___x_487_ = lean_uint32_dec_eq(v_c_482_, v___x_486_);
return v___x_487_;
}
else
{
return v___x_485_;
}
}
v___jp_488_:
{
uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_489_ = 97;
v___x_490_ = lean_uint32_dec_le(v___x_489_, v_c_482_);
if (v___x_490_ == 0)
{
goto v___jp_483_;
}
else
{
uint32_t v___x_491_; uint8_t v___x_492_; 
v___x_491_ = 122;
v___x_492_ = lean_uint32_dec_le(v_c_482_, v___x_491_);
if (v___x_492_ == 0)
{
goto v___jp_483_;
}
else
{
return v___x_492_;
}
}
}
v___jp_493_:
{
uint32_t v___x_494_; uint8_t v___x_495_; 
v___x_494_ = 65;
v___x_495_ = lean_uint32_dec_le(v___x_494_, v_c_482_);
if (v___x_495_ == 0)
{
goto v___jp_488_;
}
else
{
uint32_t v___x_496_; uint8_t v___x_497_; 
v___x_496_ = 90;
v___x_497_ = lean_uint32_dec_le(v_c_482_, v___x_496_);
if (v___x_497_ == 0)
{
goto v___jp_488_;
}
else
{
return v___x_497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidDomainNameChar___boxed(lean_object* v_c_505_){
_start:
{
uint32_t v_c_boxed_506_; uint8_t v_res_507_; lean_object* v_r_508_; 
v_c_boxed_506_ = lean_unbox_uint32(v_c_505_);
lean_dec(v_c_505_);
v_res_507_ = l_Std_Http_Internal_Char_isValidDomainNameChar(v_c_boxed_506_);
v_r_508_ = lean_box(v_res_507_);
return v_r_508_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUnreserved(uint8_t v_c_509_){
_start:
{
uint8_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = 48;
v___x_530_ = lean_uint8_dec_le(v___x_529_, v_c_509_);
if (v___x_530_ == 0)
{
goto v___jp_524_;
}
else
{
uint8_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 57;
v___x_532_ = lean_uint8_dec_le(v_c_509_, v___x_531_);
if (v___x_532_ == 0)
{
goto v___jp_524_;
}
else
{
return v___x_532_;
}
}
v___jp_510_:
{
uint8_t v___x_511_; uint8_t v___x_512_; 
v___x_511_ = 45;
v___x_512_ = lean_uint8_dec_eq(v_c_509_, v___x_511_);
if (v___x_512_ == 0)
{
uint8_t v___x_513_; uint8_t v___x_514_; 
v___x_513_ = 46;
v___x_514_ = lean_uint8_dec_eq(v_c_509_, v___x_513_);
if (v___x_514_ == 0)
{
uint8_t v___x_515_; uint8_t v___x_516_; 
v___x_515_ = 95;
v___x_516_ = lean_uint8_dec_eq(v_c_509_, v___x_515_);
if (v___x_516_ == 0)
{
uint8_t v___x_517_; uint8_t v___x_518_; 
v___x_517_ = 126;
v___x_518_ = lean_uint8_dec_eq(v_c_509_, v___x_517_);
return v___x_518_;
}
else
{
return v___x_516_;
}
}
else
{
return v___x_514_;
}
}
else
{
return v___x_512_;
}
}
v___jp_519_:
{
uint8_t v___x_520_; uint8_t v___x_521_; 
v___x_520_ = 65;
v___x_521_ = lean_uint8_dec_le(v___x_520_, v_c_509_);
if (v___x_521_ == 0)
{
goto v___jp_510_;
}
else
{
uint8_t v___x_522_; uint8_t v___x_523_; 
v___x_522_ = 90;
v___x_523_ = lean_uint8_dec_le(v_c_509_, v___x_522_);
if (v___x_523_ == 0)
{
goto v___jp_510_;
}
else
{
return v___x_523_;
}
}
}
v___jp_524_:
{
uint8_t v___x_525_; uint8_t v___x_526_; 
v___x_525_ = 97;
v___x_526_ = lean_uint8_dec_le(v___x_525_, v_c_509_);
if (v___x_526_ == 0)
{
goto v___jp_519_;
}
else
{
uint8_t v___x_527_; uint8_t v___x_528_; 
v___x_527_ = 122;
v___x_528_ = lean_uint8_dec_le(v_c_509_, v___x_527_);
if (v___x_528_ == 0)
{
goto v___jp_519_;
}
else
{
return v___x_528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUnreserved___boxed(lean_object* v_c_533_){
_start:
{
uint8_t v_c_boxed_534_; uint8_t v_res_535_; lean_object* v_r_536_; 
v_c_boxed_534_ = lean_unbox(v_c_533_);
v_res_535_ = l_Std_Http_Internal_Char_isUnreserved(v_c_boxed_534_);
v_r_536_ = lean_box(v_res_535_);
return v_r_536_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isSubDelims(uint8_t v_c_537_){
_start:
{
uint8_t v___x_538_; uint8_t v___x_539_; 
v___x_538_ = 33;
v___x_539_ = lean_uint8_dec_eq(v_c_537_, v___x_538_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; uint8_t v___x_541_; 
v___x_540_ = 36;
v___x_541_ = lean_uint8_dec_eq(v_c_537_, v___x_540_);
if (v___x_541_ == 0)
{
uint8_t v___x_542_; uint8_t v___x_543_; 
v___x_542_ = 38;
v___x_543_ = lean_uint8_dec_eq(v_c_537_, v___x_542_);
if (v___x_543_ == 0)
{
uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = 39;
v___x_545_ = lean_uint8_dec_eq(v_c_537_, v___x_544_);
if (v___x_545_ == 0)
{
uint8_t v___x_546_; uint8_t v___x_547_; 
v___x_546_ = 40;
v___x_547_ = lean_uint8_dec_eq(v_c_537_, v___x_546_);
if (v___x_547_ == 0)
{
uint8_t v___x_548_; uint8_t v___x_549_; 
v___x_548_ = 41;
v___x_549_ = lean_uint8_dec_eq(v_c_537_, v___x_548_);
if (v___x_549_ == 0)
{
uint8_t v___x_550_; uint8_t v___x_551_; 
v___x_550_ = 42;
v___x_551_ = lean_uint8_dec_eq(v_c_537_, v___x_550_);
if (v___x_551_ == 0)
{
uint8_t v___x_552_; uint8_t v___x_553_; 
v___x_552_ = 43;
v___x_553_ = lean_uint8_dec_eq(v_c_537_, v___x_552_);
if (v___x_553_ == 0)
{
uint8_t v___x_554_; uint8_t v___x_555_; 
v___x_554_ = 44;
v___x_555_ = lean_uint8_dec_eq(v_c_537_, v___x_554_);
if (v___x_555_ == 0)
{
uint8_t v___x_556_; uint8_t v___x_557_; 
v___x_556_ = 59;
v___x_557_ = lean_uint8_dec_eq(v_c_537_, v___x_556_);
if (v___x_557_ == 0)
{
uint8_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = 61;
v___x_559_ = lean_uint8_dec_eq(v_c_537_, v___x_558_);
return v___x_559_;
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
else
{
return v___x_541_;
}
}
else
{
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isSubDelims___boxed(lean_object* v_c_560_){
_start:
{
uint8_t v_c_boxed_561_; uint8_t v_res_562_; lean_object* v_r_563_; 
v_c_boxed_561_ = lean_unbox(v_c_560_);
v_res_562_ = l_Std_Http_Internal_Char_isSubDelims(v_c_boxed_561_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isPChar(uint8_t v_c_564_){
_start:
{
uint8_t v___x_610_; uint8_t v___x_611_; 
v___x_610_ = 48;
v___x_611_ = lean_uint8_dec_le(v___x_610_, v_c_564_);
if (v___x_611_ == 0)
{
goto v___jp_605_;
}
else
{
uint8_t v___x_612_; uint8_t v___x_613_; 
v___x_612_ = 57;
v___x_613_ = lean_uint8_dec_le(v_c_564_, v___x_612_);
if (v___x_613_ == 0)
{
goto v___jp_605_;
}
else
{
return v___x_613_;
}
}
v___jp_565_:
{
uint8_t v___x_566_; uint8_t v___x_567_; 
v___x_566_ = 45;
v___x_567_ = lean_uint8_dec_eq(v_c_564_, v___x_566_);
if (v___x_567_ == 0)
{
uint8_t v___x_568_; uint8_t v___x_569_; 
v___x_568_ = 46;
v___x_569_ = lean_uint8_dec_eq(v_c_564_, v___x_568_);
if (v___x_569_ == 0)
{
uint8_t v___x_570_; uint8_t v___x_571_; 
v___x_570_ = 95;
v___x_571_ = lean_uint8_dec_eq(v_c_564_, v___x_570_);
if (v___x_571_ == 0)
{
uint8_t v___x_572_; uint8_t v___x_573_; 
v___x_572_ = 126;
v___x_573_ = lean_uint8_dec_eq(v_c_564_, v___x_572_);
if (v___x_573_ == 0)
{
uint8_t v___x_574_; uint8_t v___x_575_; 
v___x_574_ = 33;
v___x_575_ = lean_uint8_dec_eq(v_c_564_, v___x_574_);
if (v___x_575_ == 0)
{
uint8_t v___x_576_; uint8_t v___x_577_; 
v___x_576_ = 36;
v___x_577_ = lean_uint8_dec_eq(v_c_564_, v___x_576_);
if (v___x_577_ == 0)
{
uint8_t v___x_578_; uint8_t v___x_579_; 
v___x_578_ = 38;
v___x_579_ = lean_uint8_dec_eq(v_c_564_, v___x_578_);
if (v___x_579_ == 0)
{
uint8_t v___x_580_; uint8_t v___x_581_; 
v___x_580_ = 39;
v___x_581_ = lean_uint8_dec_eq(v_c_564_, v___x_580_);
if (v___x_581_ == 0)
{
uint8_t v___x_582_; uint8_t v___x_583_; 
v___x_582_ = 40;
v___x_583_ = lean_uint8_dec_eq(v_c_564_, v___x_582_);
if (v___x_583_ == 0)
{
uint8_t v___x_584_; uint8_t v___x_585_; 
v___x_584_ = 41;
v___x_585_ = lean_uint8_dec_eq(v_c_564_, v___x_584_);
if (v___x_585_ == 0)
{
uint8_t v___x_586_; uint8_t v___x_587_; 
v___x_586_ = 42;
v___x_587_ = lean_uint8_dec_eq(v_c_564_, v___x_586_);
if (v___x_587_ == 0)
{
uint8_t v___x_588_; uint8_t v___x_589_; 
v___x_588_ = 43;
v___x_589_ = lean_uint8_dec_eq(v_c_564_, v___x_588_);
if (v___x_589_ == 0)
{
uint8_t v___x_590_; uint8_t v___x_591_; 
v___x_590_ = 44;
v___x_591_ = lean_uint8_dec_eq(v_c_564_, v___x_590_);
if (v___x_591_ == 0)
{
uint8_t v___x_592_; uint8_t v___x_593_; 
v___x_592_ = 59;
v___x_593_ = lean_uint8_dec_eq(v_c_564_, v___x_592_);
if (v___x_593_ == 0)
{
uint8_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = 61;
v___x_595_ = lean_uint8_dec_eq(v_c_564_, v___x_594_);
if (v___x_595_ == 0)
{
uint8_t v___x_596_; uint8_t v___x_597_; 
v___x_596_ = 58;
v___x_597_ = lean_uint8_dec_eq(v_c_564_, v___x_596_);
if (v___x_597_ == 0)
{
uint8_t v___x_598_; uint8_t v___x_599_; 
v___x_598_ = 64;
v___x_599_ = lean_uint8_dec_eq(v_c_564_, v___x_598_);
return v___x_599_;
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
else
{
return v___x_569_;
}
}
else
{
return v___x_567_;
}
}
v___jp_600_:
{
uint8_t v___x_601_; uint8_t v___x_602_; 
v___x_601_ = 65;
v___x_602_ = lean_uint8_dec_le(v___x_601_, v_c_564_);
if (v___x_602_ == 0)
{
goto v___jp_565_;
}
else
{
uint8_t v___x_603_; uint8_t v___x_604_; 
v___x_603_ = 90;
v___x_604_ = lean_uint8_dec_le(v_c_564_, v___x_603_);
if (v___x_604_ == 0)
{
goto v___jp_565_;
}
else
{
return v___x_604_;
}
}
}
v___jp_605_:
{
uint8_t v___x_606_; uint8_t v___x_607_; 
v___x_606_ = 97;
v___x_607_ = lean_uint8_dec_le(v___x_606_, v_c_564_);
if (v___x_607_ == 0)
{
goto v___jp_600_;
}
else
{
uint8_t v___x_608_; uint8_t v___x_609_; 
v___x_608_ = 122;
v___x_609_ = lean_uint8_dec_le(v_c_564_, v___x_608_);
if (v___x_609_ == 0)
{
goto v___jp_600_;
}
else
{
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isPChar___boxed(lean_object* v_c_614_){
_start:
{
uint8_t v_c_boxed_615_; uint8_t v_res_616_; lean_object* v_r_617_; 
v_c_boxed_615_ = lean_unbox(v_c_614_);
v_res_616_ = l_Std_Http_Internal_Char_isPChar(v_c_boxed_615_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryChar(uint8_t v_c_618_){
_start:
{
uint8_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = 48;
v___x_669_ = lean_uint8_dec_le(v___x_668_, v_c_618_);
if (v___x_669_ == 0)
{
goto v___jp_663_;
}
else
{
uint8_t v___x_670_; uint8_t v___x_671_; 
v___x_670_ = 57;
v___x_671_ = lean_uint8_dec_le(v_c_618_, v___x_670_);
if (v___x_671_ == 0)
{
goto v___jp_663_;
}
else
{
return v___x_671_;
}
}
v___jp_619_:
{
uint8_t v___x_620_; uint8_t v___x_621_; 
v___x_620_ = 45;
v___x_621_ = lean_uint8_dec_eq(v_c_618_, v___x_620_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; uint8_t v___x_623_; 
v___x_622_ = 46;
v___x_623_ = lean_uint8_dec_eq(v_c_618_, v___x_622_);
if (v___x_623_ == 0)
{
uint8_t v___x_624_; uint8_t v___x_625_; 
v___x_624_ = 95;
v___x_625_ = lean_uint8_dec_eq(v_c_618_, v___x_624_);
if (v___x_625_ == 0)
{
uint8_t v___x_626_; uint8_t v___x_627_; 
v___x_626_ = 126;
v___x_627_ = lean_uint8_dec_eq(v_c_618_, v___x_626_);
if (v___x_627_ == 0)
{
uint8_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = 33;
v___x_629_ = lean_uint8_dec_eq(v_c_618_, v___x_628_);
if (v___x_629_ == 0)
{
uint8_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = 36;
v___x_631_ = lean_uint8_dec_eq(v_c_618_, v___x_630_);
if (v___x_631_ == 0)
{
uint8_t v___x_632_; uint8_t v___x_633_; 
v___x_632_ = 38;
v___x_633_ = lean_uint8_dec_eq(v_c_618_, v___x_632_);
if (v___x_633_ == 0)
{
uint8_t v___x_634_; uint8_t v___x_635_; 
v___x_634_ = 39;
v___x_635_ = lean_uint8_dec_eq(v_c_618_, v___x_634_);
if (v___x_635_ == 0)
{
uint8_t v___x_636_; uint8_t v___x_637_; 
v___x_636_ = 40;
v___x_637_ = lean_uint8_dec_eq(v_c_618_, v___x_636_);
if (v___x_637_ == 0)
{
uint8_t v___x_638_; uint8_t v___x_639_; 
v___x_638_ = 41;
v___x_639_ = lean_uint8_dec_eq(v_c_618_, v___x_638_);
if (v___x_639_ == 0)
{
uint8_t v___x_640_; uint8_t v___x_641_; 
v___x_640_ = 42;
v___x_641_ = lean_uint8_dec_eq(v_c_618_, v___x_640_);
if (v___x_641_ == 0)
{
uint8_t v___x_642_; uint8_t v___x_643_; 
v___x_642_ = 43;
v___x_643_ = lean_uint8_dec_eq(v_c_618_, v___x_642_);
if (v___x_643_ == 0)
{
uint8_t v___x_644_; uint8_t v___x_645_; 
v___x_644_ = 44;
v___x_645_ = lean_uint8_dec_eq(v_c_618_, v___x_644_);
if (v___x_645_ == 0)
{
uint8_t v___x_646_; uint8_t v___x_647_; 
v___x_646_ = 59;
v___x_647_ = lean_uint8_dec_eq(v_c_618_, v___x_646_);
if (v___x_647_ == 0)
{
uint8_t v___x_648_; uint8_t v___x_649_; 
v___x_648_ = 61;
v___x_649_ = lean_uint8_dec_eq(v_c_618_, v___x_648_);
if (v___x_649_ == 0)
{
uint8_t v___x_650_; uint8_t v___x_651_; 
v___x_650_ = 58;
v___x_651_ = lean_uint8_dec_eq(v_c_618_, v___x_650_);
if (v___x_651_ == 0)
{
uint8_t v___x_652_; uint8_t v___x_653_; 
v___x_652_ = 64;
v___x_653_ = lean_uint8_dec_eq(v_c_618_, v___x_652_);
if (v___x_653_ == 0)
{
uint8_t v___x_654_; uint8_t v___x_655_; 
v___x_654_ = 47;
v___x_655_ = lean_uint8_dec_eq(v_c_618_, v___x_654_);
if (v___x_655_ == 0)
{
uint8_t v___x_656_; uint8_t v___x_657_; 
v___x_656_ = 63;
v___x_657_ = lean_uint8_dec_eq(v_c_618_, v___x_656_);
return v___x_657_;
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
v___jp_658_:
{
uint8_t v___x_659_; uint8_t v___x_660_; 
v___x_659_ = 65;
v___x_660_ = lean_uint8_dec_le(v___x_659_, v_c_618_);
if (v___x_660_ == 0)
{
goto v___jp_619_;
}
else
{
uint8_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = 90;
v___x_662_ = lean_uint8_dec_le(v_c_618_, v___x_661_);
if (v___x_662_ == 0)
{
goto v___jp_619_;
}
else
{
return v___x_662_;
}
}
}
v___jp_663_:
{
uint8_t v___x_664_; uint8_t v___x_665_; 
v___x_664_ = 97;
v___x_665_ = lean_uint8_dec_le(v___x_664_, v_c_618_);
if (v___x_665_ == 0)
{
goto v___jp_658_;
}
else
{
uint8_t v___x_666_; uint8_t v___x_667_; 
v___x_666_ = 122;
v___x_667_ = lean_uint8_dec_le(v_c_618_, v___x_666_);
if (v___x_667_ == 0)
{
goto v___jp_658_;
}
else
{
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryChar___boxed(lean_object* v_c_672_){
_start:
{
uint8_t v_c_boxed_673_; uint8_t v_res_674_; lean_object* v_r_675_; 
v_c_boxed_673_ = lean_unbox(v_c_672_);
v_res_674_ = l_Std_Http_Internal_Char_isQueryChar(v_c_boxed_673_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isFragmentChar(uint8_t v_c_676_){
_start:
{
uint8_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 48;
v___x_727_ = lean_uint8_dec_le(v___x_726_, v_c_676_);
if (v___x_727_ == 0)
{
goto v___jp_721_;
}
else
{
uint8_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 57;
v___x_729_ = lean_uint8_dec_le(v_c_676_, v___x_728_);
if (v___x_729_ == 0)
{
goto v___jp_721_;
}
else
{
return v___x_729_;
}
}
v___jp_677_:
{
uint8_t v___x_678_; uint8_t v___x_679_; 
v___x_678_ = 45;
v___x_679_ = lean_uint8_dec_eq(v_c_676_, v___x_678_);
if (v___x_679_ == 0)
{
uint8_t v___x_680_; uint8_t v___x_681_; 
v___x_680_ = 46;
v___x_681_ = lean_uint8_dec_eq(v_c_676_, v___x_680_);
if (v___x_681_ == 0)
{
uint8_t v___x_682_; uint8_t v___x_683_; 
v___x_682_ = 95;
v___x_683_ = lean_uint8_dec_eq(v_c_676_, v___x_682_);
if (v___x_683_ == 0)
{
uint8_t v___x_684_; uint8_t v___x_685_; 
v___x_684_ = 126;
v___x_685_ = lean_uint8_dec_eq(v_c_676_, v___x_684_);
if (v___x_685_ == 0)
{
uint8_t v___x_686_; uint8_t v___x_687_; 
v___x_686_ = 33;
v___x_687_ = lean_uint8_dec_eq(v_c_676_, v___x_686_);
if (v___x_687_ == 0)
{
uint8_t v___x_688_; uint8_t v___x_689_; 
v___x_688_ = 36;
v___x_689_ = lean_uint8_dec_eq(v_c_676_, v___x_688_);
if (v___x_689_ == 0)
{
uint8_t v___x_690_; uint8_t v___x_691_; 
v___x_690_ = 38;
v___x_691_ = lean_uint8_dec_eq(v_c_676_, v___x_690_);
if (v___x_691_ == 0)
{
uint8_t v___x_692_; uint8_t v___x_693_; 
v___x_692_ = 39;
v___x_693_ = lean_uint8_dec_eq(v_c_676_, v___x_692_);
if (v___x_693_ == 0)
{
uint8_t v___x_694_; uint8_t v___x_695_; 
v___x_694_ = 40;
v___x_695_ = lean_uint8_dec_eq(v_c_676_, v___x_694_);
if (v___x_695_ == 0)
{
uint8_t v___x_696_; uint8_t v___x_697_; 
v___x_696_ = 41;
v___x_697_ = lean_uint8_dec_eq(v_c_676_, v___x_696_);
if (v___x_697_ == 0)
{
uint8_t v___x_698_; uint8_t v___x_699_; 
v___x_698_ = 42;
v___x_699_ = lean_uint8_dec_eq(v_c_676_, v___x_698_);
if (v___x_699_ == 0)
{
uint8_t v___x_700_; uint8_t v___x_701_; 
v___x_700_ = 43;
v___x_701_ = lean_uint8_dec_eq(v_c_676_, v___x_700_);
if (v___x_701_ == 0)
{
uint8_t v___x_702_; uint8_t v___x_703_; 
v___x_702_ = 44;
v___x_703_ = lean_uint8_dec_eq(v_c_676_, v___x_702_);
if (v___x_703_ == 0)
{
uint8_t v___x_704_; uint8_t v___x_705_; 
v___x_704_ = 59;
v___x_705_ = lean_uint8_dec_eq(v_c_676_, v___x_704_);
if (v___x_705_ == 0)
{
uint8_t v___x_706_; uint8_t v___x_707_; 
v___x_706_ = 61;
v___x_707_ = lean_uint8_dec_eq(v_c_676_, v___x_706_);
if (v___x_707_ == 0)
{
uint8_t v___x_708_; uint8_t v___x_709_; 
v___x_708_ = 58;
v___x_709_ = lean_uint8_dec_eq(v_c_676_, v___x_708_);
if (v___x_709_ == 0)
{
uint8_t v___x_710_; uint8_t v___x_711_; 
v___x_710_ = 64;
v___x_711_ = lean_uint8_dec_eq(v_c_676_, v___x_710_);
if (v___x_711_ == 0)
{
uint8_t v___x_712_; uint8_t v___x_713_; 
v___x_712_ = 47;
v___x_713_ = lean_uint8_dec_eq(v_c_676_, v___x_712_);
if (v___x_713_ == 0)
{
uint8_t v___x_714_; uint8_t v___x_715_; 
v___x_714_ = 63;
v___x_715_ = lean_uint8_dec_eq(v_c_676_, v___x_714_);
return v___x_715_;
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
else
{
return v___x_681_;
}
}
else
{
return v___x_679_;
}
}
v___jp_716_:
{
uint8_t v___x_717_; uint8_t v___x_718_; 
v___x_717_ = 65;
v___x_718_ = lean_uint8_dec_le(v___x_717_, v_c_676_);
if (v___x_718_ == 0)
{
goto v___jp_677_;
}
else
{
uint8_t v___x_719_; uint8_t v___x_720_; 
v___x_719_ = 90;
v___x_720_ = lean_uint8_dec_le(v_c_676_, v___x_719_);
if (v___x_720_ == 0)
{
goto v___jp_677_;
}
else
{
return v___x_720_;
}
}
}
v___jp_721_:
{
uint8_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = 97;
v___x_723_ = lean_uint8_dec_le(v___x_722_, v_c_676_);
if (v___x_723_ == 0)
{
goto v___jp_716_;
}
else
{
uint8_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = 122;
v___x_725_ = lean_uint8_dec_le(v_c_676_, v___x_724_);
if (v___x_725_ == 0)
{
goto v___jp_716_;
}
else
{
return v___x_725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isFragmentChar___boxed(lean_object* v_c_730_){
_start:
{
uint8_t v_c_boxed_731_; uint8_t v_res_732_; lean_object* v_r_733_; 
v_c_boxed_731_ = lean_unbox(v_c_730_);
v_res_732_ = l_Std_Http_Internal_Char_isFragmentChar(v_c_boxed_731_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUserInfoChar(uint8_t v_c_734_){
_start:
{
uint8_t v___x_778_; uint8_t v___x_779_; 
v___x_778_ = 48;
v___x_779_ = lean_uint8_dec_le(v___x_778_, v_c_734_);
if (v___x_779_ == 0)
{
goto v___jp_773_;
}
else
{
uint8_t v___x_780_; uint8_t v___x_781_; 
v___x_780_ = 57;
v___x_781_ = lean_uint8_dec_le(v_c_734_, v___x_780_);
if (v___x_781_ == 0)
{
goto v___jp_773_;
}
else
{
return v___x_781_;
}
}
v___jp_735_:
{
uint8_t v___x_736_; uint8_t v___x_737_; 
v___x_736_ = 45;
v___x_737_ = lean_uint8_dec_eq(v_c_734_, v___x_736_);
if (v___x_737_ == 0)
{
uint8_t v___x_738_; uint8_t v___x_739_; 
v___x_738_ = 46;
v___x_739_ = lean_uint8_dec_eq(v_c_734_, v___x_738_);
if (v___x_739_ == 0)
{
uint8_t v___x_740_; uint8_t v___x_741_; 
v___x_740_ = 95;
v___x_741_ = lean_uint8_dec_eq(v_c_734_, v___x_740_);
if (v___x_741_ == 0)
{
uint8_t v___x_742_; uint8_t v___x_743_; 
v___x_742_ = 126;
v___x_743_ = lean_uint8_dec_eq(v_c_734_, v___x_742_);
if (v___x_743_ == 0)
{
uint8_t v___x_744_; uint8_t v___x_745_; 
v___x_744_ = 33;
v___x_745_ = lean_uint8_dec_eq(v_c_734_, v___x_744_);
if (v___x_745_ == 0)
{
uint8_t v___x_746_; uint8_t v___x_747_; 
v___x_746_ = 36;
v___x_747_ = lean_uint8_dec_eq(v_c_734_, v___x_746_);
if (v___x_747_ == 0)
{
uint8_t v___x_748_; uint8_t v___x_749_; 
v___x_748_ = 38;
v___x_749_ = lean_uint8_dec_eq(v_c_734_, v___x_748_);
if (v___x_749_ == 0)
{
uint8_t v___x_750_; uint8_t v___x_751_; 
v___x_750_ = 39;
v___x_751_ = lean_uint8_dec_eq(v_c_734_, v___x_750_);
if (v___x_751_ == 0)
{
uint8_t v___x_752_; uint8_t v___x_753_; 
v___x_752_ = 40;
v___x_753_ = lean_uint8_dec_eq(v_c_734_, v___x_752_);
if (v___x_753_ == 0)
{
uint8_t v___x_754_; uint8_t v___x_755_; 
v___x_754_ = 41;
v___x_755_ = lean_uint8_dec_eq(v_c_734_, v___x_754_);
if (v___x_755_ == 0)
{
uint8_t v___x_756_; uint8_t v___x_757_; 
v___x_756_ = 42;
v___x_757_ = lean_uint8_dec_eq(v_c_734_, v___x_756_);
if (v___x_757_ == 0)
{
uint8_t v___x_758_; uint8_t v___x_759_; 
v___x_758_ = 43;
v___x_759_ = lean_uint8_dec_eq(v_c_734_, v___x_758_);
if (v___x_759_ == 0)
{
uint8_t v___x_760_; uint8_t v___x_761_; 
v___x_760_ = 44;
v___x_761_ = lean_uint8_dec_eq(v_c_734_, v___x_760_);
if (v___x_761_ == 0)
{
uint8_t v___x_762_; uint8_t v___x_763_; 
v___x_762_ = 59;
v___x_763_ = lean_uint8_dec_eq(v_c_734_, v___x_762_);
if (v___x_763_ == 0)
{
uint8_t v___x_764_; uint8_t v___x_765_; 
v___x_764_ = 61;
v___x_765_ = lean_uint8_dec_eq(v_c_734_, v___x_764_);
if (v___x_765_ == 0)
{
uint8_t v___x_766_; uint8_t v___x_767_; 
v___x_766_ = 58;
v___x_767_ = lean_uint8_dec_eq(v_c_734_, v___x_766_);
return v___x_767_;
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
v___jp_768_:
{
uint8_t v___x_769_; uint8_t v___x_770_; 
v___x_769_ = 65;
v___x_770_ = lean_uint8_dec_le(v___x_769_, v_c_734_);
if (v___x_770_ == 0)
{
goto v___jp_735_;
}
else
{
uint8_t v___x_771_; uint8_t v___x_772_; 
v___x_771_ = 90;
v___x_772_ = lean_uint8_dec_le(v_c_734_, v___x_771_);
if (v___x_772_ == 0)
{
goto v___jp_735_;
}
else
{
return v___x_772_;
}
}
}
v___jp_773_:
{
uint8_t v___x_774_; uint8_t v___x_775_; 
v___x_774_ = 97;
v___x_775_ = lean_uint8_dec_le(v___x_774_, v_c_734_);
if (v___x_775_ == 0)
{
goto v___jp_768_;
}
else
{
uint8_t v___x_776_; uint8_t v___x_777_; 
v___x_776_ = 122;
v___x_777_ = lean_uint8_dec_le(v_c_734_, v___x_776_);
if (v___x_777_ == 0)
{
goto v___jp_768_;
}
else
{
return v___x_777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUserInfoChar___boxed(lean_object* v_c_782_){
_start:
{
uint8_t v_c_boxed_783_; uint8_t v_res_784_; lean_object* v_r_785_; 
v_c_boxed_783_ = lean_unbox(v_c_782_);
v_res_784_ = l_Std_Http_Internal_Char_isUserInfoChar(v_c_boxed_783_);
v_r_785_ = lean_box(v_res_784_);
return v_r_785_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryDataChar(uint8_t v_c_786_){
_start:
{
uint8_t v___x_843_; uint8_t v___x_844_; 
v___x_843_ = 48;
v___x_844_ = lean_uint8_dec_le(v___x_843_, v_c_786_);
if (v___x_844_ == 0)
{
goto v___jp_838_;
}
else
{
uint8_t v___x_845_; uint8_t v___x_846_; 
v___x_845_ = 57;
v___x_846_ = lean_uint8_dec_le(v_c_786_, v___x_845_);
if (v___x_846_ == 0)
{
goto v___jp_838_;
}
else
{
goto v___jp_787_;
}
}
v___jp_787_:
{
uint8_t v___x_788_; uint8_t v___x_789_; 
v___x_788_ = 38;
v___x_789_ = lean_uint8_dec_eq(v_c_786_, v___x_788_);
if (v___x_789_ == 0)
{
uint8_t v___x_790_; uint8_t v___x_791_; 
v___x_790_ = 61;
v___x_791_ = lean_uint8_dec_eq(v_c_786_, v___x_790_);
if (v___x_791_ == 0)
{
uint8_t v___x_792_; 
v___x_792_ = 1;
return v___x_792_;
}
else
{
return v___x_789_;
}
}
else
{
uint8_t v___x_793_; 
v___x_793_ = 0;
return v___x_793_;
}
}
v___jp_794_:
{
uint8_t v___x_795_; uint8_t v___x_796_; 
v___x_795_ = 45;
v___x_796_ = lean_uint8_dec_eq(v_c_786_, v___x_795_);
if (v___x_796_ == 0)
{
uint8_t v___x_797_; uint8_t v___x_798_; 
v___x_797_ = 46;
v___x_798_ = lean_uint8_dec_eq(v_c_786_, v___x_797_);
if (v___x_798_ == 0)
{
uint8_t v___x_799_; uint8_t v___x_800_; 
v___x_799_ = 95;
v___x_800_ = lean_uint8_dec_eq(v_c_786_, v___x_799_);
if (v___x_800_ == 0)
{
uint8_t v___x_801_; uint8_t v___x_802_; 
v___x_801_ = 126;
v___x_802_ = lean_uint8_dec_eq(v_c_786_, v___x_801_);
if (v___x_802_ == 0)
{
uint8_t v___x_803_; uint8_t v___x_804_; 
v___x_803_ = 33;
v___x_804_ = lean_uint8_dec_eq(v_c_786_, v___x_803_);
if (v___x_804_ == 0)
{
uint8_t v___x_805_; uint8_t v___x_806_; 
v___x_805_ = 36;
v___x_806_ = lean_uint8_dec_eq(v_c_786_, v___x_805_);
if (v___x_806_ == 0)
{
uint8_t v___x_807_; uint8_t v___x_808_; 
v___x_807_ = 38;
v___x_808_ = lean_uint8_dec_eq(v_c_786_, v___x_807_);
if (v___x_808_ == 0)
{
uint8_t v___x_809_; uint8_t v___x_810_; 
v___x_809_ = 39;
v___x_810_ = lean_uint8_dec_eq(v_c_786_, v___x_809_);
if (v___x_810_ == 0)
{
uint8_t v___x_811_; uint8_t v___x_812_; 
v___x_811_ = 40;
v___x_812_ = lean_uint8_dec_eq(v_c_786_, v___x_811_);
if (v___x_812_ == 0)
{
uint8_t v___x_813_; uint8_t v___x_814_; 
v___x_813_ = 41;
v___x_814_ = lean_uint8_dec_eq(v_c_786_, v___x_813_);
if (v___x_814_ == 0)
{
uint8_t v___x_815_; uint8_t v___x_816_; 
v___x_815_ = 42;
v___x_816_ = lean_uint8_dec_eq(v_c_786_, v___x_815_);
if (v___x_816_ == 0)
{
uint8_t v___x_817_; uint8_t v___x_818_; 
v___x_817_ = 43;
v___x_818_ = lean_uint8_dec_eq(v_c_786_, v___x_817_);
if (v___x_818_ == 0)
{
uint8_t v___x_819_; uint8_t v___x_820_; 
v___x_819_ = 44;
v___x_820_ = lean_uint8_dec_eq(v_c_786_, v___x_819_);
if (v___x_820_ == 0)
{
uint8_t v___x_821_; uint8_t v___x_822_; 
v___x_821_ = 59;
v___x_822_ = lean_uint8_dec_eq(v_c_786_, v___x_821_);
if (v___x_822_ == 0)
{
uint8_t v___x_823_; uint8_t v___x_824_; 
v___x_823_ = 61;
v___x_824_ = lean_uint8_dec_eq(v_c_786_, v___x_823_);
if (v___x_824_ == 0)
{
uint8_t v___x_825_; uint8_t v___x_826_; 
v___x_825_ = 58;
v___x_826_ = lean_uint8_dec_eq(v_c_786_, v___x_825_);
if (v___x_826_ == 0)
{
uint8_t v___x_827_; uint8_t v___x_828_; 
v___x_827_ = 64;
v___x_828_ = lean_uint8_dec_eq(v_c_786_, v___x_827_);
if (v___x_828_ == 0)
{
uint8_t v___x_829_; uint8_t v___x_830_; 
v___x_829_ = 47;
v___x_830_ = lean_uint8_dec_eq(v_c_786_, v___x_829_);
if (v___x_830_ == 0)
{
uint8_t v___x_831_; uint8_t v___x_832_; 
v___x_831_ = 63;
v___x_832_ = lean_uint8_dec_eq(v_c_786_, v___x_831_);
if (v___x_832_ == 0)
{
return v___x_832_;
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
else
{
goto v___jp_787_;
}
}
v___jp_833_:
{
uint8_t v___x_834_; uint8_t v___x_835_; 
v___x_834_ = 65;
v___x_835_ = lean_uint8_dec_le(v___x_834_, v_c_786_);
if (v___x_835_ == 0)
{
goto v___jp_794_;
}
else
{
uint8_t v___x_836_; uint8_t v___x_837_; 
v___x_836_ = 90;
v___x_837_ = lean_uint8_dec_le(v_c_786_, v___x_836_);
if (v___x_837_ == 0)
{
goto v___jp_794_;
}
else
{
goto v___jp_787_;
}
}
}
v___jp_838_:
{
uint8_t v___x_839_; uint8_t v___x_840_; 
v___x_839_ = 97;
v___x_840_ = lean_uint8_dec_le(v___x_839_, v_c_786_);
if (v___x_840_ == 0)
{
goto v___jp_833_;
}
else
{
uint8_t v___x_841_; uint8_t v___x_842_; 
v___x_841_ = 122;
v___x_842_ = lean_uint8_dec_le(v_c_786_, v___x_841_);
if (v___x_842_ == 0)
{
goto v___jp_833_;
}
else
{
goto v___jp_787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryDataChar___boxed(lean_object* v_c_847_){
_start:
{
uint8_t v_c_boxed_848_; uint8_t v_res_849_; lean_object* v_r_850_; 
v_c_boxed_848_ = lean_unbox(v_c_847_);
v_res_849_ = l_Std_Http_Internal_Char_isQueryDataChar(v_c_boxed_848_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
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
