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
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryNameChar(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryNameChar___boxed(lean_object*);
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
uint32_t v___x_259_; uint8_t v___x_260_; 
v___x_259_ = 33;
v___x_260_ = lean_uint32_dec_le(v___x_259_, v_c_255_);
if (v___x_260_ == 0)
{
goto v___jp_256_;
}
else
{
uint32_t v___x_261_; uint8_t v___x_262_; 
v___x_261_ = 126;
v___x_262_ = lean_uint32_dec_le(v_c_255_, v___x_261_);
if (v___x_262_ == 0)
{
goto v___jp_256_;
}
else
{
return v___x_262_;
}
}
v___jp_256_:
{
uint32_t v___x_257_; uint8_t v___x_258_; 
v___x_257_ = 128;
v___x_258_ = lean_uint32_dec_le(v___x_257_, v_c_255_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldVchar___boxed(lean_object* v_c_263_){
_start:
{
uint32_t v_c_boxed_264_; uint8_t v_res_265_; lean_object* v_r_266_; 
v_c_boxed_264_ = lean_unbox_uint32(v_c_263_);
lean_dec(v_c_263_);
v_res_265_ = l_Std_Http_Internal_Char_fieldVchar(v_c_boxed_264_);
v_r_266_ = lean_box(v_res_265_);
return v_r_266_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_fieldContent(uint32_t v_c_267_){
_start:
{
uint32_t v___x_275_; uint8_t v___x_276_; 
v___x_275_ = 33;
v___x_276_ = lean_uint32_dec_le(v___x_275_, v_c_267_);
if (v___x_276_ == 0)
{
goto v___jp_268_;
}
else
{
uint32_t v___x_277_; uint8_t v___x_278_; 
v___x_277_ = 126;
v___x_278_ = lean_uint32_dec_le(v_c_267_, v___x_277_);
if (v___x_278_ == 0)
{
goto v___jp_268_;
}
else
{
return v___x_278_;
}
}
v___jp_268_:
{
uint32_t v___x_269_; uint8_t v___x_270_; 
v___x_269_ = 128;
v___x_270_ = lean_uint32_dec_le(v___x_269_, v_c_267_);
if (v___x_270_ == 0)
{
uint32_t v___x_271_; uint8_t v___x_272_; 
v___x_271_ = 32;
v___x_272_ = lean_uint32_dec_eq(v_c_267_, v___x_271_);
if (v___x_272_ == 0)
{
uint32_t v___x_273_; uint8_t v___x_274_; 
v___x_273_ = 9;
v___x_274_ = lean_uint32_dec_eq(v_c_267_, v___x_273_);
return v___x_274_;
}
else
{
return v___x_272_;
}
}
else
{
return v___x_270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldContent___boxed(lean_object* v_c_279_){
_start:
{
uint32_t v_c_boxed_280_; uint8_t v_res_281_; lean_object* v_r_282_; 
v_c_boxed_280_ = lean_unbox_uint32(v_c_279_);
lean_dec(v_c_279_);
v_res_281_ = l_Std_Http_Internal_Char_fieldContent(v_c_boxed_280_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_ctext(uint32_t v_c_283_){
_start:
{
uint32_t v___x_294_; uint8_t v___x_295_; 
v___x_294_ = 9;
v___x_295_ = lean_uint32_dec_eq(v_c_283_, v___x_294_);
if (v___x_295_ == 0)
{
uint32_t v___x_296_; uint8_t v___x_297_; 
v___x_296_ = 32;
v___x_297_ = lean_uint32_dec_eq(v_c_283_, v___x_296_);
if (v___x_297_ == 0)
{
uint32_t v___x_298_; uint8_t v___x_299_; 
v___x_298_ = 33;
v___x_299_ = lean_uint32_dec_le(v___x_298_, v_c_283_);
if (v___x_299_ == 0)
{
goto v___jp_289_;
}
else
{
uint32_t v___x_300_; uint8_t v___x_301_; 
v___x_300_ = 39;
v___x_301_ = lean_uint32_dec_le(v_c_283_, v___x_300_);
if (v___x_301_ == 0)
{
goto v___jp_289_;
}
else
{
return v___x_301_;
}
}
}
else
{
return v___x_297_;
}
}
else
{
return v___x_295_;
}
v___jp_284_:
{
uint32_t v___x_285_; uint8_t v___x_286_; 
v___x_285_ = 93;
v___x_286_ = lean_uint32_dec_le(v___x_285_, v_c_283_);
if (v___x_286_ == 0)
{
return v___x_286_;
}
else
{
uint32_t v___x_287_; uint8_t v___x_288_; 
v___x_287_ = 126;
v___x_288_ = lean_uint32_dec_le(v_c_283_, v___x_287_);
return v___x_288_;
}
}
v___jp_289_:
{
uint32_t v___x_290_; uint8_t v___x_291_; 
v___x_290_ = 42;
v___x_291_ = lean_uint32_dec_le(v___x_290_, v_c_283_);
if (v___x_291_ == 0)
{
goto v___jp_284_;
}
else
{
uint32_t v___x_292_; uint8_t v___x_293_; 
v___x_292_ = 91;
v___x_293_ = lean_uint32_dec_le(v_c_283_, v___x_292_);
if (v___x_293_ == 0)
{
goto v___jp_284_;
}
else
{
return v___x_293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ctext___boxed(lean_object* v_c_302_){
_start:
{
uint32_t v_c_boxed_303_; uint8_t v_res_304_; lean_object* v_r_305_; 
v_c_boxed_303_ = lean_unbox_uint32(v_c_302_);
lean_dec(v_c_302_);
v_res_304_ = l_Std_Http_Internal_Char_ctext(v_c_boxed_303_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_etagc(uint32_t v_c_306_){
_start:
{
uint32_t v___x_307_; uint8_t v___x_308_; 
v___x_307_ = 33;
v___x_308_ = lean_uint32_dec_eq(v_c_306_, v___x_307_);
if (v___x_308_ == 0)
{
uint32_t v___x_309_; uint8_t v___x_310_; 
v___x_309_ = 35;
v___x_310_ = lean_uint32_dec_le(v___x_309_, v_c_306_);
if (v___x_310_ == 0)
{
return v___x_310_;
}
else
{
uint32_t v___x_311_; uint8_t v___x_312_; 
v___x_311_ = 126;
v___x_312_ = lean_uint32_dec_le(v_c_306_, v___x_311_);
return v___x_312_;
}
}
else
{
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_etagc___boxed(lean_object* v_c_313_){
_start:
{
uint32_t v_c_boxed_314_; uint8_t v_res_315_; lean_object* v_r_316_; 
v_c_boxed_314_ = lean_unbox_uint32(v_c_313_);
lean_dec(v_c_313_);
v_res_315_ = l_Std_Http_Internal_Char_etagc(v_c_boxed_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_ows(uint32_t v_c_317_){
_start:
{
uint32_t v___x_318_; uint8_t v___x_319_; 
v___x_318_ = 32;
v___x_319_ = lean_uint32_dec_eq(v_c_317_, v___x_318_);
if (v___x_319_ == 0)
{
uint32_t v___x_320_; uint8_t v___x_321_; 
v___x_320_ = 9;
v___x_321_ = lean_uint32_dec_eq(v_c_317_, v___x_320_);
return v___x_321_;
}
else
{
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ows___boxed(lean_object* v_c_322_){
_start:
{
uint32_t v_c_boxed_323_; uint8_t v_res_324_; lean_object* v_r_325_; 
v_c_boxed_323_ = lean_unbox_uint32(v_c_322_);
lean_dec(v_c_322_);
v_res_324_ = l_Std_Http_Internal_Char_ows(v_c_boxed_323_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_bws(uint32_t v_c_326_){
_start:
{
uint32_t v___x_327_; uint8_t v___x_328_; 
v___x_327_ = 32;
v___x_328_ = lean_uint32_dec_eq(v_c_326_, v___x_327_);
if (v___x_328_ == 0)
{
uint32_t v___x_329_; uint8_t v___x_330_; 
v___x_329_ = 9;
v___x_330_ = lean_uint32_dec_eq(v_c_326_, v___x_329_);
return v___x_330_;
}
else
{
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_bws___boxed(lean_object* v_c_331_){
_start:
{
uint32_t v_c_boxed_332_; uint8_t v_res_333_; lean_object* v_r_334_; 
v_c_boxed_332_ = lean_unbox_uint32(v_c_331_);
lean_dec(v_c_331_);
v_res_333_ = l_Std_Http_Internal_Char_bws(v_c_boxed_332_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_rws(uint32_t v_c_335_){
_start:
{
uint32_t v___x_336_; uint8_t v___x_337_; 
v___x_336_ = 32;
v___x_337_ = lean_uint32_dec_eq(v_c_335_, v___x_336_);
if (v___x_337_ == 0)
{
uint32_t v___x_338_; uint8_t v___x_339_; 
v___x_338_ = 9;
v___x_339_ = lean_uint32_dec_eq(v_c_335_, v___x_338_);
return v___x_339_;
}
else
{
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_rws___boxed(lean_object* v_c_340_){
_start:
{
uint32_t v_c_boxed_341_; uint8_t v_res_342_; lean_object* v_r_343_; 
v_c_boxed_341_ = lean_unbox_uint32(v_c_340_);
lean_dec(v_c_340_);
v_res_342_ = l_Std_Http_Internal_Char_rws(v_c_boxed_341_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_obsText(uint32_t v_c_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_345_ = lean_unsigned_to_nat(128u);
v___x_346_ = lean_uint32_to_nat(v_c_344_);
v___x_347_ = lean_nat_dec_le(v___x_345_, v___x_346_);
lean_dec(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_obsText___boxed(lean_object* v_c_348_){
_start:
{
uint32_t v_c_boxed_349_; uint8_t v_res_350_; lean_object* v_r_351_; 
v_c_boxed_349_ = lean_unbox_uint32(v_c_348_);
lean_dec(v_c_348_);
v_res_350_ = l_Std_Http_Internal_Char_obsText(v_c_boxed_349_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_reasonPhraseChar(uint32_t v_c_352_){
_start:
{
uint32_t v___x_356_; uint8_t v___x_357_; 
v___x_356_ = 9;
v___x_357_ = lean_uint32_dec_eq(v_c_352_, v___x_356_);
if (v___x_357_ == 0)
{
uint32_t v___x_358_; uint8_t v___x_359_; 
v___x_358_ = 32;
v___x_359_ = lean_uint32_dec_eq(v_c_352_, v___x_358_);
if (v___x_359_ == 0)
{
uint32_t v___x_360_; uint8_t v___x_361_; 
v___x_360_ = 33;
v___x_361_ = lean_uint32_dec_le(v___x_360_, v_c_352_);
if (v___x_361_ == 0)
{
goto v___jp_353_;
}
else
{
uint32_t v___x_362_; uint8_t v___x_363_; 
v___x_362_ = 126;
v___x_363_ = lean_uint32_dec_le(v_c_352_, v___x_362_);
if (v___x_363_ == 0)
{
goto v___jp_353_;
}
else
{
return v___x_363_;
}
}
}
else
{
return v___x_359_;
}
}
else
{
return v___x_357_;
}
v___jp_353_:
{
uint32_t v___x_354_; uint8_t v___x_355_; 
v___x_354_ = 128;
v___x_355_ = lean_uint32_dec_le(v___x_354_, v_c_352_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_reasonPhraseChar___boxed(lean_object* v_c_364_){
_start:
{
uint32_t v_c_boxed_365_; uint8_t v_res_366_; lean_object* v_r_367_; 
v_c_boxed_365_ = lean_unbox_uint32(v_c_364_);
lean_dec(v_c_364_);
v_res_366_ = l_Std_Http_Internal_Char_reasonPhraseChar(v_c_boxed_365_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isHexDigit(uint32_t v_c_368_){
_start:
{
uint32_t v___x_369_; uint8_t v___x_370_; 
v___x_369_ = 97;
v___x_370_ = lean_uint32_dec_eq(v_c_368_, v___x_369_);
if (v___x_370_ == 0)
{
uint32_t v___x_371_; uint8_t v___x_372_; 
v___x_371_ = 98;
v___x_372_ = lean_uint32_dec_eq(v_c_368_, v___x_371_);
if (v___x_372_ == 0)
{
uint32_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 99;
v___x_374_ = lean_uint32_dec_eq(v_c_368_, v___x_373_);
if (v___x_374_ == 0)
{
uint32_t v___x_375_; uint8_t v___x_376_; 
v___x_375_ = 100;
v___x_376_ = lean_uint32_dec_eq(v_c_368_, v___x_375_);
if (v___x_376_ == 0)
{
uint32_t v___x_377_; uint8_t v___x_378_; 
v___x_377_ = 101;
v___x_378_ = lean_uint32_dec_eq(v_c_368_, v___x_377_);
if (v___x_378_ == 0)
{
uint32_t v___x_379_; uint8_t v___x_380_; 
v___x_379_ = 102;
v___x_380_ = lean_uint32_dec_eq(v_c_368_, v___x_379_);
if (v___x_380_ == 0)
{
uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = 65;
v___x_382_ = lean_uint32_dec_eq(v_c_368_, v___x_381_);
if (v___x_382_ == 0)
{
uint32_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = 66;
v___x_384_ = lean_uint32_dec_eq(v_c_368_, v___x_383_);
if (v___x_384_ == 0)
{
uint32_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 67;
v___x_386_ = lean_uint32_dec_eq(v_c_368_, v___x_385_);
if (v___x_386_ == 0)
{
uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 68;
v___x_388_ = lean_uint32_dec_eq(v_c_368_, v___x_387_);
if (v___x_388_ == 0)
{
uint32_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 69;
v___x_390_ = lean_uint32_dec_eq(v_c_368_, v___x_389_);
if (v___x_390_ == 0)
{
uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 70;
v___x_392_ = lean_uint32_dec_eq(v_c_368_, v___x_391_);
if (v___x_392_ == 0)
{
uint32_t v___x_393_; uint8_t v___x_394_; 
v___x_393_ = 48;
v___x_394_ = lean_uint32_dec_le(v___x_393_, v_c_368_);
if (v___x_394_ == 0)
{
return v___x_394_;
}
else
{
uint32_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = 57;
v___x_396_ = lean_uint32_dec_le(v_c_368_, v___x_395_);
return v___x_396_;
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
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigit___boxed(lean_object* v_c_397_){
_start:
{
uint32_t v_c_boxed_398_; uint8_t v_res_399_; lean_object* v_r_400_; 
v_c_boxed_398_ = lean_unbox_uint32(v_c_397_);
lean_dec(v_c_397_);
v_res_399_ = l_Std_Http_Internal_Char_isHexDigit(v_c_boxed_398_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isHexDigitByte(uint8_t v_c_401_){
_start:
{
uint8_t v___x_412_; uint8_t v___x_413_; 
v___x_412_ = 48;
v___x_413_ = lean_uint8_dec_le(v___x_412_, v_c_401_);
if (v___x_413_ == 0)
{
goto v___jp_407_;
}
else
{
uint8_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = 57;
v___x_415_ = lean_uint8_dec_le(v_c_401_, v___x_414_);
if (v___x_415_ == 0)
{
goto v___jp_407_;
}
else
{
return v___x_415_;
}
}
v___jp_402_:
{
uint8_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 65;
v___x_404_ = lean_uint8_dec_le(v___x_403_, v_c_401_);
if (v___x_404_ == 0)
{
return v___x_404_;
}
else
{
uint8_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 70;
v___x_406_ = lean_uint8_dec_le(v_c_401_, v___x_405_);
return v___x_406_;
}
}
v___jp_407_:
{
uint8_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 97;
v___x_409_ = lean_uint8_dec_le(v___x_408_, v_c_401_);
if (v___x_409_ == 0)
{
goto v___jp_402_;
}
else
{
uint8_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 102;
v___x_411_ = lean_uint8_dec_le(v_c_401_, v___x_410_);
if (v___x_411_ == 0)
{
goto v___jp_402_;
}
else
{
return v___x_411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigitByte___boxed(lean_object* v_c_416_){
_start:
{
uint8_t v_c_boxed_417_; uint8_t v_res_418_; lean_object* v_r_419_; 
v_c_boxed_417_ = lean_unbox(v_c_416_);
v_res_418_ = l_Std_Http_Internal_Char_isHexDigitByte(v_c_boxed_417_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAlphaNum(uint8_t v_c_420_){
_start:
{
uint8_t v___x_431_; uint8_t v___x_432_; 
v___x_431_ = 48;
v___x_432_ = lean_uint8_dec_le(v___x_431_, v_c_420_);
if (v___x_432_ == 0)
{
goto v___jp_426_;
}
else
{
uint8_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = 57;
v___x_434_ = lean_uint8_dec_le(v_c_420_, v___x_433_);
if (v___x_434_ == 0)
{
goto v___jp_426_;
}
else
{
return v___x_434_;
}
}
v___jp_421_:
{
uint8_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = 65;
v___x_423_ = lean_uint8_dec_le(v___x_422_, v_c_420_);
if (v___x_423_ == 0)
{
return v___x_423_;
}
else
{
uint8_t v___x_424_; uint8_t v___x_425_; 
v___x_424_ = 90;
v___x_425_ = lean_uint8_dec_le(v_c_420_, v___x_424_);
return v___x_425_;
}
}
v___jp_426_:
{
uint8_t v___x_427_; uint8_t v___x_428_; 
v___x_427_ = 97;
v___x_428_ = lean_uint8_dec_le(v___x_427_, v_c_420_);
if (v___x_428_ == 0)
{
goto v___jp_421_;
}
else
{
uint8_t v___x_429_; uint8_t v___x_430_; 
v___x_429_ = 122;
v___x_430_ = lean_uint8_dec_le(v_c_420_, v___x_429_);
if (v___x_430_ == 0)
{
goto v___jp_421_;
}
else
{
return v___x_430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAlphaNum___boxed(lean_object* v_c_435_){
_start:
{
uint8_t v_c_boxed_436_; uint8_t v_res_437_; lean_object* v_r_438_; 
v_c_boxed_436_ = lean_unbox(v_c_435_);
v_res_437_ = l_Std_Http_Internal_Char_isAlphaNum(v_c_boxed_436_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAsciiAlphaNumChar(uint32_t v_c_439_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_450_ = lean_uint32_to_nat(v_c_439_);
v___x_451_ = lean_unsigned_to_nat(128u);
v___x_452_ = lean_nat_dec_lt(v___x_450_, v___x_451_);
lean_dec(v___x_450_);
if (v___x_452_ == 0)
{
return v___x_452_;
}
else
{
uint32_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = 48;
v___x_454_ = lean_uint32_dec_le(v___x_453_, v_c_439_);
if (v___x_454_ == 0)
{
goto v___jp_445_;
}
else
{
uint32_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 57;
v___x_456_ = lean_uint32_dec_le(v_c_439_, v___x_455_);
if (v___x_456_ == 0)
{
goto v___jp_445_;
}
else
{
return v___x_456_;
}
}
}
v___jp_440_:
{
uint32_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 97;
v___x_442_ = lean_uint32_dec_le(v___x_441_, v_c_439_);
if (v___x_442_ == 0)
{
return v___x_442_;
}
else
{
uint32_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 122;
v___x_444_ = lean_uint32_dec_le(v_c_439_, v___x_443_);
return v___x_444_;
}
}
v___jp_445_:
{
uint32_t v___x_446_; uint8_t v___x_447_; 
v___x_446_ = 65;
v___x_447_ = lean_uint32_dec_le(v___x_446_, v_c_439_);
if (v___x_447_ == 0)
{
goto v___jp_440_;
}
else
{
uint32_t v___x_448_; uint8_t v___x_449_; 
v___x_448_ = 90;
v___x_449_ = lean_uint32_dec_le(v_c_439_, v___x_448_);
if (v___x_449_ == 0)
{
goto v___jp_440_;
}
else
{
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAsciiAlphaNumChar___boxed(lean_object* v_c_457_){
_start:
{
uint32_t v_c_boxed_458_; uint8_t v_res_459_; lean_object* v_r_460_; 
v_c_boxed_458_ = lean_unbox_uint32(v_c_457_);
lean_dec(v_c_457_);
v_res_459_ = l_Std_Http_Internal_Char_isAsciiAlphaNumChar(v_c_boxed_458_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isValidSchemeChar(uint32_t v_c_461_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_479_ = lean_uint32_to_nat(v_c_461_);
v___x_480_ = lean_unsigned_to_nat(128u);
v___x_481_ = lean_nat_dec_lt(v___x_479_, v___x_480_);
lean_dec(v___x_479_);
if (v___x_481_ == 0)
{
goto v___jp_462_;
}
else
{
uint32_t v___x_482_; uint8_t v___x_483_; 
v___x_482_ = 48;
v___x_483_ = lean_uint32_dec_le(v___x_482_, v_c_461_);
if (v___x_483_ == 0)
{
goto v___jp_474_;
}
else
{
uint32_t v___x_484_; uint8_t v___x_485_; 
v___x_484_ = 57;
v___x_485_ = lean_uint32_dec_le(v_c_461_, v___x_484_);
if (v___x_485_ == 0)
{
goto v___jp_474_;
}
else
{
return v___x_485_;
}
}
}
v___jp_462_:
{
uint32_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = 43;
v___x_464_ = lean_uint32_dec_eq(v_c_461_, v___x_463_);
if (v___x_464_ == 0)
{
uint32_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = 45;
v___x_466_ = lean_uint32_dec_eq(v_c_461_, v___x_465_);
if (v___x_466_ == 0)
{
uint32_t v___x_467_; uint8_t v___x_468_; 
v___x_467_ = 46;
v___x_468_ = lean_uint32_dec_eq(v_c_461_, v___x_467_);
return v___x_468_;
}
else
{
return v___x_466_;
}
}
else
{
return v___x_464_;
}
}
v___jp_469_:
{
uint32_t v___x_470_; uint8_t v___x_471_; 
v___x_470_ = 97;
v___x_471_ = lean_uint32_dec_le(v___x_470_, v_c_461_);
if (v___x_471_ == 0)
{
goto v___jp_462_;
}
else
{
uint32_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = 122;
v___x_473_ = lean_uint32_dec_le(v_c_461_, v___x_472_);
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
v___jp_474_:
{
uint32_t v___x_475_; uint8_t v___x_476_; 
v___x_475_ = 65;
v___x_476_ = lean_uint32_dec_le(v___x_475_, v_c_461_);
if (v___x_476_ == 0)
{
goto v___jp_469_;
}
else
{
uint32_t v___x_477_; uint8_t v___x_478_; 
v___x_477_ = 90;
v___x_478_ = lean_uint32_dec_le(v_c_461_, v___x_477_);
if (v___x_478_ == 0)
{
goto v___jp_469_;
}
else
{
return v___x_478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidSchemeChar___boxed(lean_object* v_c_486_){
_start:
{
uint32_t v_c_boxed_487_; uint8_t v_res_488_; lean_object* v_r_489_; 
v_c_boxed_487_ = lean_unbox_uint32(v_c_486_);
lean_dec(v_c_486_);
v_res_488_ = l_Std_Http_Internal_Char_isValidSchemeChar(v_c_boxed_487_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUnreserved(uint8_t v_c_490_){
_start:
{
uint8_t v___x_510_; uint8_t v___x_511_; 
v___x_510_ = 48;
v___x_511_ = lean_uint8_dec_le(v___x_510_, v_c_490_);
if (v___x_511_ == 0)
{
goto v___jp_505_;
}
else
{
uint8_t v___x_512_; uint8_t v___x_513_; 
v___x_512_ = 57;
v___x_513_ = lean_uint8_dec_le(v_c_490_, v___x_512_);
if (v___x_513_ == 0)
{
goto v___jp_505_;
}
else
{
return v___x_513_;
}
}
v___jp_491_:
{
uint8_t v___x_492_; uint8_t v___x_493_; 
v___x_492_ = 45;
v___x_493_ = lean_uint8_dec_eq(v_c_490_, v___x_492_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; uint8_t v___x_495_; 
v___x_494_ = 46;
v___x_495_ = lean_uint8_dec_eq(v_c_490_, v___x_494_);
if (v___x_495_ == 0)
{
uint8_t v___x_496_; uint8_t v___x_497_; 
v___x_496_ = 95;
v___x_497_ = lean_uint8_dec_eq(v_c_490_, v___x_496_);
if (v___x_497_ == 0)
{
uint8_t v___x_498_; uint8_t v___x_499_; 
v___x_498_ = 126;
v___x_499_ = lean_uint8_dec_eq(v_c_490_, v___x_498_);
return v___x_499_;
}
else
{
return v___x_497_;
}
}
else
{
return v___x_495_;
}
}
else
{
return v___x_493_;
}
}
v___jp_500_:
{
uint8_t v___x_501_; uint8_t v___x_502_; 
v___x_501_ = 65;
v___x_502_ = lean_uint8_dec_le(v___x_501_, v_c_490_);
if (v___x_502_ == 0)
{
goto v___jp_491_;
}
else
{
uint8_t v___x_503_; uint8_t v___x_504_; 
v___x_503_ = 90;
v___x_504_ = lean_uint8_dec_le(v_c_490_, v___x_503_);
if (v___x_504_ == 0)
{
goto v___jp_491_;
}
else
{
return v___x_504_;
}
}
}
v___jp_505_:
{
uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = 97;
v___x_507_ = lean_uint8_dec_le(v___x_506_, v_c_490_);
if (v___x_507_ == 0)
{
goto v___jp_500_;
}
else
{
uint8_t v___x_508_; uint8_t v___x_509_; 
v___x_508_ = 122;
v___x_509_ = lean_uint8_dec_le(v_c_490_, v___x_508_);
if (v___x_509_ == 0)
{
goto v___jp_500_;
}
else
{
return v___x_509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUnreserved___boxed(lean_object* v_c_514_){
_start:
{
uint8_t v_c_boxed_515_; uint8_t v_res_516_; lean_object* v_r_517_; 
v_c_boxed_515_ = lean_unbox(v_c_514_);
v_res_516_ = l_Std_Http_Internal_Char_isUnreserved(v_c_boxed_515_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isSubDelims(uint8_t v_c_518_){
_start:
{
uint8_t v___x_519_; uint8_t v___x_520_; 
v___x_519_ = 33;
v___x_520_ = lean_uint8_dec_eq(v_c_518_, v___x_519_);
if (v___x_520_ == 0)
{
uint8_t v___x_521_; uint8_t v___x_522_; 
v___x_521_ = 36;
v___x_522_ = lean_uint8_dec_eq(v_c_518_, v___x_521_);
if (v___x_522_ == 0)
{
uint8_t v___x_523_; uint8_t v___x_524_; 
v___x_523_ = 38;
v___x_524_ = lean_uint8_dec_eq(v_c_518_, v___x_523_);
if (v___x_524_ == 0)
{
uint8_t v___x_525_; uint8_t v___x_526_; 
v___x_525_ = 39;
v___x_526_ = lean_uint8_dec_eq(v_c_518_, v___x_525_);
if (v___x_526_ == 0)
{
uint8_t v___x_527_; uint8_t v___x_528_; 
v___x_527_ = 40;
v___x_528_ = lean_uint8_dec_eq(v_c_518_, v___x_527_);
if (v___x_528_ == 0)
{
uint8_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = 41;
v___x_530_ = lean_uint8_dec_eq(v_c_518_, v___x_529_);
if (v___x_530_ == 0)
{
uint8_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 42;
v___x_532_ = lean_uint8_dec_eq(v_c_518_, v___x_531_);
if (v___x_532_ == 0)
{
uint8_t v___x_533_; uint8_t v___x_534_; 
v___x_533_ = 43;
v___x_534_ = lean_uint8_dec_eq(v_c_518_, v___x_533_);
if (v___x_534_ == 0)
{
uint8_t v___x_535_; uint8_t v___x_536_; 
v___x_535_ = 44;
v___x_536_ = lean_uint8_dec_eq(v_c_518_, v___x_535_);
if (v___x_536_ == 0)
{
uint8_t v___x_537_; uint8_t v___x_538_; 
v___x_537_ = 59;
v___x_538_ = lean_uint8_dec_eq(v_c_518_, v___x_537_);
if (v___x_538_ == 0)
{
uint8_t v___x_539_; uint8_t v___x_540_; 
v___x_539_ = 61;
v___x_540_ = lean_uint8_dec_eq(v_c_518_, v___x_539_);
return v___x_540_;
}
else
{
return v___x_538_;
}
}
else
{
return v___x_536_;
}
}
else
{
return v___x_534_;
}
}
else
{
return v___x_532_;
}
}
else
{
return v___x_530_;
}
}
else
{
return v___x_528_;
}
}
else
{
return v___x_526_;
}
}
else
{
return v___x_524_;
}
}
else
{
return v___x_522_;
}
}
else
{
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isSubDelims___boxed(lean_object* v_c_541_){
_start:
{
uint8_t v_c_boxed_542_; uint8_t v_res_543_; lean_object* v_r_544_; 
v_c_boxed_542_ = lean_unbox(v_c_541_);
v_res_543_ = l_Std_Http_Internal_Char_isSubDelims(v_c_boxed_542_);
v_r_544_ = lean_box(v_res_543_);
return v_r_544_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isPChar(uint8_t v_c_545_){
_start:
{
uint8_t v___x_591_; uint8_t v___x_592_; 
v___x_591_ = 48;
v___x_592_ = lean_uint8_dec_le(v___x_591_, v_c_545_);
if (v___x_592_ == 0)
{
goto v___jp_586_;
}
else
{
uint8_t v___x_593_; uint8_t v___x_594_; 
v___x_593_ = 57;
v___x_594_ = lean_uint8_dec_le(v_c_545_, v___x_593_);
if (v___x_594_ == 0)
{
goto v___jp_586_;
}
else
{
return v___x_594_;
}
}
v___jp_546_:
{
uint8_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = 45;
v___x_548_ = lean_uint8_dec_eq(v_c_545_, v___x_547_);
if (v___x_548_ == 0)
{
uint8_t v___x_549_; uint8_t v___x_550_; 
v___x_549_ = 46;
v___x_550_ = lean_uint8_dec_eq(v_c_545_, v___x_549_);
if (v___x_550_ == 0)
{
uint8_t v___x_551_; uint8_t v___x_552_; 
v___x_551_ = 95;
v___x_552_ = lean_uint8_dec_eq(v_c_545_, v___x_551_);
if (v___x_552_ == 0)
{
uint8_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = 126;
v___x_554_ = lean_uint8_dec_eq(v_c_545_, v___x_553_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = 33;
v___x_556_ = lean_uint8_dec_eq(v_c_545_, v___x_555_);
if (v___x_556_ == 0)
{
uint8_t v___x_557_; uint8_t v___x_558_; 
v___x_557_ = 36;
v___x_558_ = lean_uint8_dec_eq(v_c_545_, v___x_557_);
if (v___x_558_ == 0)
{
uint8_t v___x_559_; uint8_t v___x_560_; 
v___x_559_ = 38;
v___x_560_ = lean_uint8_dec_eq(v_c_545_, v___x_559_);
if (v___x_560_ == 0)
{
uint8_t v___x_561_; uint8_t v___x_562_; 
v___x_561_ = 39;
v___x_562_ = lean_uint8_dec_eq(v_c_545_, v___x_561_);
if (v___x_562_ == 0)
{
uint8_t v___x_563_; uint8_t v___x_564_; 
v___x_563_ = 40;
v___x_564_ = lean_uint8_dec_eq(v_c_545_, v___x_563_);
if (v___x_564_ == 0)
{
uint8_t v___x_565_; uint8_t v___x_566_; 
v___x_565_ = 41;
v___x_566_ = lean_uint8_dec_eq(v_c_545_, v___x_565_);
if (v___x_566_ == 0)
{
uint8_t v___x_567_; uint8_t v___x_568_; 
v___x_567_ = 42;
v___x_568_ = lean_uint8_dec_eq(v_c_545_, v___x_567_);
if (v___x_568_ == 0)
{
uint8_t v___x_569_; uint8_t v___x_570_; 
v___x_569_ = 43;
v___x_570_ = lean_uint8_dec_eq(v_c_545_, v___x_569_);
if (v___x_570_ == 0)
{
uint8_t v___x_571_; uint8_t v___x_572_; 
v___x_571_ = 44;
v___x_572_ = lean_uint8_dec_eq(v_c_545_, v___x_571_);
if (v___x_572_ == 0)
{
uint8_t v___x_573_; uint8_t v___x_574_; 
v___x_573_ = 59;
v___x_574_ = lean_uint8_dec_eq(v_c_545_, v___x_573_);
if (v___x_574_ == 0)
{
uint8_t v___x_575_; uint8_t v___x_576_; 
v___x_575_ = 61;
v___x_576_ = lean_uint8_dec_eq(v_c_545_, v___x_575_);
if (v___x_576_ == 0)
{
uint8_t v___x_577_; uint8_t v___x_578_; 
v___x_577_ = 58;
v___x_578_ = lean_uint8_dec_eq(v_c_545_, v___x_577_);
if (v___x_578_ == 0)
{
uint8_t v___x_579_; uint8_t v___x_580_; 
v___x_579_ = 64;
v___x_580_ = lean_uint8_dec_eq(v_c_545_, v___x_579_);
return v___x_580_;
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
else
{
return v___x_566_;
}
}
else
{
return v___x_564_;
}
}
else
{
return v___x_562_;
}
}
else
{
return v___x_560_;
}
}
else
{
return v___x_558_;
}
}
else
{
return v___x_556_;
}
}
else
{
return v___x_554_;
}
}
else
{
return v___x_552_;
}
}
else
{
return v___x_550_;
}
}
else
{
return v___x_548_;
}
}
v___jp_581_:
{
uint8_t v___x_582_; uint8_t v___x_583_; 
v___x_582_ = 65;
v___x_583_ = lean_uint8_dec_le(v___x_582_, v_c_545_);
if (v___x_583_ == 0)
{
goto v___jp_546_;
}
else
{
uint8_t v___x_584_; uint8_t v___x_585_; 
v___x_584_ = 90;
v___x_585_ = lean_uint8_dec_le(v_c_545_, v___x_584_);
if (v___x_585_ == 0)
{
goto v___jp_546_;
}
else
{
return v___x_585_;
}
}
}
v___jp_586_:
{
uint8_t v___x_587_; uint8_t v___x_588_; 
v___x_587_ = 97;
v___x_588_ = lean_uint8_dec_le(v___x_587_, v_c_545_);
if (v___x_588_ == 0)
{
goto v___jp_581_;
}
else
{
uint8_t v___x_589_; uint8_t v___x_590_; 
v___x_589_ = 122;
v___x_590_ = lean_uint8_dec_le(v_c_545_, v___x_589_);
if (v___x_590_ == 0)
{
goto v___jp_581_;
}
else
{
return v___x_590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isPChar___boxed(lean_object* v_c_595_){
_start:
{
uint8_t v_c_boxed_596_; uint8_t v_res_597_; lean_object* v_r_598_; 
v_c_boxed_596_ = lean_unbox(v_c_595_);
v_res_597_ = l_Std_Http_Internal_Char_isPChar(v_c_boxed_596_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryChar(uint8_t v_c_599_){
_start:
{
uint8_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = 48;
v___x_650_ = lean_uint8_dec_le(v___x_649_, v_c_599_);
if (v___x_650_ == 0)
{
goto v___jp_644_;
}
else
{
uint8_t v___x_651_; uint8_t v___x_652_; 
v___x_651_ = 57;
v___x_652_ = lean_uint8_dec_le(v_c_599_, v___x_651_);
if (v___x_652_ == 0)
{
goto v___jp_644_;
}
else
{
return v___x_652_;
}
}
v___jp_600_:
{
uint8_t v___x_601_; uint8_t v___x_602_; 
v___x_601_ = 45;
v___x_602_ = lean_uint8_dec_eq(v_c_599_, v___x_601_);
if (v___x_602_ == 0)
{
uint8_t v___x_603_; uint8_t v___x_604_; 
v___x_603_ = 46;
v___x_604_ = lean_uint8_dec_eq(v_c_599_, v___x_603_);
if (v___x_604_ == 0)
{
uint8_t v___x_605_; uint8_t v___x_606_; 
v___x_605_ = 95;
v___x_606_ = lean_uint8_dec_eq(v_c_599_, v___x_605_);
if (v___x_606_ == 0)
{
uint8_t v___x_607_; uint8_t v___x_608_; 
v___x_607_ = 126;
v___x_608_ = lean_uint8_dec_eq(v_c_599_, v___x_607_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; uint8_t v___x_610_; 
v___x_609_ = 33;
v___x_610_ = lean_uint8_dec_eq(v_c_599_, v___x_609_);
if (v___x_610_ == 0)
{
uint8_t v___x_611_; uint8_t v___x_612_; 
v___x_611_ = 36;
v___x_612_ = lean_uint8_dec_eq(v_c_599_, v___x_611_);
if (v___x_612_ == 0)
{
uint8_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = 38;
v___x_614_ = lean_uint8_dec_eq(v_c_599_, v___x_613_);
if (v___x_614_ == 0)
{
uint8_t v___x_615_; uint8_t v___x_616_; 
v___x_615_ = 39;
v___x_616_ = lean_uint8_dec_eq(v_c_599_, v___x_615_);
if (v___x_616_ == 0)
{
uint8_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = 40;
v___x_618_ = lean_uint8_dec_eq(v_c_599_, v___x_617_);
if (v___x_618_ == 0)
{
uint8_t v___x_619_; uint8_t v___x_620_; 
v___x_619_ = 41;
v___x_620_ = lean_uint8_dec_eq(v_c_599_, v___x_619_);
if (v___x_620_ == 0)
{
uint8_t v___x_621_; uint8_t v___x_622_; 
v___x_621_ = 42;
v___x_622_ = lean_uint8_dec_eq(v_c_599_, v___x_621_);
if (v___x_622_ == 0)
{
uint8_t v___x_623_; uint8_t v___x_624_; 
v___x_623_ = 43;
v___x_624_ = lean_uint8_dec_eq(v_c_599_, v___x_623_);
if (v___x_624_ == 0)
{
uint8_t v___x_625_; uint8_t v___x_626_; 
v___x_625_ = 44;
v___x_626_ = lean_uint8_dec_eq(v_c_599_, v___x_625_);
if (v___x_626_ == 0)
{
uint8_t v___x_627_; uint8_t v___x_628_; 
v___x_627_ = 59;
v___x_628_ = lean_uint8_dec_eq(v_c_599_, v___x_627_);
if (v___x_628_ == 0)
{
uint8_t v___x_629_; uint8_t v___x_630_; 
v___x_629_ = 61;
v___x_630_ = lean_uint8_dec_eq(v_c_599_, v___x_629_);
if (v___x_630_ == 0)
{
uint8_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = 58;
v___x_632_ = lean_uint8_dec_eq(v_c_599_, v___x_631_);
if (v___x_632_ == 0)
{
uint8_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = 64;
v___x_634_ = lean_uint8_dec_eq(v_c_599_, v___x_633_);
if (v___x_634_ == 0)
{
uint8_t v___x_635_; uint8_t v___x_636_; 
v___x_635_ = 47;
v___x_636_ = lean_uint8_dec_eq(v_c_599_, v___x_635_);
if (v___x_636_ == 0)
{
uint8_t v___x_637_; uint8_t v___x_638_; 
v___x_637_ = 63;
v___x_638_ = lean_uint8_dec_eq(v_c_599_, v___x_637_);
return v___x_638_;
}
else
{
return v___x_636_;
}
}
else
{
return v___x_634_;
}
}
else
{
return v___x_632_;
}
}
else
{
return v___x_630_;
}
}
else
{
return v___x_628_;
}
}
else
{
return v___x_626_;
}
}
else
{
return v___x_624_;
}
}
else
{
return v___x_622_;
}
}
else
{
return v___x_620_;
}
}
else
{
return v___x_618_;
}
}
else
{
return v___x_616_;
}
}
else
{
return v___x_614_;
}
}
else
{
return v___x_612_;
}
}
else
{
return v___x_610_;
}
}
else
{
return v___x_608_;
}
}
else
{
return v___x_606_;
}
}
else
{
return v___x_604_;
}
}
else
{
return v___x_602_;
}
}
v___jp_639_:
{
uint8_t v___x_640_; uint8_t v___x_641_; 
v___x_640_ = 65;
v___x_641_ = lean_uint8_dec_le(v___x_640_, v_c_599_);
if (v___x_641_ == 0)
{
goto v___jp_600_;
}
else
{
uint8_t v___x_642_; uint8_t v___x_643_; 
v___x_642_ = 90;
v___x_643_ = lean_uint8_dec_le(v_c_599_, v___x_642_);
if (v___x_643_ == 0)
{
goto v___jp_600_;
}
else
{
return v___x_643_;
}
}
}
v___jp_644_:
{
uint8_t v___x_645_; uint8_t v___x_646_; 
v___x_645_ = 97;
v___x_646_ = lean_uint8_dec_le(v___x_645_, v_c_599_);
if (v___x_646_ == 0)
{
goto v___jp_639_;
}
else
{
uint8_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = 122;
v___x_648_ = lean_uint8_dec_le(v_c_599_, v___x_647_);
if (v___x_648_ == 0)
{
goto v___jp_639_;
}
else
{
return v___x_648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryChar___boxed(lean_object* v_c_653_){
_start:
{
uint8_t v_c_boxed_654_; uint8_t v_res_655_; lean_object* v_r_656_; 
v_c_boxed_654_ = lean_unbox(v_c_653_);
v_res_655_ = l_Std_Http_Internal_Char_isQueryChar(v_c_boxed_654_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isFragmentChar(uint8_t v_c_657_){
_start:
{
uint8_t v___x_707_; uint8_t v___x_708_; 
v___x_707_ = 48;
v___x_708_ = lean_uint8_dec_le(v___x_707_, v_c_657_);
if (v___x_708_ == 0)
{
goto v___jp_702_;
}
else
{
uint8_t v___x_709_; uint8_t v___x_710_; 
v___x_709_ = 57;
v___x_710_ = lean_uint8_dec_le(v_c_657_, v___x_709_);
if (v___x_710_ == 0)
{
goto v___jp_702_;
}
else
{
return v___x_710_;
}
}
v___jp_658_:
{
uint8_t v___x_659_; uint8_t v___x_660_; 
v___x_659_ = 45;
v___x_660_ = lean_uint8_dec_eq(v_c_657_, v___x_659_);
if (v___x_660_ == 0)
{
uint8_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = 46;
v___x_662_ = lean_uint8_dec_eq(v_c_657_, v___x_661_);
if (v___x_662_ == 0)
{
uint8_t v___x_663_; uint8_t v___x_664_; 
v___x_663_ = 95;
v___x_664_ = lean_uint8_dec_eq(v_c_657_, v___x_663_);
if (v___x_664_ == 0)
{
uint8_t v___x_665_; uint8_t v___x_666_; 
v___x_665_ = 126;
v___x_666_ = lean_uint8_dec_eq(v_c_657_, v___x_665_);
if (v___x_666_ == 0)
{
uint8_t v___x_667_; uint8_t v___x_668_; 
v___x_667_ = 33;
v___x_668_ = lean_uint8_dec_eq(v_c_657_, v___x_667_);
if (v___x_668_ == 0)
{
uint8_t v___x_669_; uint8_t v___x_670_; 
v___x_669_ = 36;
v___x_670_ = lean_uint8_dec_eq(v_c_657_, v___x_669_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; uint8_t v___x_672_; 
v___x_671_ = 38;
v___x_672_ = lean_uint8_dec_eq(v_c_657_, v___x_671_);
if (v___x_672_ == 0)
{
uint8_t v___x_673_; uint8_t v___x_674_; 
v___x_673_ = 39;
v___x_674_ = lean_uint8_dec_eq(v_c_657_, v___x_673_);
if (v___x_674_ == 0)
{
uint8_t v___x_675_; uint8_t v___x_676_; 
v___x_675_ = 40;
v___x_676_ = lean_uint8_dec_eq(v_c_657_, v___x_675_);
if (v___x_676_ == 0)
{
uint8_t v___x_677_; uint8_t v___x_678_; 
v___x_677_ = 41;
v___x_678_ = lean_uint8_dec_eq(v_c_657_, v___x_677_);
if (v___x_678_ == 0)
{
uint8_t v___x_679_; uint8_t v___x_680_; 
v___x_679_ = 42;
v___x_680_ = lean_uint8_dec_eq(v_c_657_, v___x_679_);
if (v___x_680_ == 0)
{
uint8_t v___x_681_; uint8_t v___x_682_; 
v___x_681_ = 43;
v___x_682_ = lean_uint8_dec_eq(v_c_657_, v___x_681_);
if (v___x_682_ == 0)
{
uint8_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = 44;
v___x_684_ = lean_uint8_dec_eq(v_c_657_, v___x_683_);
if (v___x_684_ == 0)
{
uint8_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = 59;
v___x_686_ = lean_uint8_dec_eq(v_c_657_, v___x_685_);
if (v___x_686_ == 0)
{
uint8_t v___x_687_; uint8_t v___x_688_; 
v___x_687_ = 61;
v___x_688_ = lean_uint8_dec_eq(v_c_657_, v___x_687_);
if (v___x_688_ == 0)
{
uint8_t v___x_689_; uint8_t v___x_690_; 
v___x_689_ = 58;
v___x_690_ = lean_uint8_dec_eq(v_c_657_, v___x_689_);
if (v___x_690_ == 0)
{
uint8_t v___x_691_; uint8_t v___x_692_; 
v___x_691_ = 64;
v___x_692_ = lean_uint8_dec_eq(v_c_657_, v___x_691_);
if (v___x_692_ == 0)
{
uint8_t v___x_693_; uint8_t v___x_694_; 
v___x_693_ = 47;
v___x_694_ = lean_uint8_dec_eq(v_c_657_, v___x_693_);
if (v___x_694_ == 0)
{
uint8_t v___x_695_; uint8_t v___x_696_; 
v___x_695_ = 63;
v___x_696_ = lean_uint8_dec_eq(v_c_657_, v___x_695_);
return v___x_696_;
}
else
{
return v___x_694_;
}
}
else
{
return v___x_692_;
}
}
else
{
return v___x_690_;
}
}
else
{
return v___x_688_;
}
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
v___jp_697_:
{
uint8_t v___x_698_; uint8_t v___x_699_; 
v___x_698_ = 65;
v___x_699_ = lean_uint8_dec_le(v___x_698_, v_c_657_);
if (v___x_699_ == 0)
{
goto v___jp_658_;
}
else
{
uint8_t v___x_700_; uint8_t v___x_701_; 
v___x_700_ = 90;
v___x_701_ = lean_uint8_dec_le(v_c_657_, v___x_700_);
if (v___x_701_ == 0)
{
goto v___jp_658_;
}
else
{
return v___x_701_;
}
}
}
v___jp_702_:
{
uint8_t v___x_703_; uint8_t v___x_704_; 
v___x_703_ = 97;
v___x_704_ = lean_uint8_dec_le(v___x_703_, v_c_657_);
if (v___x_704_ == 0)
{
goto v___jp_697_;
}
else
{
uint8_t v___x_705_; uint8_t v___x_706_; 
v___x_705_ = 122;
v___x_706_ = lean_uint8_dec_le(v_c_657_, v___x_705_);
if (v___x_706_ == 0)
{
goto v___jp_697_;
}
else
{
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isFragmentChar___boxed(lean_object* v_c_711_){
_start:
{
uint8_t v_c_boxed_712_; uint8_t v_res_713_; lean_object* v_r_714_; 
v_c_boxed_712_ = lean_unbox(v_c_711_);
v_res_713_ = l_Std_Http_Internal_Char_isFragmentChar(v_c_boxed_712_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUserInfoChar(uint8_t v_c_715_){
_start:
{
uint8_t v___x_759_; uint8_t v___x_760_; 
v___x_759_ = 48;
v___x_760_ = lean_uint8_dec_le(v___x_759_, v_c_715_);
if (v___x_760_ == 0)
{
goto v___jp_754_;
}
else
{
uint8_t v___x_761_; uint8_t v___x_762_; 
v___x_761_ = 57;
v___x_762_ = lean_uint8_dec_le(v_c_715_, v___x_761_);
if (v___x_762_ == 0)
{
goto v___jp_754_;
}
else
{
return v___x_762_;
}
}
v___jp_716_:
{
uint8_t v___x_717_; uint8_t v___x_718_; 
v___x_717_ = 45;
v___x_718_ = lean_uint8_dec_eq(v_c_715_, v___x_717_);
if (v___x_718_ == 0)
{
uint8_t v___x_719_; uint8_t v___x_720_; 
v___x_719_ = 46;
v___x_720_ = lean_uint8_dec_eq(v_c_715_, v___x_719_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; uint8_t v___x_722_; 
v___x_721_ = 95;
v___x_722_ = lean_uint8_dec_eq(v_c_715_, v___x_721_);
if (v___x_722_ == 0)
{
uint8_t v___x_723_; uint8_t v___x_724_; 
v___x_723_ = 126;
v___x_724_ = lean_uint8_dec_eq(v_c_715_, v___x_723_);
if (v___x_724_ == 0)
{
uint8_t v___x_725_; uint8_t v___x_726_; 
v___x_725_ = 33;
v___x_726_ = lean_uint8_dec_eq(v_c_715_, v___x_725_);
if (v___x_726_ == 0)
{
uint8_t v___x_727_; uint8_t v___x_728_; 
v___x_727_ = 36;
v___x_728_ = lean_uint8_dec_eq(v_c_715_, v___x_727_);
if (v___x_728_ == 0)
{
uint8_t v___x_729_; uint8_t v___x_730_; 
v___x_729_ = 38;
v___x_730_ = lean_uint8_dec_eq(v_c_715_, v___x_729_);
if (v___x_730_ == 0)
{
uint8_t v___x_731_; uint8_t v___x_732_; 
v___x_731_ = 39;
v___x_732_ = lean_uint8_dec_eq(v_c_715_, v___x_731_);
if (v___x_732_ == 0)
{
uint8_t v___x_733_; uint8_t v___x_734_; 
v___x_733_ = 40;
v___x_734_ = lean_uint8_dec_eq(v_c_715_, v___x_733_);
if (v___x_734_ == 0)
{
uint8_t v___x_735_; uint8_t v___x_736_; 
v___x_735_ = 41;
v___x_736_ = lean_uint8_dec_eq(v_c_715_, v___x_735_);
if (v___x_736_ == 0)
{
uint8_t v___x_737_; uint8_t v___x_738_; 
v___x_737_ = 42;
v___x_738_ = lean_uint8_dec_eq(v_c_715_, v___x_737_);
if (v___x_738_ == 0)
{
uint8_t v___x_739_; uint8_t v___x_740_; 
v___x_739_ = 43;
v___x_740_ = lean_uint8_dec_eq(v_c_715_, v___x_739_);
if (v___x_740_ == 0)
{
uint8_t v___x_741_; uint8_t v___x_742_; 
v___x_741_ = 44;
v___x_742_ = lean_uint8_dec_eq(v_c_715_, v___x_741_);
if (v___x_742_ == 0)
{
uint8_t v___x_743_; uint8_t v___x_744_; 
v___x_743_ = 59;
v___x_744_ = lean_uint8_dec_eq(v_c_715_, v___x_743_);
if (v___x_744_ == 0)
{
uint8_t v___x_745_; uint8_t v___x_746_; 
v___x_745_ = 61;
v___x_746_ = lean_uint8_dec_eq(v_c_715_, v___x_745_);
if (v___x_746_ == 0)
{
uint8_t v___x_747_; uint8_t v___x_748_; 
v___x_747_ = 58;
v___x_748_ = lean_uint8_dec_eq(v_c_715_, v___x_747_);
return v___x_748_;
}
else
{
return v___x_746_;
}
}
else
{
return v___x_744_;
}
}
else
{
return v___x_742_;
}
}
else
{
return v___x_740_;
}
}
else
{
return v___x_738_;
}
}
else
{
return v___x_736_;
}
}
else
{
return v___x_734_;
}
}
else
{
return v___x_732_;
}
}
else
{
return v___x_730_;
}
}
else
{
return v___x_728_;
}
}
else
{
return v___x_726_;
}
}
else
{
return v___x_724_;
}
}
else
{
return v___x_722_;
}
}
else
{
return v___x_720_;
}
}
else
{
return v___x_718_;
}
}
v___jp_749_:
{
uint8_t v___x_750_; uint8_t v___x_751_; 
v___x_750_ = 65;
v___x_751_ = lean_uint8_dec_le(v___x_750_, v_c_715_);
if (v___x_751_ == 0)
{
goto v___jp_716_;
}
else
{
uint8_t v___x_752_; uint8_t v___x_753_; 
v___x_752_ = 90;
v___x_753_ = lean_uint8_dec_le(v_c_715_, v___x_752_);
if (v___x_753_ == 0)
{
goto v___jp_716_;
}
else
{
return v___x_753_;
}
}
}
v___jp_754_:
{
uint8_t v___x_755_; uint8_t v___x_756_; 
v___x_755_ = 97;
v___x_756_ = lean_uint8_dec_le(v___x_755_, v_c_715_);
if (v___x_756_ == 0)
{
goto v___jp_749_;
}
else
{
uint8_t v___x_757_; uint8_t v___x_758_; 
v___x_757_ = 122;
v___x_758_ = lean_uint8_dec_le(v_c_715_, v___x_757_);
if (v___x_758_ == 0)
{
goto v___jp_749_;
}
else
{
return v___x_758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUserInfoChar___boxed(lean_object* v_c_763_){
_start:
{
uint8_t v_c_boxed_764_; uint8_t v_res_765_; lean_object* v_r_766_; 
v_c_boxed_764_ = lean_unbox(v_c_763_);
v_res_765_ = l_Std_Http_Internal_Char_isUserInfoChar(v_c_boxed_764_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryDataChar(uint8_t v_c_767_){
_start:
{
uint8_t v___x_822_; uint8_t v___x_823_; 
v___x_822_ = 48;
v___x_823_ = lean_uint8_dec_le(v___x_822_, v_c_767_);
if (v___x_823_ == 0)
{
goto v___jp_817_;
}
else
{
uint8_t v___x_824_; uint8_t v___x_825_; 
v___x_824_ = 57;
v___x_825_ = lean_uint8_dec_le(v_c_767_, v___x_824_);
if (v___x_825_ == 0)
{
goto v___jp_817_;
}
else
{
goto v___jp_768_;
}
}
v___jp_768_:
{
uint8_t v___x_769_; uint8_t v___x_770_; 
v___x_769_ = 38;
v___x_770_ = lean_uint8_dec_eq(v_c_767_, v___x_769_);
if (v___x_770_ == 0)
{
uint8_t v___x_771_; 
v___x_771_ = 1;
return v___x_771_;
}
else
{
uint8_t v___x_772_; 
v___x_772_ = 0;
return v___x_772_;
}
}
v___jp_773_:
{
uint8_t v___x_774_; uint8_t v___x_775_; 
v___x_774_ = 45;
v___x_775_ = lean_uint8_dec_eq(v_c_767_, v___x_774_);
if (v___x_775_ == 0)
{
uint8_t v___x_776_; uint8_t v___x_777_; 
v___x_776_ = 46;
v___x_777_ = lean_uint8_dec_eq(v_c_767_, v___x_776_);
if (v___x_777_ == 0)
{
uint8_t v___x_778_; uint8_t v___x_779_; 
v___x_778_ = 95;
v___x_779_ = lean_uint8_dec_eq(v_c_767_, v___x_778_);
if (v___x_779_ == 0)
{
uint8_t v___x_780_; uint8_t v___x_781_; 
v___x_780_ = 126;
v___x_781_ = lean_uint8_dec_eq(v_c_767_, v___x_780_);
if (v___x_781_ == 0)
{
uint8_t v___x_782_; uint8_t v___x_783_; 
v___x_782_ = 33;
v___x_783_ = lean_uint8_dec_eq(v_c_767_, v___x_782_);
if (v___x_783_ == 0)
{
uint8_t v___x_784_; uint8_t v___x_785_; 
v___x_784_ = 36;
v___x_785_ = lean_uint8_dec_eq(v_c_767_, v___x_784_);
if (v___x_785_ == 0)
{
uint8_t v___x_786_; uint8_t v___x_787_; 
v___x_786_ = 38;
v___x_787_ = lean_uint8_dec_eq(v_c_767_, v___x_786_);
if (v___x_787_ == 0)
{
uint8_t v___x_788_; uint8_t v___x_789_; 
v___x_788_ = 39;
v___x_789_ = lean_uint8_dec_eq(v_c_767_, v___x_788_);
if (v___x_789_ == 0)
{
uint8_t v___x_790_; uint8_t v___x_791_; 
v___x_790_ = 40;
v___x_791_ = lean_uint8_dec_eq(v_c_767_, v___x_790_);
if (v___x_791_ == 0)
{
uint8_t v___x_792_; uint8_t v___x_793_; 
v___x_792_ = 41;
v___x_793_ = lean_uint8_dec_eq(v_c_767_, v___x_792_);
if (v___x_793_ == 0)
{
uint8_t v___x_794_; uint8_t v___x_795_; 
v___x_794_ = 42;
v___x_795_ = lean_uint8_dec_eq(v_c_767_, v___x_794_);
if (v___x_795_ == 0)
{
uint8_t v___x_796_; uint8_t v___x_797_; 
v___x_796_ = 43;
v___x_797_ = lean_uint8_dec_eq(v_c_767_, v___x_796_);
if (v___x_797_ == 0)
{
uint8_t v___x_798_; uint8_t v___x_799_; 
v___x_798_ = 44;
v___x_799_ = lean_uint8_dec_eq(v_c_767_, v___x_798_);
if (v___x_799_ == 0)
{
uint8_t v___x_800_; uint8_t v___x_801_; 
v___x_800_ = 59;
v___x_801_ = lean_uint8_dec_eq(v_c_767_, v___x_800_);
if (v___x_801_ == 0)
{
uint8_t v___x_802_; uint8_t v___x_803_; 
v___x_802_ = 61;
v___x_803_ = lean_uint8_dec_eq(v_c_767_, v___x_802_);
if (v___x_803_ == 0)
{
uint8_t v___x_804_; uint8_t v___x_805_; 
v___x_804_ = 58;
v___x_805_ = lean_uint8_dec_eq(v_c_767_, v___x_804_);
if (v___x_805_ == 0)
{
uint8_t v___x_806_; uint8_t v___x_807_; 
v___x_806_ = 64;
v___x_807_ = lean_uint8_dec_eq(v_c_767_, v___x_806_);
if (v___x_807_ == 0)
{
uint8_t v___x_808_; uint8_t v___x_809_; 
v___x_808_ = 47;
v___x_809_ = lean_uint8_dec_eq(v_c_767_, v___x_808_);
if (v___x_809_ == 0)
{
uint8_t v___x_810_; uint8_t v___x_811_; 
v___x_810_ = 63;
v___x_811_ = lean_uint8_dec_eq(v_c_767_, v___x_810_);
if (v___x_811_ == 0)
{
return v___x_811_;
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
else
{
goto v___jp_768_;
}
}
v___jp_812_:
{
uint8_t v___x_813_; uint8_t v___x_814_; 
v___x_813_ = 65;
v___x_814_ = lean_uint8_dec_le(v___x_813_, v_c_767_);
if (v___x_814_ == 0)
{
goto v___jp_773_;
}
else
{
uint8_t v___x_815_; uint8_t v___x_816_; 
v___x_815_ = 90;
v___x_816_ = lean_uint8_dec_le(v_c_767_, v___x_815_);
if (v___x_816_ == 0)
{
goto v___jp_773_;
}
else
{
goto v___jp_768_;
}
}
}
v___jp_817_:
{
uint8_t v___x_818_; uint8_t v___x_819_; 
v___x_818_ = 97;
v___x_819_ = lean_uint8_dec_le(v___x_818_, v_c_767_);
if (v___x_819_ == 0)
{
goto v___jp_812_;
}
else
{
uint8_t v___x_820_; uint8_t v___x_821_; 
v___x_820_ = 122;
v___x_821_ = lean_uint8_dec_le(v_c_767_, v___x_820_);
if (v___x_821_ == 0)
{
goto v___jp_812_;
}
else
{
goto v___jp_768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryDataChar___boxed(lean_object* v_c_826_){
_start:
{
uint8_t v_c_boxed_827_; uint8_t v_res_828_; lean_object* v_r_829_; 
v_c_boxed_827_ = lean_unbox(v_c_826_);
v_res_828_ = l_Std_Http_Internal_Char_isQueryDataChar(v_c_boxed_827_);
v_r_829_ = lean_box(v_res_828_);
return v_r_829_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryNameChar(uint8_t v_c_830_){
_start:
{
uint8_t v___x_887_; uint8_t v___x_888_; 
v___x_887_ = 48;
v___x_888_ = lean_uint8_dec_le(v___x_887_, v_c_830_);
if (v___x_888_ == 0)
{
goto v___jp_882_;
}
else
{
uint8_t v___x_889_; uint8_t v___x_890_; 
v___x_889_ = 57;
v___x_890_ = lean_uint8_dec_le(v_c_830_, v___x_889_);
if (v___x_890_ == 0)
{
goto v___jp_882_;
}
else
{
goto v___jp_831_;
}
}
v___jp_831_:
{
uint8_t v___x_832_; uint8_t v___x_833_; 
v___x_832_ = 38;
v___x_833_ = lean_uint8_dec_eq(v_c_830_, v___x_832_);
if (v___x_833_ == 0)
{
uint8_t v___x_834_; uint8_t v___x_835_; 
v___x_834_ = 61;
v___x_835_ = lean_uint8_dec_eq(v_c_830_, v___x_834_);
if (v___x_835_ == 0)
{
uint8_t v___x_836_; 
v___x_836_ = 1;
return v___x_836_;
}
else
{
return v___x_833_;
}
}
else
{
uint8_t v___x_837_; 
v___x_837_ = 0;
return v___x_837_;
}
}
v___jp_838_:
{
uint8_t v___x_839_; uint8_t v___x_840_; 
v___x_839_ = 45;
v___x_840_ = lean_uint8_dec_eq(v_c_830_, v___x_839_);
if (v___x_840_ == 0)
{
uint8_t v___x_841_; uint8_t v___x_842_; 
v___x_841_ = 46;
v___x_842_ = lean_uint8_dec_eq(v_c_830_, v___x_841_);
if (v___x_842_ == 0)
{
uint8_t v___x_843_; uint8_t v___x_844_; 
v___x_843_ = 95;
v___x_844_ = lean_uint8_dec_eq(v_c_830_, v___x_843_);
if (v___x_844_ == 0)
{
uint8_t v___x_845_; uint8_t v___x_846_; 
v___x_845_ = 126;
v___x_846_ = lean_uint8_dec_eq(v_c_830_, v___x_845_);
if (v___x_846_ == 0)
{
uint8_t v___x_847_; uint8_t v___x_848_; 
v___x_847_ = 33;
v___x_848_ = lean_uint8_dec_eq(v_c_830_, v___x_847_);
if (v___x_848_ == 0)
{
uint8_t v___x_849_; uint8_t v___x_850_; 
v___x_849_ = 36;
v___x_850_ = lean_uint8_dec_eq(v_c_830_, v___x_849_);
if (v___x_850_ == 0)
{
uint8_t v___x_851_; uint8_t v___x_852_; 
v___x_851_ = 38;
v___x_852_ = lean_uint8_dec_eq(v_c_830_, v___x_851_);
if (v___x_852_ == 0)
{
uint8_t v___x_853_; uint8_t v___x_854_; 
v___x_853_ = 39;
v___x_854_ = lean_uint8_dec_eq(v_c_830_, v___x_853_);
if (v___x_854_ == 0)
{
uint8_t v___x_855_; uint8_t v___x_856_; 
v___x_855_ = 40;
v___x_856_ = lean_uint8_dec_eq(v_c_830_, v___x_855_);
if (v___x_856_ == 0)
{
uint8_t v___x_857_; uint8_t v___x_858_; 
v___x_857_ = 41;
v___x_858_ = lean_uint8_dec_eq(v_c_830_, v___x_857_);
if (v___x_858_ == 0)
{
uint8_t v___x_859_; uint8_t v___x_860_; 
v___x_859_ = 42;
v___x_860_ = lean_uint8_dec_eq(v_c_830_, v___x_859_);
if (v___x_860_ == 0)
{
uint8_t v___x_861_; uint8_t v___x_862_; 
v___x_861_ = 43;
v___x_862_ = lean_uint8_dec_eq(v_c_830_, v___x_861_);
if (v___x_862_ == 0)
{
uint8_t v___x_863_; uint8_t v___x_864_; 
v___x_863_ = 44;
v___x_864_ = lean_uint8_dec_eq(v_c_830_, v___x_863_);
if (v___x_864_ == 0)
{
uint8_t v___x_865_; uint8_t v___x_866_; 
v___x_865_ = 59;
v___x_866_ = lean_uint8_dec_eq(v_c_830_, v___x_865_);
if (v___x_866_ == 0)
{
uint8_t v___x_867_; uint8_t v___x_868_; 
v___x_867_ = 61;
v___x_868_ = lean_uint8_dec_eq(v_c_830_, v___x_867_);
if (v___x_868_ == 0)
{
uint8_t v___x_869_; uint8_t v___x_870_; 
v___x_869_ = 58;
v___x_870_ = lean_uint8_dec_eq(v_c_830_, v___x_869_);
if (v___x_870_ == 0)
{
uint8_t v___x_871_; uint8_t v___x_872_; 
v___x_871_ = 64;
v___x_872_ = lean_uint8_dec_eq(v_c_830_, v___x_871_);
if (v___x_872_ == 0)
{
uint8_t v___x_873_; uint8_t v___x_874_; 
v___x_873_ = 47;
v___x_874_ = lean_uint8_dec_eq(v_c_830_, v___x_873_);
if (v___x_874_ == 0)
{
uint8_t v___x_875_; uint8_t v___x_876_; 
v___x_875_ = 63;
v___x_876_ = lean_uint8_dec_eq(v_c_830_, v___x_875_);
if (v___x_876_ == 0)
{
return v___x_876_;
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
v___jp_877_:
{
uint8_t v___x_878_; uint8_t v___x_879_; 
v___x_878_ = 65;
v___x_879_ = lean_uint8_dec_le(v___x_878_, v_c_830_);
if (v___x_879_ == 0)
{
goto v___jp_838_;
}
else
{
uint8_t v___x_880_; uint8_t v___x_881_; 
v___x_880_ = 90;
v___x_881_ = lean_uint8_dec_le(v_c_830_, v___x_880_);
if (v___x_881_ == 0)
{
goto v___jp_838_;
}
else
{
goto v___jp_831_;
}
}
}
v___jp_882_:
{
uint8_t v___x_883_; uint8_t v___x_884_; 
v___x_883_ = 97;
v___x_884_ = lean_uint8_dec_le(v___x_883_, v_c_830_);
if (v___x_884_ == 0)
{
goto v___jp_877_;
}
else
{
uint8_t v___x_885_; uint8_t v___x_886_; 
v___x_885_ = 122;
v___x_886_ = lean_uint8_dec_le(v_c_830_, v___x_885_);
if (v___x_886_ == 0)
{
goto v___jp_877_;
}
else
{
goto v___jp_831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryNameChar___boxed(lean_object* v_c_891_){
_start:
{
uint8_t v_c_boxed_892_; uint8_t v_res_893_; lean_object* v_r_894_; 
v_c_boxed_892_ = lean_unbox(v_c_891_);
v_res_893_ = l_Std_Http_Internal_Char_isQueryNameChar(v_c_boxed_892_);
v_r_894_ = lean_box(v_res_893_);
return v_r_894_;
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
