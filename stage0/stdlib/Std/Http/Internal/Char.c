// Lean compiler output
// Module: Std.Http.Internal.Char
// Imports: public import Init.Data.Char public import Init.Data.String.Basic public import Init.Data.Int public import Init.Grind
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
uint8_t lean_uint32_to_uint8(uint32_t);
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
static lean_once_cell_t l_Std_Http_Internal_Char_isDigitByte___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isDigitByte___closed__0;
static lean_once_cell_t l_Std_Http_Internal_Char_isDigitByte___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isDigitByte___closed__1;
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isDigitByte(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isDigitByte___boxed(lean_object*);
static lean_once_cell_t l_Std_Http_Internal_Char_isAlphaByte___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isAlphaByte___closed__0;
static lean_once_cell_t l_Std_Http_Internal_Char_isAlphaByte___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isAlphaByte___closed__1;
static lean_once_cell_t l_Std_Http_Internal_Char_isAlphaByte___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isAlphaByte___closed__2;
static lean_once_cell_t l_Std_Http_Internal_Char_isAlphaByte___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isAlphaByte___closed__3;
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
static lean_once_cell_t l_Std_Http_Internal_Char_isHexDigitByte___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isHexDigitByte___closed__0;
static lean_once_cell_t l_Std_Http_Internal_Char_isHexDigitByte___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isHexDigitByte___closed__1;
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
static lean_once_cell_t l_Std_Http_Internal_Char_isUnreserved___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isUnreserved___closed__0;
static lean_once_cell_t l_Std_Http_Internal_Char_isUnreserved___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isUnreserved___closed__1;
static lean_once_cell_t l_Std_Http_Internal_Char_isUnreserved___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isUnreserved___closed__2;
static lean_once_cell_t l_Std_Http_Internal_Char_isUnreserved___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isUnreserved___closed__3;
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUnreserved(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUnreserved___boxed(lean_object*);
static lean_once_cell_t l_Std_Http_Internal_Char_isSubDelims___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isSubDelims___closed__0;
static lean_once_cell_t l_Std_Http_Internal_Char_isSubDelims___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isSubDelims___closed__1;
static lean_once_cell_t l_Std_Http_Internal_Char_isSubDelims___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isSubDelims___closed__2;
static lean_once_cell_t l_Std_Http_Internal_Char_isSubDelims___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isSubDelims___closed__3;
static lean_once_cell_t l_Std_Http_Internal_Char_isSubDelims___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isSubDelims___closed__4;
static lean_once_cell_t l_Std_Http_Internal_Char_isSubDelims___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isSubDelims___closed__5;
static lean_once_cell_t l_Std_Http_Internal_Char_isSubDelims___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isSubDelims___closed__6;
static lean_once_cell_t l_Std_Http_Internal_Char_isSubDelims___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isSubDelims___closed__7;
static lean_once_cell_t l_Std_Http_Internal_Char_isSubDelims___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isSubDelims___closed__8;
static lean_once_cell_t l_Std_Http_Internal_Char_isSubDelims___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isSubDelims___closed__9;
static lean_once_cell_t l_Std_Http_Internal_Char_isSubDelims___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isSubDelims___closed__10;
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isSubDelims(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isSubDelims___boxed(lean_object*);
static lean_once_cell_t l_Std_Http_Internal_Char_isPChar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isPChar___closed__0;
static lean_once_cell_t l_Std_Http_Internal_Char_isPChar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isPChar___closed__1;
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isPChar(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isPChar___boxed(lean_object*);
static lean_once_cell_t l_Std_Http_Internal_Char_isQueryChar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isQueryChar___closed__0;
static lean_once_cell_t l_Std_Http_Internal_Char_isQueryChar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isQueryChar___closed__1;
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
static uint8_t _init_l_Std_Http_Internal_Char_isDigitByte___closed__0(void){
_start:
{
uint32_t v___x_16_; uint8_t v___x_17_; 
v___x_16_ = 48;
v___x_17_ = lean_uint32_to_uint8(v___x_16_);
return v___x_17_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isDigitByte___closed__1(void){
_start:
{
uint32_t v___x_18_; uint8_t v___x_19_; 
v___x_18_ = 57;
v___x_19_ = lean_uint32_to_uint8(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isDigitByte(uint8_t v_c_20_){
_start:
{
uint8_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_22_ = lean_uint8_dec_le(v___x_21_, v_c_20_);
if (v___x_22_ == 0)
{
return v___x_22_;
}
else
{
uint8_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_24_ = lean_uint8_dec_le(v_c_20_, v___x_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isDigitByte___boxed(lean_object* v_c_25_){
_start:
{
uint8_t v_c_boxed_26_; uint8_t v_res_27_; lean_object* v_r_28_; 
v_c_boxed_26_ = lean_unbox(v_c_25_);
v_res_27_ = l_Std_Http_Internal_Char_isDigitByte(v_c_boxed_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0(void){
_start:
{
uint32_t v___x_29_; uint8_t v___x_30_; 
v___x_29_ = 97;
v___x_30_ = lean_uint32_to_uint8(v___x_29_);
return v___x_30_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1(void){
_start:
{
uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 122;
v___x_32_ = lean_uint32_to_uint8(v___x_31_);
return v___x_32_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2(void){
_start:
{
uint32_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = 65;
v___x_34_ = lean_uint32_to_uint8(v___x_33_);
return v___x_34_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3(void){
_start:
{
uint32_t v___x_35_; uint8_t v___x_36_; 
v___x_35_ = 90;
v___x_36_ = lean_uint32_to_uint8(v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAlphaByte(uint8_t v_c_37_){
_start:
{
uint8_t v___x_43_; uint8_t v___x_44_; 
v___x_43_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_44_ = lean_uint8_dec_le(v___x_43_, v_c_37_);
if (v___x_44_ == 0)
{
goto v___jp_38_;
}
else
{
uint8_t v___x_45_; uint8_t v___x_46_; 
v___x_45_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
v___x_46_ = lean_uint8_dec_le(v_c_37_, v___x_45_);
if (v___x_46_ == 0)
{
goto v___jp_38_;
}
else
{
return v___x_46_;
}
}
v___jp_38_:
{
uint8_t v___x_39_; uint8_t v___x_40_; 
v___x_39_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_40_ = lean_uint8_dec_le(v___x_39_, v_c_37_);
if (v___x_40_ == 0)
{
return v___x_40_;
}
else
{
uint8_t v___x_41_; uint8_t v___x_42_; 
v___x_41_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
v___x_42_ = lean_uint8_dec_le(v_c_37_, v___x_41_);
return v___x_42_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAlphaByte___boxed(lean_object* v_c_47_){
_start:
{
uint8_t v_c_boxed_48_; uint8_t v_res_49_; lean_object* v_r_50_; 
v_c_boxed_48_ = lean_unbox(v_c_47_);
v_res_49_ = l_Std_Http_Internal_Char_isAlphaByte(v_c_boxed_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_tchar(uint32_t v_c_51_){
_start:
{
uint8_t v___y_53_; uint32_t v___x_63_; uint8_t v___x_64_; 
v___x_63_ = 33;
v___x_64_ = lean_uint32_dec_eq(v_c_51_, v___x_63_);
if (v___x_64_ == 0)
{
uint32_t v___x_65_; uint8_t v___x_66_; 
v___x_65_ = 35;
v___x_66_ = lean_uint32_dec_eq(v_c_51_, v___x_65_);
if (v___x_66_ == 0)
{
uint32_t v___x_67_; uint8_t v___x_68_; 
v___x_67_ = 36;
v___x_68_ = lean_uint32_dec_eq(v_c_51_, v___x_67_);
if (v___x_68_ == 0)
{
uint32_t v___x_69_; uint8_t v___x_70_; 
v___x_69_ = 37;
v___x_70_ = lean_uint32_dec_eq(v_c_51_, v___x_69_);
if (v___x_70_ == 0)
{
uint32_t v___x_71_; uint8_t v___x_72_; 
v___x_71_ = 38;
v___x_72_ = lean_uint32_dec_eq(v_c_51_, v___x_71_);
if (v___x_72_ == 0)
{
uint32_t v___x_73_; uint8_t v___x_74_; 
v___x_73_ = 39;
v___x_74_ = lean_uint32_dec_eq(v_c_51_, v___x_73_);
if (v___x_74_ == 0)
{
uint32_t v___x_75_; uint8_t v___x_76_; 
v___x_75_ = 42;
v___x_76_ = lean_uint32_dec_eq(v_c_51_, v___x_75_);
if (v___x_76_ == 0)
{
uint32_t v___x_77_; uint8_t v___x_78_; 
v___x_77_ = 43;
v___x_78_ = lean_uint32_dec_eq(v_c_51_, v___x_77_);
if (v___x_78_ == 0)
{
uint32_t v___x_79_; uint8_t v___x_80_; 
v___x_79_ = 45;
v___x_80_ = lean_uint32_dec_eq(v_c_51_, v___x_79_);
if (v___x_80_ == 0)
{
uint32_t v___x_81_; uint8_t v___x_82_; 
v___x_81_ = 46;
v___x_82_ = lean_uint32_dec_eq(v_c_51_, v___x_81_);
if (v___x_82_ == 0)
{
uint32_t v___x_83_; uint8_t v___x_84_; 
v___x_83_ = 94;
v___x_84_ = lean_uint32_dec_eq(v_c_51_, v___x_83_);
if (v___x_84_ == 0)
{
uint32_t v___x_85_; uint8_t v___x_86_; 
v___x_85_ = 95;
v___x_86_ = lean_uint32_dec_eq(v_c_51_, v___x_85_);
if (v___x_86_ == 0)
{
uint32_t v___x_87_; uint8_t v___x_88_; 
v___x_87_ = 96;
v___x_88_ = lean_uint32_dec_eq(v_c_51_, v___x_87_);
if (v___x_88_ == 0)
{
uint32_t v___x_89_; uint8_t v___x_90_; 
v___x_89_ = 124;
v___x_90_ = lean_uint32_dec_eq(v_c_51_, v___x_89_);
if (v___x_90_ == 0)
{
uint32_t v___x_91_; uint8_t v___x_92_; 
v___x_91_ = 126;
v___x_92_ = lean_uint32_dec_eq(v_c_51_, v___x_91_);
if (v___x_92_ == 0)
{
uint32_t v___x_93_; uint8_t v___x_94_; 
v___x_93_ = 48;
v___x_94_ = lean_uint32_dec_le(v___x_93_, v_c_51_);
if (v___x_94_ == 0)
{
goto v___jp_58_;
}
else
{
uint32_t v___x_95_; uint8_t v___x_96_; 
v___x_95_ = 57;
v___x_96_ = lean_uint32_dec_le(v_c_51_, v___x_95_);
if (v___x_96_ == 0)
{
goto v___jp_58_;
}
else
{
return v___x_96_;
}
}
}
else
{
return v___x_92_;
}
}
else
{
return v___x_90_;
}
}
else
{
return v___x_88_;
}
}
else
{
return v___x_86_;
}
}
else
{
return v___x_84_;
}
}
else
{
return v___x_82_;
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
v___jp_52_:
{
if (v___y_53_ == 0)
{
uint32_t v___x_54_; uint8_t v___x_55_; 
v___x_54_ = 97;
v___x_55_ = lean_uint32_dec_le(v___x_54_, v_c_51_);
if (v___x_55_ == 0)
{
return v___x_55_;
}
else
{
uint32_t v___x_56_; uint8_t v___x_57_; 
v___x_56_ = 122;
v___x_57_ = lean_uint32_dec_le(v_c_51_, v___x_56_);
return v___x_57_;
}
}
else
{
return v___y_53_;
}
}
v___jp_58_:
{
uint32_t v___x_59_; uint8_t v___x_60_; 
v___x_59_ = 65;
v___x_60_ = lean_uint32_dec_le(v___x_59_, v_c_51_);
if (v___x_60_ == 0)
{
v___y_53_ = v___x_60_;
goto v___jp_52_;
}
else
{
uint32_t v___x_61_; uint8_t v___x_62_; 
v___x_61_ = 90;
v___x_62_ = lean_uint32_dec_le(v_c_51_, v___x_61_);
v___y_53_ = v___x_62_;
goto v___jp_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_tchar___boxed(lean_object* v_c_97_){
_start:
{
uint32_t v_c_boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v_c_boxed_98_ = lean_unbox_uint32(v_c_97_);
lean_dec(v_c_97_);
v_res_99_ = l_Std_Http_Internal_Char_tchar(v_c_boxed_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_vchar(uint32_t v_c_101_){
_start:
{
uint32_t v___x_102_; uint8_t v___x_103_; 
v___x_102_ = 33;
v___x_103_ = lean_uint32_dec_le(v___x_102_, v_c_101_);
if (v___x_103_ == 0)
{
return v___x_103_;
}
else
{
uint32_t v___x_104_; uint8_t v___x_105_; 
v___x_104_ = 126;
v___x_105_ = lean_uint32_dec_le(v_c_101_, v___x_104_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_vchar___boxed(lean_object* v_c_106_){
_start:
{
uint32_t v_c_boxed_107_; uint8_t v_res_108_; lean_object* v_r_109_; 
v_c_boxed_107_ = lean_unbox_uint32(v_c_106_);
lean_dec(v_c_106_);
v_res_108_ = l_Std_Http_Internal_Char_vchar(v_c_boxed_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_qdtext(uint32_t v_c_110_){
_start:
{
uint8_t v___y_112_; uint32_t v___x_117_; uint8_t v___x_118_; 
v___x_117_ = 9;
v___x_118_ = lean_uint32_dec_eq(v_c_110_, v___x_117_);
if (v___x_118_ == 0)
{
uint32_t v___x_119_; uint8_t v___x_120_; 
v___x_119_ = 32;
v___x_120_ = lean_uint32_dec_eq(v_c_110_, v___x_119_);
if (v___x_120_ == 0)
{
uint32_t v___x_121_; uint8_t v___x_122_; 
v___x_121_ = 33;
v___x_122_ = lean_uint32_dec_eq(v_c_110_, v___x_121_);
if (v___x_122_ == 0)
{
uint32_t v___x_123_; uint8_t v___x_124_; 
v___x_123_ = 35;
v___x_124_ = lean_uint32_dec_le(v___x_123_, v_c_110_);
if (v___x_124_ == 0)
{
v___y_112_ = v___x_124_;
goto v___jp_111_;
}
else
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 91;
v___x_126_ = lean_uint32_dec_le(v_c_110_, v___x_125_);
v___y_112_ = v___x_126_;
goto v___jp_111_;
}
}
else
{
return v___x_122_;
}
}
else
{
return v___x_120_;
}
}
else
{
return v___x_118_;
}
v___jp_111_:
{
if (v___y_112_ == 0)
{
uint32_t v___x_113_; uint8_t v___x_114_; 
v___x_113_ = 93;
v___x_114_ = lean_uint32_dec_le(v___x_113_, v_c_110_);
if (v___x_114_ == 0)
{
return v___x_114_;
}
else
{
uint32_t v___x_115_; uint8_t v___x_116_; 
v___x_115_ = 126;
v___x_116_ = lean_uint32_dec_le(v_c_110_, v___x_115_);
return v___x_116_;
}
}
else
{
return v___y_112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_qdtext___boxed(lean_object* v_c_127_){
_start:
{
uint32_t v_c_boxed_128_; uint8_t v_res_129_; lean_object* v_r_130_; 
v_c_boxed_128_ = lean_unbox_uint32(v_c_127_);
lean_dec(v_c_127_);
v_res_129_ = l_Std_Http_Internal_Char_qdtext(v_c_boxed_128_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_quotedPairChar(uint32_t v_c_131_){
_start:
{
uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 9;
v___x_133_ = lean_uint32_dec_eq(v_c_131_, v___x_132_);
if (v___x_133_ == 0)
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 32;
v___x_135_ = lean_uint32_dec_eq(v_c_131_, v___x_134_);
if (v___x_135_ == 0)
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 33;
v___x_137_ = lean_uint32_dec_le(v___x_136_, v_c_131_);
if (v___x_137_ == 0)
{
return v___x_137_;
}
else
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 126;
v___x_139_ = lean_uint32_dec_le(v_c_131_, v___x_138_);
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
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_quotedPairChar___boxed(lean_object* v_c_140_){
_start:
{
uint32_t v_c_boxed_141_; uint8_t v_res_142_; lean_object* v_r_143_; 
v_c_boxed_141_ = lean_unbox_uint32(v_c_140_);
lean_dec(v_c_140_);
v_res_142_ = l_Std_Http_Internal_Char_quotedPairChar(v_c_boxed_141_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_quotedStringChar(uint32_t v_c_144_){
_start:
{
uint32_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = 9;
v___x_146_ = lean_uint32_dec_eq(v_c_144_, v___x_145_);
if (v___x_146_ == 0)
{
uint32_t v___x_147_; uint8_t v___x_148_; 
v___x_147_ = 32;
v___x_148_ = lean_uint32_dec_eq(v_c_144_, v___x_147_);
if (v___x_148_ == 0)
{
uint32_t v___x_149_; uint8_t v___y_151_; uint8_t v___y_152_; uint8_t v___y_155_; uint8_t v___x_160_; 
v___x_149_ = 33;
v___x_160_ = lean_uint32_dec_eq(v_c_144_, v___x_149_);
if (v___x_160_ == 0)
{
uint32_t v___x_161_; uint8_t v___x_162_; 
v___x_161_ = 35;
v___x_162_ = lean_uint32_dec_le(v___x_161_, v_c_144_);
if (v___x_162_ == 0)
{
v___y_155_ = v___x_162_;
goto v___jp_154_;
}
else
{
uint32_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 91;
v___x_164_ = lean_uint32_dec_le(v_c_144_, v___x_163_);
v___y_155_ = v___x_164_;
goto v___jp_154_;
}
}
else
{
return v___x_160_;
}
v___jp_150_:
{
if (v___y_152_ == 0)
{
if (v___x_146_ == 0)
{
if (v___x_148_ == 0)
{
uint8_t v___x_153_; 
v___x_153_ = lean_uint32_dec_le(v___x_149_, v_c_144_);
if (v___x_153_ == 0)
{
return v___x_153_;
}
else
{
return v___y_151_;
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
}
else
{
return v___y_152_;
}
}
v___jp_154_:
{
if (v___y_155_ == 0)
{
uint32_t v___x_156_; uint8_t v___x_157_; uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_156_ = 93;
v___x_157_ = lean_uint32_dec_le(v___x_156_, v_c_144_);
v___x_158_ = 126;
v___x_159_ = lean_uint32_dec_le(v_c_144_, v___x_158_);
if (v___x_157_ == 0)
{
v___y_151_ = v___x_159_;
v___y_152_ = v___x_157_;
goto v___jp_150_;
}
else
{
v___y_151_ = v___x_159_;
v___y_152_ = v___x_159_;
goto v___jp_150_;
}
}
else
{
return v___y_155_;
}
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
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_quotedStringChar___boxed(lean_object* v_c_165_){
_start:
{
uint32_t v_c_boxed_166_; uint8_t v_res_167_; lean_object* v_r_168_; 
v_c_boxed_166_ = lean_unbox_uint32(v_c_165_);
lean_dec(v_c_165_);
v_res_167_ = l_Std_Http_Internal_Char_quotedStringChar(v_c_boxed_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg(uint32_t v_c_169_, lean_object* v_h__1_170_, lean_object* v_h__2_171_, lean_object* v_h__3_172_, lean_object* v_h__4_173_){
_start:
{
uint32_t v___x_174_; uint8_t v___x_175_; 
v___x_174_ = 9;
v___x_175_ = lean_uint32_dec_eq(v_c_169_, v___x_174_);
if (v___x_175_ == 0)
{
uint32_t v___x_176_; uint8_t v___x_177_; 
lean_dec(v_h__1_170_);
v___x_176_ = 32;
v___x_177_ = lean_uint32_dec_eq(v_c_169_, v___x_176_);
if (v___x_177_ == 0)
{
uint32_t v___x_178_; uint8_t v___x_179_; 
lean_dec(v_h__2_171_);
v___x_178_ = 33;
v___x_179_ = lean_uint32_dec_eq(v_c_169_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_h__3_172_);
v___x_180_ = lean_box_uint32(v_c_169_);
v___x_181_ = lean_apply_4(v_h__4_173_, v___x_180_, lean_box(0), lean_box(0), lean_box(0));
return v___x_181_;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec(v_h__4_173_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_apply_1(v_h__3_172_, v___x_182_);
return v___x_183_;
}
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec(v_h__4_173_);
lean_dec(v_h__3_172_);
v___x_184_ = lean_box(0);
v___x_185_ = lean_apply_1(v_h__2_171_, v___x_184_);
return v___x_185_;
}
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec(v_h__4_173_);
lean_dec(v_h__3_172_);
lean_dec(v_h__2_171_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_apply_1(v_h__1_170_, v___x_186_);
return v___x_187_;
}
}
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
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(lean_object* v_motive_195_, uint32_t v_c_196_, lean_object* v_h__1_197_, lean_object* v_h__2_198_, lean_object* v_h__3_199_, lean_object* v_h__4_200_){
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
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___boxed(lean_object* v_motive_215_, lean_object* v_c_216_, lean_object* v_h__1_217_, lean_object* v_h__2_218_, lean_object* v_h__3_219_, lean_object* v_h__4_220_){
_start:
{
uint32_t v_c_104__boxed_221_; lean_object* v_res_222_; 
v_c_104__boxed_221_ = lean_unbox_uint32(v_c_216_);
lean_dec(v_c_216_);
v_res_222_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(v_motive_215_, v_c_104__boxed_221_, v_h__1_217_, v_h__2_218_, v_h__3_219_, v_h__4_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(uint32_t v_c_223_, lean_object* v_h__1_224_, lean_object* v_h__2_225_, lean_object* v_h__3_226_){
_start:
{
uint32_t v___x_227_; uint8_t v___x_228_; 
v___x_227_ = 9;
v___x_228_ = lean_uint32_dec_eq(v_c_223_, v___x_227_);
if (v___x_228_ == 0)
{
uint32_t v___x_229_; uint8_t v___x_230_; 
lean_dec(v_h__1_224_);
v___x_229_ = 32;
v___x_230_ = lean_uint32_dec_eq(v_c_223_, v___x_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec(v_h__2_225_);
v___x_231_ = lean_box_uint32(v_c_223_);
v___x_232_ = lean_apply_3(v_h__3_226_, v___x_231_, lean_box(0), lean_box(0));
return v___x_232_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v_h__3_226_);
v___x_233_ = lean_box(0);
v___x_234_ = lean_apply_1(v_h__2_225_, v___x_233_);
return v___x_234_;
}
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec(v_h__3_226_);
lean_dec(v_h__2_225_);
v___x_235_ = lean_box(0);
v___x_236_ = lean_apply_1(v_h__1_224_, v___x_235_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg___boxed(lean_object* v_c_237_, lean_object* v_h__1_238_, lean_object* v_h__2_239_, lean_object* v_h__3_240_){
_start:
{
uint32_t v_c_51__boxed_241_; lean_object* v_res_242_; 
v_c_51__boxed_241_ = lean_unbox_uint32(v_c_237_);
lean_dec(v_c_237_);
v_res_242_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(v_c_51__boxed_241_, v_h__1_238_, v_h__2_239_, v_h__3_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(lean_object* v_motive_243_, uint32_t v_c_244_, lean_object* v_h__1_245_, lean_object* v_h__2_246_, lean_object* v_h__3_247_){
_start:
{
uint32_t v___x_248_; uint8_t v___x_249_; 
v___x_248_ = 9;
v___x_249_ = lean_uint32_dec_eq(v_c_244_, v___x_248_);
if (v___x_249_ == 0)
{
uint32_t v___x_250_; uint8_t v___x_251_; 
lean_dec(v_h__1_245_);
v___x_250_ = 32;
v___x_251_ = lean_uint32_dec_eq(v_c_244_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec(v_h__2_246_);
v___x_252_ = lean_box_uint32(v_c_244_);
v___x_253_ = lean_apply_3(v_h__3_247_, v___x_252_, lean_box(0), lean_box(0));
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v_h__3_247_);
v___x_254_ = lean_box(0);
v___x_255_ = lean_apply_1(v_h__2_246_, v___x_254_);
return v___x_255_;
}
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec(v_h__3_247_);
lean_dec(v_h__2_246_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_apply_1(v_h__1_245_, v___x_256_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___boxed(lean_object* v_motive_258_, lean_object* v_c_259_, lean_object* v_h__1_260_, lean_object* v_h__2_261_, lean_object* v_h__3_262_){
_start:
{
uint32_t v_c_74__boxed_263_; lean_object* v_res_264_; 
v_c_74__boxed_263_ = lean_unbox_uint32(v_c_259_);
lean_dec(v_c_259_);
v_res_264_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(v_motive_258_, v_c_74__boxed_263_, v_h__1_260_, v_h__2_261_, v_h__3_262_);
return v_res_264_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_fieldVchar(uint32_t v_c_265_){
_start:
{
uint32_t v___x_266_; uint8_t v___x_267_; 
v___x_266_ = 33;
v___x_267_ = lean_uint32_dec_le(v___x_266_, v_c_265_);
if (v___x_267_ == 0)
{
return v___x_267_;
}
else
{
uint32_t v___x_268_; uint8_t v___x_269_; 
v___x_268_ = 126;
v___x_269_ = lean_uint32_dec_le(v_c_265_, v___x_268_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldVchar___boxed(lean_object* v_c_270_){
_start:
{
uint32_t v_c_boxed_271_; uint8_t v_res_272_; lean_object* v_r_273_; 
v_c_boxed_271_ = lean_unbox_uint32(v_c_270_);
lean_dec(v_c_270_);
v_res_272_ = l_Std_Http_Internal_Char_fieldVchar(v_c_boxed_271_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_fieldContent(uint32_t v_c_274_){
_start:
{
uint8_t v___y_276_; uint32_t v___x_281_; uint8_t v___x_282_; 
v___x_281_ = 33;
v___x_282_ = lean_uint32_dec_le(v___x_281_, v_c_274_);
if (v___x_282_ == 0)
{
v___y_276_ = v___x_282_;
goto v___jp_275_;
}
else
{
uint32_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = 126;
v___x_284_ = lean_uint32_dec_le(v_c_274_, v___x_283_);
v___y_276_ = v___x_284_;
goto v___jp_275_;
}
v___jp_275_:
{
if (v___y_276_ == 0)
{
uint32_t v___x_277_; uint8_t v___x_278_; 
v___x_277_ = 32;
v___x_278_ = lean_uint32_dec_eq(v_c_274_, v___x_277_);
if (v___x_278_ == 0)
{
uint32_t v___x_279_; uint8_t v___x_280_; 
v___x_279_ = 9;
v___x_280_ = lean_uint32_dec_eq(v_c_274_, v___x_279_);
return v___x_280_;
}
else
{
return v___x_278_;
}
}
else
{
return v___y_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldContent___boxed(lean_object* v_c_285_){
_start:
{
uint32_t v_c_boxed_286_; uint8_t v_res_287_; lean_object* v_r_288_; 
v_c_boxed_286_ = lean_unbox_uint32(v_c_285_);
lean_dec(v_c_285_);
v_res_287_ = l_Std_Http_Internal_Char_fieldContent(v_c_boxed_286_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_ctext(uint32_t v_c_289_){
_start:
{
uint8_t v___y_291_; uint8_t v___y_297_; uint32_t v___x_302_; uint8_t v___x_303_; 
v___x_302_ = 9;
v___x_303_ = lean_uint32_dec_eq(v_c_289_, v___x_302_);
if (v___x_303_ == 0)
{
uint32_t v___x_304_; uint8_t v___x_305_; 
v___x_304_ = 32;
v___x_305_ = lean_uint32_dec_eq(v_c_289_, v___x_304_);
if (v___x_305_ == 0)
{
uint32_t v___x_306_; uint8_t v___x_307_; 
v___x_306_ = 33;
v___x_307_ = lean_uint32_dec_le(v___x_306_, v_c_289_);
if (v___x_307_ == 0)
{
v___y_297_ = v___x_307_;
goto v___jp_296_;
}
else
{
uint32_t v___x_308_; uint8_t v___x_309_; 
v___x_308_ = 39;
v___x_309_ = lean_uint32_dec_le(v_c_289_, v___x_308_);
v___y_297_ = v___x_309_;
goto v___jp_296_;
}
}
else
{
return v___x_305_;
}
}
else
{
return v___x_303_;
}
v___jp_290_:
{
if (v___y_291_ == 0)
{
uint32_t v___x_292_; uint8_t v___x_293_; 
v___x_292_ = 93;
v___x_293_ = lean_uint32_dec_le(v___x_292_, v_c_289_);
if (v___x_293_ == 0)
{
return v___x_293_;
}
else
{
uint32_t v___x_294_; uint8_t v___x_295_; 
v___x_294_ = 126;
v___x_295_ = lean_uint32_dec_le(v_c_289_, v___x_294_);
return v___x_295_;
}
}
else
{
return v___y_291_;
}
}
v___jp_296_:
{
if (v___y_297_ == 0)
{
uint32_t v___x_298_; uint8_t v___x_299_; 
v___x_298_ = 42;
v___x_299_ = lean_uint32_dec_le(v___x_298_, v_c_289_);
if (v___x_299_ == 0)
{
v___y_291_ = v___x_299_;
goto v___jp_290_;
}
else
{
uint32_t v___x_300_; uint8_t v___x_301_; 
v___x_300_ = 91;
v___x_301_ = lean_uint32_dec_le(v_c_289_, v___x_300_);
v___y_291_ = v___x_301_;
goto v___jp_290_;
}
}
else
{
return v___y_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ctext___boxed(lean_object* v_c_310_){
_start:
{
uint32_t v_c_boxed_311_; uint8_t v_res_312_; lean_object* v_r_313_; 
v_c_boxed_311_ = lean_unbox_uint32(v_c_310_);
lean_dec(v_c_310_);
v_res_312_ = l_Std_Http_Internal_Char_ctext(v_c_boxed_311_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_etagc(uint32_t v_c_314_){
_start:
{
uint32_t v___x_315_; uint8_t v___x_316_; 
v___x_315_ = 33;
v___x_316_ = lean_uint32_dec_eq(v_c_314_, v___x_315_);
if (v___x_316_ == 0)
{
uint32_t v___x_317_; uint8_t v___x_318_; 
v___x_317_ = 35;
v___x_318_ = lean_uint32_dec_le(v___x_317_, v_c_314_);
if (v___x_318_ == 0)
{
return v___x_318_;
}
else
{
uint32_t v___x_319_; uint8_t v___x_320_; 
v___x_319_ = 126;
v___x_320_ = lean_uint32_dec_le(v_c_314_, v___x_319_);
return v___x_320_;
}
}
else
{
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_etagc___boxed(lean_object* v_c_321_){
_start:
{
uint32_t v_c_boxed_322_; uint8_t v_res_323_; lean_object* v_r_324_; 
v_c_boxed_322_ = lean_unbox_uint32(v_c_321_);
lean_dec(v_c_321_);
v_res_323_ = l_Std_Http_Internal_Char_etagc(v_c_boxed_322_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_ows(uint32_t v_c_325_){
_start:
{
uint32_t v___x_326_; uint8_t v___x_327_; 
v___x_326_ = 32;
v___x_327_ = lean_uint32_dec_eq(v_c_325_, v___x_326_);
if (v___x_327_ == 0)
{
uint32_t v___x_328_; uint8_t v___x_329_; 
v___x_328_ = 9;
v___x_329_ = lean_uint32_dec_eq(v_c_325_, v___x_328_);
return v___x_329_;
}
else
{
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ows___boxed(lean_object* v_c_330_){
_start:
{
uint32_t v_c_boxed_331_; uint8_t v_res_332_; lean_object* v_r_333_; 
v_c_boxed_331_ = lean_unbox_uint32(v_c_330_);
lean_dec(v_c_330_);
v_res_332_ = l_Std_Http_Internal_Char_ows(v_c_boxed_331_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_bws(uint32_t v_c_334_){
_start:
{
uint32_t v___x_335_; uint8_t v___x_336_; 
v___x_335_ = 32;
v___x_336_ = lean_uint32_dec_eq(v_c_334_, v___x_335_);
if (v___x_336_ == 0)
{
uint32_t v___x_337_; uint8_t v___x_338_; 
v___x_337_ = 9;
v___x_338_ = lean_uint32_dec_eq(v_c_334_, v___x_337_);
return v___x_338_;
}
else
{
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_bws___boxed(lean_object* v_c_339_){
_start:
{
uint32_t v_c_boxed_340_; uint8_t v_res_341_; lean_object* v_r_342_; 
v_c_boxed_340_ = lean_unbox_uint32(v_c_339_);
lean_dec(v_c_339_);
v_res_341_ = l_Std_Http_Internal_Char_bws(v_c_boxed_340_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_rws(uint32_t v_c_343_){
_start:
{
uint32_t v___x_344_; uint8_t v___x_345_; 
v___x_344_ = 32;
v___x_345_ = lean_uint32_dec_eq(v_c_343_, v___x_344_);
if (v___x_345_ == 0)
{
uint32_t v___x_346_; uint8_t v___x_347_; 
v___x_346_ = 9;
v___x_347_ = lean_uint32_dec_eq(v_c_343_, v___x_346_);
return v___x_347_;
}
else
{
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_rws___boxed(lean_object* v_c_348_){
_start:
{
uint32_t v_c_boxed_349_; uint8_t v_res_350_; lean_object* v_r_351_; 
v_c_boxed_349_ = lean_unbox_uint32(v_c_348_);
lean_dec(v_c_348_);
v_res_350_ = l_Std_Http_Internal_Char_rws(v_c_boxed_349_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_obsText(uint32_t v_c_352_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_353_ = lean_unsigned_to_nat(128u);
v___x_354_ = lean_uint32_to_nat(v_c_352_);
v___x_355_ = lean_nat_dec_le(v___x_353_, v___x_354_);
lean_dec(v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_obsText___boxed(lean_object* v_c_356_){
_start:
{
uint32_t v_c_boxed_357_; uint8_t v_res_358_; lean_object* v_r_359_; 
v_c_boxed_357_ = lean_unbox_uint32(v_c_356_);
lean_dec(v_c_356_);
v_res_358_ = l_Std_Http_Internal_Char_obsText(v_c_boxed_357_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_reasonPhraseChar(uint32_t v_c_360_){
_start:
{
uint32_t v___x_361_; uint8_t v___x_362_; 
v___x_361_ = 9;
v___x_362_ = lean_uint32_dec_eq(v_c_360_, v___x_361_);
if (v___x_362_ == 0)
{
uint32_t v___x_363_; uint8_t v___x_364_; 
v___x_363_ = 32;
v___x_364_ = lean_uint32_dec_eq(v_c_360_, v___x_363_);
if (v___x_364_ == 0)
{
uint32_t v___x_365_; uint8_t v___x_366_; 
v___x_365_ = 33;
v___x_366_ = lean_uint32_dec_le(v___x_365_, v_c_360_);
if (v___x_366_ == 0)
{
return v___x_366_;
}
else
{
uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = 126;
v___x_368_ = lean_uint32_dec_le(v_c_360_, v___x_367_);
return v___x_368_;
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_reasonPhraseChar___boxed(lean_object* v_c_369_){
_start:
{
uint32_t v_c_boxed_370_; uint8_t v_res_371_; lean_object* v_r_372_; 
v_c_boxed_370_ = lean_unbox_uint32(v_c_369_);
lean_dec(v_c_369_);
v_res_371_ = l_Std_Http_Internal_Char_reasonPhraseChar(v_c_boxed_370_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isHexDigit(uint32_t v_c_373_){
_start:
{
uint32_t v___x_374_; uint8_t v___x_375_; 
v___x_374_ = 97;
v___x_375_ = lean_uint32_dec_eq(v_c_373_, v___x_374_);
if (v___x_375_ == 0)
{
uint32_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = 98;
v___x_377_ = lean_uint32_dec_eq(v_c_373_, v___x_376_);
if (v___x_377_ == 0)
{
uint32_t v___x_378_; uint8_t v___x_379_; 
v___x_378_ = 99;
v___x_379_ = lean_uint32_dec_eq(v_c_373_, v___x_378_);
if (v___x_379_ == 0)
{
uint32_t v___x_380_; uint8_t v___x_381_; 
v___x_380_ = 100;
v___x_381_ = lean_uint32_dec_eq(v_c_373_, v___x_380_);
if (v___x_381_ == 0)
{
uint32_t v___x_382_; uint8_t v___x_383_; 
v___x_382_ = 101;
v___x_383_ = lean_uint32_dec_eq(v_c_373_, v___x_382_);
if (v___x_383_ == 0)
{
uint32_t v___x_384_; uint8_t v___x_385_; 
v___x_384_ = 102;
v___x_385_ = lean_uint32_dec_eq(v_c_373_, v___x_384_);
if (v___x_385_ == 0)
{
uint32_t v___x_386_; uint8_t v___x_387_; 
v___x_386_ = 65;
v___x_387_ = lean_uint32_dec_eq(v_c_373_, v___x_386_);
if (v___x_387_ == 0)
{
uint32_t v___x_388_; uint8_t v___x_389_; 
v___x_388_ = 66;
v___x_389_ = lean_uint32_dec_eq(v_c_373_, v___x_388_);
if (v___x_389_ == 0)
{
uint32_t v___x_390_; uint8_t v___x_391_; 
v___x_390_ = 67;
v___x_391_ = lean_uint32_dec_eq(v_c_373_, v___x_390_);
if (v___x_391_ == 0)
{
uint32_t v___x_392_; uint8_t v___x_393_; 
v___x_392_ = 68;
v___x_393_ = lean_uint32_dec_eq(v_c_373_, v___x_392_);
if (v___x_393_ == 0)
{
uint32_t v___x_394_; uint8_t v___x_395_; 
v___x_394_ = 69;
v___x_395_ = lean_uint32_dec_eq(v_c_373_, v___x_394_);
if (v___x_395_ == 0)
{
uint32_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 70;
v___x_397_ = lean_uint32_dec_eq(v_c_373_, v___x_396_);
if (v___x_397_ == 0)
{
uint32_t v___x_398_; uint8_t v___x_399_; 
v___x_398_ = 48;
v___x_399_ = lean_uint32_dec_le(v___x_398_, v_c_373_);
if (v___x_399_ == 0)
{
return v___x_399_;
}
else
{
uint32_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 57;
v___x_401_ = lean_uint32_dec_le(v_c_373_, v___x_400_);
return v___x_401_;
}
}
else
{
return v___x_397_;
}
}
else
{
return v___x_395_;
}
}
else
{
return v___x_393_;
}
}
else
{
return v___x_391_;
}
}
else
{
return v___x_389_;
}
}
else
{
return v___x_387_;
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
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigit___boxed(lean_object* v_c_402_){
_start:
{
uint32_t v_c_boxed_403_; uint8_t v_res_404_; lean_object* v_r_405_; 
v_c_boxed_403_ = lean_unbox_uint32(v_c_402_);
lean_dec(v_c_402_);
v_res_404_ = l_Std_Http_Internal_Char_isHexDigit(v_c_boxed_403_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__0(void){
_start:
{
uint32_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = 70;
v___x_407_ = lean_uint32_to_uint8(v___x_406_);
return v___x_407_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__1(void){
_start:
{
uint32_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 102;
v___x_409_ = lean_uint32_to_uint8(v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isHexDigitByte(uint8_t v_c_410_){
_start:
{
uint8_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_422_ = lean_uint8_dec_le(v___x_421_, v_c_410_);
if (v___x_422_ == 0)
{
goto v___jp_416_;
}
else
{
uint8_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_424_ = lean_uint8_dec_le(v_c_410_, v___x_423_);
if (v___x_424_ == 0)
{
goto v___jp_416_;
}
else
{
return v___x_424_;
}
}
v___jp_411_:
{
uint8_t v___x_412_; uint8_t v___x_413_; 
v___x_412_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_413_ = lean_uint8_dec_le(v___x_412_, v_c_410_);
if (v___x_413_ == 0)
{
return v___x_413_;
}
else
{
uint8_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_uint8_once(&l_Std_Http_Internal_Char_isHexDigitByte___closed__0, &l_Std_Http_Internal_Char_isHexDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__0);
v___x_415_ = lean_uint8_dec_le(v_c_410_, v___x_414_);
return v___x_415_;
}
}
v___jp_416_:
{
uint8_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_418_ = lean_uint8_dec_le(v___x_417_, v_c_410_);
if (v___x_418_ == 0)
{
goto v___jp_411_;
}
else
{
uint8_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = lean_uint8_once(&l_Std_Http_Internal_Char_isHexDigitByte___closed__1, &l_Std_Http_Internal_Char_isHexDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__1);
v___x_420_ = lean_uint8_dec_le(v_c_410_, v___x_419_);
if (v___x_420_ == 0)
{
goto v___jp_411_;
}
else
{
return v___x_420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigitByte___boxed(lean_object* v_c_425_){
_start:
{
uint8_t v_c_boxed_426_; uint8_t v_res_427_; lean_object* v_r_428_; 
v_c_boxed_426_ = lean_unbox(v_c_425_);
v_res_427_ = l_Std_Http_Internal_Char_isHexDigitByte(v_c_boxed_426_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAlphaNum(uint8_t v_c_429_){
_start:
{
uint8_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_441_ = lean_uint8_dec_le(v___x_440_, v_c_429_);
if (v___x_441_ == 0)
{
goto v___jp_435_;
}
else
{
uint8_t v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_443_ = lean_uint8_dec_le(v_c_429_, v___x_442_);
if (v___x_443_ == 0)
{
goto v___jp_435_;
}
else
{
return v___x_443_;
}
}
v___jp_430_:
{
uint8_t v___x_431_; uint8_t v___x_432_; 
v___x_431_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_432_ = lean_uint8_dec_le(v___x_431_, v_c_429_);
if (v___x_432_ == 0)
{
return v___x_432_;
}
else
{
uint8_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
v___x_434_ = lean_uint8_dec_le(v_c_429_, v___x_433_);
return v___x_434_;
}
}
v___jp_435_:
{
uint8_t v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_437_ = lean_uint8_dec_le(v___x_436_, v_c_429_);
if (v___x_437_ == 0)
{
goto v___jp_430_;
}
else
{
uint8_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
v___x_439_ = lean_uint8_dec_le(v_c_429_, v___x_438_);
if (v___x_439_ == 0)
{
goto v___jp_430_;
}
else
{
return v___x_439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAlphaNum___boxed(lean_object* v_c_444_){
_start:
{
uint8_t v_c_boxed_445_; uint8_t v_res_446_; lean_object* v_r_447_; 
v_c_boxed_445_ = lean_unbox(v_c_444_);
v_res_446_ = l_Std_Http_Internal_Char_isAlphaNum(v_c_boxed_445_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAsciiAlphaNumChar(uint32_t v_c_448_){
_start:
{
uint8_t v___y_450_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = lean_uint32_to_nat(v_c_448_);
v___x_461_ = lean_unsigned_to_nat(128u);
v___x_462_ = lean_nat_dec_lt(v___x_460_, v___x_461_);
lean_dec(v___x_460_);
if (v___x_462_ == 0)
{
return v___x_462_;
}
else
{
uint32_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = 48;
v___x_464_ = lean_uint32_dec_le(v___x_463_, v_c_448_);
if (v___x_464_ == 0)
{
goto v___jp_455_;
}
else
{
uint32_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = 57;
v___x_466_ = lean_uint32_dec_le(v_c_448_, v___x_465_);
if (v___x_466_ == 0)
{
goto v___jp_455_;
}
else
{
return v___x_466_;
}
}
}
v___jp_449_:
{
if (v___y_450_ == 0)
{
uint32_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = 97;
v___x_452_ = lean_uint32_dec_le(v___x_451_, v_c_448_);
if (v___x_452_ == 0)
{
return v___x_452_;
}
else
{
uint32_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = 122;
v___x_454_ = lean_uint32_dec_le(v_c_448_, v___x_453_);
return v___x_454_;
}
}
else
{
return v___y_450_;
}
}
v___jp_455_:
{
uint32_t v___x_456_; uint8_t v___x_457_; 
v___x_456_ = 65;
v___x_457_ = lean_uint32_dec_le(v___x_456_, v_c_448_);
if (v___x_457_ == 0)
{
v___y_450_ = v___x_457_;
goto v___jp_449_;
}
else
{
uint32_t v___x_458_; uint8_t v___x_459_; 
v___x_458_ = 90;
v___x_459_ = lean_uint32_dec_le(v_c_448_, v___x_458_);
v___y_450_ = v___x_459_;
goto v___jp_449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAsciiAlphaNumChar___boxed(lean_object* v_c_467_){
_start:
{
uint32_t v_c_boxed_468_; uint8_t v_res_469_; lean_object* v_r_470_; 
v_c_boxed_468_ = lean_unbox_uint32(v_c_467_);
lean_dec(v_c_467_);
v_res_469_ = l_Std_Http_Internal_Char_isAsciiAlphaNumChar(v_c_boxed_468_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isValidSchemeChar(uint32_t v_c_471_){
_start:
{
uint8_t v___y_480_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_490_ = lean_uint32_to_nat(v_c_471_);
v___x_491_ = lean_unsigned_to_nat(128u);
v___x_492_ = lean_nat_dec_lt(v___x_490_, v___x_491_);
lean_dec(v___x_490_);
if (v___x_492_ == 0)
{
goto v___jp_472_;
}
else
{
uint32_t v___x_493_; uint8_t v___x_494_; 
v___x_493_ = 48;
v___x_494_ = lean_uint32_dec_le(v___x_493_, v_c_471_);
if (v___x_494_ == 0)
{
goto v___jp_485_;
}
else
{
uint32_t v___x_495_; uint8_t v___x_496_; 
v___x_495_ = 57;
v___x_496_ = lean_uint32_dec_le(v_c_471_, v___x_495_);
if (v___x_496_ == 0)
{
goto v___jp_485_;
}
else
{
return v___x_496_;
}
}
}
v___jp_472_:
{
uint32_t v___x_473_; uint8_t v___x_474_; 
v___x_473_ = 43;
v___x_474_ = lean_uint32_dec_eq(v_c_471_, v___x_473_);
if (v___x_474_ == 0)
{
uint32_t v___x_475_; uint8_t v___x_476_; 
v___x_475_ = 45;
v___x_476_ = lean_uint32_dec_eq(v_c_471_, v___x_475_);
if (v___x_476_ == 0)
{
uint32_t v___x_477_; uint8_t v___x_478_; 
v___x_477_ = 46;
v___x_478_ = lean_uint32_dec_eq(v_c_471_, v___x_477_);
return v___x_478_;
}
else
{
return v___x_476_;
}
}
else
{
return v___x_474_;
}
}
v___jp_479_:
{
if (v___y_480_ == 0)
{
uint32_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = 97;
v___x_482_ = lean_uint32_dec_le(v___x_481_, v_c_471_);
if (v___x_482_ == 0)
{
goto v___jp_472_;
}
else
{
uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 122;
v___x_484_ = lean_uint32_dec_le(v_c_471_, v___x_483_);
if (v___x_484_ == 0)
{
goto v___jp_472_;
}
else
{
return v___x_484_;
}
}
}
else
{
return v___y_480_;
}
}
v___jp_485_:
{
uint32_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = 65;
v___x_487_ = lean_uint32_dec_le(v___x_486_, v_c_471_);
if (v___x_487_ == 0)
{
v___y_480_ = v___x_487_;
goto v___jp_479_;
}
else
{
uint32_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = 90;
v___x_489_ = lean_uint32_dec_le(v_c_471_, v___x_488_);
v___y_480_ = v___x_489_;
goto v___jp_479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidSchemeChar___boxed(lean_object* v_c_497_){
_start:
{
uint32_t v_c_boxed_498_; uint8_t v_res_499_; lean_object* v_r_500_; 
v_c_boxed_498_ = lean_unbox_uint32(v_c_497_);
lean_dec(v_c_497_);
v_res_499_ = l_Std_Http_Internal_Char_isValidSchemeChar(v_c_boxed_498_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isValidDomainNameChar(uint32_t v_c_501_){
_start:
{
uint8_t v___y_508_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_518_ = lean_uint32_to_nat(v_c_501_);
v___x_519_ = lean_unsigned_to_nat(128u);
v___x_520_ = lean_nat_dec_lt(v___x_518_, v___x_519_);
lean_dec(v___x_518_);
if (v___x_520_ == 0)
{
goto v___jp_502_;
}
else
{
uint32_t v___x_521_; uint8_t v___x_522_; 
v___x_521_ = 48;
v___x_522_ = lean_uint32_dec_le(v___x_521_, v_c_501_);
if (v___x_522_ == 0)
{
goto v___jp_513_;
}
else
{
uint32_t v___x_523_; uint8_t v___x_524_; 
v___x_523_ = 57;
v___x_524_ = lean_uint32_dec_le(v_c_501_, v___x_523_);
if (v___x_524_ == 0)
{
goto v___jp_513_;
}
else
{
return v___x_524_;
}
}
}
v___jp_502_:
{
uint32_t v___x_503_; uint8_t v___x_504_; 
v___x_503_ = 45;
v___x_504_ = lean_uint32_dec_eq(v_c_501_, v___x_503_);
if (v___x_504_ == 0)
{
uint32_t v___x_505_; uint8_t v___x_506_; 
v___x_505_ = 46;
v___x_506_ = lean_uint32_dec_eq(v_c_501_, v___x_505_);
return v___x_506_;
}
else
{
return v___x_504_;
}
}
v___jp_507_:
{
if (v___y_508_ == 0)
{
uint32_t v___x_509_; uint8_t v___x_510_; 
v___x_509_ = 97;
v___x_510_ = lean_uint32_dec_le(v___x_509_, v_c_501_);
if (v___x_510_ == 0)
{
goto v___jp_502_;
}
else
{
uint32_t v___x_511_; uint8_t v___x_512_; 
v___x_511_ = 122;
v___x_512_ = lean_uint32_dec_le(v_c_501_, v___x_511_);
if (v___x_512_ == 0)
{
goto v___jp_502_;
}
else
{
return v___x_512_;
}
}
}
else
{
return v___y_508_;
}
}
v___jp_513_:
{
uint32_t v___x_514_; uint8_t v___x_515_; 
v___x_514_ = 65;
v___x_515_ = lean_uint32_dec_le(v___x_514_, v_c_501_);
if (v___x_515_ == 0)
{
v___y_508_ = v___x_515_;
goto v___jp_507_;
}
else
{
uint32_t v___x_516_; uint8_t v___x_517_; 
v___x_516_ = 90;
v___x_517_ = lean_uint32_dec_le(v_c_501_, v___x_516_);
v___y_508_ = v___x_517_;
goto v___jp_507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidDomainNameChar___boxed(lean_object* v_c_525_){
_start:
{
uint32_t v_c_boxed_526_; uint8_t v_res_527_; lean_object* v_r_528_; 
v_c_boxed_526_ = lean_unbox_uint32(v_c_525_);
lean_dec(v_c_525_);
v_res_527_ = l_Std_Http_Internal_Char_isValidDomainNameChar(v_c_boxed_526_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isUnreserved___closed__0(void){
_start:
{
uint32_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = 45;
v___x_530_ = lean_uint32_to_uint8(v___x_529_);
return v___x_530_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isUnreserved___closed__1(void){
_start:
{
uint32_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 46;
v___x_532_ = lean_uint32_to_uint8(v___x_531_);
return v___x_532_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isUnreserved___closed__2(void){
_start:
{
uint32_t v___x_533_; uint8_t v___x_534_; 
v___x_533_ = 95;
v___x_534_ = lean_uint32_to_uint8(v___x_533_);
return v___x_534_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isUnreserved___closed__3(void){
_start:
{
uint32_t v___x_535_; uint8_t v___x_536_; 
v___x_535_ = 126;
v___x_536_ = lean_uint32_to_uint8(v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUnreserved(uint8_t v_c_537_){
_start:
{
uint8_t v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_558_ = lean_uint8_dec_le(v___x_557_, v_c_537_);
if (v___x_558_ == 0)
{
goto v___jp_552_;
}
else
{
uint8_t v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
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
v___x_539_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
v___x_540_ = lean_uint8_dec_eq(v_c_537_, v___x_539_);
if (v___x_540_ == 0)
{
uint8_t v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
v___x_542_ = lean_uint8_dec_eq(v_c_537_, v___x_541_);
if (v___x_542_ == 0)
{
uint8_t v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
v___x_544_ = lean_uint8_dec_eq(v_c_537_, v___x_543_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
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
v___x_548_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_549_ = lean_uint8_dec_le(v___x_548_, v_c_537_);
if (v___x_549_ == 0)
{
goto v___jp_538_;
}
else
{
uint8_t v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
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
v___x_553_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_554_ = lean_uint8_dec_le(v___x_553_, v_c_537_);
if (v___x_554_ == 0)
{
goto v___jp_547_;
}
else
{
uint8_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUnreserved___boxed(lean_object* v_c_561_){
_start:
{
uint8_t v_c_boxed_562_; uint8_t v_res_563_; lean_object* v_r_564_; 
v_c_boxed_562_ = lean_unbox(v_c_561_);
v_res_563_ = l_Std_Http_Internal_Char_isUnreserved(v_c_boxed_562_);
v_r_564_ = lean_box(v_res_563_);
return v_r_564_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__0(void){
_start:
{
uint32_t v___x_565_; uint8_t v___x_566_; 
v___x_565_ = 33;
v___x_566_ = lean_uint32_to_uint8(v___x_565_);
return v___x_566_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__1(void){
_start:
{
uint32_t v___x_567_; uint8_t v___x_568_; 
v___x_567_ = 36;
v___x_568_ = lean_uint32_to_uint8(v___x_567_);
return v___x_568_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__2(void){
_start:
{
uint32_t v___x_569_; uint8_t v___x_570_; 
v___x_569_ = 38;
v___x_570_ = lean_uint32_to_uint8(v___x_569_);
return v___x_570_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__3(void){
_start:
{
uint32_t v___x_571_; uint8_t v___x_572_; 
v___x_571_ = 39;
v___x_572_ = lean_uint32_to_uint8(v___x_571_);
return v___x_572_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__4(void){
_start:
{
uint32_t v___x_573_; uint8_t v___x_574_; 
v___x_573_ = 40;
v___x_574_ = lean_uint32_to_uint8(v___x_573_);
return v___x_574_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__5(void){
_start:
{
uint32_t v___x_575_; uint8_t v___x_576_; 
v___x_575_ = 41;
v___x_576_ = lean_uint32_to_uint8(v___x_575_);
return v___x_576_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__6(void){
_start:
{
uint32_t v___x_577_; uint8_t v___x_578_; 
v___x_577_ = 42;
v___x_578_ = lean_uint32_to_uint8(v___x_577_);
return v___x_578_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__7(void){
_start:
{
uint32_t v___x_579_; uint8_t v___x_580_; 
v___x_579_ = 43;
v___x_580_ = lean_uint32_to_uint8(v___x_579_);
return v___x_580_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__8(void){
_start:
{
uint32_t v___x_581_; uint8_t v___x_582_; 
v___x_581_ = 44;
v___x_582_ = lean_uint32_to_uint8(v___x_581_);
return v___x_582_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__9(void){
_start:
{
uint32_t v___x_583_; uint8_t v___x_584_; 
v___x_583_ = 59;
v___x_584_ = lean_uint32_to_uint8(v___x_583_);
return v___x_584_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__10(void){
_start:
{
uint32_t v___x_585_; uint8_t v___x_586_; 
v___x_585_ = 61;
v___x_586_ = lean_uint32_to_uint8(v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isSubDelims(uint8_t v_c_587_){
_start:
{
uint8_t v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
v___x_589_ = lean_uint8_dec_eq(v_c_587_, v___x_588_);
if (v___x_589_ == 0)
{
uint8_t v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
v___x_591_ = lean_uint8_dec_eq(v_c_587_, v___x_590_);
if (v___x_591_ == 0)
{
uint8_t v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
v___x_593_ = lean_uint8_dec_eq(v_c_587_, v___x_592_);
if (v___x_593_ == 0)
{
uint8_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
v___x_595_ = lean_uint8_dec_eq(v_c_587_, v___x_594_);
if (v___x_595_ == 0)
{
uint8_t v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
v___x_597_ = lean_uint8_dec_eq(v_c_587_, v___x_596_);
if (v___x_597_ == 0)
{
uint8_t v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
v___x_599_ = lean_uint8_dec_eq(v_c_587_, v___x_598_);
if (v___x_599_ == 0)
{
uint8_t v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
v___x_601_ = lean_uint8_dec_eq(v_c_587_, v___x_600_);
if (v___x_601_ == 0)
{
uint8_t v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
v___x_603_ = lean_uint8_dec_eq(v_c_587_, v___x_602_);
if (v___x_603_ == 0)
{
uint8_t v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
v___x_605_ = lean_uint8_dec_eq(v_c_587_, v___x_604_);
if (v___x_605_ == 0)
{
uint8_t v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
v___x_607_ = lean_uint8_dec_eq(v_c_587_, v___x_606_);
if (v___x_607_ == 0)
{
uint8_t v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
v___x_609_ = lean_uint8_dec_eq(v_c_587_, v___x_608_);
return v___x_609_;
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
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isSubDelims___boxed(lean_object* v_c_610_){
_start:
{
uint8_t v_c_boxed_611_; uint8_t v_res_612_; lean_object* v_r_613_; 
v_c_boxed_611_ = lean_unbox(v_c_610_);
v_res_612_ = l_Std_Http_Internal_Char_isSubDelims(v_c_boxed_611_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isPChar___closed__0(void){
_start:
{
uint32_t v___x_614_; uint8_t v___x_615_; 
v___x_614_ = 58;
v___x_615_ = lean_uint32_to_uint8(v___x_614_);
return v___x_615_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isPChar___closed__1(void){
_start:
{
uint32_t v___x_616_; uint8_t v___x_617_; 
v___x_616_ = 64;
v___x_617_ = lean_uint32_to_uint8(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isPChar(uint8_t v_c_618_){
_start:
{
uint8_t v___x_664_; uint8_t v___x_665_; 
v___x_664_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_665_ = lean_uint8_dec_le(v___x_664_, v_c_618_);
if (v___x_665_ == 0)
{
goto v___jp_659_;
}
else
{
uint8_t v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_667_ = lean_uint8_dec_le(v_c_618_, v___x_666_);
if (v___x_667_ == 0)
{
goto v___jp_659_;
}
else
{
return v___x_667_;
}
}
v___jp_619_:
{
uint8_t v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
v___x_621_ = lean_uint8_dec_eq(v_c_618_, v___x_620_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
v___x_623_ = lean_uint8_dec_eq(v_c_618_, v___x_622_);
if (v___x_623_ == 0)
{
uint8_t v___x_624_; uint8_t v___x_625_; 
v___x_624_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
v___x_625_ = lean_uint8_dec_eq(v_c_618_, v___x_624_);
if (v___x_625_ == 0)
{
uint8_t v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
v___x_627_ = lean_uint8_dec_eq(v_c_618_, v___x_626_);
if (v___x_627_ == 0)
{
uint8_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
v___x_629_ = lean_uint8_dec_eq(v_c_618_, v___x_628_);
if (v___x_629_ == 0)
{
uint8_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
v___x_631_ = lean_uint8_dec_eq(v_c_618_, v___x_630_);
if (v___x_631_ == 0)
{
uint8_t v___x_632_; uint8_t v___x_633_; 
v___x_632_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
v___x_633_ = lean_uint8_dec_eq(v_c_618_, v___x_632_);
if (v___x_633_ == 0)
{
uint8_t v___x_634_; uint8_t v___x_635_; 
v___x_634_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
v___x_635_ = lean_uint8_dec_eq(v_c_618_, v___x_634_);
if (v___x_635_ == 0)
{
uint8_t v___x_636_; uint8_t v___x_637_; 
v___x_636_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
v___x_637_ = lean_uint8_dec_eq(v_c_618_, v___x_636_);
if (v___x_637_ == 0)
{
uint8_t v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
v___x_639_ = lean_uint8_dec_eq(v_c_618_, v___x_638_);
if (v___x_639_ == 0)
{
uint8_t v___x_640_; uint8_t v___x_641_; 
v___x_640_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
v___x_641_ = lean_uint8_dec_eq(v_c_618_, v___x_640_);
if (v___x_641_ == 0)
{
uint8_t v___x_642_; uint8_t v___x_643_; 
v___x_642_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
v___x_643_ = lean_uint8_dec_eq(v_c_618_, v___x_642_);
if (v___x_643_ == 0)
{
uint8_t v___x_644_; uint8_t v___x_645_; 
v___x_644_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
v___x_645_ = lean_uint8_dec_eq(v_c_618_, v___x_644_);
if (v___x_645_ == 0)
{
uint8_t v___x_646_; uint8_t v___x_647_; 
v___x_646_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
v___x_647_ = lean_uint8_dec_eq(v_c_618_, v___x_646_);
if (v___x_647_ == 0)
{
uint8_t v___x_648_; uint8_t v___x_649_; 
v___x_648_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
v___x_649_ = lean_uint8_dec_eq(v_c_618_, v___x_648_);
if (v___x_649_ == 0)
{
uint8_t v___x_650_; uint8_t v___x_651_; 
v___x_650_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__0, &l_Std_Http_Internal_Char_isPChar___closed__0_once, _init_l_Std_Http_Internal_Char_isPChar___closed__0);
v___x_651_ = lean_uint8_dec_eq(v_c_618_, v___x_650_);
if (v___x_651_ == 0)
{
uint8_t v___x_652_; uint8_t v___x_653_; 
v___x_652_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__1, &l_Std_Http_Internal_Char_isPChar___closed__1_once, _init_l_Std_Http_Internal_Char_isPChar___closed__1);
v___x_653_ = lean_uint8_dec_eq(v_c_618_, v___x_652_);
return v___x_653_;
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
v___jp_654_:
{
uint8_t v___x_655_; uint8_t v___x_656_; 
v___x_655_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_656_ = lean_uint8_dec_le(v___x_655_, v_c_618_);
if (v___x_656_ == 0)
{
goto v___jp_619_;
}
else
{
uint8_t v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
v___x_658_ = lean_uint8_dec_le(v_c_618_, v___x_657_);
if (v___x_658_ == 0)
{
goto v___jp_619_;
}
else
{
return v___x_658_;
}
}
}
v___jp_659_:
{
uint8_t v___x_660_; uint8_t v___x_661_; 
v___x_660_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_661_ = lean_uint8_dec_le(v___x_660_, v_c_618_);
if (v___x_661_ == 0)
{
goto v___jp_654_;
}
else
{
uint8_t v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
v___x_663_ = lean_uint8_dec_le(v_c_618_, v___x_662_);
if (v___x_663_ == 0)
{
goto v___jp_654_;
}
else
{
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isPChar___boxed(lean_object* v_c_668_){
_start:
{
uint8_t v_c_boxed_669_; uint8_t v_res_670_; lean_object* v_r_671_; 
v_c_boxed_669_ = lean_unbox(v_c_668_);
v_res_670_ = l_Std_Http_Internal_Char_isPChar(v_c_boxed_669_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isQueryChar___closed__0(void){
_start:
{
uint32_t v___x_672_; uint8_t v___x_673_; 
v___x_672_ = 47;
v___x_673_ = lean_uint32_to_uint8(v___x_672_);
return v___x_673_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isQueryChar___closed__1(void){
_start:
{
uint32_t v___x_674_; uint8_t v___x_675_; 
v___x_674_ = 63;
v___x_675_ = lean_uint32_to_uint8(v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryChar(uint8_t v_c_676_){
_start:
{
uint8_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_727_ = lean_uint8_dec_le(v___x_726_, v_c_676_);
if (v___x_727_ == 0)
{
goto v___jp_721_;
}
else
{
uint8_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
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
v___x_678_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
v___x_679_ = lean_uint8_dec_eq(v_c_676_, v___x_678_);
if (v___x_679_ == 0)
{
uint8_t v___x_680_; uint8_t v___x_681_; 
v___x_680_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
v___x_681_ = lean_uint8_dec_eq(v_c_676_, v___x_680_);
if (v___x_681_ == 0)
{
uint8_t v___x_682_; uint8_t v___x_683_; 
v___x_682_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
v___x_683_ = lean_uint8_dec_eq(v_c_676_, v___x_682_);
if (v___x_683_ == 0)
{
uint8_t v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
v___x_685_ = lean_uint8_dec_eq(v_c_676_, v___x_684_);
if (v___x_685_ == 0)
{
uint8_t v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
v___x_687_ = lean_uint8_dec_eq(v_c_676_, v___x_686_);
if (v___x_687_ == 0)
{
uint8_t v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
v___x_689_ = lean_uint8_dec_eq(v_c_676_, v___x_688_);
if (v___x_689_ == 0)
{
uint8_t v___x_690_; uint8_t v___x_691_; 
v___x_690_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
v___x_691_ = lean_uint8_dec_eq(v_c_676_, v___x_690_);
if (v___x_691_ == 0)
{
uint8_t v___x_692_; uint8_t v___x_693_; 
v___x_692_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
v___x_693_ = lean_uint8_dec_eq(v_c_676_, v___x_692_);
if (v___x_693_ == 0)
{
uint8_t v___x_694_; uint8_t v___x_695_; 
v___x_694_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
v___x_695_ = lean_uint8_dec_eq(v_c_676_, v___x_694_);
if (v___x_695_ == 0)
{
uint8_t v___x_696_; uint8_t v___x_697_; 
v___x_696_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
v___x_697_ = lean_uint8_dec_eq(v_c_676_, v___x_696_);
if (v___x_697_ == 0)
{
uint8_t v___x_698_; uint8_t v___x_699_; 
v___x_698_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
v___x_699_ = lean_uint8_dec_eq(v_c_676_, v___x_698_);
if (v___x_699_ == 0)
{
uint8_t v___x_700_; uint8_t v___x_701_; 
v___x_700_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
v___x_701_ = lean_uint8_dec_eq(v_c_676_, v___x_700_);
if (v___x_701_ == 0)
{
uint8_t v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
v___x_703_ = lean_uint8_dec_eq(v_c_676_, v___x_702_);
if (v___x_703_ == 0)
{
uint8_t v___x_704_; uint8_t v___x_705_; 
v___x_704_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
v___x_705_ = lean_uint8_dec_eq(v_c_676_, v___x_704_);
if (v___x_705_ == 0)
{
uint8_t v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
v___x_707_ = lean_uint8_dec_eq(v_c_676_, v___x_706_);
if (v___x_707_ == 0)
{
uint8_t v___x_708_; uint8_t v___x_709_; 
v___x_708_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__0, &l_Std_Http_Internal_Char_isPChar___closed__0_once, _init_l_Std_Http_Internal_Char_isPChar___closed__0);
v___x_709_ = lean_uint8_dec_eq(v_c_676_, v___x_708_);
if (v___x_709_ == 0)
{
uint8_t v___x_710_; uint8_t v___x_711_; 
v___x_710_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__1, &l_Std_Http_Internal_Char_isPChar___closed__1_once, _init_l_Std_Http_Internal_Char_isPChar___closed__1);
v___x_711_ = lean_uint8_dec_eq(v_c_676_, v___x_710_);
if (v___x_711_ == 0)
{
uint8_t v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__0, &l_Std_Http_Internal_Char_isQueryChar___closed__0_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__0);
v___x_713_ = lean_uint8_dec_eq(v_c_676_, v___x_712_);
if (v___x_713_ == 0)
{
uint8_t v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__1, &l_Std_Http_Internal_Char_isQueryChar___closed__1_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__1);
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
v___x_717_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_718_ = lean_uint8_dec_le(v___x_717_, v_c_676_);
if (v___x_718_ == 0)
{
goto v___jp_677_;
}
else
{
uint8_t v___x_719_; uint8_t v___x_720_; 
v___x_719_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
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
v___x_722_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_723_ = lean_uint8_dec_le(v___x_722_, v_c_676_);
if (v___x_723_ == 0)
{
goto v___jp_716_;
}
else
{
uint8_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryChar___boxed(lean_object* v_c_730_){
_start:
{
uint8_t v_c_boxed_731_; uint8_t v_res_732_; lean_object* v_r_733_; 
v_c_boxed_731_ = lean_unbox(v_c_730_);
v_res_732_ = l_Std_Http_Internal_Char_isQueryChar(v_c_boxed_731_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isFragmentChar(uint8_t v_c_734_){
_start:
{
uint8_t v___x_784_; uint8_t v___x_785_; 
v___x_784_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_785_ = lean_uint8_dec_le(v___x_784_, v_c_734_);
if (v___x_785_ == 0)
{
goto v___jp_779_;
}
else
{
uint8_t v___x_786_; uint8_t v___x_787_; 
v___x_786_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_787_ = lean_uint8_dec_le(v_c_734_, v___x_786_);
if (v___x_787_ == 0)
{
goto v___jp_779_;
}
else
{
return v___x_787_;
}
}
v___jp_735_:
{
uint8_t v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
v___x_737_ = lean_uint8_dec_eq(v_c_734_, v___x_736_);
if (v___x_737_ == 0)
{
uint8_t v___x_738_; uint8_t v___x_739_; 
v___x_738_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
v___x_739_ = lean_uint8_dec_eq(v_c_734_, v___x_738_);
if (v___x_739_ == 0)
{
uint8_t v___x_740_; uint8_t v___x_741_; 
v___x_740_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
v___x_741_ = lean_uint8_dec_eq(v_c_734_, v___x_740_);
if (v___x_741_ == 0)
{
uint8_t v___x_742_; uint8_t v___x_743_; 
v___x_742_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
v___x_743_ = lean_uint8_dec_eq(v_c_734_, v___x_742_);
if (v___x_743_ == 0)
{
uint8_t v___x_744_; uint8_t v___x_745_; 
v___x_744_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
v___x_745_ = lean_uint8_dec_eq(v_c_734_, v___x_744_);
if (v___x_745_ == 0)
{
uint8_t v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
v___x_747_ = lean_uint8_dec_eq(v_c_734_, v___x_746_);
if (v___x_747_ == 0)
{
uint8_t v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
v___x_749_ = lean_uint8_dec_eq(v_c_734_, v___x_748_);
if (v___x_749_ == 0)
{
uint8_t v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
v___x_751_ = lean_uint8_dec_eq(v_c_734_, v___x_750_);
if (v___x_751_ == 0)
{
uint8_t v___x_752_; uint8_t v___x_753_; 
v___x_752_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
v___x_753_ = lean_uint8_dec_eq(v_c_734_, v___x_752_);
if (v___x_753_ == 0)
{
uint8_t v___x_754_; uint8_t v___x_755_; 
v___x_754_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
v___x_755_ = lean_uint8_dec_eq(v_c_734_, v___x_754_);
if (v___x_755_ == 0)
{
uint8_t v___x_756_; uint8_t v___x_757_; 
v___x_756_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
v___x_757_ = lean_uint8_dec_eq(v_c_734_, v___x_756_);
if (v___x_757_ == 0)
{
uint8_t v___x_758_; uint8_t v___x_759_; 
v___x_758_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
v___x_759_ = lean_uint8_dec_eq(v_c_734_, v___x_758_);
if (v___x_759_ == 0)
{
uint8_t v___x_760_; uint8_t v___x_761_; 
v___x_760_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
v___x_761_ = lean_uint8_dec_eq(v_c_734_, v___x_760_);
if (v___x_761_ == 0)
{
uint8_t v___x_762_; uint8_t v___x_763_; 
v___x_762_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
v___x_763_ = lean_uint8_dec_eq(v_c_734_, v___x_762_);
if (v___x_763_ == 0)
{
uint8_t v___x_764_; uint8_t v___x_765_; 
v___x_764_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
v___x_765_ = lean_uint8_dec_eq(v_c_734_, v___x_764_);
if (v___x_765_ == 0)
{
uint8_t v___x_766_; uint8_t v___x_767_; 
v___x_766_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__0, &l_Std_Http_Internal_Char_isPChar___closed__0_once, _init_l_Std_Http_Internal_Char_isPChar___closed__0);
v___x_767_ = lean_uint8_dec_eq(v_c_734_, v___x_766_);
if (v___x_767_ == 0)
{
uint8_t v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__1, &l_Std_Http_Internal_Char_isPChar___closed__1_once, _init_l_Std_Http_Internal_Char_isPChar___closed__1);
v___x_769_ = lean_uint8_dec_eq(v_c_734_, v___x_768_);
if (v___x_769_ == 0)
{
uint8_t v___x_770_; uint8_t v___x_771_; 
v___x_770_ = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__0, &l_Std_Http_Internal_Char_isQueryChar___closed__0_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__0);
v___x_771_ = lean_uint8_dec_eq(v_c_734_, v___x_770_);
if (v___x_771_ == 0)
{
uint8_t v___x_772_; uint8_t v___x_773_; 
v___x_772_ = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__1, &l_Std_Http_Internal_Char_isQueryChar___closed__1_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__1);
v___x_773_ = lean_uint8_dec_eq(v_c_734_, v___x_772_);
return v___x_773_;
}
else
{
return v___x_771_;
}
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
v___jp_774_:
{
uint8_t v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_776_ = lean_uint8_dec_le(v___x_775_, v_c_734_);
if (v___x_776_ == 0)
{
goto v___jp_735_;
}
else
{
uint8_t v___x_777_; uint8_t v___x_778_; 
v___x_777_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
v___x_778_ = lean_uint8_dec_le(v_c_734_, v___x_777_);
if (v___x_778_ == 0)
{
goto v___jp_735_;
}
else
{
return v___x_778_;
}
}
}
v___jp_779_:
{
uint8_t v___x_780_; uint8_t v___x_781_; 
v___x_780_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_781_ = lean_uint8_dec_le(v___x_780_, v_c_734_);
if (v___x_781_ == 0)
{
goto v___jp_774_;
}
else
{
uint8_t v___x_782_; uint8_t v___x_783_; 
v___x_782_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
v___x_783_ = lean_uint8_dec_le(v_c_734_, v___x_782_);
if (v___x_783_ == 0)
{
goto v___jp_774_;
}
else
{
return v___x_783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isFragmentChar___boxed(lean_object* v_c_788_){
_start:
{
uint8_t v_c_boxed_789_; uint8_t v_res_790_; lean_object* v_r_791_; 
v_c_boxed_789_ = lean_unbox(v_c_788_);
v_res_790_ = l_Std_Http_Internal_Char_isFragmentChar(v_c_boxed_789_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUserInfoChar(uint8_t v_c_792_){
_start:
{
uint8_t v___x_836_; uint8_t v___x_837_; 
v___x_836_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_837_ = lean_uint8_dec_le(v___x_836_, v_c_792_);
if (v___x_837_ == 0)
{
goto v___jp_831_;
}
else
{
uint8_t v___x_838_; uint8_t v___x_839_; 
v___x_838_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_839_ = lean_uint8_dec_le(v_c_792_, v___x_838_);
if (v___x_839_ == 0)
{
goto v___jp_831_;
}
else
{
return v___x_839_;
}
}
v___jp_793_:
{
uint8_t v___x_794_; uint8_t v___x_795_; 
v___x_794_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
v___x_795_ = lean_uint8_dec_eq(v_c_792_, v___x_794_);
if (v___x_795_ == 0)
{
uint8_t v___x_796_; uint8_t v___x_797_; 
v___x_796_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
v___x_797_ = lean_uint8_dec_eq(v_c_792_, v___x_796_);
if (v___x_797_ == 0)
{
uint8_t v___x_798_; uint8_t v___x_799_; 
v___x_798_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
v___x_799_ = lean_uint8_dec_eq(v_c_792_, v___x_798_);
if (v___x_799_ == 0)
{
uint8_t v___x_800_; uint8_t v___x_801_; 
v___x_800_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
v___x_801_ = lean_uint8_dec_eq(v_c_792_, v___x_800_);
if (v___x_801_ == 0)
{
uint8_t v___x_802_; uint8_t v___x_803_; 
v___x_802_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
v___x_803_ = lean_uint8_dec_eq(v_c_792_, v___x_802_);
if (v___x_803_ == 0)
{
uint8_t v___x_804_; uint8_t v___x_805_; 
v___x_804_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
v___x_805_ = lean_uint8_dec_eq(v_c_792_, v___x_804_);
if (v___x_805_ == 0)
{
uint8_t v___x_806_; uint8_t v___x_807_; 
v___x_806_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
v___x_807_ = lean_uint8_dec_eq(v_c_792_, v___x_806_);
if (v___x_807_ == 0)
{
uint8_t v___x_808_; uint8_t v___x_809_; 
v___x_808_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
v___x_809_ = lean_uint8_dec_eq(v_c_792_, v___x_808_);
if (v___x_809_ == 0)
{
uint8_t v___x_810_; uint8_t v___x_811_; 
v___x_810_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
v___x_811_ = lean_uint8_dec_eq(v_c_792_, v___x_810_);
if (v___x_811_ == 0)
{
uint8_t v___x_812_; uint8_t v___x_813_; 
v___x_812_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
v___x_813_ = lean_uint8_dec_eq(v_c_792_, v___x_812_);
if (v___x_813_ == 0)
{
uint8_t v___x_814_; uint8_t v___x_815_; 
v___x_814_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
v___x_815_ = lean_uint8_dec_eq(v_c_792_, v___x_814_);
if (v___x_815_ == 0)
{
uint8_t v___x_816_; uint8_t v___x_817_; 
v___x_816_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
v___x_817_ = lean_uint8_dec_eq(v_c_792_, v___x_816_);
if (v___x_817_ == 0)
{
uint8_t v___x_818_; uint8_t v___x_819_; 
v___x_818_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
v___x_819_ = lean_uint8_dec_eq(v_c_792_, v___x_818_);
if (v___x_819_ == 0)
{
uint8_t v___x_820_; uint8_t v___x_821_; 
v___x_820_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
v___x_821_ = lean_uint8_dec_eq(v_c_792_, v___x_820_);
if (v___x_821_ == 0)
{
uint8_t v___x_822_; uint8_t v___x_823_; 
v___x_822_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
v___x_823_ = lean_uint8_dec_eq(v_c_792_, v___x_822_);
if (v___x_823_ == 0)
{
uint8_t v___x_824_; uint8_t v___x_825_; 
v___x_824_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__0, &l_Std_Http_Internal_Char_isPChar___closed__0_once, _init_l_Std_Http_Internal_Char_isPChar___closed__0);
v___x_825_ = lean_uint8_dec_eq(v_c_792_, v___x_824_);
return v___x_825_;
}
else
{
return v___x_823_;
}
}
else
{
return v___x_821_;
}
}
else
{
return v___x_819_;
}
}
else
{
return v___x_817_;
}
}
else
{
return v___x_815_;
}
}
else
{
return v___x_813_;
}
}
else
{
return v___x_811_;
}
}
else
{
return v___x_809_;
}
}
else
{
return v___x_807_;
}
}
else
{
return v___x_805_;
}
}
else
{
return v___x_803_;
}
}
else
{
return v___x_801_;
}
}
else
{
return v___x_799_;
}
}
else
{
return v___x_797_;
}
}
else
{
return v___x_795_;
}
}
v___jp_826_:
{
uint8_t v___x_827_; uint8_t v___x_828_; 
v___x_827_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_828_ = lean_uint8_dec_le(v___x_827_, v_c_792_);
if (v___x_828_ == 0)
{
goto v___jp_793_;
}
else
{
uint8_t v___x_829_; uint8_t v___x_830_; 
v___x_829_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
v___x_830_ = lean_uint8_dec_le(v_c_792_, v___x_829_);
if (v___x_830_ == 0)
{
goto v___jp_793_;
}
else
{
return v___x_830_;
}
}
}
v___jp_831_:
{
uint8_t v___x_832_; uint8_t v___x_833_; 
v___x_832_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_833_ = lean_uint8_dec_le(v___x_832_, v_c_792_);
if (v___x_833_ == 0)
{
goto v___jp_826_;
}
else
{
uint8_t v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
v___x_835_ = lean_uint8_dec_le(v_c_792_, v___x_834_);
if (v___x_835_ == 0)
{
goto v___jp_826_;
}
else
{
return v___x_835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUserInfoChar___boxed(lean_object* v_c_840_){
_start:
{
uint8_t v_c_boxed_841_; uint8_t v_res_842_; lean_object* v_r_843_; 
v_c_boxed_841_ = lean_unbox(v_c_840_);
v_res_842_ = l_Std_Http_Internal_Char_isUserInfoChar(v_c_boxed_841_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryDataChar(uint8_t v_c_844_){
_start:
{
uint8_t v___x_901_; uint8_t v___x_902_; 
v___x_901_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_902_ = lean_uint8_dec_le(v___x_901_, v_c_844_);
if (v___x_902_ == 0)
{
goto v___jp_896_;
}
else
{
uint8_t v___x_903_; uint8_t v___x_904_; 
v___x_903_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_904_ = lean_uint8_dec_le(v_c_844_, v___x_903_);
if (v___x_904_ == 0)
{
goto v___jp_896_;
}
else
{
goto v___jp_845_;
}
}
v___jp_845_:
{
uint8_t v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
v___x_847_ = lean_uint8_dec_eq(v_c_844_, v___x_846_);
if (v___x_847_ == 0)
{
uint8_t v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
v___x_849_ = lean_uint8_dec_eq(v_c_844_, v___x_848_);
if (v___x_849_ == 0)
{
uint8_t v___x_850_; 
v___x_850_ = 1;
return v___x_850_;
}
else
{
return v___x_847_;
}
}
else
{
uint8_t v___x_851_; 
v___x_851_ = 0;
return v___x_851_;
}
}
v___jp_852_:
{
uint8_t v___x_853_; uint8_t v___x_854_; 
v___x_853_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
v___x_854_ = lean_uint8_dec_eq(v_c_844_, v___x_853_);
if (v___x_854_ == 0)
{
uint8_t v___x_855_; uint8_t v___x_856_; 
v___x_855_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
v___x_856_ = lean_uint8_dec_eq(v_c_844_, v___x_855_);
if (v___x_856_ == 0)
{
uint8_t v___x_857_; uint8_t v___x_858_; 
v___x_857_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
v___x_858_ = lean_uint8_dec_eq(v_c_844_, v___x_857_);
if (v___x_858_ == 0)
{
uint8_t v___x_859_; uint8_t v___x_860_; 
v___x_859_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
v___x_860_ = lean_uint8_dec_eq(v_c_844_, v___x_859_);
if (v___x_860_ == 0)
{
uint8_t v___x_861_; uint8_t v___x_862_; 
v___x_861_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
v___x_862_ = lean_uint8_dec_eq(v_c_844_, v___x_861_);
if (v___x_862_ == 0)
{
uint8_t v___x_863_; uint8_t v___x_864_; 
v___x_863_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
v___x_864_ = lean_uint8_dec_eq(v_c_844_, v___x_863_);
if (v___x_864_ == 0)
{
uint8_t v___x_865_; uint8_t v___x_866_; 
v___x_865_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
v___x_866_ = lean_uint8_dec_eq(v_c_844_, v___x_865_);
if (v___x_866_ == 0)
{
uint8_t v___x_867_; uint8_t v___x_868_; 
v___x_867_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
v___x_868_ = lean_uint8_dec_eq(v_c_844_, v___x_867_);
if (v___x_868_ == 0)
{
uint8_t v___x_869_; uint8_t v___x_870_; 
v___x_869_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
v___x_870_ = lean_uint8_dec_eq(v_c_844_, v___x_869_);
if (v___x_870_ == 0)
{
uint8_t v___x_871_; uint8_t v___x_872_; 
v___x_871_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
v___x_872_ = lean_uint8_dec_eq(v_c_844_, v___x_871_);
if (v___x_872_ == 0)
{
uint8_t v___x_873_; uint8_t v___x_874_; 
v___x_873_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
v___x_874_ = lean_uint8_dec_eq(v_c_844_, v___x_873_);
if (v___x_874_ == 0)
{
uint8_t v___x_875_; uint8_t v___x_876_; 
v___x_875_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
v___x_876_ = lean_uint8_dec_eq(v_c_844_, v___x_875_);
if (v___x_876_ == 0)
{
uint8_t v___x_877_; uint8_t v___x_878_; 
v___x_877_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
v___x_878_ = lean_uint8_dec_eq(v_c_844_, v___x_877_);
if (v___x_878_ == 0)
{
uint8_t v___x_879_; uint8_t v___x_880_; 
v___x_879_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
v___x_880_ = lean_uint8_dec_eq(v_c_844_, v___x_879_);
if (v___x_880_ == 0)
{
uint8_t v___x_881_; uint8_t v___x_882_; 
v___x_881_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
v___x_882_ = lean_uint8_dec_eq(v_c_844_, v___x_881_);
if (v___x_882_ == 0)
{
uint8_t v___x_883_; uint8_t v___x_884_; 
v___x_883_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__0, &l_Std_Http_Internal_Char_isPChar___closed__0_once, _init_l_Std_Http_Internal_Char_isPChar___closed__0);
v___x_884_ = lean_uint8_dec_eq(v_c_844_, v___x_883_);
if (v___x_884_ == 0)
{
uint8_t v___x_885_; uint8_t v___x_886_; 
v___x_885_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__1, &l_Std_Http_Internal_Char_isPChar___closed__1_once, _init_l_Std_Http_Internal_Char_isPChar___closed__1);
v___x_886_ = lean_uint8_dec_eq(v_c_844_, v___x_885_);
if (v___x_886_ == 0)
{
uint8_t v___x_887_; uint8_t v___x_888_; 
v___x_887_ = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__0, &l_Std_Http_Internal_Char_isQueryChar___closed__0_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__0);
v___x_888_ = lean_uint8_dec_eq(v_c_844_, v___x_887_);
if (v___x_888_ == 0)
{
uint8_t v___x_889_; uint8_t v___x_890_; 
v___x_889_ = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__1, &l_Std_Http_Internal_Char_isQueryChar___closed__1_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__1);
v___x_890_ = lean_uint8_dec_eq(v_c_844_, v___x_889_);
if (v___x_890_ == 0)
{
return v___x_890_;
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
v___jp_891_:
{
uint8_t v___x_892_; uint8_t v___x_893_; 
v___x_892_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_893_ = lean_uint8_dec_le(v___x_892_, v_c_844_);
if (v___x_893_ == 0)
{
goto v___jp_852_;
}
else
{
uint8_t v___x_894_; uint8_t v___x_895_; 
v___x_894_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
v___x_895_ = lean_uint8_dec_le(v_c_844_, v___x_894_);
if (v___x_895_ == 0)
{
goto v___jp_852_;
}
else
{
goto v___jp_845_;
}
}
}
v___jp_896_:
{
uint8_t v___x_897_; uint8_t v___x_898_; 
v___x_897_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_898_ = lean_uint8_dec_le(v___x_897_, v_c_844_);
if (v___x_898_ == 0)
{
goto v___jp_891_;
}
else
{
uint8_t v___x_899_; uint8_t v___x_900_; 
v___x_899_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
v___x_900_ = lean_uint8_dec_le(v_c_844_, v___x_899_);
if (v___x_900_ == 0)
{
goto v___jp_891_;
}
else
{
goto v___jp_845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryDataChar___boxed(lean_object* v_c_905_){
_start:
{
uint8_t v_c_boxed_906_; uint8_t v_res_907_; lean_object* v_r_908_; 
v_c_boxed_906_ = lean_unbox(v_c_905_);
v_res_907_ = l_Std_Http_Internal_Char_isQueryDataChar(v_c_boxed_906_);
v_r_908_ = lean_box(v_res_907_);
return v_r_908_;
}
}
lean_object* runtime_initialize_Init_Data_Char(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Int(builtin);
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
lean_object* initialize_Init_Data_Int(uint8_t builtin);
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
res = initialize_Init_Data_Int(builtin);
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
