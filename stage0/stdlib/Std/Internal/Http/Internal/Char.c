// Lean compiler output
// Module: Std.Internal.Http.Internal.Char
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_39_; uint8_t v___x_44_; uint8_t v___x_45_; 
v___x_44_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_45_ = lean_uint8_dec_le(v___x_44_, v_c_37_);
if (v___x_45_ == 0)
{
v___y_39_ = v___x_45_;
goto v___jp_38_;
}
else
{
uint8_t v___x_46_; uint8_t v___x_47_; 
v___x_46_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
v___x_47_ = lean_uint8_dec_le(v_c_37_, v___x_46_);
v___y_39_ = v___x_47_;
goto v___jp_38_;
}
v___jp_38_:
{
if (v___y_39_ == 0)
{
uint8_t v___x_40_; uint8_t v___x_41_; 
v___x_40_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_41_ = lean_uint8_dec_le(v___x_40_, v_c_37_);
if (v___x_41_ == 0)
{
return v___x_41_;
}
else
{
uint8_t v___x_42_; uint8_t v___x_43_; 
v___x_42_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
v___x_43_ = lean_uint8_dec_le(v_c_37_, v___x_42_);
return v___x_43_;
}
}
else
{
return v___y_39_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAlphaByte___boxed(lean_object* v_c_48_){
_start:
{
uint8_t v_c_boxed_49_; uint8_t v_res_50_; lean_object* v_r_51_; 
v_c_boxed_49_ = lean_unbox(v_c_48_);
v_res_50_ = l_Std_Http_Internal_Char_isAlphaByte(v_c_boxed_49_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_tchar(uint32_t v_c_52_){
_start:
{
uint8_t v___y_59_; uint32_t v___x_64_; uint8_t v___x_65_; 
v___x_64_ = 33;
v___x_65_ = lean_uint32_dec_eq(v_c_52_, v___x_64_);
if (v___x_65_ == 0)
{
uint32_t v___x_66_; uint8_t v___x_67_; 
v___x_66_ = 35;
v___x_67_ = lean_uint32_dec_eq(v_c_52_, v___x_66_);
if (v___x_67_ == 0)
{
uint32_t v___x_68_; uint8_t v___x_69_; 
v___x_68_ = 36;
v___x_69_ = lean_uint32_dec_eq(v_c_52_, v___x_68_);
if (v___x_69_ == 0)
{
uint32_t v___x_70_; uint8_t v___x_71_; 
v___x_70_ = 37;
v___x_71_ = lean_uint32_dec_eq(v_c_52_, v___x_70_);
if (v___x_71_ == 0)
{
uint32_t v___x_72_; uint8_t v___x_73_; 
v___x_72_ = 38;
v___x_73_ = lean_uint32_dec_eq(v_c_52_, v___x_72_);
if (v___x_73_ == 0)
{
uint32_t v___x_74_; uint8_t v___x_75_; 
v___x_74_ = 39;
v___x_75_ = lean_uint32_dec_eq(v_c_52_, v___x_74_);
if (v___x_75_ == 0)
{
uint32_t v___x_76_; uint8_t v___x_77_; 
v___x_76_ = 42;
v___x_77_ = lean_uint32_dec_eq(v_c_52_, v___x_76_);
if (v___x_77_ == 0)
{
uint32_t v___x_78_; uint8_t v___x_79_; 
v___x_78_ = 43;
v___x_79_ = lean_uint32_dec_eq(v_c_52_, v___x_78_);
if (v___x_79_ == 0)
{
uint32_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 45;
v___x_81_ = lean_uint32_dec_eq(v_c_52_, v___x_80_);
if (v___x_81_ == 0)
{
uint32_t v___x_82_; uint8_t v___x_83_; 
v___x_82_ = 46;
v___x_83_ = lean_uint32_dec_eq(v_c_52_, v___x_82_);
if (v___x_83_ == 0)
{
uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 94;
v___x_85_ = lean_uint32_dec_eq(v_c_52_, v___x_84_);
if (v___x_85_ == 0)
{
uint32_t v___x_86_; uint8_t v___x_87_; 
v___x_86_ = 95;
v___x_87_ = lean_uint32_dec_eq(v_c_52_, v___x_86_);
if (v___x_87_ == 0)
{
uint32_t v___x_88_; uint8_t v___x_89_; 
v___x_88_ = 96;
v___x_89_ = lean_uint32_dec_eq(v_c_52_, v___x_88_);
if (v___x_89_ == 0)
{
uint32_t v___x_90_; uint8_t v___x_91_; 
v___x_90_ = 124;
v___x_91_ = lean_uint32_dec_eq(v_c_52_, v___x_90_);
if (v___x_91_ == 0)
{
uint32_t v___x_92_; uint8_t v___x_93_; 
v___x_92_ = 126;
v___x_93_ = lean_uint32_dec_eq(v_c_52_, v___x_92_);
if (v___x_93_ == 0)
{
uint32_t v___x_94_; uint8_t v___x_95_; 
v___x_94_ = 48;
v___x_95_ = lean_uint32_dec_le(v___x_94_, v_c_52_);
if (v___x_95_ == 0)
{
v___y_59_ = v___x_95_;
goto v___jp_58_;
}
else
{
uint32_t v___x_96_; uint8_t v___x_97_; 
v___x_96_ = 57;
v___x_97_ = lean_uint32_dec_le(v_c_52_, v___x_96_);
v___y_59_ = v___x_97_;
goto v___jp_58_;
}
}
else
{
return v___x_93_;
}
}
else
{
return v___x_91_;
}
}
else
{
return v___x_89_;
}
}
else
{
return v___x_87_;
}
}
else
{
return v___x_85_;
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
v___jp_53_:
{
uint32_t v___x_54_; uint8_t v___x_55_; 
v___x_54_ = 97;
v___x_55_ = lean_uint32_dec_le(v___x_54_, v_c_52_);
if (v___x_55_ == 0)
{
return v___x_55_;
}
else
{
uint32_t v___x_56_; uint8_t v___x_57_; 
v___x_56_ = 122;
v___x_57_ = lean_uint32_dec_le(v_c_52_, v___x_56_);
return v___x_57_;
}
}
v___jp_58_:
{
if (v___y_59_ == 0)
{
uint32_t v___x_60_; uint8_t v___x_61_; 
v___x_60_ = 65;
v___x_61_ = lean_uint32_dec_le(v___x_60_, v_c_52_);
if (v___x_61_ == 0)
{
goto v___jp_53_;
}
else
{
uint32_t v___x_62_; uint8_t v___x_63_; 
v___x_62_ = 90;
v___x_63_ = lean_uint32_dec_le(v_c_52_, v___x_62_);
if (v___x_63_ == 0)
{
goto v___jp_53_;
}
else
{
return v___x_63_;
}
}
}
else
{
return v___y_59_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_tchar___boxed(lean_object* v_c_98_){
_start:
{
uint32_t v_c_boxed_99_; uint8_t v_res_100_; lean_object* v_r_101_; 
v_c_boxed_99_ = lean_unbox_uint32(v_c_98_);
lean_dec(v_c_98_);
v_res_100_ = l_Std_Http_Internal_Char_tchar(v_c_boxed_99_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_vchar(uint32_t v_c_102_){
_start:
{
uint32_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = 33;
v___x_104_ = lean_uint32_dec_le(v___x_103_, v_c_102_);
if (v___x_104_ == 0)
{
return v___x_104_;
}
else
{
uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_105_ = 126;
v___x_106_ = lean_uint32_dec_le(v_c_102_, v___x_105_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_vchar___boxed(lean_object* v_c_107_){
_start:
{
uint32_t v_c_boxed_108_; uint8_t v_res_109_; lean_object* v_r_110_; 
v_c_boxed_108_ = lean_unbox_uint32(v_c_107_);
lean_dec(v_c_107_);
v_res_109_ = l_Std_Http_Internal_Char_vchar(v_c_boxed_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_qdtext(uint32_t v_c_111_){
_start:
{
uint32_t v___x_117_; uint8_t v___x_118_; 
v___x_117_ = 9;
v___x_118_ = lean_uint32_dec_eq(v_c_111_, v___x_117_);
if (v___x_118_ == 0)
{
uint32_t v___x_119_; uint8_t v___x_120_; 
v___x_119_ = 32;
v___x_120_ = lean_uint32_dec_eq(v_c_111_, v___x_119_);
if (v___x_120_ == 0)
{
uint32_t v___x_121_; uint8_t v___x_122_; 
v___x_121_ = 33;
v___x_122_ = lean_uint32_dec_eq(v_c_111_, v___x_121_);
if (v___x_122_ == 0)
{
uint32_t v___x_123_; uint8_t v___x_124_; 
v___x_123_ = 35;
v___x_124_ = lean_uint32_dec_le(v___x_123_, v_c_111_);
if (v___x_124_ == 0)
{
goto v___jp_112_;
}
else
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 91;
v___x_126_ = lean_uint32_dec_le(v_c_111_, v___x_125_);
if (v___x_126_ == 0)
{
goto v___jp_112_;
}
else
{
return v___x_126_;
}
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
v___jp_112_:
{
uint32_t v___x_113_; uint8_t v___x_114_; 
v___x_113_ = 93;
v___x_114_ = lean_uint32_dec_le(v___x_113_, v_c_111_);
if (v___x_114_ == 0)
{
return v___x_114_;
}
else
{
uint32_t v___x_115_; uint8_t v___x_116_; 
v___x_115_ = 126;
v___x_116_ = lean_uint32_dec_le(v_c_111_, v___x_115_);
return v___x_116_;
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
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 9;
v___x_160_ = lean_uint32_dec_eq(v_c_144_, v___x_159_);
if (v___x_160_ == 0)
{
uint32_t v___x_161_; uint8_t v___x_162_; 
v___x_161_ = 32;
v___x_162_ = lean_uint32_dec_eq(v_c_144_, v___x_161_);
if (v___x_162_ == 0)
{
uint32_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 33;
v___x_164_ = lean_uint32_dec_eq(v_c_144_, v___x_163_);
if (v___x_164_ == 0)
{
uint32_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 35;
v___x_166_ = lean_uint32_dec_le(v___x_165_, v_c_144_);
if (v___x_166_ == 0)
{
goto v___jp_154_;
}
else
{
uint32_t v___x_167_; uint8_t v___x_168_; 
v___x_167_ = 91;
v___x_168_ = lean_uint32_dec_le(v_c_144_, v___x_167_);
if (v___x_168_ == 0)
{
goto v___jp_154_;
}
else
{
return v___x_168_;
}
}
}
else
{
return v___x_164_;
}
}
else
{
return v___x_162_;
}
}
else
{
return v___x_160_;
}
v___jp_145_:
{
uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_146_ = 9;
v___x_147_ = lean_uint32_dec_eq(v_c_144_, v___x_146_);
if (v___x_147_ == 0)
{
uint32_t v___x_148_; uint8_t v___x_149_; 
v___x_148_ = 32;
v___x_149_ = lean_uint32_dec_eq(v_c_144_, v___x_148_);
if (v___x_149_ == 0)
{
uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_150_ = 33;
v___x_151_ = lean_uint32_dec_le(v___x_150_, v_c_144_);
if (v___x_151_ == 0)
{
return v___x_151_;
}
else
{
uint32_t v___x_152_; uint8_t v___x_153_; 
v___x_152_ = 126;
v___x_153_ = lean_uint32_dec_le(v_c_144_, v___x_152_);
return v___x_153_;
}
}
else
{
return v___x_149_;
}
}
else
{
return v___x_147_;
}
}
v___jp_154_:
{
uint32_t v___x_155_; uint8_t v___x_156_; 
v___x_155_ = 93;
v___x_156_ = lean_uint32_dec_le(v___x_155_, v_c_144_);
if (v___x_156_ == 0)
{
goto v___jp_145_;
}
else
{
uint32_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 126;
v___x_158_ = lean_uint32_dec_le(v_c_144_, v___x_157_);
if (v___x_158_ == 0)
{
goto v___jp_145_;
}
else
{
return v___x_158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_quotedStringChar___boxed(lean_object* v_c_169_){
_start:
{
uint32_t v_c_boxed_170_; uint8_t v_res_171_; lean_object* v_r_172_; 
v_c_boxed_170_ = lean_unbox_uint32(v_c_169_);
lean_dec(v_c_169_);
v_res_171_ = l_Std_Http_Internal_Char_quotedStringChar(v_c_boxed_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg(uint32_t v_c_173_, lean_object* v_h__1_174_, lean_object* v_h__2_175_, lean_object* v_h__3_176_, lean_object* v_h__4_177_){
_start:
{
uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = 9;
v___x_179_ = lean_uint32_dec_eq(v_c_173_, v___x_178_);
if (v___x_179_ == 0)
{
uint32_t v___x_180_; uint8_t v___x_181_; 
lean_dec(v_h__1_174_);
v___x_180_ = 32;
v___x_181_ = lean_uint32_dec_eq(v_c_173_, v___x_180_);
if (v___x_181_ == 0)
{
uint32_t v___x_182_; uint8_t v___x_183_; 
lean_dec(v_h__2_175_);
v___x_182_ = 33;
v___x_183_ = lean_uint32_dec_eq(v_c_173_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec(v_h__3_176_);
v___x_184_ = lean_box_uint32(v_c_173_);
v___x_185_ = lean_apply_4(v_h__4_177_, v___x_184_, lean_box(0), lean_box(0), lean_box(0));
return v___x_185_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec(v_h__4_177_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_apply_1(v_h__3_176_, v___x_186_);
return v___x_187_;
}
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v_h__4_177_);
lean_dec(v_h__3_176_);
v___x_188_ = lean_box(0);
v___x_189_ = lean_apply_1(v_h__2_175_, v___x_188_);
return v___x_189_;
}
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v_h__4_177_);
lean_dec(v_h__3_176_);
lean_dec(v_h__2_175_);
v___x_190_ = lean_box(0);
v___x_191_ = lean_apply_1(v_h__1_174_, v___x_190_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg___boxed(lean_object* v_c_192_, lean_object* v_h__1_193_, lean_object* v_h__2_194_, lean_object* v_h__3_195_, lean_object* v_h__4_196_){
_start:
{
uint32_t v_c_46__boxed_197_; lean_object* v_res_198_; 
v_c_46__boxed_197_ = lean_unbox_uint32(v_c_192_);
lean_dec(v_c_192_);
v_res_198_ = l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg(v_c_46__boxed_197_, v_h__1_193_, v_h__2_194_, v_h__3_195_, v_h__4_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(lean_object* v_motive_199_, uint32_t v_c_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_, lean_object* v_h__3_203_, lean_object* v_h__4_204_){
_start:
{
uint32_t v___x_205_; uint8_t v___x_206_; 
v___x_205_ = 9;
v___x_206_ = lean_uint32_dec_eq(v_c_200_, v___x_205_);
if (v___x_206_ == 0)
{
uint32_t v___x_207_; uint8_t v___x_208_; 
lean_dec(v_h__1_201_);
v___x_207_ = 32;
v___x_208_ = lean_uint32_dec_eq(v_c_200_, v___x_207_);
if (v___x_208_ == 0)
{
uint32_t v___x_209_; uint8_t v___x_210_; 
lean_dec(v_h__2_202_);
v___x_209_ = 33;
v___x_210_ = lean_uint32_dec_eq(v_c_200_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_h__3_203_);
v___x_211_ = lean_box_uint32(v_c_200_);
v___x_212_ = lean_apply_4(v_h__4_204_, v___x_211_, lean_box(0), lean_box(0), lean_box(0));
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v_h__4_204_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_apply_1(v_h__3_203_, v___x_213_);
return v___x_214_;
}
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec(v_h__4_204_);
lean_dec(v_h__3_203_);
v___x_215_ = lean_box(0);
v___x_216_ = lean_apply_1(v_h__2_202_, v___x_215_);
return v___x_216_;
}
}
else
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec(v_h__4_204_);
lean_dec(v_h__3_203_);
lean_dec(v_h__2_202_);
v___x_217_ = lean_box(0);
v___x_218_ = lean_apply_1(v_h__1_201_, v___x_217_);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___boxed(lean_object* v_motive_219_, lean_object* v_c_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_, lean_object* v_h__3_223_, lean_object* v_h__4_224_){
_start:
{
uint32_t v_c_77__boxed_225_; lean_object* v_res_226_; 
v_c_77__boxed_225_ = lean_unbox_uint32(v_c_220_);
lean_dec(v_c_220_);
v_res_226_ = l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(v_motive_219_, v_c_77__boxed_225_, v_h__1_221_, v_h__2_222_, v_h__3_223_, v_h__4_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(uint32_t v_c_227_, lean_object* v_h__1_228_, lean_object* v_h__2_229_, lean_object* v_h__3_230_){
_start:
{
uint32_t v___x_231_; uint8_t v___x_232_; 
v___x_231_ = 9;
v___x_232_ = lean_uint32_dec_eq(v_c_227_, v___x_231_);
if (v___x_232_ == 0)
{
uint32_t v___x_233_; uint8_t v___x_234_; 
lean_dec(v_h__1_228_);
v___x_233_ = 32;
v___x_234_ = lean_uint32_dec_eq(v_c_227_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec(v_h__2_229_);
v___x_235_ = lean_box_uint32(v_c_227_);
v___x_236_ = lean_apply_3(v_h__3_230_, v___x_235_, lean_box(0), lean_box(0));
return v___x_236_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec(v_h__3_230_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_apply_1(v_h__2_229_, v___x_237_);
return v___x_238_;
}
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec(v_h__3_230_);
lean_dec(v_h__2_229_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_apply_1(v_h__1_228_, v___x_239_);
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg___boxed(lean_object* v_c_241_, lean_object* v_h__1_242_, lean_object* v_h__2_243_, lean_object* v_h__3_244_){
_start:
{
uint32_t v_c_33__boxed_245_; lean_object* v_res_246_; 
v_c_33__boxed_245_ = lean_unbox_uint32(v_c_241_);
lean_dec(v_c_241_);
v_res_246_ = l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(v_c_33__boxed_245_, v_h__1_242_, v_h__2_243_, v_h__3_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(lean_object* v_motive_247_, uint32_t v_c_248_, lean_object* v_h__1_249_, lean_object* v_h__2_250_, lean_object* v_h__3_251_){
_start:
{
uint32_t v___x_252_; uint8_t v___x_253_; 
v___x_252_ = 9;
v___x_253_ = lean_uint32_dec_eq(v_c_248_, v___x_252_);
if (v___x_253_ == 0)
{
uint32_t v___x_254_; uint8_t v___x_255_; 
lean_dec(v_h__1_249_);
v___x_254_ = 32;
v___x_255_ = lean_uint32_dec_eq(v_c_248_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec(v_h__2_250_);
v___x_256_ = lean_box_uint32(v_c_248_);
v___x_257_ = lean_apply_3(v_h__3_251_, v___x_256_, lean_box(0), lean_box(0));
return v___x_257_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec(v_h__3_251_);
v___x_258_ = lean_box(0);
v___x_259_ = lean_apply_1(v_h__2_250_, v___x_258_);
return v___x_259_;
}
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_h__3_251_);
lean_dec(v_h__2_250_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_apply_1(v_h__1_249_, v___x_260_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___boxed(lean_object* v_motive_262_, lean_object* v_c_263_, lean_object* v_h__1_264_, lean_object* v_h__2_265_, lean_object* v_h__3_266_){
_start:
{
uint32_t v_c_56__boxed_267_; lean_object* v_res_268_; 
v_c_56__boxed_267_ = lean_unbox_uint32(v_c_263_);
lean_dec(v_c_263_);
v_res_268_ = l___private_Std_Internal_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(v_motive_262_, v_c_56__boxed_267_, v_h__1_264_, v_h__2_265_, v_h__3_266_);
return v_res_268_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_fieldVchar(uint32_t v_c_269_){
_start:
{
uint32_t v___x_270_; uint8_t v___x_271_; 
v___x_270_ = 33;
v___x_271_ = lean_uint32_dec_le(v___x_270_, v_c_269_);
if (v___x_271_ == 0)
{
return v___x_271_;
}
else
{
uint32_t v___x_272_; uint8_t v___x_273_; 
v___x_272_ = 126;
v___x_273_ = lean_uint32_dec_le(v_c_269_, v___x_272_);
return v___x_273_;
}
}
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
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_fieldContent(uint32_t v_c_278_){
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldContent___boxed(lean_object* v_c_288_){
_start:
{
uint32_t v_c_boxed_289_; uint8_t v_res_290_; lean_object* v_r_291_; 
v_c_boxed_289_ = lean_unbox_uint32(v_c_288_);
lean_dec(v_c_288_);
v_res_290_ = l_Std_Http_Internal_Char_fieldContent(v_c_boxed_289_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_ctext(uint32_t v_c_292_){
_start:
{
uint32_t v___x_303_; uint8_t v___x_304_; 
v___x_303_ = 9;
v___x_304_ = lean_uint32_dec_eq(v_c_292_, v___x_303_);
if (v___x_304_ == 0)
{
uint32_t v___x_305_; uint8_t v___x_306_; 
v___x_305_ = 32;
v___x_306_ = lean_uint32_dec_eq(v_c_292_, v___x_305_);
if (v___x_306_ == 0)
{
uint32_t v___x_307_; uint8_t v___x_308_; 
v___x_307_ = 33;
v___x_308_ = lean_uint32_dec_le(v___x_307_, v_c_292_);
if (v___x_308_ == 0)
{
goto v___jp_298_;
}
else
{
uint32_t v___x_309_; uint8_t v___x_310_; 
v___x_309_ = 39;
v___x_310_ = lean_uint32_dec_le(v_c_292_, v___x_309_);
if (v___x_310_ == 0)
{
goto v___jp_298_;
}
else
{
return v___x_310_;
}
}
}
else
{
return v___x_306_;
}
}
else
{
return v___x_304_;
}
v___jp_293_:
{
uint32_t v___x_294_; uint8_t v___x_295_; 
v___x_294_ = 93;
v___x_295_ = lean_uint32_dec_le(v___x_294_, v_c_292_);
if (v___x_295_ == 0)
{
return v___x_295_;
}
else
{
uint32_t v___x_296_; uint8_t v___x_297_; 
v___x_296_ = 126;
v___x_297_ = lean_uint32_dec_le(v_c_292_, v___x_296_);
return v___x_297_;
}
}
v___jp_298_:
{
uint32_t v___x_299_; uint8_t v___x_300_; 
v___x_299_ = 42;
v___x_300_ = lean_uint32_dec_le(v___x_299_, v_c_292_);
if (v___x_300_ == 0)
{
goto v___jp_293_;
}
else
{
uint32_t v___x_301_; uint8_t v___x_302_; 
v___x_301_ = 91;
v___x_302_ = lean_uint32_dec_le(v_c_292_, v___x_301_);
if (v___x_302_ == 0)
{
goto v___jp_293_;
}
else
{
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ctext___boxed(lean_object* v_c_311_){
_start:
{
uint32_t v_c_boxed_312_; uint8_t v_res_313_; lean_object* v_r_314_; 
v_c_boxed_312_ = lean_unbox_uint32(v_c_311_);
lean_dec(v_c_311_);
v_res_313_ = l_Std_Http_Internal_Char_ctext(v_c_boxed_312_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_etagc(uint32_t v_c_315_){
_start:
{
uint32_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 33;
v___x_317_ = lean_uint32_dec_eq(v_c_315_, v___x_316_);
if (v___x_317_ == 0)
{
uint32_t v___x_318_; uint8_t v___x_319_; 
v___x_318_ = 35;
v___x_319_ = lean_uint32_dec_le(v___x_318_, v_c_315_);
if (v___x_319_ == 0)
{
return v___x_317_;
}
else
{
uint32_t v___x_320_; uint8_t v___x_321_; 
v___x_320_ = 126;
v___x_321_ = lean_uint32_dec_le(v_c_315_, v___x_320_);
if (v___x_321_ == 0)
{
return v___x_317_;
}
else
{
return v___x_321_;
}
}
}
else
{
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_etagc___boxed(lean_object* v_c_322_){
_start:
{
uint32_t v_c_boxed_323_; uint8_t v_res_324_; lean_object* v_r_325_; 
v_c_boxed_323_ = lean_unbox_uint32(v_c_322_);
lean_dec(v_c_322_);
v_res_324_ = l_Std_Http_Internal_Char_etagc(v_c_boxed_323_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_ows(uint32_t v_c_326_){
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ows___boxed(lean_object* v_c_331_){
_start:
{
uint32_t v_c_boxed_332_; uint8_t v_res_333_; lean_object* v_r_334_; 
v_c_boxed_332_ = lean_unbox_uint32(v_c_331_);
lean_dec(v_c_331_);
v_res_333_ = l_Std_Http_Internal_Char_ows(v_c_boxed_332_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_bws(uint32_t v_c_335_){
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_bws___boxed(lean_object* v_c_340_){
_start:
{
uint32_t v_c_boxed_341_; uint8_t v_res_342_; lean_object* v_r_343_; 
v_c_boxed_341_ = lean_unbox_uint32(v_c_340_);
lean_dec(v_c_340_);
v_res_342_ = l_Std_Http_Internal_Char_bws(v_c_boxed_341_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_rws(uint32_t v_c_344_){
_start:
{
uint32_t v___x_345_; uint8_t v___x_346_; 
v___x_345_ = 32;
v___x_346_ = lean_uint32_dec_eq(v_c_344_, v___x_345_);
if (v___x_346_ == 0)
{
uint32_t v___x_347_; uint8_t v___x_348_; 
v___x_347_ = 9;
v___x_348_ = lean_uint32_dec_eq(v_c_344_, v___x_347_);
return v___x_348_;
}
else
{
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_rws___boxed(lean_object* v_c_349_){
_start:
{
uint32_t v_c_boxed_350_; uint8_t v_res_351_; lean_object* v_r_352_; 
v_c_boxed_350_ = lean_unbox_uint32(v_c_349_);
lean_dec(v_c_349_);
v_res_351_ = l_Std_Http_Internal_Char_rws(v_c_boxed_350_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_obsText(uint32_t v_c_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_354_ = lean_unsigned_to_nat(128u);
v___x_355_ = lean_uint32_to_nat(v_c_353_);
v___x_356_ = lean_nat_dec_le(v___x_354_, v___x_355_);
lean_dec(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_obsText___boxed(lean_object* v_c_357_){
_start:
{
uint32_t v_c_boxed_358_; uint8_t v_res_359_; lean_object* v_r_360_; 
v_c_boxed_358_ = lean_unbox_uint32(v_c_357_);
lean_dec(v_c_357_);
v_res_359_ = l_Std_Http_Internal_Char_obsText(v_c_boxed_358_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_reasonPhraseChar(uint32_t v_c_361_){
_start:
{
uint32_t v___x_362_; uint8_t v___x_363_; 
v___x_362_ = 9;
v___x_363_ = lean_uint32_dec_eq(v_c_361_, v___x_362_);
if (v___x_363_ == 0)
{
uint32_t v___x_364_; uint8_t v___x_365_; 
v___x_364_ = 32;
v___x_365_ = lean_uint32_dec_eq(v_c_361_, v___x_364_);
if (v___x_365_ == 0)
{
uint32_t v___x_366_; uint8_t v___x_367_; 
v___x_366_ = 33;
v___x_367_ = lean_uint32_dec_le(v___x_366_, v_c_361_);
if (v___x_367_ == 0)
{
return v___x_367_;
}
else
{
uint32_t v___x_368_; uint8_t v___x_369_; 
v___x_368_ = 126;
v___x_369_ = lean_uint32_dec_le(v_c_361_, v___x_368_);
return v___x_369_;
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_reasonPhraseChar___boxed(lean_object* v_c_370_){
_start:
{
uint32_t v_c_boxed_371_; uint8_t v_res_372_; lean_object* v_r_373_; 
v_c_boxed_371_ = lean_unbox_uint32(v_c_370_);
lean_dec(v_c_370_);
v_res_372_ = l_Std_Http_Internal_Char_reasonPhraseChar(v_c_boxed_371_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isHexDigit(uint32_t v_c_374_){
_start:
{
uint32_t v___x_375_; uint8_t v___x_376_; 
v___x_375_ = 97;
v___x_376_ = lean_uint32_dec_eq(v_c_374_, v___x_375_);
if (v___x_376_ == 0)
{
uint32_t v___x_377_; uint8_t v___x_378_; 
v___x_377_ = 98;
v___x_378_ = lean_uint32_dec_eq(v_c_374_, v___x_377_);
if (v___x_378_ == 0)
{
uint32_t v___x_379_; uint8_t v___x_380_; 
v___x_379_ = 99;
v___x_380_ = lean_uint32_dec_eq(v_c_374_, v___x_379_);
if (v___x_380_ == 0)
{
uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = 100;
v___x_382_ = lean_uint32_dec_eq(v_c_374_, v___x_381_);
if (v___x_382_ == 0)
{
uint32_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = 101;
v___x_384_ = lean_uint32_dec_eq(v_c_374_, v___x_383_);
if (v___x_384_ == 0)
{
uint32_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 102;
v___x_386_ = lean_uint32_dec_eq(v_c_374_, v___x_385_);
if (v___x_386_ == 0)
{
uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 65;
v___x_388_ = lean_uint32_dec_eq(v_c_374_, v___x_387_);
if (v___x_388_ == 0)
{
uint32_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 66;
v___x_390_ = lean_uint32_dec_eq(v_c_374_, v___x_389_);
if (v___x_390_ == 0)
{
uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 67;
v___x_392_ = lean_uint32_dec_eq(v_c_374_, v___x_391_);
if (v___x_392_ == 0)
{
uint32_t v___x_393_; uint8_t v___x_394_; 
v___x_393_ = 68;
v___x_394_ = lean_uint32_dec_eq(v_c_374_, v___x_393_);
if (v___x_394_ == 0)
{
uint32_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = 69;
v___x_396_ = lean_uint32_dec_eq(v_c_374_, v___x_395_);
if (v___x_396_ == 0)
{
uint32_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 70;
v___x_398_ = lean_uint32_dec_eq(v_c_374_, v___x_397_);
if (v___x_398_ == 0)
{
uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_399_ = 48;
v___x_400_ = lean_uint32_dec_le(v___x_399_, v_c_374_);
if (v___x_400_ == 0)
{
return v___x_400_;
}
else
{
uint32_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = 57;
v___x_402_ = lean_uint32_dec_le(v_c_374_, v___x_401_);
return v___x_402_;
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
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigit___boxed(lean_object* v_c_403_){
_start:
{
uint32_t v_c_boxed_404_; uint8_t v_res_405_; lean_object* v_r_406_; 
v_c_boxed_404_ = lean_unbox_uint32(v_c_403_);
lean_dec(v_c_403_);
v_res_405_ = l_Std_Http_Internal_Char_isHexDigit(v_c_boxed_404_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__0(void){
_start:
{
uint32_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = 70;
v___x_408_ = lean_uint32_to_uint8(v___x_407_);
return v___x_408_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__1(void){
_start:
{
uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 102;
v___x_410_ = lean_uint32_to_uint8(v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isHexDigitByte(uint8_t v_c_411_){
_start:
{
uint8_t v___y_413_; uint8_t v___y_419_; uint8_t v___x_424_; uint8_t v___x_425_; 
v___x_424_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_425_ = lean_uint8_dec_le(v___x_424_, v_c_411_);
if (v___x_425_ == 0)
{
v___y_419_ = v___x_425_;
goto v___jp_418_;
}
else
{
uint8_t v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_427_ = lean_uint8_dec_le(v_c_411_, v___x_426_);
v___y_419_ = v___x_427_;
goto v___jp_418_;
}
v___jp_412_:
{
if (v___y_413_ == 0)
{
uint8_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_415_ = lean_uint8_dec_le(v___x_414_, v_c_411_);
if (v___x_415_ == 0)
{
return v___x_415_;
}
else
{
uint8_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = lean_uint8_once(&l_Std_Http_Internal_Char_isHexDigitByte___closed__0, &l_Std_Http_Internal_Char_isHexDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__0);
v___x_417_ = lean_uint8_dec_le(v_c_411_, v___x_416_);
return v___x_417_;
}
}
else
{
return v___y_413_;
}
}
v___jp_418_:
{
if (v___y_419_ == 0)
{
uint8_t v___x_420_; uint8_t v___x_421_; 
v___x_420_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_421_ = lean_uint8_dec_le(v___x_420_, v_c_411_);
if (v___x_421_ == 0)
{
v___y_413_ = v___x_421_;
goto v___jp_412_;
}
else
{
uint8_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = lean_uint8_once(&l_Std_Http_Internal_Char_isHexDigitByte___closed__1, &l_Std_Http_Internal_Char_isHexDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__1);
v___x_423_ = lean_uint8_dec_le(v_c_411_, v___x_422_);
v___y_413_ = v___x_423_;
goto v___jp_412_;
}
}
else
{
return v___y_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigitByte___boxed(lean_object* v_c_428_){
_start:
{
uint8_t v_c_boxed_429_; uint8_t v_res_430_; lean_object* v_r_431_; 
v_c_boxed_429_ = lean_unbox(v_c_428_);
v_res_430_ = l_Std_Http_Internal_Char_isHexDigitByte(v_c_boxed_429_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAlphaNum(uint8_t v_c_432_){
_start:
{
uint8_t v___y_434_; uint8_t v___y_440_; uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_446_ = lean_uint8_dec_le(v___x_445_, v_c_432_);
if (v___x_446_ == 0)
{
v___y_440_ = v___x_446_;
goto v___jp_439_;
}
else
{
uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_448_ = lean_uint8_dec_le(v_c_432_, v___x_447_);
v___y_440_ = v___x_448_;
goto v___jp_439_;
}
v___jp_433_:
{
if (v___y_434_ == 0)
{
uint8_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_436_ = lean_uint8_dec_le(v___x_435_, v_c_432_);
if (v___x_436_ == 0)
{
return v___x_436_;
}
else
{
uint8_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
v___x_438_ = lean_uint8_dec_le(v_c_432_, v___x_437_);
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
if (v___y_440_ == 0)
{
uint8_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_442_ = lean_uint8_dec_le(v___x_441_, v_c_432_);
if (v___x_442_ == 0)
{
v___y_434_ = v___x_442_;
goto v___jp_433_;
}
else
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
v___x_444_ = lean_uint8_dec_le(v_c_432_, v___x_443_);
v___y_434_ = v___x_444_;
goto v___jp_433_;
}
}
else
{
return v___y_440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAlphaNum___boxed(lean_object* v_c_449_){
_start:
{
uint8_t v_c_boxed_450_; uint8_t v_res_451_; lean_object* v_r_452_; 
v_c_boxed_450_ = lean_unbox(v_c_449_);
v_res_451_ = l_Std_Http_Internal_Char_isAlphaNum(v_c_boxed_450_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAsciiAlphaNumChar(uint32_t v_c_453_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; uint8_t v___y_463_; 
v___x_459_ = lean_uint32_to_nat(v_c_453_);
v___x_460_ = lean_unsigned_to_nat(128u);
v___x_461_ = lean_nat_dec_lt(v___x_459_, v___x_460_);
lean_dec(v___x_459_);
if (v___x_461_ == 0)
{
return v___x_461_;
}
else
{
uint32_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = 48;
v___x_469_ = lean_uint32_dec_le(v___x_468_, v_c_453_);
if (v___x_469_ == 0)
{
v___y_463_ = v___x_469_;
goto v___jp_462_;
}
else
{
uint32_t v___x_470_; uint8_t v___x_471_; 
v___x_470_ = 57;
v___x_471_ = lean_uint32_dec_le(v_c_453_, v___x_470_);
v___y_463_ = v___x_471_;
goto v___jp_462_;
}
}
v___jp_454_:
{
uint32_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 97;
v___x_456_ = lean_uint32_dec_le(v___x_455_, v_c_453_);
if (v___x_456_ == 0)
{
return v___x_456_;
}
else
{
uint32_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = 122;
v___x_458_ = lean_uint32_dec_le(v_c_453_, v___x_457_);
return v___x_458_;
}
}
v___jp_462_:
{
if (v___y_463_ == 0)
{
uint32_t v___x_464_; uint8_t v___x_465_; 
v___x_464_ = 65;
v___x_465_ = lean_uint32_dec_le(v___x_464_, v_c_453_);
if (v___x_465_ == 0)
{
goto v___jp_454_;
}
else
{
uint32_t v___x_466_; uint8_t v___x_467_; 
v___x_466_ = 90;
v___x_467_ = lean_uint32_dec_le(v_c_453_, v___x_466_);
if (v___x_467_ == 0)
{
goto v___jp_454_;
}
else
{
return v___x_461_;
}
}
}
else
{
return v___y_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAsciiAlphaNumChar___boxed(lean_object* v_c_472_){
_start:
{
uint32_t v_c_boxed_473_; uint8_t v_res_474_; lean_object* v_r_475_; 
v_c_boxed_473_ = lean_unbox_uint32(v_c_472_);
lean_dec(v_c_472_);
v_res_474_ = l_Std_Http_Internal_Char_isAsciiAlphaNumChar(v_c_boxed_473_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isValidSchemeChar(uint32_t v_c_476_){
_start:
{
uint8_t v___y_478_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; uint8_t v___y_494_; 
v___x_490_ = lean_uint32_to_nat(v_c_476_);
v___x_491_ = lean_unsigned_to_nat(128u);
v___x_492_ = lean_nat_dec_lt(v___x_490_, v___x_491_);
lean_dec(v___x_490_);
if (v___x_492_ == 0)
{
v___y_478_ = v___x_492_;
goto v___jp_477_;
}
else
{
uint32_t v___x_499_; uint8_t v___x_500_; 
v___x_499_ = 48;
v___x_500_ = lean_uint32_dec_le(v___x_499_, v_c_476_);
if (v___x_500_ == 0)
{
v___y_494_ = v___x_500_;
goto v___jp_493_;
}
else
{
uint32_t v___x_501_; uint8_t v___x_502_; 
v___x_501_ = 57;
v___x_502_ = lean_uint32_dec_le(v_c_476_, v___x_501_);
v___y_494_ = v___x_502_;
goto v___jp_493_;
}
}
v___jp_477_:
{
if (v___y_478_ == 0)
{
uint32_t v___x_479_; uint8_t v___x_480_; 
v___x_479_ = 43;
v___x_480_ = lean_uint32_dec_eq(v_c_476_, v___x_479_);
if (v___x_480_ == 0)
{
uint32_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = 45;
v___x_482_ = lean_uint32_dec_eq(v_c_476_, v___x_481_);
if (v___x_482_ == 0)
{
uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 46;
v___x_484_ = lean_uint32_dec_eq(v_c_476_, v___x_483_);
if (v___x_484_ == 0)
{
return v___y_478_;
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
else
{
return v___x_480_;
}
}
else
{
return v___y_478_;
}
}
v___jp_485_:
{
uint32_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = 97;
v___x_487_ = lean_uint32_dec_le(v___x_486_, v_c_476_);
if (v___x_487_ == 0)
{
v___y_478_ = v___x_487_;
goto v___jp_477_;
}
else
{
uint32_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = 122;
v___x_489_ = lean_uint32_dec_le(v_c_476_, v___x_488_);
v___y_478_ = v___x_489_;
goto v___jp_477_;
}
}
v___jp_493_:
{
if (v___y_494_ == 0)
{
uint32_t v___x_495_; uint8_t v___x_496_; 
v___x_495_ = 65;
v___x_496_ = lean_uint32_dec_le(v___x_495_, v_c_476_);
if (v___x_496_ == 0)
{
goto v___jp_485_;
}
else
{
uint32_t v___x_497_; uint8_t v___x_498_; 
v___x_497_ = 90;
v___x_498_ = lean_uint32_dec_le(v_c_476_, v___x_497_);
if (v___x_498_ == 0)
{
goto v___jp_485_;
}
else
{
v___y_478_ = v___x_492_;
goto v___jp_477_;
}
}
}
else
{
return v___y_494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidSchemeChar___boxed(lean_object* v_c_503_){
_start:
{
uint32_t v_c_boxed_504_; uint8_t v_res_505_; lean_object* v_r_506_; 
v_c_boxed_504_ = lean_unbox_uint32(v_c_503_);
lean_dec(v_c_503_);
v_res_505_ = l_Std_Http_Internal_Char_isValidSchemeChar(v_c_boxed_504_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isValidDomainNameChar(uint32_t v_c_507_){
_start:
{
uint8_t v___y_509_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; uint8_t v___y_523_; 
v___x_519_ = lean_uint32_to_nat(v_c_507_);
v___x_520_ = lean_unsigned_to_nat(128u);
v___x_521_ = lean_nat_dec_lt(v___x_519_, v___x_520_);
lean_dec(v___x_519_);
if (v___x_521_ == 0)
{
v___y_509_ = v___x_521_;
goto v___jp_508_;
}
else
{
uint32_t v___x_528_; uint8_t v___x_529_; 
v___x_528_ = 48;
v___x_529_ = lean_uint32_dec_le(v___x_528_, v_c_507_);
if (v___x_529_ == 0)
{
v___y_523_ = v___x_529_;
goto v___jp_522_;
}
else
{
uint32_t v___x_530_; uint8_t v___x_531_; 
v___x_530_ = 57;
v___x_531_ = lean_uint32_dec_le(v_c_507_, v___x_530_);
v___y_523_ = v___x_531_;
goto v___jp_522_;
}
}
v___jp_508_:
{
if (v___y_509_ == 0)
{
uint32_t v___x_510_; uint8_t v___x_511_; 
v___x_510_ = 45;
v___x_511_ = lean_uint32_dec_eq(v_c_507_, v___x_510_);
if (v___x_511_ == 0)
{
uint32_t v___x_512_; uint8_t v___x_513_; 
v___x_512_ = 46;
v___x_513_ = lean_uint32_dec_eq(v_c_507_, v___x_512_);
if (v___x_513_ == 0)
{
return v___y_509_;
}
else
{
return v___x_513_;
}
}
else
{
return v___x_511_;
}
}
else
{
return v___y_509_;
}
}
v___jp_514_:
{
uint32_t v___x_515_; uint8_t v___x_516_; 
v___x_515_ = 97;
v___x_516_ = lean_uint32_dec_le(v___x_515_, v_c_507_);
if (v___x_516_ == 0)
{
v___y_509_ = v___x_516_;
goto v___jp_508_;
}
else
{
uint32_t v___x_517_; uint8_t v___x_518_; 
v___x_517_ = 122;
v___x_518_ = lean_uint32_dec_le(v_c_507_, v___x_517_);
v___y_509_ = v___x_518_;
goto v___jp_508_;
}
}
v___jp_522_:
{
if (v___y_523_ == 0)
{
uint32_t v___x_524_; uint8_t v___x_525_; 
v___x_524_ = 65;
v___x_525_ = lean_uint32_dec_le(v___x_524_, v_c_507_);
if (v___x_525_ == 0)
{
goto v___jp_514_;
}
else
{
uint32_t v___x_526_; uint8_t v___x_527_; 
v___x_526_ = 90;
v___x_527_ = lean_uint32_dec_le(v_c_507_, v___x_526_);
if (v___x_527_ == 0)
{
goto v___jp_514_;
}
else
{
v___y_509_ = v___x_521_;
goto v___jp_508_;
}
}
}
else
{
return v___y_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidDomainNameChar___boxed(lean_object* v_c_532_){
_start:
{
uint32_t v_c_boxed_533_; uint8_t v_res_534_; lean_object* v_r_535_; 
v_c_boxed_533_ = lean_unbox_uint32(v_c_532_);
lean_dec(v_c_532_);
v_res_534_ = l_Std_Http_Internal_Char_isValidDomainNameChar(v_c_boxed_533_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isUnreserved___closed__0(void){
_start:
{
uint32_t v___x_536_; uint8_t v___x_537_; 
v___x_536_ = 95;
v___x_537_ = lean_uint32_to_uint8(v___x_536_);
return v___x_537_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isUnreserved___closed__1(void){
_start:
{
uint32_t v___x_538_; uint8_t v___x_539_; 
v___x_538_ = 126;
v___x_539_ = lean_uint32_to_uint8(v___x_538_);
return v___x_539_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isUnreserved___closed__2(void){
_start:
{
uint32_t v___x_540_; uint8_t v___x_541_; 
v___x_540_ = 45;
v___x_541_ = lean_uint32_to_uint8(v___x_540_);
return v___x_541_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isUnreserved___closed__3(void){
_start:
{
uint32_t v___x_542_; uint8_t v___x_543_; 
v___x_542_ = 46;
v___x_543_ = lean_uint32_to_uint8(v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUnreserved(uint8_t v_c_544_){
_start:
{
uint8_t v___y_546_; uint8_t v___y_552_; uint8_t v___y_558_; uint8_t v___y_564_; uint8_t v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_570_ = lean_uint8_dec_le(v___x_569_, v_c_544_);
if (v___x_570_ == 0)
{
v___y_564_ = v___x_570_;
goto v___jp_563_;
}
else
{
uint8_t v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_572_ = lean_uint8_dec_le(v_c_544_, v___x_571_);
v___y_564_ = v___x_572_;
goto v___jp_563_;
}
v___jp_545_:
{
if (v___y_546_ == 0)
{
uint8_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
v___x_548_ = lean_uint8_dec_eq(v_c_544_, v___x_547_);
if (v___x_548_ == 0)
{
uint8_t v___x_549_; uint8_t v___x_550_; 
v___x_549_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
v___x_550_ = lean_uint8_dec_eq(v_c_544_, v___x_549_);
return v___x_550_;
}
else
{
return v___x_548_;
}
}
else
{
return v___y_546_;
}
}
v___jp_551_:
{
if (v___y_552_ == 0)
{
uint8_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
v___x_554_ = lean_uint8_dec_eq(v_c_544_, v___x_553_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
v___x_556_ = lean_uint8_dec_eq(v_c_544_, v___x_555_);
v___y_546_ = v___x_556_;
goto v___jp_545_;
}
else
{
v___y_546_ = v___x_554_;
goto v___jp_545_;
}
}
else
{
return v___y_552_;
}
}
v___jp_557_:
{
if (v___y_558_ == 0)
{
uint8_t v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_560_ = lean_uint8_dec_le(v___x_559_, v_c_544_);
if (v___x_560_ == 0)
{
v___y_552_ = v___x_560_;
goto v___jp_551_;
}
else
{
uint8_t v___x_561_; uint8_t v___x_562_; 
v___x_561_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
v___x_562_ = lean_uint8_dec_le(v_c_544_, v___x_561_);
v___y_552_ = v___x_562_;
goto v___jp_551_;
}
}
else
{
return v___y_558_;
}
}
v___jp_563_:
{
if (v___y_564_ == 0)
{
uint8_t v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_566_ = lean_uint8_dec_le(v___x_565_, v_c_544_);
if (v___x_566_ == 0)
{
v___y_558_ = v___x_566_;
goto v___jp_557_;
}
else
{
uint8_t v___x_567_; uint8_t v___x_568_; 
v___x_567_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
v___x_568_ = lean_uint8_dec_le(v_c_544_, v___x_567_);
v___y_558_ = v___x_568_;
goto v___jp_557_;
}
}
else
{
return v___y_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUnreserved___boxed(lean_object* v_c_573_){
_start:
{
uint8_t v_c_boxed_574_; uint8_t v_res_575_; lean_object* v_r_576_; 
v_c_boxed_574_ = lean_unbox(v_c_573_);
v_res_575_ = l_Std_Http_Internal_Char_isUnreserved(v_c_boxed_574_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__0(void){
_start:
{
uint32_t v___x_577_; uint8_t v___x_578_; 
v___x_577_ = 38;
v___x_578_ = lean_uint32_to_uint8(v___x_577_);
return v___x_578_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__1(void){
_start:
{
uint32_t v___x_579_; uint8_t v___x_580_; 
v___x_579_ = 39;
v___x_580_ = lean_uint32_to_uint8(v___x_579_);
return v___x_580_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__2(void){
_start:
{
uint32_t v___x_581_; uint8_t v___x_582_; 
v___x_581_ = 40;
v___x_582_ = lean_uint32_to_uint8(v___x_581_);
return v___x_582_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__3(void){
_start:
{
uint32_t v___x_583_; uint8_t v___x_584_; 
v___x_583_ = 41;
v___x_584_ = lean_uint32_to_uint8(v___x_583_);
return v___x_584_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__4(void){
_start:
{
uint32_t v___x_585_; uint8_t v___x_586_; 
v___x_585_ = 42;
v___x_586_ = lean_uint32_to_uint8(v___x_585_);
return v___x_586_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__5(void){
_start:
{
uint32_t v___x_587_; uint8_t v___x_588_; 
v___x_587_ = 43;
v___x_588_ = lean_uint32_to_uint8(v___x_587_);
return v___x_588_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__6(void){
_start:
{
uint32_t v___x_589_; uint8_t v___x_590_; 
v___x_589_ = 44;
v___x_590_ = lean_uint32_to_uint8(v___x_589_);
return v___x_590_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__7(void){
_start:
{
uint32_t v___x_591_; uint8_t v___x_592_; 
v___x_591_ = 59;
v___x_592_ = lean_uint32_to_uint8(v___x_591_);
return v___x_592_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__8(void){
_start:
{
uint32_t v___x_593_; uint8_t v___x_594_; 
v___x_593_ = 61;
v___x_594_ = lean_uint32_to_uint8(v___x_593_);
return v___x_594_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__9(void){
_start:
{
uint32_t v___x_595_; uint8_t v___x_596_; 
v___x_595_ = 33;
v___x_596_ = lean_uint32_to_uint8(v___x_595_);
return v___x_596_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__10(void){
_start:
{
uint32_t v___x_597_; uint8_t v___x_598_; 
v___x_597_ = 36;
v___x_598_ = lean_uint32_to_uint8(v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isSubDelims(uint8_t v_c_599_){
_start:
{
uint8_t v___y_601_; uint8_t v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
v___x_621_ = lean_uint8_dec_eq(v_c_599_, v___x_620_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
v___x_623_ = lean_uint8_dec_eq(v_c_599_, v___x_622_);
v___y_601_ = v___x_623_;
goto v___jp_600_;
}
else
{
v___y_601_ = v___x_621_;
goto v___jp_600_;
}
v___jp_600_:
{
if (v___y_601_ == 0)
{
uint8_t v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
v___x_603_ = lean_uint8_dec_eq(v_c_599_, v___x_602_);
if (v___x_603_ == 0)
{
uint8_t v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
v___x_605_ = lean_uint8_dec_eq(v_c_599_, v___x_604_);
if (v___x_605_ == 0)
{
uint8_t v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
v___x_607_ = lean_uint8_dec_eq(v_c_599_, v___x_606_);
if (v___x_607_ == 0)
{
uint8_t v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
v___x_609_ = lean_uint8_dec_eq(v_c_599_, v___x_608_);
if (v___x_609_ == 0)
{
uint8_t v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
v___x_611_ = lean_uint8_dec_eq(v_c_599_, v___x_610_);
if (v___x_611_ == 0)
{
uint8_t v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
v___x_613_ = lean_uint8_dec_eq(v_c_599_, v___x_612_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
v___x_615_ = lean_uint8_dec_eq(v_c_599_, v___x_614_);
if (v___x_615_ == 0)
{
uint8_t v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
v___x_617_ = lean_uint8_dec_eq(v_c_599_, v___x_616_);
if (v___x_617_ == 0)
{
uint8_t v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
v___x_619_ = lean_uint8_dec_eq(v_c_599_, v___x_618_);
return v___x_619_;
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
return v___y_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isSubDelims___boxed(lean_object* v_c_624_){
_start:
{
uint8_t v_c_boxed_625_; uint8_t v_res_626_; lean_object* v_r_627_; 
v_c_boxed_625_ = lean_unbox(v_c_624_);
v_res_626_ = l_Std_Http_Internal_Char_isSubDelims(v_c_boxed_625_);
v_r_627_ = lean_box(v_res_626_);
return v_r_627_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isPChar___closed__0(void){
_start:
{
uint32_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = 58;
v___x_629_ = lean_uint32_to_uint8(v___x_628_);
return v___x_629_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isPChar___closed__1(void){
_start:
{
uint32_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = 64;
v___x_631_ = lean_uint32_to_uint8(v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isPChar(uint8_t v_c_632_){
_start:
{
uint8_t v___y_634_; uint8_t v___y_640_; uint8_t v___y_660_; uint8_t v___y_666_; uint8_t v___y_672_; uint8_t v___y_678_; uint8_t v___y_684_; uint8_t v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_690_ = lean_uint8_dec_le(v___x_689_, v_c_632_);
if (v___x_690_ == 0)
{
v___y_684_ = v___x_690_;
goto v___jp_683_;
}
else
{
uint8_t v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_692_ = lean_uint8_dec_le(v_c_632_, v___x_691_);
v___y_684_ = v___x_692_;
goto v___jp_683_;
}
v___jp_633_:
{
if (v___y_634_ == 0)
{
uint8_t v___x_635_; uint8_t v___x_636_; 
v___x_635_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__0, &l_Std_Http_Internal_Char_isPChar___closed__0_once, _init_l_Std_Http_Internal_Char_isPChar___closed__0);
v___x_636_ = lean_uint8_dec_eq(v_c_632_, v___x_635_);
if (v___x_636_ == 0)
{
uint8_t v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__1, &l_Std_Http_Internal_Char_isPChar___closed__1_once, _init_l_Std_Http_Internal_Char_isPChar___closed__1);
v___x_638_ = lean_uint8_dec_eq(v_c_632_, v___x_637_);
return v___x_638_;
}
else
{
return v___x_636_;
}
}
else
{
return v___y_634_;
}
}
v___jp_639_:
{
if (v___y_640_ == 0)
{
uint8_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
v___x_642_ = lean_uint8_dec_eq(v_c_632_, v___x_641_);
if (v___x_642_ == 0)
{
uint8_t v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
v___x_644_ = lean_uint8_dec_eq(v_c_632_, v___x_643_);
if (v___x_644_ == 0)
{
uint8_t v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
v___x_646_ = lean_uint8_dec_eq(v_c_632_, v___x_645_);
if (v___x_646_ == 0)
{
uint8_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
v___x_648_ = lean_uint8_dec_eq(v_c_632_, v___x_647_);
if (v___x_648_ == 0)
{
uint8_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
v___x_650_ = lean_uint8_dec_eq(v_c_632_, v___x_649_);
if (v___x_650_ == 0)
{
uint8_t v___x_651_; uint8_t v___x_652_; 
v___x_651_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
v___x_652_ = lean_uint8_dec_eq(v_c_632_, v___x_651_);
if (v___x_652_ == 0)
{
uint8_t v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
v___x_654_ = lean_uint8_dec_eq(v_c_632_, v___x_653_);
if (v___x_654_ == 0)
{
uint8_t v___x_655_; uint8_t v___x_656_; 
v___x_655_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
v___x_656_ = lean_uint8_dec_eq(v_c_632_, v___x_655_);
if (v___x_656_ == 0)
{
uint8_t v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
v___x_658_ = lean_uint8_dec_eq(v_c_632_, v___x_657_);
v___y_634_ = v___x_658_;
goto v___jp_633_;
}
else
{
v___y_634_ = v___x_656_;
goto v___jp_633_;
}
}
else
{
v___y_634_ = v___x_654_;
goto v___jp_633_;
}
}
else
{
v___y_634_ = v___x_652_;
goto v___jp_633_;
}
}
else
{
v___y_634_ = v___x_650_;
goto v___jp_633_;
}
}
else
{
v___y_634_ = v___x_648_;
goto v___jp_633_;
}
}
else
{
v___y_634_ = v___x_646_;
goto v___jp_633_;
}
}
else
{
v___y_634_ = v___x_644_;
goto v___jp_633_;
}
}
else
{
v___y_634_ = v___x_642_;
goto v___jp_633_;
}
}
else
{
return v___y_640_;
}
}
v___jp_659_:
{
if (v___y_660_ == 0)
{
uint8_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
v___x_662_ = lean_uint8_dec_eq(v_c_632_, v___x_661_);
if (v___x_662_ == 0)
{
uint8_t v___x_663_; uint8_t v___x_664_; 
v___x_663_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
v___x_664_ = lean_uint8_dec_eq(v_c_632_, v___x_663_);
v___y_640_ = v___x_664_;
goto v___jp_639_;
}
else
{
v___y_640_ = v___x_662_;
goto v___jp_639_;
}
}
else
{
return v___y_660_;
}
}
v___jp_665_:
{
if (v___y_666_ == 0)
{
uint8_t v___x_667_; uint8_t v___x_668_; 
v___x_667_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
v___x_668_ = lean_uint8_dec_eq(v_c_632_, v___x_667_);
if (v___x_668_ == 0)
{
uint8_t v___x_669_; uint8_t v___x_670_; 
v___x_669_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
v___x_670_ = lean_uint8_dec_eq(v_c_632_, v___x_669_);
v___y_660_ = v___x_670_;
goto v___jp_659_;
}
else
{
v___y_660_ = v___x_668_;
goto v___jp_659_;
}
}
else
{
return v___y_666_;
}
}
v___jp_671_:
{
if (v___y_672_ == 0)
{
uint8_t v___x_673_; uint8_t v___x_674_; 
v___x_673_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
v___x_674_ = lean_uint8_dec_eq(v_c_632_, v___x_673_);
if (v___x_674_ == 0)
{
uint8_t v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
v___x_676_ = lean_uint8_dec_eq(v_c_632_, v___x_675_);
v___y_666_ = v___x_676_;
goto v___jp_665_;
}
else
{
v___y_666_ = v___x_674_;
goto v___jp_665_;
}
}
else
{
return v___y_672_;
}
}
v___jp_677_:
{
if (v___y_678_ == 0)
{
uint8_t v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_680_ = lean_uint8_dec_le(v___x_679_, v_c_632_);
if (v___x_680_ == 0)
{
v___y_672_ = v___x_680_;
goto v___jp_671_;
}
else
{
uint8_t v___x_681_; uint8_t v___x_682_; 
v___x_681_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
v___x_682_ = lean_uint8_dec_le(v_c_632_, v___x_681_);
v___y_672_ = v___x_682_;
goto v___jp_671_;
}
}
else
{
return v___y_678_;
}
}
v___jp_683_:
{
if (v___y_684_ == 0)
{
uint8_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_686_ = lean_uint8_dec_le(v___x_685_, v_c_632_);
if (v___x_686_ == 0)
{
v___y_678_ = v___x_686_;
goto v___jp_677_;
}
else
{
uint8_t v___x_687_; uint8_t v___x_688_; 
v___x_687_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
v___x_688_ = lean_uint8_dec_le(v_c_632_, v___x_687_);
v___y_678_ = v___x_688_;
goto v___jp_677_;
}
}
else
{
return v___y_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isPChar___boxed(lean_object* v_c_693_){
_start:
{
uint8_t v_c_boxed_694_; uint8_t v_res_695_; lean_object* v_r_696_; 
v_c_boxed_694_ = lean_unbox(v_c_693_);
v_res_695_ = l_Std_Http_Internal_Char_isPChar(v_c_boxed_694_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isQueryChar___closed__0(void){
_start:
{
uint32_t v___x_697_; uint8_t v___x_698_; 
v___x_697_ = 47;
v___x_698_ = lean_uint32_to_uint8(v___x_697_);
return v___x_698_;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isQueryChar___closed__1(void){
_start:
{
uint32_t v___x_699_; uint8_t v___x_700_; 
v___x_699_ = 63;
v___x_700_ = lean_uint32_to_uint8(v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryChar(uint8_t v_c_701_){
_start:
{
uint8_t v___y_703_; uint8_t v___y_709_; uint8_t v___y_715_; uint8_t v___y_735_; uint8_t v___y_741_; uint8_t v___y_747_; uint8_t v___y_753_; uint8_t v___y_759_; uint8_t v___x_764_; uint8_t v___x_765_; 
v___x_764_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_765_ = lean_uint8_dec_le(v___x_764_, v_c_701_);
if (v___x_765_ == 0)
{
v___y_759_ = v___x_765_;
goto v___jp_758_;
}
else
{
uint8_t v___x_766_; uint8_t v___x_767_; 
v___x_766_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_767_ = lean_uint8_dec_le(v_c_701_, v___x_766_);
v___y_759_ = v___x_767_;
goto v___jp_758_;
}
v___jp_702_:
{
if (v___y_703_ == 0)
{
uint8_t v___x_704_; uint8_t v___x_705_; 
v___x_704_ = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__0, &l_Std_Http_Internal_Char_isQueryChar___closed__0_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__0);
v___x_705_ = lean_uint8_dec_eq(v_c_701_, v___x_704_);
if (v___x_705_ == 0)
{
uint8_t v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__1, &l_Std_Http_Internal_Char_isQueryChar___closed__1_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__1);
v___x_707_ = lean_uint8_dec_eq(v_c_701_, v___x_706_);
return v___x_707_;
}
else
{
return v___x_705_;
}
}
else
{
return v___y_703_;
}
}
v___jp_708_:
{
if (v___y_709_ == 0)
{
uint8_t v___x_710_; uint8_t v___x_711_; 
v___x_710_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__0, &l_Std_Http_Internal_Char_isPChar___closed__0_once, _init_l_Std_Http_Internal_Char_isPChar___closed__0);
v___x_711_ = lean_uint8_dec_eq(v_c_701_, v___x_710_);
if (v___x_711_ == 0)
{
uint8_t v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__1, &l_Std_Http_Internal_Char_isPChar___closed__1_once, _init_l_Std_Http_Internal_Char_isPChar___closed__1);
v___x_713_ = lean_uint8_dec_eq(v_c_701_, v___x_712_);
v___y_703_ = v___x_713_;
goto v___jp_702_;
}
else
{
v___y_703_ = v___x_711_;
goto v___jp_702_;
}
}
else
{
return v___y_709_;
}
}
v___jp_714_:
{
if (v___y_715_ == 0)
{
uint8_t v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
v___x_717_ = lean_uint8_dec_eq(v_c_701_, v___x_716_);
if (v___x_717_ == 0)
{
uint8_t v___x_718_; uint8_t v___x_719_; 
v___x_718_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
v___x_719_ = lean_uint8_dec_eq(v_c_701_, v___x_718_);
if (v___x_719_ == 0)
{
uint8_t v___x_720_; uint8_t v___x_721_; 
v___x_720_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
v___x_721_ = lean_uint8_dec_eq(v_c_701_, v___x_720_);
if (v___x_721_ == 0)
{
uint8_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
v___x_723_ = lean_uint8_dec_eq(v_c_701_, v___x_722_);
if (v___x_723_ == 0)
{
uint8_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
v___x_725_ = lean_uint8_dec_eq(v_c_701_, v___x_724_);
if (v___x_725_ == 0)
{
uint8_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
v___x_727_ = lean_uint8_dec_eq(v_c_701_, v___x_726_);
if (v___x_727_ == 0)
{
uint8_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
v___x_729_ = lean_uint8_dec_eq(v_c_701_, v___x_728_);
if (v___x_729_ == 0)
{
uint8_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
v___x_731_ = lean_uint8_dec_eq(v_c_701_, v___x_730_);
if (v___x_731_ == 0)
{
uint8_t v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
v___x_733_ = lean_uint8_dec_eq(v_c_701_, v___x_732_);
v___y_709_ = v___x_733_;
goto v___jp_708_;
}
else
{
v___y_709_ = v___x_731_;
goto v___jp_708_;
}
}
else
{
v___y_709_ = v___x_729_;
goto v___jp_708_;
}
}
else
{
v___y_709_ = v___x_727_;
goto v___jp_708_;
}
}
else
{
v___y_709_ = v___x_725_;
goto v___jp_708_;
}
}
else
{
v___y_709_ = v___x_723_;
goto v___jp_708_;
}
}
else
{
v___y_709_ = v___x_721_;
goto v___jp_708_;
}
}
else
{
v___y_709_ = v___x_719_;
goto v___jp_708_;
}
}
else
{
v___y_709_ = v___x_717_;
goto v___jp_708_;
}
}
else
{
return v___y_715_;
}
}
v___jp_734_:
{
if (v___y_735_ == 0)
{
uint8_t v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
v___x_737_ = lean_uint8_dec_eq(v_c_701_, v___x_736_);
if (v___x_737_ == 0)
{
uint8_t v___x_738_; uint8_t v___x_739_; 
v___x_738_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
v___x_739_ = lean_uint8_dec_eq(v_c_701_, v___x_738_);
v___y_715_ = v___x_739_;
goto v___jp_714_;
}
else
{
v___y_715_ = v___x_737_;
goto v___jp_714_;
}
}
else
{
return v___y_735_;
}
}
v___jp_740_:
{
if (v___y_741_ == 0)
{
uint8_t v___x_742_; uint8_t v___x_743_; 
v___x_742_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
v___x_743_ = lean_uint8_dec_eq(v_c_701_, v___x_742_);
if (v___x_743_ == 0)
{
uint8_t v___x_744_; uint8_t v___x_745_; 
v___x_744_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
v___x_745_ = lean_uint8_dec_eq(v_c_701_, v___x_744_);
v___y_735_ = v___x_745_;
goto v___jp_734_;
}
else
{
v___y_735_ = v___x_743_;
goto v___jp_734_;
}
}
else
{
return v___y_741_;
}
}
v___jp_746_:
{
if (v___y_747_ == 0)
{
uint8_t v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
v___x_749_ = lean_uint8_dec_eq(v_c_701_, v___x_748_);
if (v___x_749_ == 0)
{
uint8_t v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
v___x_751_ = lean_uint8_dec_eq(v_c_701_, v___x_750_);
v___y_741_ = v___x_751_;
goto v___jp_740_;
}
else
{
v___y_741_ = v___x_749_;
goto v___jp_740_;
}
}
else
{
return v___y_747_;
}
}
v___jp_752_:
{
if (v___y_753_ == 0)
{
uint8_t v___x_754_; uint8_t v___x_755_; 
v___x_754_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_755_ = lean_uint8_dec_le(v___x_754_, v_c_701_);
if (v___x_755_ == 0)
{
v___y_747_ = v___x_755_;
goto v___jp_746_;
}
else
{
uint8_t v___x_756_; uint8_t v___x_757_; 
v___x_756_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
v___x_757_ = lean_uint8_dec_le(v_c_701_, v___x_756_);
v___y_747_ = v___x_757_;
goto v___jp_746_;
}
}
else
{
return v___y_753_;
}
}
v___jp_758_:
{
if (v___y_759_ == 0)
{
uint8_t v___x_760_; uint8_t v___x_761_; 
v___x_760_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_761_ = lean_uint8_dec_le(v___x_760_, v_c_701_);
if (v___x_761_ == 0)
{
v___y_753_ = v___x_761_;
goto v___jp_752_;
}
else
{
uint8_t v___x_762_; uint8_t v___x_763_; 
v___x_762_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
v___x_763_ = lean_uint8_dec_le(v_c_701_, v___x_762_);
v___y_753_ = v___x_763_;
goto v___jp_752_;
}
}
else
{
return v___y_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryChar___boxed(lean_object* v_c_768_){
_start:
{
uint8_t v_c_boxed_769_; uint8_t v_res_770_; lean_object* v_r_771_; 
v_c_boxed_769_ = lean_unbox(v_c_768_);
v_res_770_ = l_Std_Http_Internal_Char_isQueryChar(v_c_boxed_769_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isFragmentChar(uint8_t v_c_772_){
_start:
{
uint8_t v___y_774_; uint8_t v___y_780_; uint8_t v___y_786_; uint8_t v___y_806_; uint8_t v___y_812_; uint8_t v___y_818_; uint8_t v___y_824_; uint8_t v___y_830_; uint8_t v___x_835_; uint8_t v___x_836_; 
v___x_835_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_836_ = lean_uint8_dec_le(v___x_835_, v_c_772_);
if (v___x_836_ == 0)
{
v___y_830_ = v___x_836_;
goto v___jp_829_;
}
else
{
uint8_t v___x_837_; uint8_t v___x_838_; 
v___x_837_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_838_ = lean_uint8_dec_le(v_c_772_, v___x_837_);
v___y_830_ = v___x_838_;
goto v___jp_829_;
}
v___jp_773_:
{
if (v___y_774_ == 0)
{
uint8_t v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__0, &l_Std_Http_Internal_Char_isQueryChar___closed__0_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__0);
v___x_776_ = lean_uint8_dec_eq(v_c_772_, v___x_775_);
if (v___x_776_ == 0)
{
uint8_t v___x_777_; uint8_t v___x_778_; 
v___x_777_ = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__1, &l_Std_Http_Internal_Char_isQueryChar___closed__1_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__1);
v___x_778_ = lean_uint8_dec_eq(v_c_772_, v___x_777_);
return v___x_778_;
}
else
{
return v___x_776_;
}
}
else
{
return v___y_774_;
}
}
v___jp_779_:
{
if (v___y_780_ == 0)
{
uint8_t v___x_781_; uint8_t v___x_782_; 
v___x_781_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__0, &l_Std_Http_Internal_Char_isPChar___closed__0_once, _init_l_Std_Http_Internal_Char_isPChar___closed__0);
v___x_782_ = lean_uint8_dec_eq(v_c_772_, v___x_781_);
if (v___x_782_ == 0)
{
uint8_t v___x_783_; uint8_t v___x_784_; 
v___x_783_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__1, &l_Std_Http_Internal_Char_isPChar___closed__1_once, _init_l_Std_Http_Internal_Char_isPChar___closed__1);
v___x_784_ = lean_uint8_dec_eq(v_c_772_, v___x_783_);
v___y_774_ = v___x_784_;
goto v___jp_773_;
}
else
{
v___y_774_ = v___x_782_;
goto v___jp_773_;
}
}
else
{
return v___y_780_;
}
}
v___jp_785_:
{
if (v___y_786_ == 0)
{
uint8_t v___x_787_; uint8_t v___x_788_; 
v___x_787_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
v___x_788_ = lean_uint8_dec_eq(v_c_772_, v___x_787_);
if (v___x_788_ == 0)
{
uint8_t v___x_789_; uint8_t v___x_790_; 
v___x_789_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
v___x_790_ = lean_uint8_dec_eq(v_c_772_, v___x_789_);
if (v___x_790_ == 0)
{
uint8_t v___x_791_; uint8_t v___x_792_; 
v___x_791_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
v___x_792_ = lean_uint8_dec_eq(v_c_772_, v___x_791_);
if (v___x_792_ == 0)
{
uint8_t v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
v___x_794_ = lean_uint8_dec_eq(v_c_772_, v___x_793_);
if (v___x_794_ == 0)
{
uint8_t v___x_795_; uint8_t v___x_796_; 
v___x_795_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
v___x_796_ = lean_uint8_dec_eq(v_c_772_, v___x_795_);
if (v___x_796_ == 0)
{
uint8_t v___x_797_; uint8_t v___x_798_; 
v___x_797_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
v___x_798_ = lean_uint8_dec_eq(v_c_772_, v___x_797_);
if (v___x_798_ == 0)
{
uint8_t v___x_799_; uint8_t v___x_800_; 
v___x_799_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
v___x_800_ = lean_uint8_dec_eq(v_c_772_, v___x_799_);
if (v___x_800_ == 0)
{
uint8_t v___x_801_; uint8_t v___x_802_; 
v___x_801_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
v___x_802_ = lean_uint8_dec_eq(v_c_772_, v___x_801_);
if (v___x_802_ == 0)
{
uint8_t v___x_803_; uint8_t v___x_804_; 
v___x_803_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
v___x_804_ = lean_uint8_dec_eq(v_c_772_, v___x_803_);
v___y_780_ = v___x_804_;
goto v___jp_779_;
}
else
{
v___y_780_ = v___x_802_;
goto v___jp_779_;
}
}
else
{
v___y_780_ = v___x_800_;
goto v___jp_779_;
}
}
else
{
v___y_780_ = v___x_798_;
goto v___jp_779_;
}
}
else
{
v___y_780_ = v___x_796_;
goto v___jp_779_;
}
}
else
{
v___y_780_ = v___x_794_;
goto v___jp_779_;
}
}
else
{
v___y_780_ = v___x_792_;
goto v___jp_779_;
}
}
else
{
v___y_780_ = v___x_790_;
goto v___jp_779_;
}
}
else
{
v___y_780_ = v___x_788_;
goto v___jp_779_;
}
}
else
{
return v___y_786_;
}
}
v___jp_805_:
{
if (v___y_806_ == 0)
{
uint8_t v___x_807_; uint8_t v___x_808_; 
v___x_807_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
v___x_808_ = lean_uint8_dec_eq(v_c_772_, v___x_807_);
if (v___x_808_ == 0)
{
uint8_t v___x_809_; uint8_t v___x_810_; 
v___x_809_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
v___x_810_ = lean_uint8_dec_eq(v_c_772_, v___x_809_);
v___y_786_ = v___x_810_;
goto v___jp_785_;
}
else
{
v___y_786_ = v___x_808_;
goto v___jp_785_;
}
}
else
{
return v___y_806_;
}
}
v___jp_811_:
{
if (v___y_812_ == 0)
{
uint8_t v___x_813_; uint8_t v___x_814_; 
v___x_813_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
v___x_814_ = lean_uint8_dec_eq(v_c_772_, v___x_813_);
if (v___x_814_ == 0)
{
uint8_t v___x_815_; uint8_t v___x_816_; 
v___x_815_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
v___x_816_ = lean_uint8_dec_eq(v_c_772_, v___x_815_);
v___y_806_ = v___x_816_;
goto v___jp_805_;
}
else
{
v___y_806_ = v___x_814_;
goto v___jp_805_;
}
}
else
{
return v___y_812_;
}
}
v___jp_817_:
{
if (v___y_818_ == 0)
{
uint8_t v___x_819_; uint8_t v___x_820_; 
v___x_819_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
v___x_820_ = lean_uint8_dec_eq(v_c_772_, v___x_819_);
if (v___x_820_ == 0)
{
uint8_t v___x_821_; uint8_t v___x_822_; 
v___x_821_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
v___x_822_ = lean_uint8_dec_eq(v_c_772_, v___x_821_);
v___y_812_ = v___x_822_;
goto v___jp_811_;
}
else
{
v___y_812_ = v___x_820_;
goto v___jp_811_;
}
}
else
{
return v___y_818_;
}
}
v___jp_823_:
{
if (v___y_824_ == 0)
{
uint8_t v___x_825_; uint8_t v___x_826_; 
v___x_825_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_826_ = lean_uint8_dec_le(v___x_825_, v_c_772_);
if (v___x_826_ == 0)
{
v___y_818_ = v___x_826_;
goto v___jp_817_;
}
else
{
uint8_t v___x_827_; uint8_t v___x_828_; 
v___x_827_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
v___x_828_ = lean_uint8_dec_le(v_c_772_, v___x_827_);
v___y_818_ = v___x_828_;
goto v___jp_817_;
}
}
else
{
return v___y_824_;
}
}
v___jp_829_:
{
if (v___y_830_ == 0)
{
uint8_t v___x_831_; uint8_t v___x_832_; 
v___x_831_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_832_ = lean_uint8_dec_le(v___x_831_, v_c_772_);
if (v___x_832_ == 0)
{
v___y_824_ = v___x_832_;
goto v___jp_823_;
}
else
{
uint8_t v___x_833_; uint8_t v___x_834_; 
v___x_833_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
v___x_834_ = lean_uint8_dec_le(v_c_772_, v___x_833_);
v___y_824_ = v___x_834_;
goto v___jp_823_;
}
}
else
{
return v___y_830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isFragmentChar___boxed(lean_object* v_c_839_){
_start:
{
uint8_t v_c_boxed_840_; uint8_t v_res_841_; lean_object* v_r_842_; 
v_c_boxed_840_ = lean_unbox(v_c_839_);
v_res_841_ = l_Std_Http_Internal_Char_isFragmentChar(v_c_boxed_840_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUserInfoChar(uint8_t v_c_843_){
_start:
{
uint8_t v___y_845_; uint8_t v___y_849_; uint8_t v___y_869_; uint8_t v___y_875_; uint8_t v___y_881_; uint8_t v___y_887_; uint8_t v___y_893_; uint8_t v___x_898_; uint8_t v___x_899_; 
v___x_898_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_899_ = lean_uint8_dec_le(v___x_898_, v_c_843_);
if (v___x_899_ == 0)
{
v___y_893_ = v___x_899_;
goto v___jp_892_;
}
else
{
uint8_t v___x_900_; uint8_t v___x_901_; 
v___x_900_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_901_ = lean_uint8_dec_le(v_c_843_, v___x_900_);
v___y_893_ = v___x_901_;
goto v___jp_892_;
}
v___jp_844_:
{
if (v___y_845_ == 0)
{
uint8_t v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__0, &l_Std_Http_Internal_Char_isPChar___closed__0_once, _init_l_Std_Http_Internal_Char_isPChar___closed__0);
v___x_847_ = lean_uint8_dec_eq(v_c_843_, v___x_846_);
return v___x_847_;
}
else
{
return v___y_845_;
}
}
v___jp_848_:
{
if (v___y_849_ == 0)
{
uint8_t v___x_850_; uint8_t v___x_851_; 
v___x_850_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
v___x_851_ = lean_uint8_dec_eq(v_c_843_, v___x_850_);
if (v___x_851_ == 0)
{
uint8_t v___x_852_; uint8_t v___x_853_; 
v___x_852_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
v___x_853_ = lean_uint8_dec_eq(v_c_843_, v___x_852_);
if (v___x_853_ == 0)
{
uint8_t v___x_854_; uint8_t v___x_855_; 
v___x_854_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
v___x_855_ = lean_uint8_dec_eq(v_c_843_, v___x_854_);
if (v___x_855_ == 0)
{
uint8_t v___x_856_; uint8_t v___x_857_; 
v___x_856_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
v___x_857_ = lean_uint8_dec_eq(v_c_843_, v___x_856_);
if (v___x_857_ == 0)
{
uint8_t v___x_858_; uint8_t v___x_859_; 
v___x_858_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
v___x_859_ = lean_uint8_dec_eq(v_c_843_, v___x_858_);
if (v___x_859_ == 0)
{
uint8_t v___x_860_; uint8_t v___x_861_; 
v___x_860_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
v___x_861_ = lean_uint8_dec_eq(v_c_843_, v___x_860_);
if (v___x_861_ == 0)
{
uint8_t v___x_862_; uint8_t v___x_863_; 
v___x_862_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
v___x_863_ = lean_uint8_dec_eq(v_c_843_, v___x_862_);
if (v___x_863_ == 0)
{
uint8_t v___x_864_; uint8_t v___x_865_; 
v___x_864_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
v___x_865_ = lean_uint8_dec_eq(v_c_843_, v___x_864_);
if (v___x_865_ == 0)
{
uint8_t v___x_866_; uint8_t v___x_867_; 
v___x_866_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
v___x_867_ = lean_uint8_dec_eq(v_c_843_, v___x_866_);
v___y_845_ = v___x_867_;
goto v___jp_844_;
}
else
{
v___y_845_ = v___x_865_;
goto v___jp_844_;
}
}
else
{
v___y_845_ = v___x_863_;
goto v___jp_844_;
}
}
else
{
v___y_845_ = v___x_861_;
goto v___jp_844_;
}
}
else
{
v___y_845_ = v___x_859_;
goto v___jp_844_;
}
}
else
{
v___y_845_ = v___x_857_;
goto v___jp_844_;
}
}
else
{
v___y_845_ = v___x_855_;
goto v___jp_844_;
}
}
else
{
v___y_845_ = v___x_853_;
goto v___jp_844_;
}
}
else
{
v___y_845_ = v___x_851_;
goto v___jp_844_;
}
}
else
{
return v___y_849_;
}
}
v___jp_868_:
{
if (v___y_869_ == 0)
{
uint8_t v___x_870_; uint8_t v___x_871_; 
v___x_870_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
v___x_871_ = lean_uint8_dec_eq(v_c_843_, v___x_870_);
if (v___x_871_ == 0)
{
uint8_t v___x_872_; uint8_t v___x_873_; 
v___x_872_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
v___x_873_ = lean_uint8_dec_eq(v_c_843_, v___x_872_);
v___y_849_ = v___x_873_;
goto v___jp_848_;
}
else
{
v___y_849_ = v___x_871_;
goto v___jp_848_;
}
}
else
{
return v___y_869_;
}
}
v___jp_874_:
{
if (v___y_875_ == 0)
{
uint8_t v___x_876_; uint8_t v___x_877_; 
v___x_876_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
v___x_877_ = lean_uint8_dec_eq(v_c_843_, v___x_876_);
if (v___x_877_ == 0)
{
uint8_t v___x_878_; uint8_t v___x_879_; 
v___x_878_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
v___x_879_ = lean_uint8_dec_eq(v_c_843_, v___x_878_);
v___y_869_ = v___x_879_;
goto v___jp_868_;
}
else
{
v___y_869_ = v___x_877_;
goto v___jp_868_;
}
}
else
{
return v___y_875_;
}
}
v___jp_880_:
{
if (v___y_881_ == 0)
{
uint8_t v___x_882_; uint8_t v___x_883_; 
v___x_882_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
v___x_883_ = lean_uint8_dec_eq(v_c_843_, v___x_882_);
if (v___x_883_ == 0)
{
uint8_t v___x_884_; uint8_t v___x_885_; 
v___x_884_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
v___x_885_ = lean_uint8_dec_eq(v_c_843_, v___x_884_);
v___y_875_ = v___x_885_;
goto v___jp_874_;
}
else
{
v___y_875_ = v___x_883_;
goto v___jp_874_;
}
}
else
{
return v___y_881_;
}
}
v___jp_886_:
{
if (v___y_887_ == 0)
{
uint8_t v___x_888_; uint8_t v___x_889_; 
v___x_888_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_889_ = lean_uint8_dec_le(v___x_888_, v_c_843_);
if (v___x_889_ == 0)
{
v___y_881_ = v___x_889_;
goto v___jp_880_;
}
else
{
uint8_t v___x_890_; uint8_t v___x_891_; 
v___x_890_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
v___x_891_ = lean_uint8_dec_le(v_c_843_, v___x_890_);
v___y_881_ = v___x_891_;
goto v___jp_880_;
}
}
else
{
return v___y_887_;
}
}
v___jp_892_:
{
if (v___y_893_ == 0)
{
uint8_t v___x_894_; uint8_t v___x_895_; 
v___x_894_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_895_ = lean_uint8_dec_le(v___x_894_, v_c_843_);
if (v___x_895_ == 0)
{
v___y_887_ = v___x_895_;
goto v___jp_886_;
}
else
{
uint8_t v___x_896_; uint8_t v___x_897_; 
v___x_896_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
v___x_897_ = lean_uint8_dec_le(v_c_843_, v___x_896_);
v___y_887_ = v___x_897_;
goto v___jp_886_;
}
}
else
{
return v___y_893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUserInfoChar___boxed(lean_object* v_c_902_){
_start:
{
uint8_t v_c_boxed_903_; uint8_t v_res_904_; lean_object* v_r_905_; 
v_c_boxed_903_ = lean_unbox(v_c_902_);
v_res_904_ = l_Std_Http_Internal_Char_isUserInfoChar(v_c_boxed_903_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryDataChar(uint8_t v_c_906_){
_start:
{
uint8_t v___y_915_; uint8_t v___y_917_; uint8_t v___y_923_; uint8_t v___y_929_; uint8_t v___y_949_; uint8_t v___y_955_; uint8_t v___y_961_; uint8_t v___y_967_; uint8_t v___y_973_; uint8_t v___x_978_; uint8_t v___x_979_; 
v___x_978_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
v___x_979_ = lean_uint8_dec_le(v___x_978_, v_c_906_);
if (v___x_979_ == 0)
{
v___y_973_ = v___x_979_;
goto v___jp_972_;
}
else
{
uint8_t v___x_980_; uint8_t v___x_981_; 
v___x_980_ = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
v___x_981_ = lean_uint8_dec_le(v_c_906_, v___x_980_);
v___y_973_ = v___x_981_;
goto v___jp_972_;
}
v___jp_907_:
{
uint8_t v___x_908_; uint8_t v___x_909_; 
v___x_908_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
v___x_909_ = lean_uint8_dec_eq(v_c_906_, v___x_908_);
if (v___x_909_ == 0)
{
uint8_t v___x_910_; uint8_t v___x_911_; 
v___x_910_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
v___x_911_ = lean_uint8_dec_eq(v_c_906_, v___x_910_);
if (v___x_911_ == 0)
{
uint8_t v___x_912_; 
v___x_912_ = 1;
return v___x_912_;
}
else
{
return v___x_909_;
}
}
else
{
uint8_t v___x_913_; 
v___x_913_ = 0;
return v___x_913_;
}
}
v___jp_914_:
{
if (v___y_915_ == 0)
{
return v___y_915_;
}
else
{
goto v___jp_907_;
}
}
v___jp_916_:
{
if (v___y_917_ == 0)
{
uint8_t v___x_918_; uint8_t v___x_919_; 
v___x_918_ = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__0, &l_Std_Http_Internal_Char_isQueryChar___closed__0_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__0);
v___x_919_ = lean_uint8_dec_eq(v_c_906_, v___x_918_);
if (v___x_919_ == 0)
{
uint8_t v___x_920_; uint8_t v___x_921_; 
v___x_920_ = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__1, &l_Std_Http_Internal_Char_isQueryChar___closed__1_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__1);
v___x_921_ = lean_uint8_dec_eq(v_c_906_, v___x_920_);
v___y_915_ = v___x_921_;
goto v___jp_914_;
}
else
{
v___y_915_ = v___x_919_;
goto v___jp_914_;
}
}
else
{
goto v___jp_907_;
}
}
v___jp_922_:
{
if (v___y_923_ == 0)
{
uint8_t v___x_924_; uint8_t v___x_925_; 
v___x_924_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__0, &l_Std_Http_Internal_Char_isPChar___closed__0_once, _init_l_Std_Http_Internal_Char_isPChar___closed__0);
v___x_925_ = lean_uint8_dec_eq(v_c_906_, v___x_924_);
if (v___x_925_ == 0)
{
uint8_t v___x_926_; uint8_t v___x_927_; 
v___x_926_ = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__1, &l_Std_Http_Internal_Char_isPChar___closed__1_once, _init_l_Std_Http_Internal_Char_isPChar___closed__1);
v___x_927_ = lean_uint8_dec_eq(v_c_906_, v___x_926_);
v___y_917_ = v___x_927_;
goto v___jp_916_;
}
else
{
v___y_917_ = v___x_925_;
goto v___jp_916_;
}
}
else
{
goto v___jp_907_;
}
}
v___jp_928_:
{
if (v___y_929_ == 0)
{
uint8_t v___x_930_; uint8_t v___x_931_; 
v___x_930_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
v___x_931_ = lean_uint8_dec_eq(v_c_906_, v___x_930_);
if (v___x_931_ == 0)
{
uint8_t v___x_932_; uint8_t v___x_933_; 
v___x_932_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
v___x_933_ = lean_uint8_dec_eq(v_c_906_, v___x_932_);
if (v___x_933_ == 0)
{
uint8_t v___x_934_; uint8_t v___x_935_; 
v___x_934_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
v___x_935_ = lean_uint8_dec_eq(v_c_906_, v___x_934_);
if (v___x_935_ == 0)
{
uint8_t v___x_936_; uint8_t v___x_937_; 
v___x_936_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
v___x_937_ = lean_uint8_dec_eq(v_c_906_, v___x_936_);
if (v___x_937_ == 0)
{
uint8_t v___x_938_; uint8_t v___x_939_; 
v___x_938_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
v___x_939_ = lean_uint8_dec_eq(v_c_906_, v___x_938_);
if (v___x_939_ == 0)
{
uint8_t v___x_940_; uint8_t v___x_941_; 
v___x_940_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
v___x_941_ = lean_uint8_dec_eq(v_c_906_, v___x_940_);
if (v___x_941_ == 0)
{
uint8_t v___x_942_; uint8_t v___x_943_; 
v___x_942_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
v___x_943_ = lean_uint8_dec_eq(v_c_906_, v___x_942_);
if (v___x_943_ == 0)
{
uint8_t v___x_944_; uint8_t v___x_945_; 
v___x_944_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
v___x_945_ = lean_uint8_dec_eq(v_c_906_, v___x_944_);
if (v___x_945_ == 0)
{
uint8_t v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
v___x_947_ = lean_uint8_dec_eq(v_c_906_, v___x_946_);
v___y_923_ = v___x_947_;
goto v___jp_922_;
}
else
{
v___y_923_ = v___x_945_;
goto v___jp_922_;
}
}
else
{
v___y_923_ = v___x_943_;
goto v___jp_922_;
}
}
else
{
v___y_923_ = v___x_941_;
goto v___jp_922_;
}
}
else
{
v___y_923_ = v___x_939_;
goto v___jp_922_;
}
}
else
{
v___y_923_ = v___x_937_;
goto v___jp_922_;
}
}
else
{
v___y_923_ = v___x_935_;
goto v___jp_922_;
}
}
else
{
v___y_923_ = v___x_933_;
goto v___jp_922_;
}
}
else
{
v___y_923_ = v___x_931_;
goto v___jp_922_;
}
}
else
{
goto v___jp_907_;
}
}
v___jp_948_:
{
if (v___y_949_ == 0)
{
uint8_t v___x_950_; uint8_t v___x_951_; 
v___x_950_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
v___x_951_ = lean_uint8_dec_eq(v_c_906_, v___x_950_);
if (v___x_951_ == 0)
{
uint8_t v___x_952_; uint8_t v___x_953_; 
v___x_952_ = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
v___x_953_ = lean_uint8_dec_eq(v_c_906_, v___x_952_);
v___y_929_ = v___x_953_;
goto v___jp_928_;
}
else
{
v___y_929_ = v___x_951_;
goto v___jp_928_;
}
}
else
{
goto v___jp_907_;
}
}
v___jp_954_:
{
if (v___y_955_ == 0)
{
uint8_t v___x_956_; uint8_t v___x_957_; 
v___x_956_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
v___x_957_ = lean_uint8_dec_eq(v_c_906_, v___x_956_);
if (v___x_957_ == 0)
{
uint8_t v___x_958_; uint8_t v___x_959_; 
v___x_958_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
v___x_959_ = lean_uint8_dec_eq(v_c_906_, v___x_958_);
v___y_949_ = v___x_959_;
goto v___jp_948_;
}
else
{
v___y_949_ = v___x_957_;
goto v___jp_948_;
}
}
else
{
goto v___jp_907_;
}
}
v___jp_960_:
{
if (v___y_961_ == 0)
{
uint8_t v___x_962_; uint8_t v___x_963_; 
v___x_962_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
v___x_963_ = lean_uint8_dec_eq(v_c_906_, v___x_962_);
if (v___x_963_ == 0)
{
uint8_t v___x_964_; uint8_t v___x_965_; 
v___x_964_ = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
v___x_965_ = lean_uint8_dec_eq(v_c_906_, v___x_964_);
v___y_955_ = v___x_965_;
goto v___jp_954_;
}
else
{
v___y_955_ = v___x_963_;
goto v___jp_954_;
}
}
else
{
goto v___jp_907_;
}
}
v___jp_966_:
{
if (v___y_967_ == 0)
{
uint8_t v___x_968_; uint8_t v___x_969_; 
v___x_968_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
v___x_969_ = lean_uint8_dec_le(v___x_968_, v_c_906_);
if (v___x_969_ == 0)
{
v___y_961_ = v___x_969_;
goto v___jp_960_;
}
else
{
uint8_t v___x_970_; uint8_t v___x_971_; 
v___x_970_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
v___x_971_ = lean_uint8_dec_le(v_c_906_, v___x_970_);
v___y_961_ = v___x_971_;
goto v___jp_960_;
}
}
else
{
goto v___jp_907_;
}
}
v___jp_972_:
{
if (v___y_973_ == 0)
{
uint8_t v___x_974_; uint8_t v___x_975_; 
v___x_974_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
v___x_975_ = lean_uint8_dec_le(v___x_974_, v_c_906_);
if (v___x_975_ == 0)
{
v___y_967_ = v___x_975_;
goto v___jp_966_;
}
else
{
uint8_t v___x_976_; uint8_t v___x_977_; 
v___x_976_ = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
v___x_977_ = lean_uint8_dec_le(v_c_906_, v___x_976_);
v___y_967_ = v___x_977_;
goto v___jp_966_;
}
}
else
{
goto v___jp_907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryDataChar___boxed(lean_object* v_c_982_){
_start:
{
uint8_t v_c_boxed_983_; uint8_t v_res_984_; lean_object* v_r_985_; 
v_c_boxed_983_ = lean_unbox(v_c_982_);
v_res_984_ = l_Std_Http_Internal_Char_isQueryDataChar(v_c_boxed_983_);
v_r_985_ = lean_box(v_res_984_);
return v_r_985_;
}
}
lean_object* runtime_initialize_Init_Data_Char(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Internal_Char(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Internal_Char(uint8_t builtin) {
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
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Internal_Char(uint8_t builtin) {
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
res = runtime_initialize_Std_Internal_Http_Internal_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Internal_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Internal_Char(builtin);
}
#ifdef __cplusplus
}
#endif
