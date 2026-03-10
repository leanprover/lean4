// Lean compiler output
// Module: Std.Internal.Http.Internal.Char
// Imports: public import Init.Data.String
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
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAscii(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAscii___boxed(lean_object*);
uint8_t lean_uint8_dec_lt(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAsciiByte(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAsciiByte___boxed(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
static lean_once_cell_t l_Std_Http_Internal_Char_isDigitByte___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isDigitByte___closed__0;
static lean_once_cell_t l_Std_Http_Internal_Char_isDigitByte___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Internal_Char_isDigitByte___closed__1;
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
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
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAscii(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = lean_unsigned_to_nat(128u);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAscii___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_isAscii(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAsciiByte(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 128;
x_3 = lean_uint8_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAsciiByte___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Http_Internal_Char_isAsciiByte(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isDigitByte___closed__0(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 48;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isDigitByte___closed__1(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 57;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isDigitByte(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
x_3 = lean_uint8_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
uint8_t x_4; uint8_t x_5; 
x_4 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
x_5 = lean_uint8_dec_le(x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isDigitByte___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Http_Internal_Char_isDigitByte(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 97;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 122;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 65;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 90;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAlphaByte(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_8; uint8_t x_9; 
x_8 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
x_9 = lean_uint8_dec_le(x_8, x_1);
if (x_9 == 0)
{
x_2 = x_9;
goto block_7;
}
else
{
uint8_t x_10; uint8_t x_11; 
x_10 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
x_11 = lean_uint8_dec_le(x_1, x_10);
x_2 = x_11;
goto block_7;
}
block_7:
{
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; 
x_3 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
x_4 = lean_uint8_dec_le(x_3, x_1);
if (x_4 == 0)
{
return x_4;
}
else
{
uint8_t x_5; uint8_t x_6; 
x_5 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
x_6 = lean_uint8_dec_le(x_1, x_5);
return x_6;
}
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAlphaByte___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Http_Internal_Char_isAlphaByte(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_tchar(uint32_t x_1) {
_start:
{
uint8_t x_7; uint32_t x_13; uint8_t x_14; 
x_13 = 33;
x_14 = lean_uint32_dec_eq(x_1, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 35;
x_16 = lean_uint32_dec_eq(x_1, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 36;
x_18 = lean_uint32_dec_eq(x_1, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 37;
x_20 = lean_uint32_dec_eq(x_1, x_19);
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 38;
x_22 = lean_uint32_dec_eq(x_1, x_21);
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 39;
x_24 = lean_uint32_dec_eq(x_1, x_23);
if (x_24 == 0)
{
uint32_t x_25; uint8_t x_26; 
x_25 = 42;
x_26 = lean_uint32_dec_eq(x_1, x_25);
if (x_26 == 0)
{
uint32_t x_27; uint8_t x_28; 
x_27 = 43;
x_28 = lean_uint32_dec_eq(x_1, x_27);
if (x_28 == 0)
{
uint32_t x_29; uint8_t x_30; 
x_29 = 45;
x_30 = lean_uint32_dec_eq(x_1, x_29);
if (x_30 == 0)
{
uint32_t x_31; uint8_t x_32; 
x_31 = 46;
x_32 = lean_uint32_dec_eq(x_1, x_31);
if (x_32 == 0)
{
uint32_t x_33; uint8_t x_34; 
x_33 = 94;
x_34 = lean_uint32_dec_eq(x_1, x_33);
if (x_34 == 0)
{
uint32_t x_35; uint8_t x_36; 
x_35 = 95;
x_36 = lean_uint32_dec_eq(x_1, x_35);
if (x_36 == 0)
{
uint32_t x_37; uint8_t x_38; 
x_37 = 96;
x_38 = lean_uint32_dec_eq(x_1, x_37);
if (x_38 == 0)
{
uint32_t x_39; uint8_t x_40; 
x_39 = 124;
x_40 = lean_uint32_dec_eq(x_1, x_39);
if (x_40 == 0)
{
uint32_t x_41; uint8_t x_42; 
x_41 = 126;
x_42 = lean_uint32_dec_eq(x_1, x_41);
if (x_42 == 0)
{
uint32_t x_43; uint8_t x_44; 
x_43 = 48;
x_44 = lean_uint32_dec_le(x_43, x_1);
if (x_44 == 0)
{
x_7 = x_44;
goto block_12;
}
else
{
uint32_t x_45; uint8_t x_46; 
x_45 = 57;
x_46 = lean_uint32_dec_le(x_1, x_45);
x_7 = x_46;
goto block_12;
}
}
else
{
return x_42;
}
}
else
{
return x_40;
}
}
else
{
return x_38;
}
}
else
{
return x_36;
}
}
else
{
return x_34;
}
}
else
{
return x_32;
}
}
else
{
return x_30;
}
}
else
{
return x_28;
}
}
else
{
return x_26;
}
}
else
{
return x_24;
}
}
else
{
return x_22;
}
}
else
{
return x_20;
}
}
else
{
return x_18;
}
}
else
{
return x_16;
}
}
else
{
return x_14;
}
block_6:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 97;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 122;
x_5 = lean_uint32_dec_le(x_1, x_4);
return x_5;
}
}
block_12:
{
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 65;
x_9 = lean_uint32_dec_le(x_8, x_1);
if (x_9 == 0)
{
goto block_6;
}
else
{
uint32_t x_10; uint8_t x_11; 
x_10 = 90;
x_11 = lean_uint32_dec_le(x_1, x_10);
if (x_11 == 0)
{
goto block_6;
}
else
{
return x_11;
}
}
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_tchar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_tchar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_vchar(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 33;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 126;
x_5 = lean_uint32_dec_le(x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_vchar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_vchar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_qdtext(uint32_t x_1) {
_start:
{
uint32_t x_7; uint8_t x_8; 
x_7 = 9;
x_8 = lean_uint32_dec_eq(x_1, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 32;
x_10 = lean_uint32_dec_eq(x_1, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 33;
x_12 = lean_uint32_dec_eq(x_1, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 35;
x_14 = lean_uint32_dec_le(x_13, x_1);
if (x_14 == 0)
{
goto block_6;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 91;
x_16 = lean_uint32_dec_le(x_1, x_15);
if (x_16 == 0)
{
goto block_6;
}
else
{
return x_16;
}
}
}
else
{
return x_12;
}
}
else
{
return x_10;
}
}
else
{
return x_8;
}
block_6:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 93;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 126;
x_5 = lean_uint32_dec_le(x_1, x_4);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_qdtext___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_qdtext(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_quotedPairChar(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 9;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 32;
x_5 = lean_uint32_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 33;
x_7 = lean_uint32_dec_le(x_6, x_1);
if (x_7 == 0)
{
return x_7;
}
else
{
uint32_t x_8; uint8_t x_9; 
x_8 = 126;
x_9 = lean_uint32_dec_le(x_1, x_8);
return x_9;
}
}
else
{
return x_5;
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_quotedPairChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_quotedPairChar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_quotedStringChar(uint32_t x_1) {
_start:
{
uint32_t x_16; uint8_t x_17; 
x_16 = 9;
x_17 = lean_uint32_dec_eq(x_1, x_16);
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = 32;
x_19 = lean_uint32_dec_eq(x_1, x_18);
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 33;
x_21 = lean_uint32_dec_eq(x_1, x_20);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 35;
x_23 = lean_uint32_dec_le(x_22, x_1);
if (x_23 == 0)
{
goto block_15;
}
else
{
uint32_t x_24; uint8_t x_25; 
x_24 = 91;
x_25 = lean_uint32_dec_le(x_1, x_24);
if (x_25 == 0)
{
goto block_15;
}
else
{
return x_25;
}
}
}
else
{
return x_21;
}
}
else
{
return x_19;
}
}
else
{
return x_17;
}
block_10:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 9;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 32;
x_5 = lean_uint32_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 33;
x_7 = lean_uint32_dec_le(x_6, x_1);
if (x_7 == 0)
{
return x_7;
}
else
{
uint32_t x_8; uint8_t x_9; 
x_8 = 126;
x_9 = lean_uint32_dec_le(x_1, x_8);
return x_9;
}
}
else
{
return x_5;
}
}
else
{
return x_3;
}
}
block_15:
{
uint32_t x_11; uint8_t x_12; 
x_11 = 93;
x_12 = lean_uint32_dec_le(x_11, x_1);
if (x_12 == 0)
{
goto block_10;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 126;
x_14 = lean_uint32_dec_le(x_1, x_13);
if (x_14 == 0)
{
goto block_10;
}
else
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_quotedStringChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_quotedStringChar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_fieldVchar(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 33;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 126;
x_5 = lean_uint32_dec_le(x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldVchar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_fieldVchar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_fieldContent(uint32_t x_1) {
_start:
{
uint32_t x_7; uint8_t x_8; 
x_7 = 33;
x_8 = lean_uint32_dec_le(x_7, x_1);
if (x_8 == 0)
{
goto block_6;
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = 126;
x_10 = lean_uint32_dec_le(x_1, x_9);
if (x_10 == 0)
{
goto block_6;
}
else
{
return x_10;
}
}
block_6:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 32;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 9;
x_5 = lean_uint32_dec_eq(x_1, x_4);
return x_5;
}
else
{
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_fieldContent___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_fieldContent(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_ctext(uint32_t x_1) {
_start:
{
uint32_t x_12; uint8_t x_13; 
x_12 = 9;
x_13 = lean_uint32_dec_eq(x_1, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 32;
x_15 = lean_uint32_dec_eq(x_1, x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 33;
x_17 = lean_uint32_dec_le(x_16, x_1);
if (x_17 == 0)
{
goto block_11;
}
else
{
uint32_t x_18; uint8_t x_19; 
x_18 = 39;
x_19 = lean_uint32_dec_le(x_1, x_18);
if (x_19 == 0)
{
goto block_11;
}
else
{
return x_19;
}
}
}
else
{
return x_15;
}
}
else
{
return x_13;
}
block_6:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 93;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 126;
x_5 = lean_uint32_dec_le(x_1, x_4);
return x_5;
}
}
block_11:
{
uint32_t x_7; uint8_t x_8; 
x_7 = 42;
x_8 = lean_uint32_dec_le(x_7, x_1);
if (x_8 == 0)
{
goto block_6;
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = 91;
x_10 = lean_uint32_dec_le(x_1, x_9);
if (x_10 == 0)
{
goto block_6;
}
else
{
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ctext___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_ctext(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_etagc(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 33;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 35;
x_5 = lean_uint32_dec_le(x_4, x_1);
if (x_5 == 0)
{
return x_3;
}
else
{
uint32_t x_6; uint8_t x_7; 
x_6 = 126;
x_7 = lean_uint32_dec_le(x_1, x_6);
if (x_7 == 0)
{
return x_3;
}
else
{
return x_7;
}
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_etagc___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_etagc(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_ows(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 32;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 9;
x_5 = lean_uint32_dec_eq(x_1, x_4);
return x_5;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_ows___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_ows(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_bws(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 32;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 9;
x_5 = lean_uint32_dec_eq(x_1, x_4);
return x_5;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_bws___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_bws(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_rws(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 32;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 9;
x_5 = lean_uint32_dec_eq(x_1, x_4);
return x_5;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_rws___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_rws(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_obsText(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(128u);
x_3 = lean_uint32_to_nat(x_1);
x_4 = lean_nat_dec_le(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_obsText___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_obsText(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_reasonPhraseChar(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 9;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 32;
x_5 = lean_uint32_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 33;
x_7 = lean_uint32_dec_le(x_6, x_1);
if (x_7 == 0)
{
return x_7;
}
else
{
uint32_t x_8; uint8_t x_9; 
x_8 = 126;
x_9 = lean_uint32_dec_le(x_1, x_8);
return x_9;
}
}
else
{
return x_5;
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_reasonPhraseChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_reasonPhraseChar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isHexDigit(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 97;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 98;
x_5 = lean_uint32_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 99;
x_7 = lean_uint32_dec_eq(x_1, x_6);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 100;
x_9 = lean_uint32_dec_eq(x_1, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 101;
x_11 = lean_uint32_dec_eq(x_1, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 102;
x_13 = lean_uint32_dec_eq(x_1, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 65;
x_15 = lean_uint32_dec_eq(x_1, x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 66;
x_17 = lean_uint32_dec_eq(x_1, x_16);
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = 67;
x_19 = lean_uint32_dec_eq(x_1, x_18);
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 68;
x_21 = lean_uint32_dec_eq(x_1, x_20);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 69;
x_23 = lean_uint32_dec_eq(x_1, x_22);
if (x_23 == 0)
{
uint32_t x_24; uint8_t x_25; 
x_24 = 70;
x_25 = lean_uint32_dec_eq(x_1, x_24);
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = 48;
x_27 = lean_uint32_dec_le(x_26, x_1);
if (x_27 == 0)
{
return x_27;
}
else
{
uint32_t x_28; uint8_t x_29; 
x_28 = 57;
x_29 = lean_uint32_dec_le(x_1, x_28);
return x_29;
}
}
else
{
return x_25;
}
}
else
{
return x_23;
}
}
else
{
return x_21;
}
}
else
{
return x_19;
}
}
else
{
return x_17;
}
}
else
{
return x_15;
}
}
else
{
return x_13;
}
}
else
{
return x_11;
}
}
else
{
return x_9;
}
}
else
{
return x_7;
}
}
else
{
return x_5;
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigit___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_isHexDigit(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__0(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 70;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__1(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 102;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isHexDigitByte(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_8; uint8_t x_14; uint8_t x_15; 
x_14 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
x_15 = lean_uint8_dec_le(x_14, x_1);
if (x_15 == 0)
{
x_8 = x_15;
goto block_13;
}
else
{
uint8_t x_16; uint8_t x_17; 
x_16 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
x_17 = lean_uint8_dec_le(x_1, x_16);
x_8 = x_17;
goto block_13;
}
block_7:
{
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; 
x_3 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
x_4 = lean_uint8_dec_le(x_3, x_1);
if (x_4 == 0)
{
return x_4;
}
else
{
uint8_t x_5; uint8_t x_6; 
x_5 = lean_uint8_once(&l_Std_Http_Internal_Char_isHexDigitByte___closed__0, &l_Std_Http_Internal_Char_isHexDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__0);
x_6 = lean_uint8_dec_le(x_1, x_5);
return x_6;
}
}
else
{
return x_2;
}
}
block_13:
{
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
x_10 = lean_uint8_dec_le(x_9, x_1);
if (x_10 == 0)
{
x_2 = x_10;
goto block_7;
}
else
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_uint8_once(&l_Std_Http_Internal_Char_isHexDigitByte___closed__1, &l_Std_Http_Internal_Char_isHexDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__1);
x_12 = lean_uint8_dec_le(x_1, x_11);
x_2 = x_12;
goto block_7;
}
}
else
{
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isHexDigitByte___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Http_Internal_Char_isHexDigitByte(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAlphaNum(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_8; uint8_t x_14; uint8_t x_15; 
x_14 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
x_15 = lean_uint8_dec_le(x_14, x_1);
if (x_15 == 0)
{
x_8 = x_15;
goto block_13;
}
else
{
uint8_t x_16; uint8_t x_17; 
x_16 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
x_17 = lean_uint8_dec_le(x_1, x_16);
x_8 = x_17;
goto block_13;
}
block_7:
{
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; 
x_3 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
x_4 = lean_uint8_dec_le(x_3, x_1);
if (x_4 == 0)
{
return x_4;
}
else
{
uint8_t x_5; uint8_t x_6; 
x_5 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
x_6 = lean_uint8_dec_le(x_1, x_5);
return x_6;
}
}
else
{
return x_2;
}
}
block_13:
{
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
x_10 = lean_uint8_dec_le(x_9, x_1);
if (x_10 == 0)
{
x_2 = x_10;
goto block_7;
}
else
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
x_12 = lean_uint8_dec_le(x_1, x_11);
x_2 = x_12;
goto block_7;
}
}
else
{
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAlphaNum___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Http_Internal_Char_isAlphaNum(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isAsciiAlphaNumChar(uint32_t x_1) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_7 = lean_uint32_to_nat(x_1);
x_8 = lean_unsigned_to_nat(128u);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
return x_9;
}
else
{
uint32_t x_16; uint8_t x_17; 
x_16 = 48;
x_17 = lean_uint32_dec_le(x_16, x_1);
if (x_17 == 0)
{
x_10 = x_17;
goto block_15;
}
else
{
uint32_t x_18; uint8_t x_19; 
x_18 = 57;
x_19 = lean_uint32_dec_le(x_1, x_18);
x_10 = x_19;
goto block_15;
}
}
block_6:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 97;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 122;
x_5 = lean_uint32_dec_le(x_1, x_4);
return x_5;
}
}
block_15:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 65;
x_12 = lean_uint32_dec_le(x_11, x_1);
if (x_12 == 0)
{
goto block_6;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 90;
x_14 = lean_uint32_dec_le(x_1, x_13);
if (x_14 == 0)
{
goto block_6;
}
else
{
return x_9;
}
}
}
else
{
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isAsciiAlphaNumChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_isAsciiAlphaNumChar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isValidSchemeChar(uint32_t x_1) {
_start:
{
uint8_t x_2; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_15 = lean_uint32_to_nat(x_1);
x_16 = lean_unsigned_to_nat(128u);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
x_2 = x_17;
goto block_9;
}
else
{
uint32_t x_24; uint8_t x_25; 
x_24 = 48;
x_25 = lean_uint32_dec_le(x_24, x_1);
if (x_25 == 0)
{
x_18 = x_25;
goto block_23;
}
else
{
uint32_t x_26; uint8_t x_27; 
x_26 = 57;
x_27 = lean_uint32_dec_le(x_1, x_26);
x_18 = x_27;
goto block_23;
}
}
block_9:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 43;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 45;
x_6 = lean_uint32_dec_eq(x_1, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 46;
x_8 = lean_uint32_dec_eq(x_1, x_7);
if (x_8 == 0)
{
return x_2;
}
else
{
return x_8;
}
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
block_14:
{
uint32_t x_10; uint8_t x_11; 
x_10 = 97;
x_11 = lean_uint32_dec_le(x_10, x_1);
if (x_11 == 0)
{
x_2 = x_11;
goto block_9;
}
else
{
uint32_t x_12; uint8_t x_13; 
x_12 = 122;
x_13 = lean_uint32_dec_le(x_1, x_12);
x_2 = x_13;
goto block_9;
}
}
block_23:
{
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 65;
x_20 = lean_uint32_dec_le(x_19, x_1);
if (x_20 == 0)
{
goto block_14;
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 90;
x_22 = lean_uint32_dec_le(x_1, x_21);
if (x_22 == 0)
{
goto block_14;
}
else
{
x_2 = x_17;
goto block_9;
}
}
}
else
{
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidSchemeChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_isValidSchemeChar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isValidDomainNameChar(uint32_t x_1) {
_start:
{
uint8_t x_2; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_13 = lean_uint32_to_nat(x_1);
x_14 = lean_unsigned_to_nat(128u);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
x_2 = x_15;
goto block_7;
}
else
{
uint32_t x_22; uint8_t x_23; 
x_22 = 48;
x_23 = lean_uint32_dec_le(x_22, x_1);
if (x_23 == 0)
{
x_16 = x_23;
goto block_21;
}
else
{
uint32_t x_24; uint8_t x_25; 
x_24 = 57;
x_25 = lean_uint32_dec_le(x_1, x_24);
x_16 = x_25;
goto block_21;
}
}
block_7:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 45;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 46;
x_6 = lean_uint32_dec_eq(x_1, x_5);
if (x_6 == 0)
{
return x_2;
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
block_12:
{
uint32_t x_8; uint8_t x_9; 
x_8 = 97;
x_9 = lean_uint32_dec_le(x_8, x_1);
if (x_9 == 0)
{
x_2 = x_9;
goto block_7;
}
else
{
uint32_t x_10; uint8_t x_11; 
x_10 = 122;
x_11 = lean_uint32_dec_le(x_1, x_10);
x_2 = x_11;
goto block_7;
}
}
block_21:
{
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 65;
x_18 = lean_uint32_dec_le(x_17, x_1);
if (x_18 == 0)
{
goto block_12;
}
else
{
uint32_t x_19; uint8_t x_20; 
x_19 = 90;
x_20 = lean_uint32_dec_le(x_1, x_19);
if (x_20 == 0)
{
goto block_12;
}
else
{
x_2 = x_15;
goto block_7;
}
}
}
else
{
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isValidDomainNameChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Std_Http_Internal_Char_isValidDomainNameChar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isUnreserved___closed__0(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 95;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isUnreserved___closed__1(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 126;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isUnreserved___closed__2(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 45;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isUnreserved___closed__3(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 46;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUnreserved(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_8; uint8_t x_14; uint8_t x_20; uint8_t x_26; uint8_t x_27; 
x_26 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
x_27 = lean_uint8_dec_le(x_26, x_1);
if (x_27 == 0)
{
x_20 = x_27;
goto block_25;
}
else
{
uint8_t x_28; uint8_t x_29; 
x_28 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
x_29 = lean_uint8_dec_le(x_1, x_28);
x_20 = x_29;
goto block_25;
}
block_7:
{
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; 
x_3 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
x_4 = lean_uint8_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; uint8_t x_6; 
x_5 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
x_6 = lean_uint8_dec_eq(x_1, x_5);
return x_6;
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
block_13:
{
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
x_10 = lean_uint8_dec_eq(x_1, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
x_12 = lean_uint8_dec_eq(x_1, x_11);
x_2 = x_12;
goto block_7;
}
else
{
x_2 = x_10;
goto block_7;
}
}
else
{
return x_8;
}
}
block_19:
{
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; 
x_15 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
x_16 = lean_uint8_dec_le(x_15, x_1);
if (x_16 == 0)
{
x_8 = x_16;
goto block_13;
}
else
{
uint8_t x_17; uint8_t x_18; 
x_17 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
x_18 = lean_uint8_dec_le(x_1, x_17);
x_8 = x_18;
goto block_13;
}
}
else
{
return x_14;
}
}
block_25:
{
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; 
x_21 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
x_22 = lean_uint8_dec_le(x_21, x_1);
if (x_22 == 0)
{
x_14 = x_22;
goto block_19;
}
else
{
uint8_t x_23; uint8_t x_24; 
x_23 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
x_24 = lean_uint8_dec_le(x_1, x_23);
x_14 = x_24;
goto block_19;
}
}
else
{
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUnreserved___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Http_Internal_Char_isUnreserved(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__0(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 38;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__1(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 39;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__2(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 40;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__3(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 41;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__4(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 42;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__5(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 43;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__6(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 44;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__7(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 59;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__8(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 61;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__9(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 33;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isSubDelims___closed__10(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 36;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isSubDelims(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_22; uint8_t x_23; 
x_22 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
x_23 = lean_uint8_dec_eq(x_1, x_22);
if (x_23 == 0)
{
uint8_t x_24; uint8_t x_25; 
x_24 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
x_25 = lean_uint8_dec_eq(x_1, x_24);
x_2 = x_25;
goto block_21;
}
else
{
x_2 = x_23;
goto block_21;
}
block_21:
{
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; 
x_3 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
x_4 = lean_uint8_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; uint8_t x_6; 
x_5 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
x_6 = lean_uint8_dec_eq(x_1, x_5);
if (x_6 == 0)
{
uint8_t x_7; uint8_t x_8; 
x_7 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
x_8 = lean_uint8_dec_eq(x_1, x_7);
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
x_10 = lean_uint8_dec_eq(x_1, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
x_12 = lean_uint8_dec_eq(x_1, x_11);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; 
x_13 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
x_14 = lean_uint8_dec_eq(x_1, x_13);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; 
x_15 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
x_16 = lean_uint8_dec_eq(x_1, x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; 
x_17 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
x_18 = lean_uint8_dec_eq(x_1, x_17);
if (x_18 == 0)
{
uint8_t x_19; uint8_t x_20; 
x_19 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
x_20 = lean_uint8_dec_eq(x_1, x_19);
return x_20;
}
else
{
return x_18;
}
}
else
{
return x_16;
}
}
else
{
return x_14;
}
}
else
{
return x_12;
}
}
else
{
return x_10;
}
}
else
{
return x_8;
}
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isSubDelims___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Http_Internal_Char_isSubDelims(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isPChar___closed__0(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 58;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isPChar___closed__1(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 64;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isPChar(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_8; uint8_t x_28; uint8_t x_34; uint8_t x_40; uint8_t x_46; uint8_t x_52; uint8_t x_58; uint8_t x_59; 
x_58 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
x_59 = lean_uint8_dec_le(x_58, x_1);
if (x_59 == 0)
{
x_52 = x_59;
goto block_57;
}
else
{
uint8_t x_60; uint8_t x_61; 
x_60 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
x_61 = lean_uint8_dec_le(x_1, x_60);
x_52 = x_61;
goto block_57;
}
block_7:
{
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; 
x_3 = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__0, &l_Std_Http_Internal_Char_isPChar___closed__0_once, _init_l_Std_Http_Internal_Char_isPChar___closed__0);
x_4 = lean_uint8_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; uint8_t x_6; 
x_5 = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__1, &l_Std_Http_Internal_Char_isPChar___closed__1_once, _init_l_Std_Http_Internal_Char_isPChar___closed__1);
x_6 = lean_uint8_dec_eq(x_1, x_5);
return x_6;
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
block_27:
{
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
x_10 = lean_uint8_dec_eq(x_1, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
x_12 = lean_uint8_dec_eq(x_1, x_11);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; 
x_13 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
x_14 = lean_uint8_dec_eq(x_1, x_13);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; 
x_15 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
x_16 = lean_uint8_dec_eq(x_1, x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; 
x_17 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
x_18 = lean_uint8_dec_eq(x_1, x_17);
if (x_18 == 0)
{
uint8_t x_19; uint8_t x_20; 
x_19 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
x_20 = lean_uint8_dec_eq(x_1, x_19);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; 
x_21 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
x_22 = lean_uint8_dec_eq(x_1, x_21);
if (x_22 == 0)
{
uint8_t x_23; uint8_t x_24; 
x_23 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
x_24 = lean_uint8_dec_eq(x_1, x_23);
if (x_24 == 0)
{
uint8_t x_25; uint8_t x_26; 
x_25 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
x_26 = lean_uint8_dec_eq(x_1, x_25);
x_2 = x_26;
goto block_7;
}
else
{
x_2 = x_24;
goto block_7;
}
}
else
{
x_2 = x_22;
goto block_7;
}
}
else
{
x_2 = x_20;
goto block_7;
}
}
else
{
x_2 = x_18;
goto block_7;
}
}
else
{
x_2 = x_16;
goto block_7;
}
}
else
{
x_2 = x_14;
goto block_7;
}
}
else
{
x_2 = x_12;
goto block_7;
}
}
else
{
x_2 = x_10;
goto block_7;
}
}
else
{
return x_8;
}
}
block_33:
{
if (x_28 == 0)
{
uint8_t x_29; uint8_t x_30; 
x_29 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
x_30 = lean_uint8_dec_eq(x_1, x_29);
if (x_30 == 0)
{
uint8_t x_31; uint8_t x_32; 
x_31 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
x_32 = lean_uint8_dec_eq(x_1, x_31);
x_8 = x_32;
goto block_27;
}
else
{
x_8 = x_30;
goto block_27;
}
}
else
{
return x_28;
}
}
block_39:
{
if (x_34 == 0)
{
uint8_t x_35; uint8_t x_36; 
x_35 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
x_36 = lean_uint8_dec_eq(x_1, x_35);
if (x_36 == 0)
{
uint8_t x_37; uint8_t x_38; 
x_37 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
x_38 = lean_uint8_dec_eq(x_1, x_37);
x_28 = x_38;
goto block_33;
}
else
{
x_28 = x_36;
goto block_33;
}
}
else
{
return x_34;
}
}
block_45:
{
if (x_40 == 0)
{
uint8_t x_41; uint8_t x_42; 
x_41 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
x_42 = lean_uint8_dec_eq(x_1, x_41);
if (x_42 == 0)
{
uint8_t x_43; uint8_t x_44; 
x_43 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
x_44 = lean_uint8_dec_eq(x_1, x_43);
x_34 = x_44;
goto block_39;
}
else
{
x_34 = x_42;
goto block_39;
}
}
else
{
return x_40;
}
}
block_51:
{
if (x_46 == 0)
{
uint8_t x_47; uint8_t x_48; 
x_47 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
x_48 = lean_uint8_dec_le(x_47, x_1);
if (x_48 == 0)
{
x_40 = x_48;
goto block_45;
}
else
{
uint8_t x_49; uint8_t x_50; 
x_49 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
x_50 = lean_uint8_dec_le(x_1, x_49);
x_40 = x_50;
goto block_45;
}
}
else
{
return x_46;
}
}
block_57:
{
if (x_52 == 0)
{
uint8_t x_53; uint8_t x_54; 
x_53 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
x_54 = lean_uint8_dec_le(x_53, x_1);
if (x_54 == 0)
{
x_46 = x_54;
goto block_51;
}
else
{
uint8_t x_55; uint8_t x_56; 
x_55 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
x_56 = lean_uint8_dec_le(x_1, x_55);
x_46 = x_56;
goto block_51;
}
}
else
{
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isPChar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Http_Internal_Char_isPChar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isQueryChar___closed__0(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 47;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Http_Internal_Char_isQueryChar___closed__1(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 63;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isQueryChar(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_8; uint8_t x_14; uint8_t x_34; uint8_t x_40; uint8_t x_46; uint8_t x_52; uint8_t x_58; uint8_t x_64; uint8_t x_65; 
x_64 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
x_65 = lean_uint8_dec_le(x_64, x_1);
if (x_65 == 0)
{
x_58 = x_65;
goto block_63;
}
else
{
uint8_t x_66; uint8_t x_67; 
x_66 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
x_67 = lean_uint8_dec_le(x_1, x_66);
x_58 = x_67;
goto block_63;
}
block_7:
{
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; 
x_3 = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__0, &l_Std_Http_Internal_Char_isQueryChar___closed__0_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__0);
x_4 = lean_uint8_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; uint8_t x_6; 
x_5 = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__1, &l_Std_Http_Internal_Char_isQueryChar___closed__1_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__1);
x_6 = lean_uint8_dec_eq(x_1, x_5);
return x_6;
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
block_13:
{
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__0, &l_Std_Http_Internal_Char_isPChar___closed__0_once, _init_l_Std_Http_Internal_Char_isPChar___closed__0);
x_10 = lean_uint8_dec_eq(x_1, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__1, &l_Std_Http_Internal_Char_isPChar___closed__1_once, _init_l_Std_Http_Internal_Char_isPChar___closed__1);
x_12 = lean_uint8_dec_eq(x_1, x_11);
x_2 = x_12;
goto block_7;
}
else
{
x_2 = x_10;
goto block_7;
}
}
else
{
return x_8;
}
}
block_33:
{
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; 
x_15 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
x_16 = lean_uint8_dec_eq(x_1, x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; 
x_17 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
x_18 = lean_uint8_dec_eq(x_1, x_17);
if (x_18 == 0)
{
uint8_t x_19; uint8_t x_20; 
x_19 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
x_20 = lean_uint8_dec_eq(x_1, x_19);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; 
x_21 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
x_22 = lean_uint8_dec_eq(x_1, x_21);
if (x_22 == 0)
{
uint8_t x_23; uint8_t x_24; 
x_23 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
x_24 = lean_uint8_dec_eq(x_1, x_23);
if (x_24 == 0)
{
uint8_t x_25; uint8_t x_26; 
x_25 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
x_26 = lean_uint8_dec_eq(x_1, x_25);
if (x_26 == 0)
{
uint8_t x_27; uint8_t x_28; 
x_27 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
x_28 = lean_uint8_dec_eq(x_1, x_27);
if (x_28 == 0)
{
uint8_t x_29; uint8_t x_30; 
x_29 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
x_30 = lean_uint8_dec_eq(x_1, x_29);
if (x_30 == 0)
{
uint8_t x_31; uint8_t x_32; 
x_31 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
x_32 = lean_uint8_dec_eq(x_1, x_31);
x_8 = x_32;
goto block_13;
}
else
{
x_8 = x_30;
goto block_13;
}
}
else
{
x_8 = x_28;
goto block_13;
}
}
else
{
x_8 = x_26;
goto block_13;
}
}
else
{
x_8 = x_24;
goto block_13;
}
}
else
{
x_8 = x_22;
goto block_13;
}
}
else
{
x_8 = x_20;
goto block_13;
}
}
else
{
x_8 = x_18;
goto block_13;
}
}
else
{
x_8 = x_16;
goto block_13;
}
}
else
{
return x_14;
}
}
block_39:
{
if (x_34 == 0)
{
uint8_t x_35; uint8_t x_36; 
x_35 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
x_36 = lean_uint8_dec_eq(x_1, x_35);
if (x_36 == 0)
{
uint8_t x_37; uint8_t x_38; 
x_37 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
x_38 = lean_uint8_dec_eq(x_1, x_37);
x_14 = x_38;
goto block_33;
}
else
{
x_14 = x_36;
goto block_33;
}
}
else
{
return x_34;
}
}
block_45:
{
if (x_40 == 0)
{
uint8_t x_41; uint8_t x_42; 
x_41 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
x_42 = lean_uint8_dec_eq(x_1, x_41);
if (x_42 == 0)
{
uint8_t x_43; uint8_t x_44; 
x_43 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
x_44 = lean_uint8_dec_eq(x_1, x_43);
x_34 = x_44;
goto block_39;
}
else
{
x_34 = x_42;
goto block_39;
}
}
else
{
return x_40;
}
}
block_51:
{
if (x_46 == 0)
{
uint8_t x_47; uint8_t x_48; 
x_47 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
x_48 = lean_uint8_dec_eq(x_1, x_47);
if (x_48 == 0)
{
uint8_t x_49; uint8_t x_50; 
x_49 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
x_50 = lean_uint8_dec_eq(x_1, x_49);
x_40 = x_50;
goto block_45;
}
else
{
x_40 = x_48;
goto block_45;
}
}
else
{
return x_46;
}
}
block_57:
{
if (x_52 == 0)
{
uint8_t x_53; uint8_t x_54; 
x_53 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
x_54 = lean_uint8_dec_le(x_53, x_1);
if (x_54 == 0)
{
x_46 = x_54;
goto block_51;
}
else
{
uint8_t x_55; uint8_t x_56; 
x_55 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
x_56 = lean_uint8_dec_le(x_1, x_55);
x_46 = x_56;
goto block_51;
}
}
else
{
return x_52;
}
}
block_63:
{
if (x_58 == 0)
{
uint8_t x_59; uint8_t x_60; 
x_59 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
x_60 = lean_uint8_dec_le(x_59, x_1);
if (x_60 == 0)
{
x_52 = x_60;
goto block_57;
}
else
{
uint8_t x_61; uint8_t x_62; 
x_61 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
x_62 = lean_uint8_dec_le(x_1, x_61);
x_52 = x_62;
goto block_57;
}
}
else
{
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isQueryChar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Http_Internal_Char_isQueryChar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isFragmentChar(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_8; uint8_t x_14; uint8_t x_34; uint8_t x_40; uint8_t x_46; uint8_t x_52; uint8_t x_58; uint8_t x_64; uint8_t x_65; 
x_64 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
x_65 = lean_uint8_dec_le(x_64, x_1);
if (x_65 == 0)
{
x_58 = x_65;
goto block_63;
}
else
{
uint8_t x_66; uint8_t x_67; 
x_66 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
x_67 = lean_uint8_dec_le(x_1, x_66);
x_58 = x_67;
goto block_63;
}
block_7:
{
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; 
x_3 = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__0, &l_Std_Http_Internal_Char_isQueryChar___closed__0_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__0);
x_4 = lean_uint8_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; uint8_t x_6; 
x_5 = lean_uint8_once(&l_Std_Http_Internal_Char_isQueryChar___closed__1, &l_Std_Http_Internal_Char_isQueryChar___closed__1_once, _init_l_Std_Http_Internal_Char_isQueryChar___closed__1);
x_6 = lean_uint8_dec_eq(x_1, x_5);
return x_6;
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
block_13:
{
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__0, &l_Std_Http_Internal_Char_isPChar___closed__0_once, _init_l_Std_Http_Internal_Char_isPChar___closed__0);
x_10 = lean_uint8_dec_eq(x_1, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__1, &l_Std_Http_Internal_Char_isPChar___closed__1_once, _init_l_Std_Http_Internal_Char_isPChar___closed__1);
x_12 = lean_uint8_dec_eq(x_1, x_11);
x_2 = x_12;
goto block_7;
}
else
{
x_2 = x_10;
goto block_7;
}
}
else
{
return x_8;
}
}
block_33:
{
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; 
x_15 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
x_16 = lean_uint8_dec_eq(x_1, x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; 
x_17 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
x_18 = lean_uint8_dec_eq(x_1, x_17);
if (x_18 == 0)
{
uint8_t x_19; uint8_t x_20; 
x_19 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
x_20 = lean_uint8_dec_eq(x_1, x_19);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; 
x_21 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
x_22 = lean_uint8_dec_eq(x_1, x_21);
if (x_22 == 0)
{
uint8_t x_23; uint8_t x_24; 
x_23 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
x_24 = lean_uint8_dec_eq(x_1, x_23);
if (x_24 == 0)
{
uint8_t x_25; uint8_t x_26; 
x_25 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
x_26 = lean_uint8_dec_eq(x_1, x_25);
if (x_26 == 0)
{
uint8_t x_27; uint8_t x_28; 
x_27 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
x_28 = lean_uint8_dec_eq(x_1, x_27);
if (x_28 == 0)
{
uint8_t x_29; uint8_t x_30; 
x_29 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
x_30 = lean_uint8_dec_eq(x_1, x_29);
if (x_30 == 0)
{
uint8_t x_31; uint8_t x_32; 
x_31 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
x_32 = lean_uint8_dec_eq(x_1, x_31);
x_8 = x_32;
goto block_13;
}
else
{
x_8 = x_30;
goto block_13;
}
}
else
{
x_8 = x_28;
goto block_13;
}
}
else
{
x_8 = x_26;
goto block_13;
}
}
else
{
x_8 = x_24;
goto block_13;
}
}
else
{
x_8 = x_22;
goto block_13;
}
}
else
{
x_8 = x_20;
goto block_13;
}
}
else
{
x_8 = x_18;
goto block_13;
}
}
else
{
x_8 = x_16;
goto block_13;
}
}
else
{
return x_14;
}
}
block_39:
{
if (x_34 == 0)
{
uint8_t x_35; uint8_t x_36; 
x_35 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
x_36 = lean_uint8_dec_eq(x_1, x_35);
if (x_36 == 0)
{
uint8_t x_37; uint8_t x_38; 
x_37 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
x_38 = lean_uint8_dec_eq(x_1, x_37);
x_14 = x_38;
goto block_33;
}
else
{
x_14 = x_36;
goto block_33;
}
}
else
{
return x_34;
}
}
block_45:
{
if (x_40 == 0)
{
uint8_t x_41; uint8_t x_42; 
x_41 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
x_42 = lean_uint8_dec_eq(x_1, x_41);
if (x_42 == 0)
{
uint8_t x_43; uint8_t x_44; 
x_43 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
x_44 = lean_uint8_dec_eq(x_1, x_43);
x_34 = x_44;
goto block_39;
}
else
{
x_34 = x_42;
goto block_39;
}
}
else
{
return x_40;
}
}
block_51:
{
if (x_46 == 0)
{
uint8_t x_47; uint8_t x_48; 
x_47 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
x_48 = lean_uint8_dec_eq(x_1, x_47);
if (x_48 == 0)
{
uint8_t x_49; uint8_t x_50; 
x_49 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
x_50 = lean_uint8_dec_eq(x_1, x_49);
x_40 = x_50;
goto block_45;
}
else
{
x_40 = x_48;
goto block_45;
}
}
else
{
return x_46;
}
}
block_57:
{
if (x_52 == 0)
{
uint8_t x_53; uint8_t x_54; 
x_53 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
x_54 = lean_uint8_dec_le(x_53, x_1);
if (x_54 == 0)
{
x_46 = x_54;
goto block_51;
}
else
{
uint8_t x_55; uint8_t x_56; 
x_55 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
x_56 = lean_uint8_dec_le(x_1, x_55);
x_46 = x_56;
goto block_51;
}
}
else
{
return x_52;
}
}
block_63:
{
if (x_58 == 0)
{
uint8_t x_59; uint8_t x_60; 
x_59 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
x_60 = lean_uint8_dec_le(x_59, x_1);
if (x_60 == 0)
{
x_52 = x_60;
goto block_57;
}
else
{
uint8_t x_61; uint8_t x_62; 
x_61 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
x_62 = lean_uint8_dec_le(x_1, x_61);
x_52 = x_62;
goto block_57;
}
}
else
{
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isFragmentChar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Http_Internal_Char_isFragmentChar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Char_isUserInfoChar(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_6; uint8_t x_26; uint8_t x_32; uint8_t x_38; uint8_t x_44; uint8_t x_50; uint8_t x_56; uint8_t x_57; 
x_56 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__0, &l_Std_Http_Internal_Char_isDigitByte___closed__0_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__0);
x_57 = lean_uint8_dec_le(x_56, x_1);
if (x_57 == 0)
{
x_50 = x_57;
goto block_55;
}
else
{
uint8_t x_58; uint8_t x_59; 
x_58 = lean_uint8_once(&l_Std_Http_Internal_Char_isDigitByte___closed__1, &l_Std_Http_Internal_Char_isDigitByte___closed__1_once, _init_l_Std_Http_Internal_Char_isDigitByte___closed__1);
x_59 = lean_uint8_dec_le(x_1, x_58);
x_50 = x_59;
goto block_55;
}
block_5:
{
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; 
x_3 = lean_uint8_once(&l_Std_Http_Internal_Char_isPChar___closed__0, &l_Std_Http_Internal_Char_isPChar___closed__0_once, _init_l_Std_Http_Internal_Char_isPChar___closed__0);
x_4 = lean_uint8_dec_eq(x_1, x_3);
return x_4;
}
else
{
return x_2;
}
}
block_25:
{
if (x_6 == 0)
{
uint8_t x_7; uint8_t x_8; 
x_7 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__0, &l_Std_Http_Internal_Char_isSubDelims___closed__0_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__0);
x_8 = lean_uint8_dec_eq(x_1, x_7);
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__1, &l_Std_Http_Internal_Char_isSubDelims___closed__1_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__1);
x_10 = lean_uint8_dec_eq(x_1, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__2, &l_Std_Http_Internal_Char_isSubDelims___closed__2_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__2);
x_12 = lean_uint8_dec_eq(x_1, x_11);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; 
x_13 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__3, &l_Std_Http_Internal_Char_isSubDelims___closed__3_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__3);
x_14 = lean_uint8_dec_eq(x_1, x_13);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; 
x_15 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__4, &l_Std_Http_Internal_Char_isSubDelims___closed__4_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__4);
x_16 = lean_uint8_dec_eq(x_1, x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; 
x_17 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__5, &l_Std_Http_Internal_Char_isSubDelims___closed__5_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
x_18 = lean_uint8_dec_eq(x_1, x_17);
if (x_18 == 0)
{
uint8_t x_19; uint8_t x_20; 
x_19 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__6, &l_Std_Http_Internal_Char_isSubDelims___closed__6_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
x_20 = lean_uint8_dec_eq(x_1, x_19);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; 
x_21 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__7, &l_Std_Http_Internal_Char_isSubDelims___closed__7_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
x_22 = lean_uint8_dec_eq(x_1, x_21);
if (x_22 == 0)
{
uint8_t x_23; uint8_t x_24; 
x_23 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__8, &l_Std_Http_Internal_Char_isSubDelims___closed__8_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
x_24 = lean_uint8_dec_eq(x_1, x_23);
x_2 = x_24;
goto block_5;
}
else
{
x_2 = x_22;
goto block_5;
}
}
else
{
x_2 = x_20;
goto block_5;
}
}
else
{
x_2 = x_18;
goto block_5;
}
}
else
{
x_2 = x_16;
goto block_5;
}
}
else
{
x_2 = x_14;
goto block_5;
}
}
else
{
x_2 = x_12;
goto block_5;
}
}
else
{
x_2 = x_10;
goto block_5;
}
}
else
{
x_2 = x_8;
goto block_5;
}
}
else
{
return x_6;
}
}
block_31:
{
if (x_26 == 0)
{
uint8_t x_27; uint8_t x_28; 
x_27 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__9, &l_Std_Http_Internal_Char_isSubDelims___closed__9_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__9);
x_28 = lean_uint8_dec_eq(x_1, x_27);
if (x_28 == 0)
{
uint8_t x_29; uint8_t x_30; 
x_29 = lean_uint8_once(&l_Std_Http_Internal_Char_isSubDelims___closed__10, &l_Std_Http_Internal_Char_isSubDelims___closed__10_once, _init_l_Std_Http_Internal_Char_isSubDelims___closed__10);
x_30 = lean_uint8_dec_eq(x_1, x_29);
x_6 = x_30;
goto block_25;
}
else
{
x_6 = x_28;
goto block_25;
}
}
else
{
return x_26;
}
}
block_37:
{
if (x_32 == 0)
{
uint8_t x_33; uint8_t x_34; 
x_33 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__0, &l_Std_Http_Internal_Char_isUnreserved___closed__0_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__0);
x_34 = lean_uint8_dec_eq(x_1, x_33);
if (x_34 == 0)
{
uint8_t x_35; uint8_t x_36; 
x_35 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__1, &l_Std_Http_Internal_Char_isUnreserved___closed__1_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__1);
x_36 = lean_uint8_dec_eq(x_1, x_35);
x_26 = x_36;
goto block_31;
}
else
{
x_26 = x_34;
goto block_31;
}
}
else
{
return x_32;
}
}
block_43:
{
if (x_38 == 0)
{
uint8_t x_39; uint8_t x_40; 
x_39 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__2, &l_Std_Http_Internal_Char_isUnreserved___closed__2_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__2);
x_40 = lean_uint8_dec_eq(x_1, x_39);
if (x_40 == 0)
{
uint8_t x_41; uint8_t x_42; 
x_41 = lean_uint8_once(&l_Std_Http_Internal_Char_isUnreserved___closed__3, &l_Std_Http_Internal_Char_isUnreserved___closed__3_once, _init_l_Std_Http_Internal_Char_isUnreserved___closed__3);
x_42 = lean_uint8_dec_eq(x_1, x_41);
x_32 = x_42;
goto block_37;
}
else
{
x_32 = x_40;
goto block_37;
}
}
else
{
return x_38;
}
}
block_49:
{
if (x_44 == 0)
{
uint8_t x_45; uint8_t x_46; 
x_45 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__2, &l_Std_Http_Internal_Char_isAlphaByte___closed__2_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2);
x_46 = lean_uint8_dec_le(x_45, x_1);
if (x_46 == 0)
{
x_38 = x_46;
goto block_43;
}
else
{
uint8_t x_47; uint8_t x_48; 
x_47 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__3, &l_Std_Http_Internal_Char_isAlphaByte___closed__3_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3);
x_48 = lean_uint8_dec_le(x_1, x_47);
x_38 = x_48;
goto block_43;
}
}
else
{
return x_44;
}
}
block_55:
{
if (x_50 == 0)
{
uint8_t x_51; uint8_t x_52; 
x_51 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__0, &l_Std_Http_Internal_Char_isAlphaByte___closed__0_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0);
x_52 = lean_uint8_dec_le(x_51, x_1);
if (x_52 == 0)
{
x_44 = x_52;
goto block_49;
}
else
{
uint8_t x_53; uint8_t x_54; 
x_53 = lean_uint8_once(&l_Std_Http_Internal_Char_isAlphaByte___closed__1, &l_Std_Http_Internal_Char_isAlphaByte___closed__1_once, _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1);
x_54 = lean_uint8_dec_le(x_1, x_53);
x_44 = x_54;
goto block_49;
}
}
else
{
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Char_isUserInfoChar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Http_Internal_Char_isUserInfoChar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* runtime_initialize_Init_Data_String(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Internal_Char(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String(builtin)
;
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
lean_object* initialize_Init_Data_String(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Internal_Char(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Internal_Char(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Internal_Char(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Internal_Char(builtin);
}
#ifdef __cplusplus
}
#endif
