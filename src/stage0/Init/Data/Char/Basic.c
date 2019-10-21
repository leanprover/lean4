// Lean compiler output
// Module: Init.Data.Char.Basic
// Imports: Init.Data.UInt
#include "runtime/lean.h"
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
uint8_t l_Char_isAlphanum(uint32_t);
lean_object* l_Char_toLower___boxed(lean_object*);
lean_object* l_Char_isDigit___boxed(lean_object*);
lean_object* l_Char_toNat___boxed(lean_object*);
uint32_t l_Char_Inhabited;
uint8_t l_Char_isLower(uint32_t);
lean_object* l_Char_decLt___boxed(lean_object*, lean_object*);
uint8_t l_Char_isAlpha(uint32_t);
lean_object* l_Char_HasLessEq;
uint32_t l_UInt32_land(uint32_t, uint32_t);
lean_object* l_Char_decLe___boxed(lean_object*, lean_object*);
lean_object* l_Char_DecidableEq___boxed(lean_object*, lean_object*);
lean_object* l_Char_HasLess;
lean_object* l_Char_toNat(uint32_t);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
uint32_t l_Char_ofNat(lean_object*);
uint8_t l_Char_isUpper(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_UInt32_decLt(uint32_t, uint32_t);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
uint8_t l_Char_isDigit(uint32_t);
uint8_t l_Char_decLe(uint32_t, uint32_t);
uint8_t l_Char_lt(uint32_t, uint32_t);
uint8_t l_Char_decLt(uint32_t, uint32_t);
lean_object* l_Char_utf8Size___boxed(lean_object*);
lean_object* l_Char_isAlpha___boxed(lean_object*);
lean_object* l_Char_lt___boxed(lean_object*, lean_object*);
uint8_t l_Char_isWhitespace(uint32_t);
lean_object* l_Char_HasSizeof(uint32_t);
lean_object* l_Char_isAlphanum___boxed(lean_object*);
uint32_t l_Char_utf8Size(uint32_t);
uint32_t lean_uint32_of_nat(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t l_Char_toLower(uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Char_isLower___boxed(lean_object*);
lean_object* l_Char_HasSizeof___boxed(lean_object*);
uint8_t l_Char_DecidableEq(uint32_t, uint32_t);
lean_object* l_Char_isUpper___boxed(lean_object*);
lean_object* l_Char_ofNat___boxed(lean_object*);
lean_object* l_Char_HasSizeof(uint32_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uint32_to_nat(x_1);
return x_2;
}
}
lean_object* l_Char_HasSizeof___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_HasSizeof(x_2);
return x_3;
}
}
uint32_t l_Char_utf8Size(uint32_t x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; uint32_t x_4; uint32_t x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_2 = 1;
x_3 = 2;
x_4 = 4;
x_5 = 128;
x_6 = x_1 & x_5;
x_7 = 0;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint32_t x_11; uint32_t x_12; uint32_t x_13; uint8_t x_14; 
x_9 = 3;
x_10 = 224;
x_11 = x_1 & x_10;
x_12 = 6;
x_13 = 192;
x_14 = x_11 == x_13;
if (x_14 == 0)
{
uint32_t x_15; uint32_t x_16; uint8_t x_17; 
x_15 = 240;
x_16 = x_1 & x_15;
x_17 = x_16 == x_10;
if (x_17 == 0)
{
uint32_t x_18; uint32_t x_19; uint8_t x_20; 
x_18 = 248;
x_19 = x_1 & x_18;
x_20 = x_19 == x_15;
if (x_20 == 0)
{
uint32_t x_21; uint32_t x_22; uint8_t x_23; 
x_21 = 252;
x_22 = x_1 & x_21;
x_23 = x_22 == x_18;
if (x_23 == 0)
{
uint32_t x_24; uint32_t x_25; uint8_t x_26; 
x_24 = 254;
x_25 = x_1 & x_24;
x_26 = x_25 == x_21;
if (x_26 == 0)
{
uint32_t x_27; uint8_t x_28; 
x_27 = 255;
x_28 = x_1 == x_27;
if (x_28 == 0)
{
return x_7;
}
else
{
return x_2;
}
}
else
{
return x_12;
}
}
else
{
uint32_t x_29; 
x_29 = 5;
return x_29;
}
}
else
{
return x_4;
}
}
else
{
return x_9;
}
}
else
{
return x_3;
}
}
else
{
return x_2;
}
}
}
lean_object* l_Char_utf8Size___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_utf8Size(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
lean_object* _init_l_Char_HasLess() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_Char_HasLessEq() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
uint8_t l_Char_lt(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 < x_2;
return x_3;
}
}
lean_object* l_Char_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Char_lt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_Char_decLt(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 < x_2;
return x_3;
}
}
lean_object* l_Char_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Char_decLt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_Char_decLe(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 <= x_2;
return x_3;
}
}
lean_object* l_Char_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Char_decLe(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint32_t l_Char_ofNat(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; uint8_t x_4; 
x_2 = lean_uint32_of_nat(x_1);
x_3 = 55296;
x_4 = x_2 < x_3;
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 57343;
x_6 = x_5 < x_2;
if (x_6 == 0)
{
uint32_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint32_t x_8; uint8_t x_9; 
x_8 = 1114112;
x_9 = x_2 < x_8;
if (x_9 == 0)
{
uint32_t x_10; 
x_10 = 0;
return x_10;
}
else
{
return x_2;
}
}
}
else
{
return x_2;
}
}
}
lean_object* l_Char_ofNat___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Char_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
lean_object* l_Char_toNat(uint32_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uint32_to_nat(x_1);
return x_2;
}
}
lean_object* l_Char_toNat___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_toNat(x_2);
return x_3;
}
}
uint8_t l_Char_DecidableEq(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 == x_2;
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
}
lean_object* l_Char_DecidableEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Char_DecidableEq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint32_t _init_l_Char_Inhabited() {
_start:
{
uint32_t x_1; 
x_1 = 65;
return x_1;
}
}
uint8_t l_Char_isWhitespace(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 32;
x_3 = x_1 == x_2;
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 9;
x_5 = x_1 == x_4;
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 10;
x_7 = x_1 == x_6;
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
}
lean_object* l_Char_isWhitespace___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_isWhitespace(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Char_isUpper(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 65;
x_3 = x_2 <= x_1;
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint32_t x_5; uint8_t x_6; 
x_5 = 90;
x_6 = x_1 <= x_5;
return x_6;
}
}
}
lean_object* l_Char_isUpper___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_isUpper(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Char_isLower(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 97;
x_3 = x_2 <= x_1;
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint32_t x_5; uint8_t x_6; 
x_5 = 122;
x_6 = x_1 <= x_5;
return x_6;
}
}
}
lean_object* l_Char_isLower___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_isLower(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Char_isAlpha(uint32_t x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Char_isUpper(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Char_isLower(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
}
}
lean_object* l_Char_isAlpha___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_isAlpha(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Char_isDigit(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 48;
x_3 = x_2 <= x_1;
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint32_t x_5; uint8_t x_6; 
x_5 = 57;
x_6 = x_1 <= x_5;
return x_6;
}
}
}
lean_object* l_Char_isDigit___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_isDigit(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Char_isAlphanum(uint32_t x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Char_isAlpha(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Char_isDigit(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
}
}
lean_object* l_Char_isAlphanum___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_isAlphanum(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint32_t l_Char_toLower(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = lean_unsigned_to_nat(65u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(90u);
x_6 = lean_nat_dec_le(x_2, x_5);
if (x_6 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; uint32_t x_9; 
x_7 = lean_unsigned_to_nat(32u);
x_8 = lean_nat_add(x_2, x_7);
lean_dec(x_2);
x_9 = l_Char_ofNat(x_8);
lean_dec(x_8);
return x_9;
}
}
}
}
lean_object* l_Char_toLower___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_toLower(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_UInt(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Char_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Char_HasLess = _init_l_Char_HasLess();
lean_mark_persistent(l_Char_HasLess);
l_Char_HasLessEq = _init_l_Char_HasLessEq();
lean_mark_persistent(l_Char_HasLessEq);
l_Char_Inhabited = _init_l_Char_Inhabited();
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
