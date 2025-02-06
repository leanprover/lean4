// Lean compiler output
// Module: Init.Data.Char.Basic
// Imports: Init.Data.UInt.BasicAux
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
LEAN_EXPORT lean_object* l_Char_isDigit___boxed(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT uint32_t l_Char_ofUInt8(uint8_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint32_t lean_uint8_to_uint32(uint8_t);
LEAN_EXPORT lean_object* l_Char_isLower___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Char_isAlpha(uint32_t);
LEAN_EXPORT lean_object* l_Char_toUInt8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_isAlpha___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_toNat(uint32_t);
LEAN_EXPORT uint8_t l_Char_instDecidableLt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_toLower(uint32_t);
LEAN_EXPORT uint8_t l_Char_isAlphanum(uint32_t);
LEAN_EXPORT uint8_t l_Char_isWhitespace(uint32_t);
LEAN_EXPORT lean_object* l_Char_toUpper(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l_Char_toUInt8(uint32_t);
LEAN_EXPORT lean_object* l_Char_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_isWhitespace___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Char_instInhabited;
LEAN_EXPORT lean_object* l_Char_toLower___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_toUpper___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_ofUInt8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_instLE;
LEAN_EXPORT uint8_t l_Char_isDigit(uint32_t);
LEAN_EXPORT uint8_t l_Char_isUpper(uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Char_instDecidableLe(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_instDecidableLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_isUpper___boxed(lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_isAlphanum___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_instLT;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_instDecidableLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Char_isLower(uint32_t);
lean_object* l_Char_ofNat(lean_object*);
static lean_object* _init_l_Char_instLT() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Char_instLE() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Char_instDecidableLt(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint32_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Char_instDecidableLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Char_instDecidableLt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Char_instDecidableLe(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint32_dec_le(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Char_instDecidableLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Char_instDecidableLe(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Char_toNat(uint32_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uint32_to_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Char_toNat___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_toNat(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Char_toUInt8(uint32_t x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Char_toUInt8___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_toUInt8(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint32_t l_Char_ofUInt8(uint8_t x_1) {
_start:
{
uint32_t x_2; 
x_2 = lean_uint8_to_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Char_ofUInt8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Char_ofUInt8(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
static uint32_t _init_l_Char_instInhabited() {
_start:
{
uint32_t x_1; 
x_1 = 65;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Char_isWhitespace(uint32_t x_1) {
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
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 13;
x_7 = lean_uint32_dec_eq(x_1, x_6);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 10;
x_9 = lean_uint32_dec_eq(x_1, x_8);
return x_9;
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
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Char_isWhitespace___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Char_isUpper(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 65;
x_3 = lean_uint32_dec_le(x_2, x_1);
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
x_6 = lean_uint32_dec_le(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Char_isUpper___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Char_isLower(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 97;
x_3 = lean_uint32_dec_le(x_2, x_1);
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
x_6 = lean_uint32_dec_le(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Char_isLower___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Char_isAlpha(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 65;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 97;
x_5 = lean_uint32_dec_le(x_4, x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint32_t x_7; uint8_t x_8; 
x_7 = 122;
x_8 = lean_uint32_dec_le(x_1, x_7);
return x_8;
}
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = 90;
x_10 = lean_uint32_dec_le(x_1, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 97;
x_12 = lean_uint32_dec_le(x_11, x_1);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
uint32_t x_14; uint8_t x_15; 
x_14 = 122;
x_15 = lean_uint32_dec_le(x_1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isAlpha___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Char_isDigit(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 48;
x_3 = lean_uint32_dec_le(x_2, x_1);
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
x_6 = lean_uint32_dec_le(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Char_isDigit___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Char_isAlphanum(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_9; uint8_t x_10; 
x_9 = 65;
x_10 = lean_uint32_dec_le(x_9, x_1);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 97;
x_12 = lean_uint32_dec_le(x_11, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_box(0);
x_2 = x_13;
goto block_8;
}
else
{
uint32_t x_14; uint8_t x_15; 
x_14 = 122;
x_15 = lean_uint32_dec_le(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
x_2 = x_16;
goto block_8;
}
else
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
}
}
else
{
uint32_t x_18; uint8_t x_19; 
x_18 = 90;
x_19 = lean_uint32_dec_le(x_1, x_18);
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 97;
x_21 = lean_uint32_dec_le(x_20, x_1);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
x_2 = x_22;
goto block_8;
}
else
{
uint32_t x_23; uint8_t x_24; 
x_23 = 122;
x_24 = lean_uint32_dec_le(x_1, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_box(0);
x_2 = x_25;
goto block_8;
}
else
{
uint8_t x_26; 
x_26 = 1;
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = 1;
return x_27;
}
}
block_8:
{
uint32_t x_3; uint8_t x_4; 
lean_dec(x_2);
x_3 = 48;
x_4 = lean_uint32_dec_le(x_3, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint32_t x_6; uint8_t x_7; 
x_6 = 57;
x_7 = lean_uint32_dec_le(x_1, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isAlphanum___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Char_toLower(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = lean_unsigned_to_nat(65u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box_uint32(x_1);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(90u);
x_7 = lean_nat_dec_le(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_box_uint32(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(32u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_11 = l_Char_ofNat(x_10);
lean_dec(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_toLower___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_toLower(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Char_toUpper(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = lean_unsigned_to_nat(97u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box_uint32(x_1);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(122u);
x_7 = lean_nat_dec_le(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_box_uint32(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(32u);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_2);
x_11 = l_Char_ofNat(x_10);
lean_dec(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_toUpper___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_toUpper(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_UInt_BasicAux(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_BasicAux(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Char_instLT = _init_l_Char_instLT();
lean_mark_persistent(l_Char_instLT);
l_Char_instLE = _init_l_Char_instLE();
lean_mark_persistent(l_Char_instLE);
l_Char_instInhabited = _init_l_Char_instInhabited();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
