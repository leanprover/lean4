// Lean compiler output
// Module: Init.Data.Char.Basic
// Imports: public import Init.Data.UInt.BasicAux
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
LEAN_EXPORT uint32_t l_Char_toLower(uint32_t);
LEAN_EXPORT uint8_t l_Char_isAlphanum(uint32_t);
LEAN_EXPORT uint8_t l_Char_isWhitespace(uint32_t);
LEAN_EXPORT uint32_t l_Char_toUpper(uint32_t);
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
LEAN_EXPORT uint8_t l_Char_instDecidableLe(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_instDecidableLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_isUpper___boxed(lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_isAlphanum___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_instLT;
LEAN_EXPORT lean_object* l_Char_instDecidableLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Char_isLower(uint32_t);
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
uint8_t x_2; uint32_t x_8; uint8_t x_9; 
x_8 = 32;
x_9 = lean_uint32_dec_eq(x_1, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 9;
x_11 = lean_uint32_dec_eq(x_1, x_10);
x_2 = x_11;
goto block_7;
}
else
{
x_2 = x_9;
goto block_7;
}
block_7:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 13;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 10;
x_6 = lean_uint32_dec_eq(x_1, x_5);
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
return x_3;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 90;
x_5 = lean_uint32_dec_le(x_1, x_4);
return x_5;
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
uint32_t x_7; uint8_t x_8; 
x_7 = 65;
x_8 = lean_uint32_dec_le(x_7, x_1);
if (x_8 == 0)
{
goto block_6;
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = 90;
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
return x_3;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 57;
x_5 = lean_uint32_dec_le(x_1, x_4);
return x_5;
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
uint8_t x_2; uint32_t x_13; uint8_t x_14; 
x_13 = 65;
x_14 = lean_uint32_dec_le(x_13, x_1);
if (x_14 == 0)
{
goto block_12;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 90;
x_16 = lean_uint32_dec_le(x_1, x_15);
if (x_16 == 0)
{
goto block_12;
}
else
{
return x_16;
}
}
block_7:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 48;
x_4 = lean_uint32_dec_le(x_3, x_1);
if (x_4 == 0)
{
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
LEAN_EXPORT uint32_t l_Char_toLower(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 65;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_1;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 90;
x_5 = lean_uint32_dec_le(x_1, x_4);
if (x_5 == 0)
{
return x_1;
}
else
{
uint32_t x_6; uint32_t x_7; 
x_6 = 32;
x_7 = lean_uint32_add(x_1, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_toLower___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint32_t l_Char_toUpper(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 97;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_1;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 122;
x_5 = lean_uint32_dec_le(x_1, x_4);
if (x_5 == 0)
{
return x_1;
}
else
{
uint32_t x_6; uint32_t x_7; 
x_6 = 4294967264;
x_7 = lean_uint32_add(x_1, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_toUpper___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_toUpper(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_BasicAux(builtin);
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
