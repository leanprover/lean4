// Lean compiler output
// Module: Init.Data.Char.Basic
// Imports: Init.Data.UInt
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
LEAN_EXPORT lean_object* l_Char_isAlpha___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Char_instDecidableLt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_toUpper(uint32_t);
LEAN_EXPORT uint8_t l_Char_isUpper(uint32_t);
LEAN_EXPORT uint8_t l_Char_isDigit(uint32_t);
LEAN_EXPORT lean_object* l_Char_instDecidableLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Char_isWhitespace(uint32_t);
LEAN_EXPORT lean_object* l_Char_toNat___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_toNat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_toLower___boxed(lean_object*);
uint8_t l_UInt32_decLt(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l_Char_isLower(uint32_t);
LEAN_EXPORT lean_object* l_Char_isAlphanum___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Char_instDecidableLe(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_isWhitespace___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Char_isAlpha(uint32_t);
LEAN_EXPORT lean_object* l_Char_instLEChar;
LEAN_EXPORT uint32_t l_Char_instInhabitedChar;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_instLTChar;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Char_isAlphanum(uint32_t);
LEAN_EXPORT lean_object* l_Char_toLower(uint32_t);
LEAN_EXPORT lean_object* l_Char_isLower___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_toUpper___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_isUpper___boxed(lean_object*);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_instDecidableLe___boxed(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Char_isDigit___boxed(lean_object*);
static lean_object* _init_l_Char_instLTChar() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Char_instLEChar() {
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
x_3 = x_1 < x_2;
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
x_3 = x_1 <= x_2;
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
static uint32_t _init_l_Char_instInhabitedChar() {
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
x_3 = x_1 == x_2;
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 9;
x_5 = x_1 == x_4;
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 13;
x_7 = x_1 == x_6;
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 10;
x_9 = x_1 == x_8;
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
lean_object* initialize_Init_Data_UInt(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Char_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Char_instLTChar = _init_l_Char_instLTChar();
lean_mark_persistent(l_Char_instLTChar);
l_Char_instLEChar = _init_l_Char_instLEChar();
lean_mark_persistent(l_Char_instLEChar);
l_Char_instInhabitedChar = _init_l_Char_instInhabitedChar();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
