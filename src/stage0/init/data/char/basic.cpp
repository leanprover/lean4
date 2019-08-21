// Lean compiler output
// Module: init.data.char.basic
// Imports: init.data.uint
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
uint8 l_Char_isAlphanum(uint32);
obj* l_Char_toLower___boxed(obj*);
obj* l_Char_isDigit___boxed(obj*);
obj* l_Char_toNat___boxed(obj*);
uint32 l_Char_Inhabited;
uint8 l_Char_isLower(uint32);
obj* l_Char_decLt___boxed(obj*, obj*);
uint8 l_Char_isAlpha(uint32);
obj* l_Char_HasLessEq;
uint32 l_UInt32_land(uint32, uint32);
obj* l_Char_decLe___boxed(obj*, obj*);
obj* l_Char_DecidableEq___boxed(obj*, obj*);
obj* l_Char_HasLess;
obj* l_Char_toNat(uint32);
uint8 l_UInt32_decLe(uint32, uint32);
uint32 l_Char_ofNat(obj*);
uint8 l_Char_isUpper(uint32);
namespace lean {
obj* nat_add(obj*, obj*);
}
uint8 l_UInt32_decLt(uint32, uint32);
uint8 l_UInt32_decEq(uint32, uint32);
obj* l_Char_isWhitespace___boxed(obj*);
uint8 l_Char_isDigit(uint32);
uint8 l_Char_decLe(uint32, uint32);
uint8 l_Char_lt(uint32, uint32);
uint8 l_Char_decLt(uint32, uint32);
obj* l_Char_utf8Size___boxed(obj*);
obj* l_Char_isAlpha___boxed(obj*);
obj* l_Char_lt___boxed(obj*, obj*);
uint8 l_Char_isWhitespace(uint32);
obj* l_Char_HasSizeof(uint32);
obj* l_Char_isAlphanum___boxed(obj*);
uint32 l_Char_utf8Size(uint32);
namespace lean {
uint32 uint32_of_nat(obj*);
}
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
uint32 l_Char_toLower(uint32);
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_Char_isLower___boxed(obj*);
obj* l_Char_HasSizeof___boxed(obj*);
uint8 l_Char_DecidableEq(uint32, uint32);
obj* l_Char_isUpper___boxed(obj*);
obj* l_Char_ofNat___boxed(obj*);
obj* l_Char_HasSizeof(uint32 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::uint32_to_nat(x_1);
return x_2;
}
}
obj* l_Char_HasSizeof___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_HasSizeof(x_2);
return x_3;
}
}
uint32 l_Char_utf8Size(uint32 x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint8 x_8; 
x_2 = 1;
x_3 = 2;
x_4 = 4;
x_5 = 128;
x_6 = x_1 & x_5;
x_7 = 0;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint8 x_14; 
x_9 = 3;
x_10 = 224;
x_11 = x_1 & x_10;
x_12 = 6;
x_13 = 192;
x_14 = x_11 == x_13;
if (x_14 == 0)
{
uint32 x_15; uint32 x_16; uint8 x_17; 
x_15 = 240;
x_16 = x_1 & x_15;
x_17 = x_16 == x_10;
if (x_17 == 0)
{
uint32 x_18; uint32 x_19; uint8 x_20; 
x_18 = 248;
x_19 = x_1 & x_18;
x_20 = x_19 == x_15;
if (x_20 == 0)
{
uint32 x_21; uint32 x_22; uint8 x_23; 
x_21 = 252;
x_22 = x_1 & x_21;
x_23 = x_22 == x_18;
if (x_23 == 0)
{
uint32 x_24; uint32 x_25; uint8 x_26; 
x_24 = 254;
x_25 = x_1 & x_24;
x_26 = x_25 == x_21;
if (x_26 == 0)
{
uint32 x_27; uint8 x_28; 
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
uint32 x_29; 
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
obj* l_Char_utf8Size___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_utf8Size(x_2);
x_4 = lean::box_uint32(x_3);
return x_4;
}
}
obj* _init_l_Char_HasLess() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* _init_l_Char_HasLessEq() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
uint8 l_Char_lt(uint32 x_1, uint32 x_2) {
_start:
{
uint8 x_3; 
x_3 = x_1 < x_2;
return x_3;
}
}
obj* l_Char_lt___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; uint32 x_4; uint8 x_5; obj* x_6; 
x_3 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_4 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_5 = l_Char_lt(x_3, x_4);
x_6 = lean::box(x_5);
return x_6;
}
}
uint8 l_Char_decLt(uint32 x_1, uint32 x_2) {
_start:
{
uint8 x_3; 
x_3 = x_1 < x_2;
return x_3;
}
}
obj* l_Char_decLt___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; uint32 x_4; uint8 x_5; obj* x_6; 
x_3 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_4 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_5 = l_Char_decLt(x_3, x_4);
x_6 = lean::box(x_5);
return x_6;
}
}
uint8 l_Char_decLe(uint32 x_1, uint32 x_2) {
_start:
{
uint8 x_3; 
x_3 = x_1 <= x_2;
return x_3;
}
}
obj* l_Char_decLe___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; uint32 x_4; uint8 x_5; obj* x_6; 
x_3 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_4 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_5 = l_Char_decLe(x_3, x_4);
x_6 = lean::box(x_5);
return x_6;
}
}
uint32 l_Char_ofNat(obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; 
x_2 = lean::uint32_of_nat(x_1);
x_3 = 55296;
x_4 = x_2 < x_3;
if (x_4 == 0)
{
uint32 x_5; uint8 x_6; 
x_5 = 57343;
x_6 = x_5 < x_2;
if (x_6 == 0)
{
uint32 x_7; 
x_7 = 0;
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = 1114112;
x_9 = x_2 < x_8;
if (x_9 == 0)
{
uint32 x_10; 
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
obj* l_Char_ofNat___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = l_Char_ofNat(x_1);
lean::dec(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
obj* l_Char_toNat(uint32 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::uint32_to_nat(x_1);
return x_2;
}
}
obj* l_Char_toNat___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_toNat(x_2);
return x_3;
}
}
uint8 l_Char_DecidableEq(uint32 x_1, uint32 x_2) {
_start:
{
uint8 x_3; 
x_3 = x_1 == x_2;
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
}
}
obj* l_Char_DecidableEq___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; uint32 x_4; uint8 x_5; obj* x_6; 
x_3 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_4 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_5 = l_Char_DecidableEq(x_3, x_4);
x_6 = lean::box(x_5);
return x_6;
}
}
uint32 _init_l_Char_Inhabited() {
_start:
{
uint32 x_1; 
x_1 = 65;
return x_1;
}
}
uint8 l_Char_isWhitespace(uint32 x_1) {
_start:
{
uint32 x_2; uint8 x_3; 
x_2 = 32;
x_3 = x_1 == x_2;
if (x_3 == 0)
{
uint32 x_4; uint8 x_5; 
x_4 = 9;
x_5 = x_1 == x_4;
if (x_5 == 0)
{
uint32 x_6; uint8 x_7; 
x_6 = 10;
x_7 = x_1 == x_6;
if (x_7 == 0)
{
uint8 x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
else
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8 x_11; 
x_11 = 1;
return x_11;
}
}
}
obj* l_Char_isWhitespace___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_isWhitespace(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Char_isUpper(uint32 x_1) {
_start:
{
uint32 x_2; uint8 x_3; 
x_2 = 65;
x_3 = x_2 <= x_1;
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint32 x_5; uint8 x_6; 
x_5 = 90;
x_6 = x_1 <= x_5;
return x_6;
}
}
}
obj* l_Char_isUpper___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_isUpper(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Char_isLower(uint32 x_1) {
_start:
{
uint32 x_2; uint8 x_3; 
x_2 = 97;
x_3 = x_2 <= x_1;
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint32 x_5; uint8 x_6; 
x_5 = 122;
x_6 = x_1 <= x_5;
return x_6;
}
}
}
obj* l_Char_isLower___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_isLower(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Char_isAlpha(uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Char_isUpper(x_1);
if (x_2 == 0)
{
uint8 x_3; 
x_3 = l_Char_isLower(x_1);
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
obj* l_Char_isAlpha___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_isAlpha(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Char_isDigit(uint32 x_1) {
_start:
{
uint32 x_2; uint8 x_3; 
x_2 = 48;
x_3 = x_2 <= x_1;
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint32 x_5; uint8 x_6; 
x_5 = 57;
x_6 = x_1 <= x_5;
return x_6;
}
}
}
obj* l_Char_isDigit___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_isDigit(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Char_isAlphanum(uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Char_isAlpha(x_1);
if (x_2 == 0)
{
uint8 x_3; 
x_3 = l_Char_isDigit(x_1);
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
obj* l_Char_isAlphanum___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_isAlphanum(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint32 l_Char_toLower(uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::uint32_to_nat(x_1);
x_3 = lean::mk_nat_obj(65u);
x_4 = lean::nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(90u);
x_6 = lean::nat_dec_le(x_2, x_5);
if (x_6 == 0)
{
lean::dec(x_2);
return x_1;
}
else
{
obj* x_7; obj* x_8; uint32 x_9; 
x_7 = lean::mk_nat_obj(32u);
x_8 = lean::nat_add(x_2, x_7);
lean::dec(x_2);
x_9 = l_Char_ofNat(x_8);
lean::dec(x_8);
return x_9;
}
}
}
}
obj* l_Char_toLower___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_toLower(x_2);
x_4 = lean::box_uint32(x_3);
return x_4;
}
}
obj* initialize_init_data_uint(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_char_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (lean::io_result_is_error(w)) return w;
l_Char_HasLess = _init_l_Char_HasLess();
lean::mark_persistent(l_Char_HasLess);
l_Char_HasLessEq = _init_l_Char_HasLessEq();
lean::mark_persistent(l_Char_HasLessEq);
l_Char_Inhabited = _init_l_Char_Inhabited();
return w;
}
