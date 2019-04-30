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
obj* l_Char_decLe___boxed(obj*, obj*);
obj* l_Char_DecidableEq___boxed(obj*, obj*);
obj* l_Char_HasLess;
obj* l_Char_toNat(uint32);
uint32 l_Char_ofNat(obj*);
uint8 l_Char_isUpper(uint32);
namespace lean {
obj* nat_add(obj*, obj*);
}
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
obj* l_Char_Inhabited___boxed;
obj* l_Char_HasSizeof(uint32 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::uint32_to_nat(x_0);
return x_1;
}
}
obj* l_Char_HasSizeof___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Char_HasSizeof(x_1);
return x_2;
}
}
uint32 l_Char_utf8Size(uint32 x_0) {
_start:
{
uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint8 x_7; 
x_1 = 1;
x_2 = 2;
x_3 = 4;
x_4 = 128;
x_5 = x_0 & x_4;
x_6 = 0;
x_7 = x_5 == x_6;
if (x_7 == 0)
{
uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint8 x_13; 
x_8 = 3;
x_9 = 224;
x_10 = x_0 & x_9;
x_11 = 6;
x_12 = 192;
x_13 = x_10 == x_12;
if (x_13 == 0)
{
uint32 x_14; uint32 x_15; uint8 x_16; 
x_14 = 240;
x_15 = x_0 & x_14;
x_16 = x_15 == x_9;
if (x_16 == 0)
{
uint32 x_17; uint32 x_18; uint8 x_19; 
x_17 = 248;
x_18 = x_0 & x_17;
x_19 = x_18 == x_14;
if (x_19 == 0)
{
uint32 x_20; uint32 x_21; uint8 x_22; 
x_20 = 252;
x_21 = x_0 & x_20;
x_22 = x_21 == x_17;
if (x_22 == 0)
{
uint32 x_23; uint32 x_24; uint8 x_25; 
x_23 = 254;
x_24 = x_0 & x_23;
x_25 = x_24 == x_20;
if (x_25 == 0)
{
uint32 x_26; uint8 x_27; 
x_26 = 255;
x_27 = x_0 == x_26;
if (x_27 == 0)
{
return x_6;
}
else
{
return x_1;
}
}
else
{
return x_11;
}
}
else
{
uint32 x_28; 
x_28 = 5;
return x_28;
}
}
else
{
return x_3;
}
}
else
{
return x_8;
}
}
else
{
return x_2;
}
}
else
{
return x_1;
}
}
}
obj* l_Char_utf8Size___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint32 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Char_utf8Size(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
obj* _init_l_Char_HasLess() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_Char_HasLessEq() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint8 l_Char_lt(uint32 x_0, uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 < x_1;
return x_2;
}
}
obj* l_Char_lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_Char_lt(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_Char_decLt(uint32 x_0, uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 < x_1;
return x_2;
}
}
obj* l_Char_decLt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_Char_decLt(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_Char_decLe(uint32 x_0, uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 <= x_1;
return x_2;
}
}
obj* l_Char_decLe___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_Char_decLe(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint32 l_Char_ofNat(obj* x_0) {
_start:
{
uint32 x_1; uint32 x_2; uint8 x_3; 
x_1 = lean::uint32_of_nat(x_0);
x_2 = 55296;
x_3 = x_1 < x_2;
if (x_3 == 0)
{
uint32 x_4; uint8 x_5; 
x_4 = 57343;
x_5 = x_4 < x_1;
if (x_5 == 0)
{
uint32 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint32 x_7; uint8 x_8; 
x_7 = 1114112;
x_8 = x_1 < x_7;
if (x_8 == 0)
{
uint32 x_9; 
x_9 = 0;
return x_9;
}
else
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
obj* l_Char_ofNat___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = l_Char_ofNat(x_0);
x_2 = lean::box_uint32(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Char_toNat(uint32 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::uint32_to_nat(x_0);
return x_1;
}
}
obj* l_Char_toNat___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Char_toNat(x_1);
return x_2;
}
}
uint8 l_Char_DecidableEq(uint32 x_0, uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 == x_1;
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
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
obj* l_Char_DecidableEq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_Char_DecidableEq(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint32 _init_l_Char_Inhabited() {
_start:
{
uint32 x_0; 
x_0 = 65;
return x_0;
}
}
obj* _init_l_Char_Inhabited___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_Inhabited;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
uint8 l_Char_isWhitespace(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = 32;
x_2 = x_0 == x_1;
if (x_2 == 0)
{
uint32 x_3; uint8 x_4; 
x_3 = 9;
x_4 = x_0 == x_3;
if (x_4 == 0)
{
uint32 x_5; uint8 x_6; 
x_5 = 10;
x_6 = x_0 == x_5;
if (x_6 == 0)
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
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
}
obj* l_Char_isWhitespace___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Char_isWhitespace(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Char_isUpper(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = 65;
x_2 = x_1 <= x_0;
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint32 x_4; uint8 x_5; 
x_4 = 90;
x_5 = x_0 <= x_4;
return x_5;
}
}
}
obj* l_Char_isUpper___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Char_isUpper(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Char_isLower(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = 97;
x_2 = x_1 <= x_0;
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint32 x_4; uint8 x_5; 
x_4 = 122;
x_5 = x_0 <= x_4;
return x_5;
}
}
}
obj* l_Char_isLower___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Char_isLower(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Char_isAlpha(uint32 x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Char_isUpper(x_0);
if (x_1 == 0)
{
uint8 x_2; 
x_2 = l_Char_isLower(x_0);
return x_2;
}
else
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
}
}
obj* l_Char_isAlpha___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Char_isAlpha(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Char_isDigit(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = 48;
x_2 = x_1 <= x_0;
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint32 x_4; uint8 x_5; 
x_4 = 57;
x_5 = x_0 <= x_4;
return x_5;
}
}
}
obj* l_Char_isDigit___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Char_isDigit(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Char_isAlphanum(uint32 x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Char_isAlpha(x_0);
if (x_1 == 0)
{
uint8 x_2; 
x_2 = l_Char_isDigit(x_0);
return x_2;
}
else
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
}
}
obj* l_Char_isAlphanum___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Char_isAlphanum(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint32 l_Char_toLower(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::uint32_to_nat(x_0);
x_2 = lean::mk_nat_obj(65ul);
x_3 = lean::nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(90ul);
x_6 = lean::nat_dec_le(x_1, x_5);
if (x_6 == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_8; obj* x_9; uint32 x_11; 
x_8 = lean::mk_nat_obj(32ul);
x_9 = lean::nat_add(x_1, x_8);
lean::dec(x_1);
x_11 = l_Char_ofNat(x_9);
lean::dec(x_9);
return x_11;
}
}
}
}
obj* l_Char_toLower___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint32 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Char_toLower(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
obj* initialize_init_data_uint(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_char_basic(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (io_result_is_error(w)) return w;
 l_Char_HasLess = _init_l_Char_HasLess();
lean::mark_persistent(l_Char_HasLess);
 l_Char_HasLessEq = _init_l_Char_HasLessEq();
lean::mark_persistent(l_Char_HasLessEq);
 l_Char_Inhabited = _init_l_Char_Inhabited();
 l_Char_Inhabited___boxed = _init_l_Char_Inhabited___boxed();
lean::mark_persistent(l_Char_Inhabited___boxed);
return w;
}
