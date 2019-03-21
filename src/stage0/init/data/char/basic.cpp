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
obj* l_Char_utf8Size___closed__10___boxed;
uint8 l_Char_isLower(uint32);
obj* l_Char_isDigit___closed__1___boxed;
obj* l_Char_decLt___boxed(obj*, obj*);
uint8 l_Char_isAlpha(uint32);
uint32 l_Char_utf8Size___closed__10;
uint32 l_Char_isLower___closed__1;
obj* l_Char_HasLt;
uint32 l_Char_isUpper___closed__2;
obj* l_Char_utf8Size___closed__9___boxed;
obj* l_Char_isDigit___closed__2___boxed;
obj* l_Char_utf8Size___closed__2___boxed;
obj* l_Char_HasLe;
uint32 l_Char_isDigit___closed__1;
obj* l_Char_decLe___boxed(obj*, obj*);
uint32 l_Char_utf8Size___closed__3;
uint32 l_Char_isWhitespace___closed__2;
obj* l_Char_DecidableEq___boxed(obj*, obj*);
obj* l_Char_ofNat___closed__2___boxed;
uint32 l_Char_utf8Size___closed__9;
obj* l_Char_isWhitespace___closed__1___boxed;
uint32 l_Char_utf8Size___closed__4;
uint32 l_Char_ofNat___closed__1;
obj* l_Char_toNat(uint32);
obj* l_Char_isUpper___closed__2___boxed;
uint32 l_Char_isLower___closed__2;
obj* l_Char_isUpper___closed__1___boxed;
uint32 l_Char_ofNat(obj*);
uint8 l_Char_isUpper(uint32);
uint32 l_Char_isWhitespace___closed__1;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Char_isWhitespace___closed__3___boxed;
obj* l_Char_isLower___closed__2___boxed;
uint32 l_Char_isWhitespace___closed__3;
obj* l_Char_utf8Size___closed__1___boxed;
obj* l_Char_utf8Size___closed__3___boxed;
obj* l_Char_utf8Size___closed__7___boxed;
obj* l_Char_isWhitespace___boxed(obj*);
uint8 l_Char_isDigit(uint32);
uint8 l_Char_decLe(uint32, uint32);
uint8 l_Char_decLt(uint32, uint32);
obj* l_Char_utf8Size___boxed(obj*);
obj* l_Char_isAlpha___boxed(obj*);
obj* l_Char_ofNat___closed__3___boxed;
uint8 l_Char_isWhitespace(uint32);
obj* l_Char_HasSizeof(uint32);
obj* l_Char_utf8Size___closed__5___boxed;
obj* l_Char_isAlphanum___boxed(obj*);
obj* l_Char_utf8Size___closed__6___boxed;
uint32 l_Char_utf8Size___closed__8;
uint32 l_Char_ofNat___closed__3;
obj* l_Char_isLower___closed__1___boxed;
uint32 l_Char_utf8Size(uint32);
uint32 l_Char_isUpper___closed__1;
obj* l_Char_ofNat___closed__1___boxed;
uint32 l_Char_utf8Size___closed__6;
namespace lean {
uint32 uint32_of_nat(obj*);
}
uint32 l_Char_ofNat___closed__2;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
uint32 l_Char_utf8Size___closed__7;
uint32 l_Char_toLower(uint32);
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_Char_isLower___boxed(obj*);
obj* l_Char_utf8Size___closed__8___boxed;
obj* l_Char_HasSizeof___boxed(obj*);
uint32 l_Char_utf8Size___closed__5;
uint32 l_Char_isDigit___closed__2;
uint8 l_Char_DecidableEq(uint32, uint32);
obj* l_Char_isUpper___boxed(obj*);
uint32 l_Char_utf8Size___closed__2;
uint32 l_Char_utf8Size___closed__1;
obj* l_Char_ofNat___boxed(obj*);
obj* l_Char_Inhabited___boxed;
obj* l_Char_utf8Size___closed__4___boxed;
obj* l_Char_isWhitespace___closed__2___boxed;
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
uint32 _init_l_Char_utf8Size___closed__1() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_2;
x_4 = x_3 + x_3;
x_5 = x_4 + x_4;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_7;
return x_8;
}
}
uint32 _init_l_Char_utf8Size___closed__2() {
_start:
{
obj* x_0; uint32 x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::uint32_of_nat(x_0);
return x_1;
}
}
uint32 _init_l_Char_utf8Size___closed__3() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_7;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
return x_10;
}
}
uint32 _init_l_Char_utf8Size___closed__4() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_4;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_7;
x_9 = x_8 + x_8;
return x_9;
}
}
uint32 _init_l_Char_utf8Size___closed__5() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_1;
x_8 = x_7 + x_7;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_10;
return x_11;
}
}
uint32 _init_l_Char_utf8Size___closed__6() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_1;
x_8 = x_7 + x_7;
x_9 = x_8 + x_1;
x_10 = x_9 + x_9;
x_11 = x_10 + x_10;
x_12 = x_11 + x_11;
return x_12;
}
}
uint32 _init_l_Char_utf8Size___closed__7() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_1;
x_8 = x_7 + x_7;
x_9 = x_8 + x_1;
x_10 = x_9 + x_9;
x_11 = x_10 + x_1;
x_12 = x_11 + x_11;
x_13 = x_12 + x_12;
return x_13;
}
}
uint32 _init_l_Char_utf8Size___closed__8() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_1;
x_8 = x_7 + x_7;
x_9 = x_8 + x_1;
x_10 = x_9 + x_9;
x_11 = x_10 + x_1;
x_12 = x_11 + x_11;
x_13 = x_12 + x_1;
x_14 = x_13 + x_13;
return x_14;
}
}
uint32 _init_l_Char_utf8Size___closed__9() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_1;
x_8 = x_7 + x_7;
x_9 = x_8 + x_1;
x_10 = x_9 + x_9;
x_11 = x_10 + x_1;
x_12 = x_11 + x_11;
x_13 = x_12 + x_1;
x_14 = x_13 + x_13;
x_15 = x_14 + x_1;
return x_15;
}
}
uint32 _init_l_Char_utf8Size___closed__10() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_2;
x_4 = x_3 + x_1;
return x_4;
}
}
uint32 l_Char_utf8Size(uint32 x_0) {
_start:
{
obj* x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint8 x_6; 
x_1 = lean::mk_nat_obj(1u);
x_2 = lean::uint32_of_nat(x_1);
x_3 = l_Char_utf8Size___closed__1;
x_4 = x_0 & x_3;
x_5 = l_Char_utf8Size___closed__2;
x_6 = x_4 == x_5;
if (x_6 == 0)
{
uint32 x_7; uint32 x_8; obj* x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint8 x_14; 
x_7 = x_2 + x_2;
x_8 = x_7 + x_7;
x_9 = lean::mk_nat_obj(0u);
x_10 = lean::uint32_of_nat(x_9);
x_11 = l_Char_utf8Size___closed__3;
x_12 = x_0 & x_11;
x_13 = l_Char_utf8Size___closed__4;
x_14 = x_12 == x_13;
if (x_14 == 0)
{
uint32 x_15; uint32 x_16; uint32 x_17; uint32 x_18; uint8 x_19; 
x_15 = x_7 + x_2;
x_16 = x_15 + x_15;
x_17 = l_Char_utf8Size___closed__5;
x_18 = x_0 & x_17;
x_19 = x_18 == x_11;
if (x_19 == 0)
{
uint32 x_20; uint32 x_21; uint8 x_22; 
x_20 = l_Char_utf8Size___closed__6;
x_21 = x_0 & x_20;
x_22 = x_21 == x_17;
if (x_22 == 0)
{
uint32 x_23; uint32 x_24; uint8 x_25; 
x_23 = l_Char_utf8Size___closed__7;
x_24 = x_0 & x_23;
x_25 = x_24 == x_20;
if (x_25 == 0)
{
uint32 x_26; uint32 x_27; uint8 x_28; 
x_26 = l_Char_utf8Size___closed__8;
x_27 = x_0 & x_26;
x_28 = x_27 == x_23;
if (x_28 == 0)
{
uint32 x_29; uint8 x_30; 
x_29 = l_Char_utf8Size___closed__9;
x_30 = x_0 == x_29;
if (x_30 == 0)
{
return x_10;
}
else
{
return x_2;
}
}
else
{
return x_16;
}
}
else
{
uint32 x_31; 
x_31 = l_Char_utf8Size___closed__10;
return x_31;
}
}
else
{
return x_8;
}
}
else
{
return x_15;
}
}
else
{
return x_7;
}
}
else
{
return x_2;
}
}
}
obj* _init_l_Char_utf8Size___closed__1___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_utf8Size___closed__1;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_utf8Size___closed__2___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_utf8Size___closed__2;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_utf8Size___closed__3___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_utf8Size___closed__3;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_utf8Size___closed__4___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_utf8Size___closed__4;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_utf8Size___closed__5___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_utf8Size___closed__5;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_utf8Size___closed__6___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_utf8Size___closed__6;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_utf8Size___closed__7___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_utf8Size___closed__7;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_utf8Size___closed__8___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_utf8Size___closed__8;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_utf8Size___closed__9___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_utf8Size___closed__9;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_utf8Size___closed__10___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_utf8Size___closed__10;
x_1 = lean::box_uint32(x_0);
return x_1;
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
obj* _init_l_Char_HasLt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_Char_HasLe() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
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
uint32 _init_l_Char_ofNat___closed__1() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; uint32 x_18; uint32 x_19; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_4;
x_6 = x_5 + x_1;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_10;
x_12 = x_11 + x_11;
x_13 = x_12 + x_12;
x_14 = x_13 + x_13;
x_15 = x_14 + x_14;
x_16 = x_15 + x_15;
x_17 = x_16 + x_16;
x_18 = x_17 + x_17;
x_19 = x_18 + x_18;
return x_19;
}
}
uint32 _init_l_Char_ofNat___closed__2() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; uint32 x_18; uint32 x_19; uint32 x_20; uint32 x_21; uint32 x_22; uint32 x_23; uint32 x_24; uint32 x_25; uint32 x_26; uint32 x_27; uint32 x_28; uint32 x_29; uint32 x_30; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_4;
x_6 = x_5 + x_1;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
x_9 = x_8 + x_8;
x_10 = x_9 + x_1;
x_11 = x_10 + x_10;
x_12 = x_11 + x_1;
x_13 = x_12 + x_12;
x_14 = x_13 + x_1;
x_15 = x_14 + x_14;
x_16 = x_15 + x_1;
x_17 = x_16 + x_16;
x_18 = x_17 + x_1;
x_19 = x_18 + x_18;
x_20 = x_19 + x_1;
x_21 = x_20 + x_20;
x_22 = x_21 + x_1;
x_23 = x_22 + x_22;
x_24 = x_23 + x_1;
x_25 = x_24 + x_24;
x_26 = x_25 + x_1;
x_27 = x_26 + x_26;
x_28 = x_27 + x_1;
x_29 = x_28 + x_28;
x_30 = x_29 + x_1;
return x_30;
}
}
uint32 _init_l_Char_ofNat___closed__3() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; uint32 x_18; uint32 x_19; uint32 x_20; uint32 x_21; uint32 x_22; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_2;
x_4 = x_3 + x_3;
x_5 = x_4 + x_4;
x_6 = x_5 + x_1;
x_7 = x_6 + x_6;
x_8 = x_7 + x_7;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_10;
x_12 = x_11 + x_11;
x_13 = x_12 + x_12;
x_14 = x_13 + x_13;
x_15 = x_14 + x_14;
x_16 = x_15 + x_15;
x_17 = x_16 + x_16;
x_18 = x_17 + x_17;
x_19 = x_18 + x_18;
x_20 = x_19 + x_19;
x_21 = x_20 + x_20;
x_22 = x_21 + x_21;
return x_22;
}
}
uint32 l_Char_ofNat(obj* x_0) {
_start:
{
uint32 x_1; uint32 x_2; uint8 x_3; 
x_1 = lean::uint32_of_nat(x_0);
x_2 = l_Char_ofNat___closed__1;
x_3 = x_1 < x_2;
if (x_3 == 0)
{
uint32 x_4; uint8 x_5; 
x_4 = l_Char_ofNat___closed__2;
x_5 = x_4 < x_1;
if (x_5 == 0)
{
uint32 x_6; 
x_6 = l_Char_utf8Size___closed__2;
return x_6;
}
else
{
uint32 x_7; uint8 x_8; 
x_7 = l_Char_ofNat___closed__3;
x_8 = x_1 < x_7;
if (x_8 == 0)
{
uint32 x_9; 
x_9 = l_Char_utf8Size___closed__2;
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
obj* _init_l_Char_ofNat___closed__1___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_ofNat___closed__1;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_ofNat___closed__2___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_ofNat___closed__2;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_ofNat___closed__3___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_ofNat___closed__3;
x_1 = lean::box_uint32(x_0);
return x_1;
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
obj* x_0; uint32 x_1; 
x_0 = lean::mk_nat_obj(65u);
x_1 = l_Char_ofNat(x_0);
return x_1;
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
uint32 _init_l_Char_isWhitespace___closed__1() {
_start:
{
obj* x_0; uint32 x_1; 
x_0 = lean::mk_nat_obj(32u);
x_1 = l_Char_ofNat(x_0);
return x_1;
}
}
uint32 _init_l_Char_isWhitespace___closed__2() {
_start:
{
obj* x_0; uint32 x_1; 
x_0 = lean::mk_nat_obj(9u);
x_1 = l_Char_ofNat(x_0);
return x_1;
}
}
uint32 _init_l_Char_isWhitespace___closed__3() {
_start:
{
obj* x_0; uint32 x_1; 
x_0 = lean::mk_nat_obj(10u);
x_1 = l_Char_ofNat(x_0);
return x_1;
}
}
uint8 l_Char_isWhitespace(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = l_Char_isWhitespace___closed__1;
x_2 = x_0 == x_1;
if (x_2 == 0)
{
uint32 x_3; uint8 x_4; 
x_3 = l_Char_isWhitespace___closed__2;
x_4 = x_0 == x_3;
if (x_4 == 0)
{
uint32 x_5; uint8 x_6; 
x_5 = l_Char_isWhitespace___closed__3;
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
obj* _init_l_Char_isWhitespace___closed__1___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_isWhitespace___closed__1;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_isWhitespace___closed__2___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_isWhitespace___closed__2;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_isWhitespace___closed__3___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_isWhitespace___closed__3;
x_1 = lean::box_uint32(x_0);
return x_1;
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
uint32 _init_l_Char_isUpper___closed__1() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_2;
x_4 = x_3 + x_3;
x_5 = x_4 + x_4;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
return x_8;
}
}
uint32 _init_l_Char_isUpper___closed__2() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_2;
x_4 = x_3 + x_1;
x_5 = x_4 + x_4;
x_6 = x_5 + x_1;
x_7 = x_6 + x_6;
x_8 = x_7 + x_7;
x_9 = x_8 + x_1;
x_10 = x_9 + x_9;
return x_10;
}
}
uint8 l_Char_isUpper(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = l_Char_isUpper___closed__1;
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
x_4 = l_Char_isUpper___closed__2;
x_5 = x_0 <= x_4;
if (x_5 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* _init_l_Char_isUpper___closed__1___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_isUpper___closed__1;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_isUpper___closed__2___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_isUpper___closed__2;
x_1 = lean::box_uint32(x_0);
return x_1;
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
uint32 _init_l_Char_isLower___closed__1() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_4;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_7;
x_9 = x_8 + x_1;
return x_9;
}
}
uint32 _init_l_Char_isLower___closed__2() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_1;
x_8 = x_7 + x_7;
x_9 = x_8 + x_8;
x_10 = x_9 + x_1;
x_11 = x_10 + x_10;
return x_11;
}
}
uint8 l_Char_isLower(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = l_Char_isLower___closed__1;
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
x_4 = l_Char_isLower___closed__2;
x_5 = x_0 <= x_4;
if (x_5 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* _init_l_Char_isLower___closed__1___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_isLower___closed__1;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_isLower___closed__2___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_isLower___closed__2;
x_1 = lean::box_uint32(x_0);
return x_1;
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
return x_1;
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
uint32 _init_l_Char_isDigit___closed__1() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_4;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
return x_7;
}
}
uint32 _init_l_Char_isDigit___closed__2() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_7;
x_9 = x_8 + x_1;
return x_9;
}
}
uint8 l_Char_isDigit(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = l_Char_isDigit___closed__1;
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
x_4 = l_Char_isDigit___closed__2;
x_5 = x_0 <= x_4;
if (x_5 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* _init_l_Char_isDigit___closed__1___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_isDigit___closed__1;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Char_isDigit___closed__2___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Char_isDigit___closed__2;
x_1 = lean::box_uint32(x_0);
return x_1;
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
return x_1;
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
x_2 = lean::mk_nat_obj(65u);
x_3 = lean::nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(90u);
x_6 = lean::nat_dec_le(x_1, x_5);
if (x_6 == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_8; obj* x_9; uint32 x_11; 
x_8 = lean::mk_nat_obj(32u);
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
 l_Char_utf8Size___closed__1 = _init_l_Char_utf8Size___closed__1();
 l_Char_utf8Size___closed__2 = _init_l_Char_utf8Size___closed__2();
 l_Char_utf8Size___closed__3 = _init_l_Char_utf8Size___closed__3();
 l_Char_utf8Size___closed__4 = _init_l_Char_utf8Size___closed__4();
 l_Char_utf8Size___closed__5 = _init_l_Char_utf8Size___closed__5();
 l_Char_utf8Size___closed__6 = _init_l_Char_utf8Size___closed__6();
 l_Char_utf8Size___closed__7 = _init_l_Char_utf8Size___closed__7();
 l_Char_utf8Size___closed__8 = _init_l_Char_utf8Size___closed__8();
 l_Char_utf8Size___closed__9 = _init_l_Char_utf8Size___closed__9();
 l_Char_utf8Size___closed__10 = _init_l_Char_utf8Size___closed__10();
 l_Char_utf8Size___closed__1___boxed = _init_l_Char_utf8Size___closed__1___boxed();
lean::mark_persistent(l_Char_utf8Size___closed__1___boxed);
 l_Char_utf8Size___closed__2___boxed = _init_l_Char_utf8Size___closed__2___boxed();
lean::mark_persistent(l_Char_utf8Size___closed__2___boxed);
 l_Char_utf8Size___closed__3___boxed = _init_l_Char_utf8Size___closed__3___boxed();
lean::mark_persistent(l_Char_utf8Size___closed__3___boxed);
 l_Char_utf8Size___closed__4___boxed = _init_l_Char_utf8Size___closed__4___boxed();
lean::mark_persistent(l_Char_utf8Size___closed__4___boxed);
 l_Char_utf8Size___closed__5___boxed = _init_l_Char_utf8Size___closed__5___boxed();
lean::mark_persistent(l_Char_utf8Size___closed__5___boxed);
 l_Char_utf8Size___closed__6___boxed = _init_l_Char_utf8Size___closed__6___boxed();
lean::mark_persistent(l_Char_utf8Size___closed__6___boxed);
 l_Char_utf8Size___closed__7___boxed = _init_l_Char_utf8Size___closed__7___boxed();
lean::mark_persistent(l_Char_utf8Size___closed__7___boxed);
 l_Char_utf8Size___closed__8___boxed = _init_l_Char_utf8Size___closed__8___boxed();
lean::mark_persistent(l_Char_utf8Size___closed__8___boxed);
 l_Char_utf8Size___closed__9___boxed = _init_l_Char_utf8Size___closed__9___boxed();
lean::mark_persistent(l_Char_utf8Size___closed__9___boxed);
 l_Char_utf8Size___closed__10___boxed = _init_l_Char_utf8Size___closed__10___boxed();
lean::mark_persistent(l_Char_utf8Size___closed__10___boxed);
 l_Char_HasLt = _init_l_Char_HasLt();
lean::mark_persistent(l_Char_HasLt);
 l_Char_HasLe = _init_l_Char_HasLe();
lean::mark_persistent(l_Char_HasLe);
 l_Char_ofNat___closed__1 = _init_l_Char_ofNat___closed__1();
 l_Char_ofNat___closed__2 = _init_l_Char_ofNat___closed__2();
 l_Char_ofNat___closed__3 = _init_l_Char_ofNat___closed__3();
 l_Char_ofNat___closed__1___boxed = _init_l_Char_ofNat___closed__1___boxed();
lean::mark_persistent(l_Char_ofNat___closed__1___boxed);
 l_Char_ofNat___closed__2___boxed = _init_l_Char_ofNat___closed__2___boxed();
lean::mark_persistent(l_Char_ofNat___closed__2___boxed);
 l_Char_ofNat___closed__3___boxed = _init_l_Char_ofNat___closed__3___boxed();
lean::mark_persistent(l_Char_ofNat___closed__3___boxed);
 l_Char_Inhabited = _init_l_Char_Inhabited();
 l_Char_Inhabited___boxed = _init_l_Char_Inhabited___boxed();
lean::mark_persistent(l_Char_Inhabited___boxed);
 l_Char_isWhitespace___closed__1 = _init_l_Char_isWhitespace___closed__1();
 l_Char_isWhitespace___closed__2 = _init_l_Char_isWhitespace___closed__2();
 l_Char_isWhitespace___closed__3 = _init_l_Char_isWhitespace___closed__3();
 l_Char_isWhitespace___closed__1___boxed = _init_l_Char_isWhitespace___closed__1___boxed();
lean::mark_persistent(l_Char_isWhitespace___closed__1___boxed);
 l_Char_isWhitespace___closed__2___boxed = _init_l_Char_isWhitespace___closed__2___boxed();
lean::mark_persistent(l_Char_isWhitespace___closed__2___boxed);
 l_Char_isWhitespace___closed__3___boxed = _init_l_Char_isWhitespace___closed__3___boxed();
lean::mark_persistent(l_Char_isWhitespace___closed__3___boxed);
 l_Char_isUpper___closed__1 = _init_l_Char_isUpper___closed__1();
 l_Char_isUpper___closed__2 = _init_l_Char_isUpper___closed__2();
 l_Char_isUpper___closed__1___boxed = _init_l_Char_isUpper___closed__1___boxed();
lean::mark_persistent(l_Char_isUpper___closed__1___boxed);
 l_Char_isUpper___closed__2___boxed = _init_l_Char_isUpper___closed__2___boxed();
lean::mark_persistent(l_Char_isUpper___closed__2___boxed);
 l_Char_isLower___closed__1 = _init_l_Char_isLower___closed__1();
 l_Char_isLower___closed__2 = _init_l_Char_isLower___closed__2();
 l_Char_isLower___closed__1___boxed = _init_l_Char_isLower___closed__1___boxed();
lean::mark_persistent(l_Char_isLower___closed__1___boxed);
 l_Char_isLower___closed__2___boxed = _init_l_Char_isLower___closed__2___boxed();
lean::mark_persistent(l_Char_isLower___closed__2___boxed);
 l_Char_isDigit___closed__1 = _init_l_Char_isDigit___closed__1();
 l_Char_isDigit___closed__2 = _init_l_Char_isDigit___closed__2();
 l_Char_isDigit___closed__1___boxed = _init_l_Char_isDigit___closed__1___boxed();
lean::mark_persistent(l_Char_isDigit___closed__1___boxed);
 l_Char_isDigit___closed__2___boxed = _init_l_Char_isDigit___closed__2___boxed();
lean::mark_persistent(l_Char_isDigit___closed__2___boxed);
return w;
}
