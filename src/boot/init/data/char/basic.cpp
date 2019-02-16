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
uint8 l_char_is__whitespace(uint32);
obj* l_char_is__upper___boxed(obj*);
uint8 l_char_is__lower(uint32);
namespace lean {
obj* nat_add(obj*, obj*);
}
uint32 l_char_to__lower(uint32);
obj* l_char_is__digit___boxed(obj*);
obj* l_char_dec__lt___boxed(obj*, obj*);
uint8 l_char_is__digit(uint32);
uint32 l_char_of__nat(obj*);
obj* l_char_has__lt;
obj* l_char_of__nat___boxed(obj*);
obj* l_char_is__alphanum___boxed(obj*);
uint8 l_char_is__upper(uint32);
uint8 l_char_is__alpha(uint32);
obj* l_char_to__lower___boxed(obj*);
obj* l_char_is__whitespace___boxed(obj*);
obj* l_char_to__nat___boxed(obj*);
obj* l_char_dec__le___boxed(obj*, obj*);
obj* l_char_has__sizeof___boxed(obj*);
obj* l_char_lt;
uint32 l_char_inhabited;
obj* l_char_has__sizeof(uint32);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
obj* uint32_to_nat(uint32);
}
uint8 l_char_dec__lt(uint32, uint32);
obj* l_char_is__lower___boxed(obj*);
obj* l_char_decidable__eq___boxed(obj*, obj*);
obj* l_char_inhabited___boxed;
uint8 l_char_dec__le(uint32, uint32);
obj* l_char_has__le;
uint8 l_char_is__alphanum(uint32);
obj* l_char_le;
uint8 l_char_decidable__eq(uint32, uint32);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_char_to__nat(uint32);
obj* l_is__valid__char;
obj* l_char_is__alpha___boxed(obj*);
obj* _init_l_is__valid__char() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_char_has__sizeof(uint32 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::uint32_to_nat(x_0);
return x_1;
}
}
obj* l_char_has__sizeof___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_has__sizeof(x_1);
return x_2;
}
}
obj* _init_l_char_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_char_le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_char_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_char_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint8 l_char_dec__lt(uint32 x_0, uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 < x_1;
return x_2;
}
}
obj* l_char_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_char_dec__lt(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_char_dec__le(uint32 x_0, uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 <= x_1;
return x_2;
}
}
obj* l_char_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_char_dec__le(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint32 l_char_of__nat(obj* x_0) {
_start:
{
uint32 x_1; uint32 x_3; uint8 x_4; 
x_1 = lean::uint32_of_nat(x_0);
lean::dec(x_0);
x_3 = 55296;
x_4 = x_1 < x_3;
if (x_4 == 0)
{
uint32 x_5; uint8 x_6; 
x_5 = 57343;
x_6 = x_5 < x_1;
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
x_9 = x_1 < x_8;
if (x_9 == 0)
{
uint32 x_10; 
x_10 = 0;
return x_10;
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
obj* l_char_of__nat___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = l_char_of__nat(x_0);
x_2 = lean::box_uint32(x_1);
return x_2;
}
}
obj* l_char_to__nat(uint32 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::uint32_to_nat(x_0);
return x_1;
}
}
obj* l_char_to__nat___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_to__nat(x_1);
return x_2;
}
}
uint8 l_char_decidable__eq(uint32 x_0, uint32 x_1) {
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
obj* l_char_decidable__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_char_decidable__eq(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint32 _init_l_char_inhabited() {
_start:
{
uint32 x_0; uint32 x_1; uint8 x_2; 
x_0 = 65;
x_1 = 55296;
x_2 = x_0 < x_1;
if (x_2 == 0)
{
uint32 x_3; uint8 x_4; 
x_3 = 57343;
x_4 = x_3 < x_0;
if (x_4 == 0)
{
uint32 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint32 x_6; uint8 x_7; 
x_6 = 1114112;
x_7 = x_0 < x_6;
if (x_7 == 0)
{
uint32 x_8; 
x_8 = 0;
return x_8;
}
else
{
return x_0;
}
}
}
else
{
return x_0;
}
}
}
obj* _init_l_char_inhabited___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_char_inhabited;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
uint8 l_char_is__whitespace(uint32 x_0) {
_start:
{
uint8 x_1; uint8 x_3; uint32 x_5; uint32 x_6; uint8 x_7; 
x_5 = 32;
x_6 = 55296;
x_7 = x_5 < x_6;
if (x_7 == 0)
{
uint32 x_8; uint8 x_9; 
x_8 = 57343;
x_9 = x_8 < x_5;
if (x_9 == 0)
{
uint32 x_10; uint8 x_11; 
x_10 = 0;
x_11 = x_0 == x_10;
if (x_11 == 0)
{
uint8 x_12; 
x_12 = 0;
x_3 = x_12;
goto lbl_4;
}
else
{
uint8 x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint32 x_14; uint8 x_15; 
x_14 = 1114112;
x_15 = x_5 < x_14;
if (x_15 == 0)
{
uint32 x_16; uint8 x_17; 
x_16 = 0;
x_17 = x_0 == x_16;
if (x_17 == 0)
{
uint8 x_18; 
x_18 = 0;
x_3 = x_18;
goto lbl_4;
}
else
{
uint8 x_19; 
x_19 = 1;
return x_19;
}
}
else
{
uint8 x_20; 
x_20 = x_0 == x_5;
if (x_20 == 0)
{
uint8 x_21; 
x_21 = 0;
x_3 = x_21;
goto lbl_4;
}
else
{
uint8 x_22; 
x_22 = 1;
return x_22;
}
}
}
}
else
{
uint8 x_23; 
x_23 = x_0 == x_5;
if (x_23 == 0)
{
uint8 x_24; 
x_24 = 0;
x_3 = x_24;
goto lbl_4;
}
else
{
uint8 x_25; 
x_25 = 1;
return x_25;
}
}
lbl_2:
{
uint32 x_26; uint32 x_27; uint8 x_28; 
x_26 = 10;
x_27 = 55296;
x_28 = x_26 < x_27;
if (x_28 == 0)
{
uint32 x_29; uint8 x_30; 
x_29 = 57343;
x_30 = x_29 < x_26;
if (x_30 == 0)
{
uint32 x_31; uint8 x_32; 
x_31 = 0;
x_32 = x_0 == x_31;
if (x_32 == 0)
{
return x_1;
}
else
{
uint8 x_33; 
x_33 = 1;
return x_33;
}
}
else
{
uint32 x_34; uint8 x_35; 
x_34 = 1114112;
x_35 = x_26 < x_34;
if (x_35 == 0)
{
uint32 x_36; uint8 x_37; 
x_36 = 0;
x_37 = x_0 == x_36;
if (x_37 == 0)
{
return x_1;
}
else
{
uint8 x_38; 
x_38 = 1;
return x_38;
}
}
else
{
uint8 x_39; 
x_39 = x_0 == x_26;
if (x_39 == 0)
{
return x_1;
}
else
{
uint8 x_40; 
x_40 = 1;
return x_40;
}
}
}
}
else
{
uint8 x_41; 
x_41 = x_0 == x_26;
if (x_41 == 0)
{
return x_1;
}
else
{
uint8 x_42; 
x_42 = 1;
return x_42;
}
}
}
lbl_4:
{
uint32 x_43; uint32 x_44; uint8 x_45; uint32 x_46; 
x_43 = 9;
x_44 = 55296;
x_45 = x_43 < x_44;
if (x_45 == 0)
{
uint32 x_48; uint8 x_49; 
x_48 = 57343;
x_49 = x_48 < x_43;
if (x_49 == 0)
{
uint32 x_50; 
x_50 = 0;
x_46 = x_50;
goto lbl_47;
}
else
{
uint32 x_51; uint8 x_52; 
x_51 = 1114112;
x_52 = x_43 < x_51;
if (x_52 == 0)
{
uint32 x_53; 
x_53 = 0;
x_46 = x_53;
goto lbl_47;
}
else
{
x_46 = x_43;
goto lbl_47;
}
}
}
else
{
x_46 = x_43;
goto lbl_47;
}
lbl_47:
{
uint8 x_54; 
x_54 = x_0 == x_46;
if (x_54 == 0)
{
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
else
{
uint8 x_55; 
x_55 = 1;
return x_55;
}
}
}
}
}
obj* l_char_is__whitespace___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_is__whitespace(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_char_is__upper(uint32 x_0) {
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
obj* l_char_is__upper___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_is__upper(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_char_is__lower(uint32 x_0) {
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
obj* l_char_is__lower___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_is__lower(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_char_is__alpha(uint32 x_0) {
_start:
{
uint8 x_1; 
x_1 = l_char_is__upper(x_0);
if (x_1 == 0)
{
uint8 x_2; 
x_2 = l_char_is__lower(x_0);
return x_2;
}
else
{
return x_1;
}
}
}
obj* l_char_is__alpha___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_is__alpha(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_char_is__digit(uint32 x_0) {
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
obj* l_char_is__digit___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_is__digit(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_char_is__alphanum(uint32 x_0) {
_start:
{
uint8 x_1; 
x_1 = l_char_is__alpha(x_0);
if (x_1 == 0)
{
uint8 x_2; 
x_2 = l_char_is__digit(x_0);
return x_2;
}
else
{
return x_1;
}
}
}
obj* l_char_is__alphanum___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_is__alphanum(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint32 l_char_to__lower(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; uint8 x_5; 
x_1 = lean::uint32_to_nat(x_0);
x_4 = lean::mk_nat_obj(65u);
x_5 = lean::nat_dec_le(x_4, x_1);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(90u);
x_9 = lean::nat_dec_le(x_1, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_12; 
x_12 = lean::box(0);
x_2 = x_12;
goto lbl_3;
}
}
lbl_3:
{
obj* x_14; obj* x_15; uint32 x_18; uint32 x_20; uint8 x_21; 
lean::dec(x_2);
x_14 = lean::mk_nat_obj(32u);
x_15 = lean::nat_add(x_1, x_14);
lean::dec(x_14);
lean::dec(x_1);
x_18 = lean::uint32_of_nat(x_15);
lean::dec(x_15);
x_20 = 55296;
x_21 = x_18 < x_20;
if (x_21 == 0)
{
uint32 x_22; uint8 x_23; 
x_22 = 57343;
x_23 = x_22 < x_18;
if (x_23 == 0)
{
uint32 x_24; 
x_24 = 0;
return x_24;
}
else
{
uint32 x_25; uint8 x_26; 
x_25 = 1114112;
x_26 = x_18 < x_25;
if (x_26 == 0)
{
uint32 x_27; 
x_27 = 0;
return x_27;
}
else
{
return x_18;
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
obj* l_char_to__lower___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint32 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_to__lower(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
void initialize_init_data_uint();
static bool _G_initialized = false;
void initialize_init_data_char_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_uint();
 l_is__valid__char = _init_l_is__valid__char();
 l_char_lt = _init_l_char_lt();
 l_char_le = _init_l_char_le();
 l_char_has__lt = _init_l_char_has__lt();
 l_char_has__le = _init_l_char_has__le();
 l_char_inhabited = _init_l_char_inhabited();
 l_char_inhabited___boxed = _init_l_char_inhabited___boxed();
}
