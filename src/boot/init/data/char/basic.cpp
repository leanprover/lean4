// Lean compiler output
// Module: init.data.char.basic
// Imports: init.data.nat.basic
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
obj* l_char_to__lower(uint32);
obj* l_char_is__digit___boxed(obj*);
obj* l_char_dec__lt___boxed(obj*, obj*);
uint8 l_char_is__digit(uint32);
obj* l_char_of__nat(obj*);
obj* l_char_has__lt;
obj* l_char_is__alphanum___boxed(obj*);
uint8 l_char_is__upper(uint32);
uint8 l_char_is__alpha(uint32);
obj* l_char_to__lower___boxed(obj*);
obj* l_char_is__whitespace___boxed(obj*);
obj* l_char_to__nat___boxed(obj*);
obj* l_char_dec__le___boxed(obj*, obj*);
obj* l_char_has__sizeof___boxed(obj*);
obj* l_char_lt;
obj* l_char_inhabited;
uint32 l_char_has__sizeof(uint32);
uint8 l_char_dec__lt(uint32, uint32);
obj* l_char_is__lower___boxed(obj*);
obj* l_char_decidable__eq___boxed(obj*, obj*);
uint8 l_char_dec__le(uint32, uint32);
obj* l_char_has__le;
uint8 l_char_is__alphanum(uint32);
obj* l_char_le;
uint8 l_char_decidable__eq(uint32, uint32);
uint32 l_char_to__nat(uint32);
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
uint32 l_char_has__sizeof(uint32 x_0) {
_start:
{
return x_0;
}
}
obj* l_char_has__sizeof___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint32 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_has__sizeof(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
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
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::box_uint32(x_0);
x_3 = lean::box_uint32(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
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
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::box_uint32(x_0);
x_3 = lean::box_uint32(x_1);
x_4 = lean::nat_dec_le(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
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
obj* l_char_of__nat(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
if (x_2 == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(57343u);
x_5 = lean::nat_dec_lt(x_4, x_0);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = lean::mk_nat_obj(0u);
return x_8;
}
else
{
obj* x_9; uint8 x_10; 
x_9 = lean::mk_nat_obj(1114112u);
x_10 = lean::nat_dec_lt(x_0, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = lean::mk_nat_obj(0u);
return x_13;
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
uint32 l_char_to__nat(uint32 x_0) {
_start:
{
return x_0;
}
}
obj* l_char_to__nat___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint32 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_to__nat(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
uint8 l_char_decidable__eq(uint32 x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::box_uint32(x_0);
x_3 = lean::box_uint32(x_1);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
if (x_4 == 0)
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
obj* _init_l_char_inhabited() {
_start:
{
obj* x_0; obj* x_1; uint8 x_2; 
x_0 = lean::mk_nat_obj(65u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
if (x_2 == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(57343u);
x_5 = lean::nat_dec_lt(x_4, x_0);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = lean::mk_nat_obj(0u);
return x_8;
}
else
{
obj* x_9; uint8 x_10; 
x_9 = lean::mk_nat_obj(1114112u);
x_10 = lean::nat_dec_lt(x_0, x_9);
lean::dec(x_9);
lean::dec(x_0);
if (x_10 == 0)
{
obj* x_13; 
x_13 = lean::mk_nat_obj(0u);
return x_13;
}
else
{
obj* x_14; 
x_14 = lean::mk_nat_obj(65u);
return x_14;
}
}
}
else
{
obj* x_16; 
lean::dec(x_0);
x_16 = lean::mk_nat_obj(65u);
return x_16;
}
}
}
uint8 l_char_is__whitespace(uint32 x_0) {
_start:
{
uint8 x_1; uint8 x_3; obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::mk_nat_obj(32u);
x_6 = lean::mk_nat_obj(55296u);
x_7 = lean::nat_dec_lt(x_5, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = lean::mk_nat_obj(57343u);
x_10 = lean::nat_dec_lt(x_9, x_5);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_13; obj* x_14; uint8 x_15; 
lean::dec(x_5);
x_13 = lean::mk_nat_obj(0u);
x_14 = lean::box_uint32(x_0);
x_15 = lean::nat_dec_eq(x_14, x_13);
lean::dec(x_13);
lean::dec(x_14);
if (x_15 == 0)
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
obj* x_20; uint8 x_21; 
x_20 = lean::mk_nat_obj(1114112u);
x_21 = lean::nat_dec_lt(x_5, x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_24; obj* x_25; uint8 x_26; 
lean::dec(x_5);
x_24 = lean::mk_nat_obj(0u);
x_25 = lean::box_uint32(x_0);
x_26 = lean::nat_dec_eq(x_25, x_24);
lean::dec(x_24);
lean::dec(x_25);
if (x_26 == 0)
{
uint8 x_29; 
x_29 = 0;
x_3 = x_29;
goto lbl_4;
}
else
{
uint8 x_30; 
x_30 = 1;
return x_30;
}
}
else
{
obj* x_31; uint8 x_32; 
x_31 = lean::box_uint32(x_0);
x_32 = lean::nat_dec_eq(x_31, x_5);
lean::dec(x_5);
lean::dec(x_31);
if (x_32 == 0)
{
uint8 x_35; 
x_35 = 0;
x_3 = x_35;
goto lbl_4;
}
else
{
uint8 x_36; 
x_36 = 1;
return x_36;
}
}
}
}
else
{
obj* x_37; uint8 x_38; 
x_37 = lean::box_uint32(x_0);
x_38 = lean::nat_dec_eq(x_37, x_5);
lean::dec(x_5);
lean::dec(x_37);
if (x_38 == 0)
{
uint8 x_41; 
x_41 = 0;
x_3 = x_41;
goto lbl_4;
}
else
{
uint8 x_42; 
x_42 = 1;
return x_42;
}
}
lbl_2:
{
obj* x_43; obj* x_44; uint8 x_45; 
x_43 = lean::mk_nat_obj(10u);
x_44 = lean::mk_nat_obj(55296u);
x_45 = lean::nat_dec_lt(x_43, x_44);
lean::dec(x_44);
if (x_45 == 0)
{
obj* x_47; uint8 x_48; 
x_47 = lean::mk_nat_obj(57343u);
x_48 = lean::nat_dec_lt(x_47, x_43);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_51; obj* x_52; uint8 x_53; 
lean::dec(x_43);
x_51 = lean::mk_nat_obj(0u);
x_52 = lean::box_uint32(x_0);
x_53 = lean::nat_dec_eq(x_52, x_51);
lean::dec(x_51);
lean::dec(x_52);
if (x_53 == 0)
{
return x_1;
}
else
{
uint8 x_56; 
x_56 = 1;
return x_56;
}
}
else
{
obj* x_57; uint8 x_58; 
x_57 = lean::mk_nat_obj(1114112u);
x_58 = lean::nat_dec_lt(x_43, x_57);
lean::dec(x_57);
if (x_58 == 0)
{
obj* x_61; obj* x_62; uint8 x_63; 
lean::dec(x_43);
x_61 = lean::mk_nat_obj(0u);
x_62 = lean::box_uint32(x_0);
x_63 = lean::nat_dec_eq(x_62, x_61);
lean::dec(x_61);
lean::dec(x_62);
if (x_63 == 0)
{
return x_1;
}
else
{
uint8 x_66; 
x_66 = 1;
return x_66;
}
}
else
{
obj* x_67; uint8 x_68; 
x_67 = lean::box_uint32(x_0);
x_68 = lean::nat_dec_eq(x_67, x_43);
lean::dec(x_43);
lean::dec(x_67);
if (x_68 == 0)
{
return x_1;
}
else
{
uint8 x_71; 
x_71 = 1;
return x_71;
}
}
}
}
else
{
obj* x_72; uint8 x_73; 
x_72 = lean::box_uint32(x_0);
x_73 = lean::nat_dec_eq(x_72, x_43);
lean::dec(x_43);
lean::dec(x_72);
if (x_73 == 0)
{
return x_1;
}
else
{
uint8 x_76; 
x_76 = 1;
return x_76;
}
}
}
lbl_4:
{
obj* x_77; obj* x_78; uint8 x_79; uint32 x_81; 
x_77 = lean::mk_nat_obj(9u);
x_78 = lean::mk_nat_obj(55296u);
x_79 = lean::nat_dec_lt(x_77, x_78);
lean::dec(x_78);
if (x_79 == 0)
{
obj* x_83; uint8 x_84; 
x_83 = lean::mk_nat_obj(57343u);
x_84 = lean::nat_dec_lt(x_83, x_77);
lean::dec(x_83);
if (x_84 == 0)
{
obj* x_87; uint32 x_88; 
lean::dec(x_77);
x_87 = lean::mk_nat_obj(0u);
x_88 = lean::unbox_uint32(x_87);
lean::dec(x_87);
x_81 = x_88;
goto lbl_82;
}
else
{
obj* x_90; uint8 x_91; 
x_90 = lean::mk_nat_obj(1114112u);
x_91 = lean::nat_dec_lt(x_77, x_90);
lean::dec(x_90);
if (x_91 == 0)
{
obj* x_94; uint32 x_95; 
lean::dec(x_77);
x_94 = lean::mk_nat_obj(0u);
x_95 = lean::unbox_uint32(x_94);
lean::dec(x_94);
x_81 = x_95;
goto lbl_82;
}
else
{
uint32 x_97; 
x_97 = lean::unbox_uint32(x_77);
lean::dec(x_77);
x_81 = x_97;
goto lbl_82;
}
}
}
else
{
uint32 x_99; 
x_99 = lean::unbox_uint32(x_77);
lean::dec(x_77);
x_81 = x_99;
goto lbl_82;
}
lbl_82:
{
obj* x_101; obj* x_102; uint8 x_103; 
x_101 = lean::box_uint32(x_0);
x_102 = lean::box_uint32(x_81);
x_103 = lean::nat_dec_eq(x_101, x_102);
lean::dec(x_102);
lean::dec(x_101);
if (x_103 == 0)
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
uint8 x_106; 
x_106 = 1;
return x_106;
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
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::mk_nat_obj(65u);
x_2 = lean::box_uint32(x_0);
x_3 = lean::nat_dec_le(x_1, x_2);
lean::dec(x_1);
if (x_3 == 0)
{
uint8 x_6; 
lean::dec(x_2);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(90u);
x_8 = lean::nat_dec_le(x_2, x_7);
lean::dec(x_7);
lean::dec(x_2);
if (x_8 == 0)
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8 x_12; 
x_12 = 1;
return x_12;
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
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::mk_nat_obj(97u);
x_2 = lean::box_uint32(x_0);
x_3 = lean::nat_dec_le(x_1, x_2);
lean::dec(x_1);
if (x_3 == 0)
{
uint8 x_6; 
lean::dec(x_2);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(122u);
x_8 = lean::nat_dec_le(x_2, x_7);
lean::dec(x_7);
lean::dec(x_2);
if (x_8 == 0)
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8 x_12; 
x_12 = 1;
return x_12;
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
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::mk_nat_obj(48u);
x_2 = lean::box_uint32(x_0);
x_3 = lean::nat_dec_le(x_1, x_2);
lean::dec(x_1);
if (x_3 == 0)
{
uint8 x_6; 
lean::dec(x_2);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(57u);
x_8 = lean::nat_dec_le(x_2, x_7);
lean::dec(x_7);
lean::dec(x_2);
if (x_8 == 0)
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8 x_12; 
x_12 = 1;
return x_12;
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
obj* l_char_to__lower(uint32 x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::mk_nat_obj(65u);
x_4 = lean::box_uint32(x_0);
x_5 = lean::nat_dec_le(x_3, x_4);
lean::dec(x_3);
if (x_5 == 0)
{
obj* x_8; 
lean::dec(x_4);
x_8 = lean::box_uint32(x_0);
return x_8;
}
else
{
obj* x_9; uint8 x_10; 
x_9 = lean::mk_nat_obj(90u);
x_10 = lean::nat_dec_le(x_4, x_9);
lean::dec(x_9);
lean::dec(x_4);
if (x_10 == 0)
{
obj* x_13; 
x_13 = lean::box_uint32(x_0);
return x_13;
}
else
{
obj* x_14; 
x_14 = lean::box(0);
x_1 = x_14;
goto lbl_2;
}
}
lbl_2:
{
obj* x_16; obj* x_17; obj* x_18; obj* x_21; uint8 x_22; 
lean::dec(x_1);
x_16 = lean::mk_nat_obj(32u);
x_17 = lean::box_uint32(x_0);
x_18 = lean::nat_add(x_17, x_16);
lean::dec(x_16);
lean::dec(x_17);
x_21 = lean::mk_nat_obj(55296u);
x_22 = lean::nat_dec_lt(x_18, x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_24; uint8 x_25; 
x_24 = lean::mk_nat_obj(57343u);
x_25 = lean::nat_dec_lt(x_24, x_18);
lean::dec(x_24);
if (x_25 == 0)
{
obj* x_28; 
lean::dec(x_18);
x_28 = lean::mk_nat_obj(0u);
return x_28;
}
else
{
obj* x_29; uint8 x_30; 
x_29 = lean::mk_nat_obj(1114112u);
x_30 = lean::nat_dec_lt(x_18, x_29);
lean::dec(x_29);
if (x_30 == 0)
{
obj* x_33; 
lean::dec(x_18);
x_33 = lean::mk_nat_obj(0u);
return x_33;
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
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_to__lower(x_1);
return x_2;
}
}
void initialize_init_data_nat_basic();
static bool _G_initialized = false;
void initialize_init_data_char_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_nat_basic();
 l_is__valid__char = _init_l_is__valid__char();
 l_char_lt = _init_l_char_lt();
 l_char_le = _init_l_char_le();
 l_char_has__lt = _init_l_char_has__lt();
 l_char_has__le = _init_l_char_has__le();
 l_char_inhabited = _init_l_char_inhabited();
}
