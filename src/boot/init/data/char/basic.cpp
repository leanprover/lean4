// Lean compiler output
// Module: init.data.char.basic
// Imports: init.data.nat.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* _l_s4_char_s11_has__sizeof_s7___boxed(obj*);
obj* _l_s4_char_s7_dec__lt(unsigned, unsigned);
obj* _l_s4_char_s2_lt;
obj* _l_s4_char_s7_to__nat_s7___boxed(obj*);
obj* _l_s15_is__valid__char;
obj* _l_s4_char_s7_dec__le(unsigned, unsigned);
unsigned char _l_s4_char_s12_is__alphanum(unsigned);
unsigned char _l_s4_char_s9_is__digit(unsigned);
obj* _l_s4_char_s9_is__lower_s7___boxed(obj*);
obj* _l_s4_char_s9_inhabited;
obj* _l_s4_char_s7_has__lt;
obj* _l_s4_char_s7_dec__le_s7___boxed(obj*, obj*);
unsigned char _l_s4_char_s9_is__alpha(unsigned);
unsigned char _l_s4_char_s9_is__upper(unsigned);
unsigned _l_s4_char_s7_to__nat(unsigned);
obj* _l_s4_char_s2_le;
unsigned _l_s4_char_s11_has__sizeof(unsigned);
obj* _l_s4_char_s12_is__alphanum_s7___boxed(obj*);
obj* _l_s4_char_s9_to__lower_s7___boxed(obj*);
unsigned char _l_s4_char_s9_is__lower(unsigned);
obj* _l_s4_char_s7_of__nat(obj*);
obj* _l_s4_char_s14_is__whitespace_s7___boxed(obj*);
obj* _l_s4_char_s9_to__lower(unsigned);
obj* _l_s4_char_s7_has__le;
unsigned char _l_s4_char_s14_is__whitespace(unsigned);
obj* _l_s4_char_s7_dec__lt_s7___boxed(obj*, obj*);
obj* _l_s4_char_s9_is__upper_s7___boxed(obj*);
obj* _l_s4_char_s13_decidable__eq_s7___boxed(obj*, obj*);
obj* _l_s4_char_s9_is__alpha_s7___boxed(obj*);
obj* _l_s4_char_s13_decidable__eq(unsigned, unsigned);
obj* _l_s4_char_s9_is__digit_s7___boxed(obj*);
obj* _init__l_s15_is__valid__char() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
unsigned _l_s4_char_s11_has__sizeof(unsigned x_0) {
_start:
{

return x_0;
}
}
obj* _l_s4_char_s11_has__sizeof_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_char_s11_has__sizeof(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
obj* _init__l_s4_char_s2_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_char_s2_le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_char_s7_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s4_char_s7_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _l_s4_char_s7_dec__lt(unsigned x_0, unsigned x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box_uint32(x_0);
x_3 = lean::box_uint32(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _l_s4_char_s7_dec__lt_s7___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s4_char_s7_dec__lt(x_2, x_3);
return x_4;
}
}
obj* _l_s4_char_s7_dec__le(unsigned x_0, unsigned x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box_uint32(x_0);
x_3 = lean::box_uint32(x_1);
x_4 = lean::nat_dec_le(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _l_s4_char_s7_dec__le_s7___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s4_char_s7_dec__le(x_2, x_3);
return x_4;
}
}
obj* _l_s4_char_s7_of__nat(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::mk_nat_obj(57343u);
x_6 = lean::nat_dec_lt(x_5, x_0);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
lean::dec(x_6);
lean::dec(x_0);
x_10 = lean::mk_nat_obj(0u);
return x_10;
}
else
{
obj* x_12; obj* x_13; 
lean::dec(x_6);
x_12 = lean::mk_nat_obj(1114112u);
x_13 = lean::nat_dec_lt(x_0, x_12);
lean::dec(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; 
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::mk_nat_obj(0u);
return x_17;
}
else
{

lean::dec(x_13);
return x_0;
}
}
}
else
{

lean::dec(x_2);
return x_0;
}
}
}
unsigned _l_s4_char_s7_to__nat(unsigned x_0) {
_start:
{

return x_0;
}
}
obj* _l_s4_char_s7_to__nat_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_char_s7_to__nat(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
obj* _l_s4_char_s13_decidable__eq(unsigned x_0, unsigned x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box_uint32(x_0);
x_3 = lean::box_uint32(x_1);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _l_s4_char_s13_decidable__eq_s7___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s4_char_s13_decidable__eq(x_2, x_3);
return x_4;
}
}
obj* _init__l_s4_char_s9_inhabited() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(65u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::mk_nat_obj(57343u);
x_6 = lean::nat_dec_lt(x_5, x_0);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
lean::dec(x_6);
lean::dec(x_0);
x_10 = lean::mk_nat_obj(0u);
return x_10;
}
else
{
obj* x_12; obj* x_13; 
lean::dec(x_6);
x_12 = lean::mk_nat_obj(1114112u);
x_13 = lean::nat_dec_lt(x_0, x_12);
lean::dec(x_12);
lean::dec(x_0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; 
lean::dec(x_13);
x_17 = lean::mk_nat_obj(0u);
return x_17;
}
else
{
obj* x_19; 
lean::dec(x_13);
x_19 = lean::mk_nat_obj(65u);
return x_19;
}
}
}
else
{
obj* x_22; 
lean::dec(x_0);
lean::dec(x_2);
x_22 = lean::mk_nat_obj(65u);
return x_22;
}
}
}
unsigned char _l_s4_char_s14_is__whitespace(unsigned x_0) {
_start:
{
unsigned char x_1; unsigned char x_3; obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::mk_nat_obj(32u);
x_6 = lean::mk_nat_obj(55296u);
x_7 = lean::nat_dec_lt(x_5, x_6);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_7);
x_10 = lean::mk_nat_obj(57343u);
x_11 = lean::nat_dec_lt(x_10, x_5);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_11);
lean::dec(x_5);
x_15 = lean::mk_nat_obj(0u);
x_16 = lean::box_uint32(x_0);
x_17 = lean::nat_dec_eq(x_16, x_15);
lean::dec(x_15);
lean::dec(x_16);
if (lean::obj_tag(x_17) == 0)
{
unsigned char x_21; 
lean::dec(x_17);
x_21 = 0;
x_3 = x_21;
goto lbl_4;
}
else
{
unsigned char x_23; 
lean::dec(x_17);
x_23 = 1;
return x_23;
}
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_11);
x_25 = lean::mk_nat_obj(1114112u);
x_26 = lean::nat_dec_lt(x_5, x_25);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_5);
lean::dec(x_26);
x_30 = lean::mk_nat_obj(0u);
x_31 = lean::box_uint32(x_0);
x_32 = lean::nat_dec_eq(x_31, x_30);
lean::dec(x_30);
lean::dec(x_31);
if (lean::obj_tag(x_32) == 0)
{
unsigned char x_36; 
lean::dec(x_32);
x_36 = 0;
x_3 = x_36;
goto lbl_4;
}
else
{
unsigned char x_38; 
lean::dec(x_32);
x_38 = 1;
return x_38;
}
}
else
{
obj* x_40; obj* x_41; 
lean::dec(x_26);
x_40 = lean::box_uint32(x_0);
x_41 = lean::nat_dec_eq(x_40, x_5);
lean::dec(x_5);
lean::dec(x_40);
if (lean::obj_tag(x_41) == 0)
{
unsigned char x_45; 
lean::dec(x_41);
x_45 = 0;
x_3 = x_45;
goto lbl_4;
}
else
{
unsigned char x_47; 
lean::dec(x_41);
x_47 = 1;
return x_47;
}
}
}
}
else
{
obj* x_49; obj* x_50; 
lean::dec(x_7);
x_49 = lean::box_uint32(x_0);
x_50 = lean::nat_dec_eq(x_49, x_5);
lean::dec(x_5);
lean::dec(x_49);
if (lean::obj_tag(x_50) == 0)
{
unsigned char x_54; 
lean::dec(x_50);
x_54 = 0;
x_3 = x_54;
goto lbl_4;
}
else
{
unsigned char x_56; 
lean::dec(x_50);
x_56 = 1;
return x_56;
}
}
lbl_2:
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = lean::mk_nat_obj(10u);
x_58 = lean::mk_nat_obj(55296u);
x_59 = lean::nat_dec_lt(x_57, x_58);
lean::dec(x_58);
if (lean::obj_tag(x_59) == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_59);
x_62 = lean::mk_nat_obj(57343u);
x_63 = lean::nat_dec_lt(x_62, x_57);
lean::dec(x_62);
if (lean::obj_tag(x_63) == 0)
{
obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_63);
lean::dec(x_57);
x_67 = lean::mk_nat_obj(0u);
x_68 = lean::box_uint32(x_0);
x_69 = lean::nat_dec_eq(x_68, x_67);
lean::dec(x_67);
lean::dec(x_68);
if (lean::obj_tag(x_69) == 0)
{

lean::dec(x_69);
return x_1;
}
else
{
unsigned char x_74; 
lean::dec(x_69);
x_74 = 1;
return x_74;
}
}
else
{
obj* x_76; obj* x_77; 
lean::dec(x_63);
x_76 = lean::mk_nat_obj(1114112u);
x_77 = lean::nat_dec_lt(x_57, x_76);
lean::dec(x_76);
if (lean::obj_tag(x_77) == 0)
{
obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_57);
lean::dec(x_77);
x_81 = lean::mk_nat_obj(0u);
x_82 = lean::box_uint32(x_0);
x_83 = lean::nat_dec_eq(x_82, x_81);
lean::dec(x_81);
lean::dec(x_82);
if (lean::obj_tag(x_83) == 0)
{

lean::dec(x_83);
return x_1;
}
else
{
unsigned char x_88; 
lean::dec(x_83);
x_88 = 1;
return x_88;
}
}
else
{
obj* x_90; obj* x_91; 
lean::dec(x_77);
x_90 = lean::box_uint32(x_0);
x_91 = lean::nat_dec_eq(x_90, x_57);
lean::dec(x_57);
lean::dec(x_90);
if (lean::obj_tag(x_91) == 0)
{

lean::dec(x_91);
return x_1;
}
else
{
unsigned char x_96; 
lean::dec(x_91);
x_96 = 1;
return x_96;
}
}
}
}
else
{
obj* x_98; obj* x_99; 
lean::dec(x_59);
x_98 = lean::box_uint32(x_0);
x_99 = lean::nat_dec_eq(x_98, x_57);
lean::dec(x_57);
lean::dec(x_98);
if (lean::obj_tag(x_99) == 0)
{

lean::dec(x_99);
return x_1;
}
else
{
unsigned char x_104; 
lean::dec(x_99);
x_104 = 1;
return x_104;
}
}
}
lbl_4:
{
obj* x_105; obj* x_106; obj* x_107; unsigned x_109; 
x_105 = lean::mk_nat_obj(9u);
x_106 = lean::mk_nat_obj(55296u);
x_107 = lean::nat_dec_lt(x_105, x_106);
lean::dec(x_106);
if (lean::obj_tag(x_107) == 0)
{
obj* x_112; obj* x_113; 
lean::dec(x_107);
x_112 = lean::mk_nat_obj(57343u);
x_113 = lean::nat_dec_lt(x_112, x_105);
lean::dec(x_112);
if (lean::obj_tag(x_113) == 0)
{
obj* x_117; unsigned x_118; 
lean::dec(x_113);
lean::dec(x_105);
x_117 = lean::mk_nat_obj(0u);
x_118 = lean::unbox_uint32(x_117);
lean::dec(x_117);
x_109 = x_118;
goto lbl_110;
}
else
{
obj* x_121; obj* x_122; 
lean::dec(x_113);
x_121 = lean::mk_nat_obj(1114112u);
x_122 = lean::nat_dec_lt(x_105, x_121);
lean::dec(x_121);
if (lean::obj_tag(x_122) == 0)
{
obj* x_126; unsigned x_127; 
lean::dec(x_122);
lean::dec(x_105);
x_126 = lean::mk_nat_obj(0u);
x_127 = lean::unbox_uint32(x_126);
lean::dec(x_126);
x_109 = x_127;
goto lbl_110;
}
else
{
unsigned x_130; 
lean::dec(x_122);
x_130 = lean::unbox_uint32(x_105);
lean::dec(x_105);
x_109 = x_130;
goto lbl_110;
}
}
}
else
{
unsigned x_133; 
lean::dec(x_107);
x_133 = lean::unbox_uint32(x_105);
lean::dec(x_105);
x_109 = x_133;
goto lbl_110;
}
lbl_110:
{
obj* x_135; obj* x_136; obj* x_137; 
x_135 = lean::box_uint32(x_0);
x_136 = lean::box_uint32(x_109);
x_137 = lean::nat_dec_eq(x_135, x_136);
lean::dec(x_136);
lean::dec(x_135);
if (lean::obj_tag(x_137) == 0)
{

lean::dec(x_137);
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
unsigned char x_142; 
lean::dec(x_137);
x_142 = 1;
return x_142;
}
}
}
}
}
obj* _l_s4_char_s14_is__whitespace_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_char_s14_is__whitespace(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_char_s9_is__upper(unsigned x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(65u);
x_2 = lean::box_uint32(x_0);
x_3 = lean::nat_dec_le(x_1, x_2);
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
unsigned char x_7; 
lean::dec(x_2);
lean::dec(x_3);
x_7 = 0;
return x_7;
}
else
{
obj* x_9; obj* x_10; 
lean::dec(x_3);
x_9 = lean::mk_nat_obj(90u);
x_10 = lean::nat_dec_le(x_2, x_9);
lean::dec(x_9);
lean::dec(x_2);
if (lean::obj_tag(x_10) == 0)
{
unsigned char x_14; 
lean::dec(x_10);
x_14 = 0;
return x_14;
}
else
{
unsigned char x_16; 
lean::dec(x_10);
x_16 = 1;
return x_16;
}
}
}
}
obj* _l_s4_char_s9_is__upper_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_char_s9_is__upper(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_char_s9_is__lower(unsigned x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(97u);
x_2 = lean::box_uint32(x_0);
x_3 = lean::nat_dec_le(x_1, x_2);
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
unsigned char x_7; 
lean::dec(x_2);
lean::dec(x_3);
x_7 = 0;
return x_7;
}
else
{
obj* x_9; obj* x_10; 
lean::dec(x_3);
x_9 = lean::mk_nat_obj(122u);
x_10 = lean::nat_dec_le(x_2, x_9);
lean::dec(x_9);
lean::dec(x_2);
if (lean::obj_tag(x_10) == 0)
{
unsigned char x_14; 
lean::dec(x_10);
x_14 = 0;
return x_14;
}
else
{
unsigned char x_16; 
lean::dec(x_10);
x_16 = 1;
return x_16;
}
}
}
}
obj* _l_s4_char_s9_is__lower_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_char_s9_is__lower(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_char_s9_is__alpha(unsigned x_0) {
_start:
{
unsigned char x_1; 
x_1 = _l_s4_char_s9_is__upper(x_0);
if (x_1 == 0)
{
unsigned char x_2; 
x_2 = _l_s4_char_s9_is__lower(x_0);
return x_2;
}
else
{

return x_1;
}
}
}
obj* _l_s4_char_s9_is__alpha_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_char_s9_is__alpha(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_char_s9_is__digit(unsigned x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(48u);
x_2 = lean::box_uint32(x_0);
x_3 = lean::nat_dec_le(x_1, x_2);
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
unsigned char x_7; 
lean::dec(x_2);
lean::dec(x_3);
x_7 = 0;
return x_7;
}
else
{
obj* x_9; obj* x_10; 
lean::dec(x_3);
x_9 = lean::mk_nat_obj(57u);
x_10 = lean::nat_dec_le(x_2, x_9);
lean::dec(x_9);
lean::dec(x_2);
if (lean::obj_tag(x_10) == 0)
{
unsigned char x_14; 
lean::dec(x_10);
x_14 = 0;
return x_14;
}
else
{
unsigned char x_16; 
lean::dec(x_10);
x_16 = 1;
return x_16;
}
}
}
}
obj* _l_s4_char_s9_is__digit_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_char_s9_is__digit(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_char_s12_is__alphanum(unsigned x_0) {
_start:
{
unsigned char x_1; 
x_1 = _l_s4_char_s9_is__alpha(x_0);
if (x_1 == 0)
{
unsigned char x_2; 
x_2 = _l_s4_char_s9_is__digit(x_0);
return x_2;
}
else
{

return x_1;
}
}
}
obj* _l_s4_char_s12_is__alphanum_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_char_s12_is__alphanum(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _l_s4_char_s9_to__lower(unsigned x_0) {
_start:
{
unsigned char x_1; obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::mk_nat_obj(65u);
x_4 = lean::box_uint32(x_0);
x_5 = lean::nat_dec_le(x_3, x_4);
lean::dec(x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; 
lean::dec(x_5);
lean::dec(x_4);
x_9 = lean::box_uint32(x_0);
return x_9;
}
else
{
obj* x_11; obj* x_12; 
lean::dec(x_5);
x_11 = lean::mk_nat_obj(90u);
x_12 = lean::nat_dec_le(x_4, x_11);
lean::dec(x_11);
lean::dec(x_4);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; 
lean::dec(x_12);
x_16 = lean::box_uint32(x_0);
return x_16;
}
else
{
unsigned char x_18; 
lean::dec(x_12);
x_18 = 0;
x_1 = x_18;
goto lbl_2;
}
}
lbl_2:
{
obj* x_19; obj* x_20; obj* x_21; obj* x_24; obj* x_25; 
x_19 = lean::mk_nat_obj(32u);
x_20 = lean::box_uint32(x_0);
x_21 = lean::nat_add(x_20, x_19);
lean::dec(x_19);
lean::dec(x_20);
x_24 = lean::mk_nat_obj(55296u);
x_25 = lean::nat_dec_lt(x_21, x_24);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_28; obj* x_29; 
lean::dec(x_25);
x_28 = lean::mk_nat_obj(57343u);
x_29 = lean::nat_dec_lt(x_28, x_21);
lean::dec(x_28);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; 
lean::dec(x_29);
lean::dec(x_21);
x_33 = lean::mk_nat_obj(0u);
return x_33;
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_29);
x_35 = lean::mk_nat_obj(1114112u);
x_36 = lean::nat_dec_lt(x_21, x_35);
lean::dec(x_35);
if (lean::obj_tag(x_36) == 0)
{
obj* x_40; 
lean::dec(x_36);
lean::dec(x_21);
x_40 = lean::mk_nat_obj(0u);
return x_40;
}
else
{

lean::dec(x_36);
return x_21;
}
}
}
else
{

lean::dec(x_25);
return x_21;
}
}
}
}
obj* _l_s4_char_s9_to__lower_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_char_s9_to__lower(x_1);
return x_2;
}
}
void _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s4_char_s5_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic();
 _l_s15_is__valid__char = _init__l_s15_is__valid__char();
 _l_s4_char_s2_lt = _init__l_s4_char_s2_lt();
 _l_s4_char_s2_le = _init__l_s4_char_s2_le();
 _l_s4_char_s7_has__lt = _init__l_s4_char_s7_has__lt();
 _l_s4_char_s7_has__le = _init__l_s4_char_s7_has__le();
 _l_s4_char_s9_inhabited = _init__l_s4_char_s9_inhabited();
}
