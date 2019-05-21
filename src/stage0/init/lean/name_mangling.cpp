// Lean compiler output
// Module: init.lean.name_mangling
// Imports: init.lean.name init.lean.parser.stringliteral
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
obj* l_Lean_Name_mangle(obj*, obj*);
uint32 l_String_Iterator_curr___main(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l___private_init_lean_name__mangling_2__Name_mangleAux___main(obj*);
obj* l___private_init_lean_name__mangling_2__Name_mangleAux(obj*);
uint8 l_Char_isAlpha(uint32);
obj* l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3;
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Nat_repr(obj*);
obj* l_String_Iterator_next___main(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
namespace lean {
obj* nat_mod(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_String_mangle(obj*);
obj* l___private_init_lean_name__mangling_2__Name_mangleAux___main___closed__1;
uint8 l_Char_isDigit(uint32);
obj* l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2;
obj* l___private_init_lean_name__mangling_1__String_mangleAux(obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1;
namespace lean {
uint32 uint32_of_nat(obj*);
}
namespace lean {
obj* nat_div(obj*, obj*);
}
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l___private_init_lean_name__mangling_1__String_mangleAux___main(obj*, obj*, obj*);
uint32 l_Nat_digitChar(obj*);
extern obj* l_String_splitAux___main___closed__1;
namespace lean {
obj* string_length(obj*);
}
obj* _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_u");
return x_0;
}
}
obj* _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_x");
return x_0;
}
}
obj* _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("__");
return x_0;
}
}
obj* l___private_init_lean_name__mangling_1__String_mangleAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; uint32 x_8; uint8 x_9; 
x_5 = lean::mk_nat_obj(1ul);
x_6 = lean::nat_sub(x_0, x_5);
lean::dec(x_0);
x_8 = l_String_Iterator_curr___main(x_1);
x_9 = l_Char_isAlpha(x_8);
if (x_9 == 0)
{
uint8 x_10; 
x_10 = l_Char_isDigit(x_8);
if (x_10 == 0)
{
uint32 x_11; uint8 x_12; 
x_11 = 95;
x_12 = x_8 == x_11;
if (x_12 == 0)
{
obj* x_13; obj* x_14; uint8 x_15; 
x_13 = lean::uint32_to_nat(x_8);
x_14 = lean::mk_nat_obj(255ul);
x_15 = lean::nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint32 x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_26; uint32 x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_33; uint32 x_34; obj* x_36; obj* x_37; uint32 x_39; obj* x_41; obj* x_42; 
x_16 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1;
x_17 = lean::string_append(x_2, x_16);
x_18 = lean::mk_nat_obj(4096ul);
x_19 = lean::nat_div(x_13, x_18);
x_20 = l_Nat_digitChar(x_19);
lean::dec(x_19);
x_22 = lean::string_push(x_17, x_20);
x_23 = lean::nat_mod(x_13, x_18);
lean::dec(x_13);
x_25 = lean::mk_nat_obj(256ul);
x_26 = lean::nat_div(x_23, x_25);
x_27 = l_Nat_digitChar(x_26);
lean::dec(x_26);
x_29 = lean::string_push(x_22, x_27);
x_30 = lean::nat_mod(x_23, x_25);
lean::dec(x_23);
x_32 = lean::mk_nat_obj(16ul);
x_33 = lean::nat_div(x_30, x_32);
x_34 = l_Nat_digitChar(x_33);
lean::dec(x_33);
x_36 = lean::string_push(x_29, x_34);
x_37 = lean::nat_mod(x_30, x_32);
lean::dec(x_30);
x_39 = l_Nat_digitChar(x_37);
lean::dec(x_37);
x_41 = lean::string_push(x_36, x_39);
x_42 = l_String_Iterator_next___main(x_1);
x_0 = x_6;
x_1 = x_42;
x_2 = x_41;
goto _start;
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; uint32 x_48; obj* x_50; obj* x_51; uint32 x_53; obj* x_55; obj* x_56; 
x_44 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2;
x_45 = lean::string_append(x_2, x_44);
x_46 = lean::mk_nat_obj(16ul);
x_47 = lean::nat_div(x_13, x_46);
x_48 = l_Nat_digitChar(x_47);
lean::dec(x_47);
x_50 = lean::string_push(x_45, x_48);
x_51 = lean::nat_mod(x_13, x_46);
lean::dec(x_13);
x_53 = l_Nat_digitChar(x_51);
lean::dec(x_51);
x_55 = lean::string_push(x_50, x_53);
x_56 = l_String_Iterator_next___main(x_1);
x_0 = x_6;
x_1 = x_56;
x_2 = x_55;
goto _start;
}
}
else
{
obj* x_58; obj* x_59; obj* x_60; 
x_58 = l_String_Iterator_next___main(x_1);
x_59 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3;
x_60 = lean::string_append(x_2, x_59);
x_0 = x_6;
x_1 = x_58;
x_2 = x_60;
goto _start;
}
}
else
{
obj* x_62; obj* x_63; 
x_62 = l_String_Iterator_next___main(x_1);
x_63 = lean::string_push(x_2, x_8);
x_0 = x_6;
x_1 = x_62;
x_2 = x_63;
goto _start;
}
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_String_Iterator_next___main(x_1);
x_66 = lean::string_push(x_2, x_8);
x_0 = x_6;
x_1 = x_65;
x_2 = x_66;
goto _start;
}
}
else
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
}
obj* l___private_init_lean_name__mangling_1__String_mangleAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_1__String_mangleAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_String_mangle(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::string_length(x_0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = l_String_splitAux___main___closed__1;
x_5 = l___private_init_lean_name__mangling_1__String_mangleAux___main(x_1, x_3, x_4);
return x_5;
}
}
obj* _init_l___private_init_lean_name__mangling_2__Name_mangleAux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_");
return x_0;
}
}
obj* l___private_init_lean_name__mangling_2__Name_mangleAux___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; 
x_1 = l_String_splitAux___main___closed__1;
return x_1;
}
case 1:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; uint8 x_9; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_Lean_String_mangle(x_4);
x_8 = lean::box(0);
x_9 = lean_name_dec_eq(x_2, x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = l___private_init_lean_name__mangling_2__Name_mangleAux___main(x_2);
x_11 = l___private_init_lean_name__mangling_2__Name_mangleAux___main___closed__1;
x_12 = lean::string_append(x_10, x_11);
x_13 = lean::string_append(x_12, x_7);
lean::dec(x_7);
return x_13;
}
else
{
lean::dec(x_2);
return x_7;
}
}
default:
{
obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
lean::dec(x_0);
x_21 = l___private_init_lean_name__mangling_2__Name_mangleAux___main(x_16);
x_22 = l___private_init_lean_name__mangling_2__Name_mangleAux___main___closed__1;
x_23 = lean::string_append(x_21, x_22);
x_24 = l_Nat_repr(x_18);
x_25 = lean::string_append(x_23, x_24);
lean::dec(x_24);
x_27 = lean::string_append(x_25, x_22);
return x_27;
}
}
}
}
obj* l___private_init_lean_name__mangling_2__Name_mangleAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_name__mangling_2__Name_mangleAux___main(x_0);
return x_1;
}
}
obj* l_Lean_Name_mangle(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l___private_init_lean_name__mangling_2__Name_mangleAux___main(x_0);
x_3 = lean::string_append(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* initialize_init_lean_name(obj*);
obj* initialize_init_lean_parser_stringliteral(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_name__mangling(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_stringliteral(w);
if (io_result_is_error(w)) return w;
 l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1 = _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1();
lean::mark_persistent(l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1);
 l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2 = _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2();
lean::mark_persistent(l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2);
 l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3 = _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3();
lean::mark_persistent(l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3);
 l___private_init_lean_name__mangling_2__Name_mangleAux___main___closed__1 = _init_l___private_init_lean_name__mangling_2__Name_mangleAux___main___closed__1();
lean::mark_persistent(l___private_init_lean_name__mangling_2__Name_mangleAux___main___closed__1);
return w;
}
