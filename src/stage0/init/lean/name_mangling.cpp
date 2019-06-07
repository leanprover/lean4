// Lean compiler output
// Module: init.lean.name_mangling
// Imports: init.lean.name
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
extern obj* l_Lean_Name_appendIndexAfter___main___closed__1;
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
uint8 l_UInt32_decEq(uint32, uint32);
uint8 l_Char_isDigit(uint32);
obj* l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2;
obj* l___private_init_lean_name__mangling_1__String_mangleAux(obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1;
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
obj* x_1; 
x_1 = lean::mk_string("_u");
return x_1;
}
}
obj* _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("_x");
return x_1;
}
}
obj* _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("__");
return x_1;
}
}
obj* l___private_init_lean_name__mangling_1__String_mangleAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint32 x_8; uint8 x_9; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_8 = l_String_Iterator_curr___main(x_2);
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
x_14 = lean::mk_nat_obj(255u);
x_15 = lean::nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint32 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; uint32 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; uint32 x_30; obj* x_31; obj* x_32; uint32 x_33; obj* x_34; obj* x_35; 
x_16 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1;
x_17 = lean::string_append(x_3, x_16);
x_18 = lean::mk_nat_obj(4096u);
x_19 = lean::nat_div(x_13, x_18);
x_20 = l_Nat_digitChar(x_19);
lean::dec(x_19);
x_21 = lean::string_push(x_17, x_20);
x_22 = lean::nat_mod(x_13, x_18);
lean::dec(x_13);
x_23 = lean::mk_nat_obj(256u);
x_24 = lean::nat_div(x_22, x_23);
x_25 = l_Nat_digitChar(x_24);
lean::dec(x_24);
x_26 = lean::string_push(x_21, x_25);
x_27 = lean::nat_mod(x_22, x_23);
lean::dec(x_22);
x_28 = lean::mk_nat_obj(16u);
x_29 = lean::nat_div(x_27, x_28);
x_30 = l_Nat_digitChar(x_29);
lean::dec(x_29);
x_31 = lean::string_push(x_26, x_30);
x_32 = lean::nat_mod(x_27, x_28);
lean::dec(x_27);
x_33 = l_Nat_digitChar(x_32);
lean::dec(x_32);
x_34 = lean::string_push(x_31, x_33);
x_35 = l_String_Iterator_next___main(x_2);
x_1 = x_7;
x_2 = x_35;
x_3 = x_34;
goto _start;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; uint32 x_41; obj* x_42; obj* x_43; uint32 x_44; obj* x_45; obj* x_46; 
x_37 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2;
x_38 = lean::string_append(x_3, x_37);
x_39 = lean::mk_nat_obj(16u);
x_40 = lean::nat_div(x_13, x_39);
x_41 = l_Nat_digitChar(x_40);
lean::dec(x_40);
x_42 = lean::string_push(x_38, x_41);
x_43 = lean::nat_mod(x_13, x_39);
lean::dec(x_13);
x_44 = l_Nat_digitChar(x_43);
lean::dec(x_43);
x_45 = lean::string_push(x_42, x_44);
x_46 = l_String_Iterator_next___main(x_2);
x_1 = x_7;
x_2 = x_46;
x_3 = x_45;
goto _start;
}
}
else
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = l_String_Iterator_next___main(x_2);
x_49 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3;
x_50 = lean::string_append(x_3, x_49);
x_1 = x_7;
x_2 = x_48;
x_3 = x_50;
goto _start;
}
}
else
{
obj* x_52; obj* x_53; 
x_52 = l_String_Iterator_next___main(x_2);
x_53 = lean::string_push(x_3, x_8);
x_1 = x_7;
x_2 = x_52;
x_3 = x_53;
goto _start;
}
}
else
{
obj* x_55; obj* x_56; 
x_55 = l_String_Iterator_next___main(x_2);
x_56 = lean::string_push(x_3, x_8);
x_1 = x_7;
x_2 = x_55;
x_3 = x_56;
goto _start;
}
}
else
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
}
obj* l___private_init_lean_name__mangling_1__String_mangleAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_name__mangling_1__String_mangleAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_String_mangle(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::string_length(x_1);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = l_String_splitAux___main___closed__1;
x_6 = l___private_init_lean_name__mangling_1__String_mangleAux___main(x_2, x_4, x_5);
return x_6;
}
}
obj* l___private_init_lean_name__mangling_2__Name_mangleAux___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; 
x_2 = l_String_splitAux___main___closed__1;
return x_2;
}
case 1:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_Lean_String_mangle(x_4);
x_6 = lean::box(0);
x_7 = lean_name_dec_eq(x_3, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = l___private_init_lean_name__mangling_2__Name_mangleAux___main(x_3);
x_9 = l_Lean_Name_appendIndexAfter___main___closed__1;
x_10 = lean::string_append(x_8, x_9);
x_11 = lean::string_append(x_10, x_5);
lean::dec(x_5);
return x_11;
}
else
{
lean::dec(x_3);
return x_5;
}
}
default: 
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::dec(x_1);
x_14 = l___private_init_lean_name__mangling_2__Name_mangleAux___main(x_12);
x_15 = l_Lean_Name_appendIndexAfter___main___closed__1;
x_16 = lean::string_append(x_14, x_15);
x_17 = l_Nat_repr(x_13);
x_18 = lean::string_append(x_16, x_17);
lean::dec(x_17);
x_19 = lean::string_append(x_18, x_15);
return x_19;
}
}
}
}
obj* l___private_init_lean_name__mangling_2__Name_mangleAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_name__mangling_2__Name_mangleAux___main(x_1);
return x_2;
}
}
obj* l_Lean_Name_mangle(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l___private_init_lean_name__mangling_2__Name_mangleAux___main(x_1);
x_4 = lean::string_append(x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* initialize_init_lean_name(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_name__mangling(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1 = _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1();
lean::mark_persistent(l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1);
l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2 = _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2();
lean::mark_persistent(l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2);
l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3 = _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3();
lean::mark_persistent(l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "String"), "mangle"), 1, l_Lean_String_mangle);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Name"), "mangle"), 2, l_Lean_Name_mangle);
return w;
}
