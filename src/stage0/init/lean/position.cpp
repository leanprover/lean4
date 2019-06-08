// Lean compiler output
// Module: init.lean.position
// Imports: init.data.nat.default init.data.rbmap.default init.lean.format
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
uint8 l_Lean_Position_lt(obj*, obj*);
extern obj* l_Nat_Inhabited;
obj* l_Lean_FileMap_toPosition___main(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Position_DecidableEq___boxed(obj*, obj*);
obj* l_Lean_Position_Lean_HasFormat(obj*);
obj* l_Lean_FileMap_ofString___closed__2;
obj* l___private_init_lean_position_1__ofStringAux___main(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_position_2__toColumnAux___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Position_Lean_HasFormat___closed__1;
obj* l_Lean_FileMap_Inhabited;
obj* l___private_init_lean_position_3__toPositionAux(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_position_2__toColumnAux___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Nat_decEq___boxed(obj*, obj*);
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Lean_FileMap_toPosition___main___boxed(obj*, obj*);
obj* l_Lean_Position_Inhabited;
obj* l_Lean_Position_lt___boxed(obj*, obj*);
obj* l_Lean_Position_lt___main___boxed(obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_Position_Lean_HasFormat___closed__2;
namespace lean {
uint8 string_utf8_at_end(obj*, obj*);
}
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_Position_lt___main___closed__1;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l___private_init_lean_position_3__toPositionAux___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Array_push(obj*, obj*, obj*);
namespace lean {
uint32 string_utf8_get(obj*, obj*);
}
obj* l___private_init_lean_position_3__toPositionAux___main(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_UInt32_decEq(uint32, uint32);
uint8 l_Lean_Position_DecidableEq(obj*, obj*);
obj* l___private_init_lean_position_2__toColumnAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Position_lt___main___closed__2;
obj* l_Nat_decLt___boxed(obj*, obj*);
extern obj* l_Lean_formatKVMap___closed__1;
uint8 l_Lean_Position_lt___main(obj*, obj*);
obj* l___private_init_lean_position_1__ofStringAux(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_FileMap_ofString___closed__1;
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(obj*);
namespace lean {
obj* string_utf8_next(obj*, obj*);
}
uint8 l_prodHasDecidableLt___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_Lean_FileMap_toPosition(obj*, obj*);
obj* l___private_init_lean_position_3__toPositionAux___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_FileMap_ofString(obj*);
obj* l_Lean_FileMap_toPosition___boxed(obj*, obj*);
obj* l___private_init_lean_position_2__toColumnAux(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_String_toFileMap(obj*);
uint8 l_Lean_Position_DecidableEq(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = lean::nat_dec_eq(x_3, x_5);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8 x_9; 
x_9 = lean::nat_dec_eq(x_4, x_6);
if (x_9 == 0)
{
uint8 x_10; 
x_10 = 0;
return x_10;
}
else
{
uint8 x_11; 
x_11 = 1;
return x_11;
}
}
}
}
obj* l_Lean_Position_DecidableEq___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Position_DecidableEq(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _init_l_Lean_Position_lt___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_decEq___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_Position_lt___main___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
uint8 l_Lean_Position_lt___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::inc(x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::inc(x_6);
lean::inc(x_5);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_6);
x_9 = l_Lean_Position_lt___main___closed__1;
x_10 = l_Lean_Position_lt___main___closed__2;
x_11 = l_prodHasDecidableLt___rarg(x_9, x_9, x_10, x_10, x_7, x_8);
return x_11;
}
}
obj* l_Lean_Position_lt___main___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Position_lt___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_Position_lt(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_Position_lt___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Position_lt___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Position_lt(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Nat_repr(x_1);
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l_Lean_Position_Lean_HasFormat___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("⟨");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Position_Lean_HasFormat___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("⟩");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Position_Lean_HasFormat(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_2);
x_5 = 0;
x_6 = l_Lean_Position_Lean_HasFormat___closed__1;
x_7 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set_scalar(x_7, sizeof(void*)*2, x_5);
x_8 = l_Lean_formatKVMap___closed__1;
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_5);
x_10 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_3);
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_5);
x_12 = l_Lean_Position_Lean_HasFormat___closed__2;
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_5);
return x_13;
}
}
obj* _init_l_Lean_Position_Inhabited() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(1u);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_FileMap_Inhabited() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::mk_empty_array(x_1);
x_3 = lean::mk_string("");
lean::inc(x_2);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_2);
return x_4;
}
}
obj* l___private_init_lean_position_1__ofStringAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = lean::string_utf8_at_end(x_1, x_2);
if (x_6 == 0)
{
uint32 x_7; obj* x_8; uint32 x_9; uint8 x_10; 
x_7 = lean::string_utf8_get(x_1, x_2);
x_8 = lean::string_utf8_next(x_1, x_2);
lean::dec(x_2);
x_9 = 10;
x_10 = x_7 == x_9;
if (x_10 == 0)
{
x_2 = x_8;
goto _start;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_3, x_12);
lean::dec(x_3);
lean::inc(x_8);
x_14 = lean::array_push(x_4, x_8);
lean::inc(x_13);
x_15 = lean::array_push(x_5, x_13);
x_2 = x_8;
x_3 = x_13;
x_4 = x_14;
x_5 = x_15;
goto _start;
}
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::array_push(x_4, x_2);
x_18 = lean::array_push(x_5, x_3);
x_19 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_17);
lean::cnstr_set(x_19, 2, x_18);
return x_19;
}
}
}
obj* l___private_init_lean_position_1__ofStringAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_position_1__ofStringAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_FileMap_ofString___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::mk_empty_array(x_1);
x_3 = lean::array_push(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_FileMap_ofString___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::mk_empty_array(x_1);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::array_push(x_2, x_3);
return x_4;
}
}
obj* l_Lean_FileMap_ofString(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::mk_nat_obj(1u);
x_4 = l_Lean_FileMap_ofString___closed__1;
x_5 = l_Lean_FileMap_ofString___closed__2;
x_6 = l___private_init_lean_position_1__ofStringAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l___private_init_lean_position_2__toColumnAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_eq(x_3, x_2);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::string_utf8_at_end(x_1, x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::string_utf8_next(x_1, x_3);
lean::dec(x_3);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_4, x_8);
lean::dec(x_4);
x_3 = x_7;
x_4 = x_9;
goto _start;
}
else
{
lean::dec(x_3);
return x_4;
}
}
else
{
lean::dec(x_3);
return x_4;
}
}
}
obj* l___private_init_lean_position_2__toColumnAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_position_2__toColumnAux___main(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_position_2__toColumnAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_position_2__toColumnAux___main(x_1, x_3, x_4, x_5);
return x_6;
}
}
obj* l___private_init_lean_position_2__toColumnAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_position_2__toColumnAux(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l___private_init_lean_position_3__toPositionAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_7 = l_Nat_Inhabited;
x_8 = lean::array_get(x_7, x_2, x_5);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_5, x_9);
x_11 = lean::nat_dec_eq(x_6, x_10);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; 
lean::dec(x_8);
x_12 = lean::nat_add(x_5, x_6);
x_13 = lean::mk_nat_obj(2u);
x_14 = lean::nat_div(x_12, x_13);
lean::dec(x_12);
x_15 = lean::array_get(x_7, x_2, x_14);
x_16 = lean::nat_dec_eq(x_4, x_15);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = lean::nat_dec_lt(x_15, x_4);
lean::dec(x_15);
if (x_17 == 0)
{
lean::dec(x_6);
x_6 = x_14;
goto _start;
}
else
{
lean::dec(x_5);
x_5 = x_14;
goto _start;
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_5);
x_20 = lean::array_get(x_7, x_3, x_14);
lean::dec(x_14);
x_21 = lean::mk_nat_obj(0u);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_6);
x_23 = lean::array_get(x_7, x_3, x_5);
lean::dec(x_5);
x_24 = lean::mk_nat_obj(0u);
x_25 = l___private_init_lean_position_2__toColumnAux___main(x_1, x_4, x_8, x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_23);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
}
obj* l___private_init_lean_position_3__toPositionAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_lean_position_3__toPositionAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l___private_init_lean_position_3__toPositionAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_lean_position_3__toPositionAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l___private_init_lean_position_3__toPositionAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_lean_position_3__toPositionAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_FileMap_toPosition___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
x_6 = lean::array_get_size(x_4);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_6, x_7);
lean::dec(x_6);
x_9 = lean::mk_nat_obj(0u);
x_10 = l___private_init_lean_position_3__toPositionAux___main(x_3, x_4, x_5, x_2, x_9, x_8);
return x_10;
}
}
obj* l_Lean_FileMap_toPosition___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_FileMap_toPosition___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_FileMap_toPosition(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_FileMap_toPosition___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_FileMap_toPosition___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_FileMap_toPosition(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_String_toFileMap(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_FileMap_ofString(x_1);
return x_2;
}
}
obj* initialize_init_data_nat_default(obj*);
obj* initialize_init_data_rbmap_default(obj*);
obj* initialize_init_lean_format(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_position(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_rbmap_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_format(w);
if (io_result_is_error(w)) return w;
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Position"), "DecidableEq"), 2, l_Lean_Position_DecidableEq___boxed);
l_Lean_Position_lt___main___closed__1 = _init_l_Lean_Position_lt___main___closed__1();
lean::mark_persistent(l_Lean_Position_lt___main___closed__1);
l_Lean_Position_lt___main___closed__2 = _init_l_Lean_Position_lt___main___closed__2();
lean::mark_persistent(l_Lean_Position_lt___main___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Position"), "lt"), 2, l_Lean_Position_lt___boxed);
l_Lean_Position_Lean_HasFormat___closed__1 = _init_l_Lean_Position_Lean_HasFormat___closed__1();
lean::mark_persistent(l_Lean_Position_Lean_HasFormat___closed__1);
l_Lean_Position_Lean_HasFormat___closed__2 = _init_l_Lean_Position_Lean_HasFormat___closed__2();
lean::mark_persistent(l_Lean_Position_Lean_HasFormat___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Position"), "Lean"), "HasFormat"), 1, l_Lean_Position_Lean_HasFormat);
l_Lean_Position_Inhabited = _init_l_Lean_Position_Inhabited();
lean::mark_persistent(l_Lean_Position_Inhabited);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Position"), "Inhabited"), l_Lean_Position_Inhabited);
l_Lean_FileMap_Inhabited = _init_l_Lean_FileMap_Inhabited();
lean::mark_persistent(l_Lean_FileMap_Inhabited);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "FileMap"), "Inhabited"), l_Lean_FileMap_Inhabited);
l_Lean_FileMap_ofString___closed__1 = _init_l_Lean_FileMap_ofString___closed__1();
lean::mark_persistent(l_Lean_FileMap_ofString___closed__1);
l_Lean_FileMap_ofString___closed__2 = _init_l_Lean_FileMap_ofString___closed__2();
lean::mark_persistent(l_Lean_FileMap_ofString___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "FileMap"), "ofString"), 1, l_Lean_FileMap_ofString);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "FileMap"), "toPosition"), 2, l_Lean_FileMap_toPosition___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "String"), "toFileMap"), 1, l_Lean_String_toFileMap);
return w;
}
