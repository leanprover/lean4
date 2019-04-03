// Lean compiler output
// Module: init.lean.position
// Imports: init.data.nat.default init.data.rbmap.default init.lean.format init.lean.parser.parsec
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
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Position_DecidableEq___boxed(obj*, obj*);
uint32 l_String_OldIterator_curr___main(obj*);
obj* l_RBNode_insert___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_position_1__fromStringAux___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Position_Lean_HasToFormat___closed__3;
obj* l_Nat_decEq___boxed(obj*, obj*);
obj* l_Lean_Position_Inhabited;
obj* l_Lean_Position_lt___boxed(obj*, obj*);
obj* l_Lean_Position_lt___main___boxed(obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_String_OldIterator_next___main(obj*);
obj* l_Lean_Position_lt___main___closed__1;
obj* l_Lean_Position_Lean_HasToFormat___closed__1;
obj* l___private_init_lean_position_1__fromStringAux___boxed(obj*, obj*, obj*);
uint8 l_String_OldIterator_hasNext___main(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_RBMap_ofList___main___at_Lean_FileMap_fromString___spec__1(obj*);
obj* l_Lean_toFmt___at_Lean_Position_Lean_HasToFormat___spec__1(obj*);
obj* l_Lean_Position_Lean_HasToFormat___closed__2;
obj* l___private_init_lean_position_1__fromStringAux(obj*, obj*, obj*);
obj* l___private_init_lean_position_1__fromStringAux___main(obj*, obj*, obj*);
uint8 l_Lean_Position_DecidableEq(obj*, obj*);
obj* l_Lean_Position_Lean_HasToFormat(obj*);
obj* l_Lean_Position_lt___main___closed__2;
obj* l_Nat_decLt___boxed(obj*, obj*);
uint8 l_Lean_Position_lt___main(obj*, obj*);
obj* l_RBMap_lowerBound___main___rarg(obj*, obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
uint8 l_prodHasDecidableLt___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_FileMap_toPosition(obj*, obj*);
obj* l_Lean_FileMap_fromString(obj*);
namespace lean {
obj* string_length(obj*);
}
uint8 l_Lean_Position_DecidableEq(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::nat_dec_eq(x_2, x_4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::nat_dec_eq(x_3, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = 0;
return x_9;
}
else
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
}
}
obj* l_Lean_Position_DecidableEq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Position_DecidableEq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Position_lt___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_decEq___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_Lean_Position_lt___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_decLt___boxed), 2, 0);
return x_0;
}
}
uint8 l_Lean_Position_lt___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_4);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_9);
x_14 = l_Lean_Position_lt___main___closed__1;
x_15 = l_Lean_Position_lt___main___closed__2;
x_16 = l_prodHasDecidableLt___rarg(x_14, x_14, x_15, x_15, x_12, x_13);
return x_16;
}
}
obj* l_Lean_Position_lt___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Position_lt___main(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_Position_lt(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_Position_lt___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Position_lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Position_lt(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_Lean_toFmt___at_Lean_Position_Lean_HasToFormat___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Nat_repr(x_0);
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Position_Lean_HasToFormat___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("\xe2\x9f\xa8");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Position_Lean_HasToFormat___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(", ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Position_Lean_HasToFormat___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("\xe2\x9f\xa9");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Position_Lean_HasToFormat(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_toFmt___at_Lean_Position_Lean_HasToFormat___spec__1(x_1);
x_7 = 0;
x_8 = l_Lean_Position_Lean_HasToFormat___closed__1;
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_6);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_7);
x_10 = x_9;
x_11 = l_Lean_Position_Lean_HasToFormat___closed__2;
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_7);
x_13 = x_12;
x_14 = l_Lean_toFmt___at_Lean_Position_Lean_HasToFormat___spec__1(x_3);
x_15 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_7);
x_16 = x_15;
x_17 = l_Lean_Position_Lean_HasToFormat___closed__3;
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_7);
x_19 = x_18;
return x_19;
}
}
obj* _init_l_Lean_Position_Inhabited() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(1ul);
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l___private_init_lean_position_1__fromStringAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_1);
if (x_5 == 0)
{
obj* x_8; 
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::box(0);
return x_8;
}
else
{
obj* x_9; obj* x_10; uint32 x_12; uint32 x_13; uint8 x_14; 
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_sub(x_0, x_9);
lean::dec(x_0);
x_12 = l_String_OldIterator_curr___main(x_1);
x_13 = 10;
x_14 = x_12 == x_13;
if (x_14 == 0)
{
obj* x_15; 
x_15 = l_String_OldIterator_next___main(x_1);
x_0 = x_10;
x_1 = x_15;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_25; 
x_17 = l_String_OldIterator_next___main(x_1);
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
x_20 = lean::nat_add(x_2, x_9);
lean::inc(x_20);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_18);
lean::cnstr_set(x_22, 1, x_20);
x_23 = l___private_init_lean_position_1__fromStringAux___main(x_10, x_17, x_20);
lean::dec(x_20);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
obj* x_28; 
lean::dec(x_1);
lean::dec(x_0);
x_28 = lean::box(0);
return x_28;
}
}
}
obj* l___private_init_lean_position_1__fromStringAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_position_1__fromStringAux___main(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_position_1__fromStringAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_position_1__fromStringAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_position_1__fromStringAux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_position_1__fromStringAux(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_ofList___main___at_Lean_FileMap_fromString___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::dec(x_2);
x_12 = l_RBMap_ofList___main___at_Lean_FileMap_fromString___spec__1(x_4);
x_13 = l_Lean_Position_lt___main___closed__2;
x_14 = l_RBNode_insert___rarg(x_13, x_12, x_7, x_9);
return x_14;
}
}
}
obj* l_Lean_FileMap_fromString(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::string_length(x_0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set(x_3, 2, x_2);
x_4 = lean::mk_nat_obj(1ul);
x_5 = l___private_init_lean_position_1__fromStringAux___main(x_1, x_3, x_4);
x_6 = l_RBMap_ofList___main___at_Lean_FileMap_fromString___spec__1(x_5);
return x_6;
}
}
obj* l_Lean_FileMap_toPosition(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_Lean_Position_lt___main___closed__2;
lean::inc(x_1);
x_4 = l_RBMap_lowerBound___main___rarg(x_2, x_0, x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(1ul);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
else
{
obj* x_7; obj* x_10; obj* x_12; obj* x_15; obj* x_18; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_15 = lean::nat_sub(x_1, x_10);
lean::dec(x_10);
lean::dec(x_1);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_12);
lean::cnstr_set(x_18, 1, x_15);
return x_18;
}
}
}
obj* initialize_init_data_nat_default(obj*);
obj* initialize_init_data_rbmap_default(obj*);
obj* initialize_init_lean_format(obj*);
obj* initialize_init_lean_parser_parsec(obj*);
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
w = initialize_init_lean_parser_parsec(w);
 l_Lean_Position_lt___main___closed__1 = _init_l_Lean_Position_lt___main___closed__1();
lean::mark_persistent(l_Lean_Position_lt___main___closed__1);
 l_Lean_Position_lt___main___closed__2 = _init_l_Lean_Position_lt___main___closed__2();
lean::mark_persistent(l_Lean_Position_lt___main___closed__2);
 l_Lean_Position_Lean_HasToFormat___closed__1 = _init_l_Lean_Position_Lean_HasToFormat___closed__1();
lean::mark_persistent(l_Lean_Position_Lean_HasToFormat___closed__1);
 l_Lean_Position_Lean_HasToFormat___closed__2 = _init_l_Lean_Position_Lean_HasToFormat___closed__2();
lean::mark_persistent(l_Lean_Position_Lean_HasToFormat___closed__2);
 l_Lean_Position_Lean_HasToFormat___closed__3 = _init_l_Lean_Position_Lean_HasToFormat___closed__3();
lean::mark_persistent(l_Lean_Position_Lean_HasToFormat___closed__3);
 l_Lean_Position_Inhabited = _init_l_Lean_Position_Inhabited();
lean::mark_persistent(l_Lean_Position_Inhabited);
return w;
}
