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
obj* l_Lean_Position_DecidableEq___boxed(obj*, obj*);
obj* l_Lean_Position_Lean_HasFormat(obj*);
obj* l_Lean_Position_Lean_HasFormat___closed__1;
obj* l_Nat_decEq___boxed(obj*, obj*);
obj* l_Lean_Position_Inhabited;
obj* l_Lean_Position_lt___boxed(obj*, obj*);
obj* l_Lean_Position_lt___main___boxed(obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_Position_Lean_HasFormat___closed__2;
obj* l_Lean_Position_lt___main___closed__1;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_Lean_Position_DecidableEq(obj*, obj*);
obj* l_Lean_Position_lt___main___closed__2;
obj* l_Nat_decLt___boxed(obj*, obj*);
extern obj* l_Lean_formatKVMap___closed__1;
uint8 l_Lean_Position_lt___main(obj*, obj*);
obj* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(obj*);
uint8 l_prodHasDecidableLt___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
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
l_Lean_Position_lt___main___closed__1 = _init_l_Lean_Position_lt___main___closed__1();
lean::mark_persistent(l_Lean_Position_lt___main___closed__1);
l_Lean_Position_lt___main___closed__2 = _init_l_Lean_Position_lt___main___closed__2();
lean::mark_persistent(l_Lean_Position_lt___main___closed__2);
l_Lean_Position_Lean_HasFormat___closed__1 = _init_l_Lean_Position_Lean_HasFormat___closed__1();
lean::mark_persistent(l_Lean_Position_Lean_HasFormat___closed__1);
l_Lean_Position_Lean_HasFormat___closed__2 = _init_l_Lean_Position_Lean_HasFormat___closed__2();
lean::mark_persistent(l_Lean_Position_Lean_HasFormat___closed__2);
l_Lean_Position_Inhabited = _init_l_Lean_Position_Inhabited();
lean::mark_persistent(l_Lean_Position_Inhabited);
return w;
}
