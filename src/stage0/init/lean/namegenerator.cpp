// Lean compiler output
// Module: init.lean.namegenerator
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
obj* l_Lean_NameGenerator_mkChild(obj*);
obj* l_Lean_NameGenerator_Inhabited___closed__1;
obj* l_Lean_NameGenerator_next(obj*);
obj* l_Lean_NameGenerator_Inhabited___closed__3;
obj* l_Lean_NameGenerator_Inhabited___closed__2;
extern "C" obj* lean_name_mk_string(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_Lean_NameGenerator_Inhabited;
obj* _init_l_Lean_NameGenerator_Inhabited___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("_uniq");
return x_1;
}
}
obj* _init_l_Lean_NameGenerator_Inhabited___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_NameGenerator_Inhabited___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_NameGenerator_Inhabited___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_NameGenerator_Inhabited___closed__2;
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_NameGenerator_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_Lean_NameGenerator_Inhabited___closed__3;
return x_1;
}
}
obj* l_Lean_NameGenerator_next(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::inc(x_3);
x_5 = lean_name_mk_numeral(x_3, x_4);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_4, x_6);
lean::dec(x_4);
lean::cnstr_set(x_1, 1, x_7);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_1);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_10);
lean::inc(x_9);
x_11 = lean_name_mk_numeral(x_9, x_10);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_10, x_12);
lean::dec(x_10);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_9);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_11);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_Lean_NameGenerator_mkChild(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::inc(x_3);
x_5 = lean_name_mk_numeral(x_3, x_4);
x_6 = lean::mk_nat_obj(1u);
lean::cnstr_set(x_1, 1, x_6);
lean::cnstr_set(x_1, 0, x_5);
x_7 = lean::nat_add(x_4, x_6);
lean::dec(x_4);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_11);
lean::inc(x_10);
x_12 = lean_name_mk_numeral(x_10, x_11);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::nat_add(x_11, x_13);
lean::dec(x_11);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_10);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
obj* initialize_init_lean_name(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_namegenerator(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
l_Lean_NameGenerator_Inhabited___closed__1 = _init_l_Lean_NameGenerator_Inhabited___closed__1();
lean::mark_persistent(l_Lean_NameGenerator_Inhabited___closed__1);
l_Lean_NameGenerator_Inhabited___closed__2 = _init_l_Lean_NameGenerator_Inhabited___closed__2();
lean::mark_persistent(l_Lean_NameGenerator_Inhabited___closed__2);
l_Lean_NameGenerator_Inhabited___closed__3 = _init_l_Lean_NameGenerator_Inhabited___closed__3();
lean::mark_persistent(l_Lean_NameGenerator_Inhabited___closed__3);
l_Lean_NameGenerator_Inhabited = _init_l_Lean_NameGenerator_Inhabited();
lean::mark_persistent(l_Lean_NameGenerator_Inhabited);
return w;
}
