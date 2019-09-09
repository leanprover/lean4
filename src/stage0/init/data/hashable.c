// Lean compiler output
// Module: init.data.hashable
// Imports: init.data.uint init.data.string.default
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_String_Hashable___closed__1;
lean_object* l_String_Hashable;
size_t l_Nat_hash(lean_object*);
size_t lean_string_hash(lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
lean_object* l_Nat_Hashable;
lean_object* l_mixHash___boxed(lean_object*, lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Nat_hash___boxed(lean_object*);
lean_object* l_Nat_Hashable___closed__1;
lean_object* l_mixHash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_usize_mix_hash(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* l_String_hash___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_string_hash(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
lean_object* _init_l_String_Hashable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_hash___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_String_Hashable() {
_start:
{
lean_object* x_1; 
x_1 = l_String_Hashable___closed__1;
return x_1;
}
}
size_t l_Nat_hash(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
lean_object* l_Nat_hash___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Nat_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
lean_object* _init_l_Nat_Hashable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_hash___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Nat_Hashable() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_Hashable___closed__1;
return x_1;
}
}
lean_object* initialize_init_data_uint(lean_object*);
lean_object* initialize_init_data_string_default(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_data_hashable(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_string_default(w);
if (lean_io_result_is_error(w)) return w;
l_String_Hashable___closed__1 = _init_l_String_Hashable___closed__1();
lean_mark_persistent(l_String_Hashable___closed__1);
l_String_Hashable = _init_l_String_Hashable();
lean_mark_persistent(l_String_Hashable);
l_Nat_Hashable___closed__1 = _init_l_Nat_Hashable___closed__1();
lean_mark_persistent(l_Nat_Hashable___closed__1);
l_Nat_Hashable = _init_l_Nat_Hashable();
lean_mark_persistent(l_Nat_Hashable);
return w;
}
#ifdef __cplusplus
}
#endif
