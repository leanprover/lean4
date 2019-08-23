// Lean compiler output
// Module: init.data.hashable
// Imports: init.data.uint init.data.string.default
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
obj* l_String_Hashable___closed__1;
obj* l_String_Hashable;
usize l_Nat_hash(obj*);
extern "C" usize lean_string_hash(obj*);
obj* l_String_hash___boxed(obj*);
obj* l_Nat_Hashable;
obj* l_mixHash___boxed(obj*, obj*);
extern "C" usize lean_usize_mix_hash(usize, usize);
extern "C" usize lean_usize_of_nat(obj*);
obj* l_Nat_hash___boxed(obj*);
obj* l_Nat_Hashable___closed__1;
obj* l_mixHash___boxed(obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; usize x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = lean_usize_mix_hash(x_3, x_4);
x_6 = lean::box_size_t(x_5);
return x_6;
}
}
obj* l_String_hash___boxed(obj* x_1) {
_start:
{
usize x_2; obj* x_3; 
x_2 = lean_string_hash(x_1);
x_3 = lean::box_size_t(x_2);
return x_3;
}
}
obj* _init_l_String_Hashable___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_String_hash___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_String_Hashable() {
_start:
{
obj* x_1; 
x_1 = l_String_Hashable___closed__1;
return x_1;
}
}
usize l_Nat_hash(obj* x_1) {
_start:
{
usize x_2; 
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
obj* l_Nat_hash___boxed(obj* x_1) {
_start:
{
usize x_2; obj* x_3; 
x_2 = l_Nat_hash(x_1);
lean::dec(x_1);
x_3 = lean::box_size_t(x_2);
return x_3;
}
}
obj* _init_l_Nat_Hashable___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_hash___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Nat_Hashable() {
_start:
{
obj* x_1; 
x_1 = l_Nat_Hashable___closed__1;
return x_1;
}
}
obj* initialize_init_data_uint(obj*);
obj* initialize_init_data_string_default(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_hashable(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_string_default(w);
if (lean::io_result_is_error(w)) return w;
l_String_Hashable___closed__1 = _init_l_String_Hashable___closed__1();
lean::mark_persistent(l_String_Hashable___closed__1);
l_String_Hashable = _init_l_String_Hashable();
lean::mark_persistent(l_String_Hashable);
l_Nat_Hashable___closed__1 = _init_l_Nat_Hashable___closed__1();
lean::mark_persistent(l_Nat_Hashable___closed__1);
l_Nat_Hashable = _init_l_Nat_Hashable();
lean::mark_persistent(l_Nat_Hashable);
return w;
}
