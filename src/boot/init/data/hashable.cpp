// Lean compiler output
// Module: init.data.hashable
// Imports: init.data.usize init.data.string.default
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* _l_s9_mix__hash_s11___closed__1_s7___boxed;
obj* _l_s3_nat_s4_hash_s7___boxed(obj*);
obj* _l_s9_mix__hash(size_t, size_t);
size_t _l_s3_nat_s4_hash(obj*);
obj* _l_s9_mix__hash_s7___boxed(obj*, obj*);
obj* _l_s3_nat_s8_hashable;
obj* _l_s6_string_s8_hashable;
size_t _l_s6_string_s4_hash(obj*);
obj* _l_s6_string_s4_hash_s7___boxed(obj*);
size_t _l_s9_mix__hash_s11___closed__1;
obj* _l_s9_mix__hash(size_t x_0, size_t x_1){
_start:
{
size_t x_2; obj* x_3; 
x_2 = _l_s9_mix__hash_s11___closed__1;
x_3 = lean::box_size_t(x_2);
return x_3;
}
}
size_t _init__l_s9_mix__hash_s11___closed__1(){
_start:
{
obj* x_0; size_t x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::usize_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _l_s9_mix__hash_s7___boxed(obj* x_0, obj* x_1){
_start:
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s9_mix__hash(x_2, x_3);
return x_4;
}
}
obj* _init__l_s9_mix__hash_s11___closed__1_s7___boxed(){
_start:
{
size_t x_0; obj* x_1; 
x_0 = _l_s9_mix__hash_s11___closed__1;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
size_t _l_s6_string_s4_hash(obj* x_0){
_start:
{
size_t x_2; 
lean::dec(x_0);
x_2 = _l_s9_mix__hash_s11___closed__1;
return x_2;
}
}
obj* _l_s6_string_s4_hash_s7___boxed(obj* x_0){
_start:
{
size_t x_1; obj* x_2; 
x_1 = _l_s6_string_s4_hash(x_0);
x_2 = lean::box_size_t(x_1);
return x_2;
}
}
obj* _init__l_s6_string_s8_hashable(){
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_string_s4_hash_s7___boxed), 1, 0);
return x_0;
}
}
size_t _l_s3_nat_s4_hash(obj* x_0){
_start:
{
size_t x_1; 
x_1 = lean::usize_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _l_s3_nat_s4_hash_s7___boxed(obj* x_0){
_start:
{
size_t x_1; obj* x_2; 
x_1 = _l_s3_nat_s4_hash(x_0);
x_2 = lean::box_size_t(x_1);
return x_2;
}
}
obj* _init__l_s3_nat_s8_hashable(){
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_nat_s4_hash_s7___boxed), 1, 0);
return x_0;
}
}
void _l_initialize__l_s4_init_s4_data_s5_usize();
void _l_initialize__l_s4_init_s4_data_s6_string_s7_default();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s8_hashable() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s5_usize();
 _l_initialize__l_s4_init_s4_data_s6_string_s7_default();
 _l_s9_mix__hash_s11___closed__1 = _init__l_s9_mix__hash_s11___closed__1();
 _l_s9_mix__hash_s11___closed__1_s7___boxed = _init__l_s9_mix__hash_s11___closed__1_s7___boxed();
 _l_s6_string_s8_hashable = _init__l_s6_string_s8_hashable();
 _l_s3_nat_s8_hashable = _init__l_s3_nat_s8_hashable();
}
