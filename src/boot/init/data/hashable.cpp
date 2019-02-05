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
obj* l_mix__hash___closed__1___boxed;
size_t l_string_hash(obj*);
obj* l_string_hashable;
obj* l_nat_hashable;
obj* l_nat_hash___boxed(obj*);
obj* l_mix__hash___boxed(obj*, obj*);
size_t l_nat_hash(obj*);
obj* l_mix__hash(size_t, size_t);
obj* l_string_hash___boxed(obj*);
size_t l_mix__hash___closed__1;
obj* l_mix__hash(size_t x_0, size_t x_1) {
_start:
{
size_t x_2; obj* x_3; 
x_2 = l_mix__hash___closed__1;
x_3 = lean::box_size_t(x_2);
return x_3;
}
}
size_t _init_l_mix__hash___closed__1() {
_start:
{
obj* x_0; size_t x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::usize_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_mix__hash___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = l_mix__hash(x_2, x_3);
return x_4;
}
}
obj* _init_l_mix__hash___closed__1___boxed() {
_start:
{
size_t x_0; obj* x_1; 
x_0 = l_mix__hash___closed__1;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
size_t l_string_hash(obj* x_0) {
_start:
{
size_t x_2; 
lean::dec(x_0);
x_2 = l_mix__hash___closed__1;
return x_2;
}
}
obj* l_string_hash___boxed(obj* x_0) {
_start:
{
size_t x_1; obj* x_2; 
x_1 = l_string_hash(x_0);
x_2 = lean::box_size_t(x_1);
return x_2;
}
}
obj* _init_l_string_hashable() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_string_hash___boxed), 1, 0);
return x_0;
}
}
size_t l_nat_hash(obj* x_0) {
_start:
{
size_t x_1; 
x_1 = lean::usize_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_nat_hash___boxed(obj* x_0) {
_start:
{
size_t x_1; obj* x_2; 
x_1 = l_nat_hash(x_0);
x_2 = lean::box_size_t(x_1);
return x_2;
}
}
obj* _init_l_nat_hashable() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_hash___boxed), 1, 0);
return x_0;
}
}
void initialize_init_data_usize();
void initialize_init_data_string_default();
static bool _G_initialized = false;
void initialize_init_data_hashable() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_usize();
 initialize_init_data_string_default();
 l_mix__hash___closed__1 = _init_l_mix__hash___closed__1();
 l_mix__hash___closed__1___boxed = _init_l_mix__hash___closed__1___boxed();
 l_string_hashable = _init_l_string_hashable();
 l_nat_hashable = _init_l_nat_hashable();
}
