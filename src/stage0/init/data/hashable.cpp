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
usize l_string_hash(obj*);
obj* l_string_hashable;
obj* l_nat_hashable;
obj* l_nat_hash___boxed(obj*);
obj* l_mix__hash___boxed(obj*, obj*);
usize l_nat_hash(obj*);
usize l_mix__hash(usize, usize);
namespace lean {
usize usize_of_nat(obj*);
}
obj* l_string_hash___boxed(obj*);
usize l_mix__hash(usize x_0, usize x_1) {
_start:
{
usize x_2; 
x_2 = 0;
return x_2;
}
}
obj* l_mix__hash___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; usize x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = l_mix__hash(x_2, x_3);
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
usize l_string_hash(obj* x_0) {
_start:
{
usize x_1; 
x_1 = 0;
return x_1;
}
}
obj* l_string_hash___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = l_string_hash(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
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
usize l_nat_hash(obj* x_0) {
_start:
{
usize x_1; 
x_1 = lean::usize_of_nat(x_0);
return x_1;
}
}
obj* l_nat_hash___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = l_nat_hash(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
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
obj* initialize_init_data_uint(obj*);
obj* initialize_init_data_string_default(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_hashable(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_string_default(w);
 l_string_hashable = _init_l_string_hashable();
lean::mark_persistent(l_string_hashable);
 l_nat_hashable = _init_l_nat_hashable();
lean::mark_persistent(l_nat_hashable);
return w;
}
