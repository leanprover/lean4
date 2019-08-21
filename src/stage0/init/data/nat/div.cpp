// Lean compiler output
// Module: init.data.nat.div
// Imports: init.wf init.data.nat.basic
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
obj* l___private_init_data_nat_div_2__div_F___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l___private_init_data_nat_div_5__mod_F___boxed(obj*, obj*, obj*);
obj* l_Nat_div___boxed(obj*, obj*);
obj* l_Nat_HasDiv___closed__1;
obj* l_Nat_HasMod___closed__1;
obj* l___private_init_data_nat_div_5__mod_F(obj*, obj*, obj*);
obj* l___private_init_data_nat_div_2__div_F(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
namespace lean {
obj* nat_mod(obj*, obj*);
}
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Nat_HasMod;
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_Nat_mod___boxed(obj*, obj*);
obj* l_Nat_HasDiv;
obj* l___private_init_data_nat_div_2__div_F(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
obj* x_6; 
lean::dec(x_3);
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::nat_dec_le(x_3, x_1);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
x_8 = lean::mk_nat_obj(0u);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::nat_sub(x_1, x_3);
x_10 = lean::apply_3(x_2, x_9, lean::box(0), x_3);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_10, x_11);
lean::dec(x_10);
return x_12;
}
}
}
}
obj* l___private_init_data_nat_div_2__div_F___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_nat_div_2__div_F(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Nat_div___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::nat_div(x_1, x_2);
return x_3;
}
}
obj* _init_l_Nat_HasDiv___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_div___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Nat_HasDiv() {
_start:
{
obj* x_1; 
x_1 = l_Nat_HasDiv___closed__1;
return x_1;
}
}
obj* l___private_init_data_nat_div_5__mod_F(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
else
{
uint8 x_6; 
x_6 = lean::nat_dec_le(x_3, x_1);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::nat_sub(x_1, x_3);
x_8 = lean::apply_3(x_2, x_7, lean::box(0), x_3);
return x_8;
}
}
}
}
obj* l___private_init_data_nat_div_5__mod_F___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_nat_div_5__mod_F(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Nat_mod___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::nat_mod(x_1, x_2);
return x_3;
}
}
obj* _init_l_Nat_HasMod___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_mod___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Nat_HasMod() {
_start:
{
obj* x_1; 
x_1 = l_Nat_HasMod___closed__1;
return x_1;
}
}
obj* initialize_init_wf(obj*);
obj* initialize_init_data_nat_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_nat_div(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_wf(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_nat_basic(w);
if (lean::io_result_is_error(w)) return w;
l_Nat_HasDiv___closed__1 = _init_l_Nat_HasDiv___closed__1();
lean::mark_persistent(l_Nat_HasDiv___closed__1);
l_Nat_HasDiv = _init_l_Nat_HasDiv();
lean::mark_persistent(l_Nat_HasDiv);
l_Nat_HasMod___closed__1 = _init_l_Nat_HasMod___closed__1();
lean::mark_persistent(l_Nat_HasMod___closed__1);
l_Nat_HasMod = _init_l_Nat_HasMod();
lean::mark_persistent(l_Nat_HasMod);
return w;
}
