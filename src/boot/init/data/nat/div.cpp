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
obj* l_nat_mod___boxed(obj*, obj*);
obj* l___private_init_data_nat_div_2__div_F___boxed(obj*, obj*, obj*);
obj* l___private_init_data_nat_div_5__mod_F___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
obj* nat_mod(obj*, obj*);
}
obj* l___private_init_data_nat_div_5__mod_F(obj*, obj*, obj*);
obj* l_nat_has__div;
obj* l___private_init_data_nat_div_2__div_F(obj*, obj*, obj*);
obj* l___private_init_data_nat_div_1__div__rec__lemma;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
obj* nat_div(obj*, obj*);
}
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_nat_has__mod;
obj* l_nat_div___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* _init_l___private_init_data_nat_div_1__div__rec__lemma() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l___private_init_data_nat_div_2__div_F(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
else
{
uint8 x_7; 
x_7 = lean::nat_dec_le(x_2, x_0);
if (x_7 == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::nat_sub(x_0, x_2);
x_11 = lean::apply_3(x_1, x_10, lean::box(0), x_2);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_11, x_12);
lean::dec(x_11);
return x_13;
}
}
}
}
obj* l___private_init_data_nat_div_2__div_F___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_nat_div_2__div_F(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_nat_div___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::nat_div(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_nat_has__div() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_div___boxed), 2, 0);
return x_0;
}
}
obj* l___private_init_data_nat_div_5__mod_F(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_2);
lean::inc(x_0);
return x_0;
}
else
{
uint8 x_8; 
x_8 = lean::nat_dec_le(x_2, x_0);
if (x_8 == 0)
{
lean::dec(x_1);
lean::dec(x_2);
lean::inc(x_0);
return x_0;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::nat_sub(x_0, x_2);
x_13 = lean::apply_3(x_1, x_12, lean::box(0), x_2);
return x_13;
}
}
}
}
obj* l___private_init_data_nat_div_5__mod_F___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_nat_div_5__mod_F(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_nat_mod___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::nat_mod(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_nat_has__mod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_mod___boxed), 2, 0);
return x_0;
}
}
void initialize_init_wf();
void initialize_init_data_nat_basic();
static bool _G_initialized = false;
void initialize_init_data_nat_div() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_wf();
 initialize_init_data_nat_basic();
 l___private_init_data_nat_div_1__div__rec__lemma = _init_l___private_init_data_nat_div_1__div__rec__lemma();
lean::mark_persistent(l___private_init_data_nat_div_1__div__rec__lemma);
 l_nat_has__div = _init_l_nat_has__div();
lean::mark_persistent(l_nat_has__div);
 l_nat_has__mod = _init_l_nat_has__mod();
lean::mark_persistent(l_nat_has__mod);
}
