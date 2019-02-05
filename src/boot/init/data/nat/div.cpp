// Lean compiler output
// Module: init.data.nat.div
// Imports: init.wf init.data.nat.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l___private_578911941__mod_F(obj*, obj*, obj*);
obj* l_nat_has__div;
obj* l___private_3925169175__div_F(obj*, obj*, obj*);
obj* l___private_56172073__div__rec__lemma;
obj* l_nat_has__mod;
obj* _init_l___private_56172073__div__rec__lemma() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l___private_3925169175__div_F(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_lt(x_3, x_2);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_10 = lean::mk_nat_obj(0u);
return x_10;
}
else
{
obj* x_12; 
lean::dec(x_4);
x_12 = lean::nat_dec_le(x_2, x_0);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; 
lean::dec(x_1);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_17 = lean::mk_nat_obj(0u);
return x_17;
}
else
{
obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_12);
x_19 = lean::nat_sub(x_0, x_2);
lean::dec(x_0);
x_21 = lean::apply_3(x_1, x_19, lean::box(0), x_2);
x_22 = lean::mk_nat_obj(1u);
x_23 = lean::nat_add(x_21, x_22);
lean::dec(x_22);
lean::dec(x_21);
return x_23;
}
}
}
}
obj* _init_l_nat_has__div() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::nat_div), 2, 0);
return x_0;
}
}
obj* l___private_578911941__mod_F(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_lt(x_3, x_2);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_0;
}
else
{
obj* x_10; 
lean::dec(x_4);
x_10 = lean::nat_dec_le(x_2, x_0);
if (lean::obj_tag(x_10) == 0)
{
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_2);
return x_0;
}
else
{
obj* x_15; obj* x_17; 
lean::dec(x_10);
x_15 = lean::nat_sub(x_0, x_2);
lean::dec(x_0);
x_17 = lean::apply_3(x_1, x_15, lean::box(0), x_2);
return x_17;
}
}
}
}
obj* _init_l_nat_has__mod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::nat_mod), 2, 0);
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
 l___private_56172073__div__rec__lemma = _init_l___private_56172073__div__rec__lemma();
 l_nat_has__div = _init_l_nat_has__div();
 l_nat_has__mod = _init_l_nat_has__mod();
}
