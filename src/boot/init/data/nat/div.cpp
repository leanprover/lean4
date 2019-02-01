// Lean compiler output
// Module: init.data.nat.div
// Imports: init.wf init.data.nat.basic
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;
obj* _l_s9___private_56172073__s15_div__rec__lemma;
obj* _l_s9___private_3925169175__s3_div_s1_F(obj*, obj*, obj*);
obj* _l_s3_nat_s8_has__div;
obj* _l_s9___private_578911941__s3_mod_s1_F(obj*, obj*, obj*);
obj* _l_s3_nat_s8_has__mod;
obj* _init__l_s9___private_56172073__s15_div__rec__lemma() {
{
obj* x_0;
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s9___private_3925169175__s3_div_s1_F(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
obj* x_4;
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_lt(x_3, x_2);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_10;
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_1);
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
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
x_17 = lean::mk_nat_obj(0u);
return x_17;
}
else
{
obj* x_19;
obj* x_21;
obj* x_22;
obj* x_23;
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
obj* _init__l_s3_nat_s8_has__div() {
{
obj* x_0;
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::nat_div), 2, 0);
return x_0;
}
}
obj* _l_s9___private_578911941__s3_mod_s1_F(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
obj* x_4;
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
obj* x_15;
obj* x_17;
lean::dec(x_10);
x_15 = lean::nat_sub(x_0, x_2);
lean::dec(x_0);
x_17 = lean::apply_3(x_1, x_15, lean::box(0), x_2);
return x_17;
}
}
}
}
obj* _init__l_s3_nat_s8_has__mod() {
{
obj* x_0;
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::nat_mod), 2, 0);
return x_0;
}
}
void _l_initialize__l_s4_init_s2_wf();
void _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s3_nat_s3_div() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s2_wf();
 _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic();
 _l_s9___private_56172073__s15_div__rec__lemma = _init__l_s9___private_56172073__s15_div__rec__lemma();
 _l_s3_nat_s8_has__div = _init__l_s3_nat_s8_has__div();
 _l_s3_nat_s8_has__mod = _init__l_s3_nat_s8_has__mod();
}
