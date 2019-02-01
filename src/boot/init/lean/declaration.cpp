// Lean compiler output
// Module: init.lean.declaration
// Imports: init.lean.expr
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s4_lean_s14_constant__info_s5_value(obj*);
obj* _l_s4_lean_s14_constant__info_s17_to__constant__val(obj*);
obj* _l_s4_lean_s14_constant__info_s5_value_s6___main(obj*);
obj* _l_s4_lean_s14_constant__info_s7_lparams(obj*);
obj* _l_s4_task_s3_get(obj*);
obj* _l_s4_lean_s14_constant__info_s2_id(obj*);
obj* _l_s4_lean_s14_constant__info_s5_hints_s6___main(obj*);
obj* _l_s4_lean_s14_constant__info_s5_hints(obj*);
obj* _l_s4_lean_s14_constant__info_s4_type(obj*);
obj* _l_s4_lean_s14_constant__info_s17_to__constant__val_s6___main(obj*);
obj* _l_s4_lean_s14_constant__info_s17_to__constant__val_s6___main(obj* x_0) {
{
obj* x_1; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
return x_4;
}
}
obj* _l_s4_lean_s14_constant__info_s17_to__constant__val(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s4_lean_s14_constant__info_s17_to__constant__val_s6___main(x_0);
return x_1;
}
}
obj* _l_s4_lean_s14_constant__info_s2_id(obj* x_0) {
{
obj* x_1; obj* x_2; 
x_1 = _l_s4_lean_s14_constant__info_s17_to__constant__val_s6___main(x_0);
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
return x_2;
}
}
obj* _l_s4_lean_s14_constant__info_s7_lparams(obj* x_0) {
{
obj* x_1; obj* x_2; 
x_1 = _l_s4_lean_s14_constant__info_s17_to__constant__val_s6___main(x_0);
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
return x_2;
}
}
obj* _l_s4_lean_s14_constant__info_s4_type(obj* x_0) {
{
obj* x_1; obj* x_2; 
x_1 = _l_s4_lean_s14_constant__info_s17_to__constant__val_s6___main(x_0);
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
lean::dec(x_1);
return x_2;
}
}
obj* _l_s4_lean_s14_constant__info_s5_value_s6___main(obj* x_0) {
{

switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_cnstr(0, 0, 0);
;
return x_2;
}
case 1:
{
obj* x_3; obj* x_6; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_6);
return x_9;
}
case 2:
{
obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_18; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = _l_s4_task_s3_get(lean::box(0));
x_17 = lean::apply_1(x_16, x_13);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
case 3:
{
obj* x_20; 
lean::dec(x_0);
x_20 = lean::alloc_cnstr(0, 0, 0);
;
return x_20;
}
case 4:
{
obj* x_22; 
lean::dec(x_0);
x_22 = lean::alloc_cnstr(0, 0, 0);
;
return x_22;
}
case 5:
{
obj* x_24; 
lean::dec(x_0);
x_24 = lean::alloc_cnstr(0, 0, 0);
;
return x_24;
}
default:
{
obj* x_26; 
lean::dec(x_0);
x_26 = lean::alloc_cnstr(0, 0, 0);
;
return x_26;
}
}
}
}
obj* _l_s4_lean_s14_constant__info_s5_value(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s4_lean_s14_constant__info_s5_value_s6___main(x_0);
return x_1;
}
}
obj* _l_s4_lean_s14_constant__info_s5_hints_s6___main(obj* x_0) {
{

switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_cnstr(0, 0, 0);
;
return x_2;
}
case 1:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
return x_6;
}
case 2:
{
obj* x_10; 
lean::dec(x_0);
x_10 = lean::alloc_cnstr(0, 0, 0);
;
return x_10;
}
case 3:
{
obj* x_12; 
lean::dec(x_0);
x_12 = lean::alloc_cnstr(0, 0, 0);
;
return x_12;
}
case 4:
{
obj* x_14; 
lean::dec(x_0);
x_14 = lean::alloc_cnstr(0, 0, 0);
;
return x_14;
}
case 5:
{
obj* x_16; 
lean::dec(x_0);
x_16 = lean::alloc_cnstr(0, 0, 0);
;
return x_16;
}
default:
{
obj* x_18; 
lean::dec(x_0);
x_18 = lean::alloc_cnstr(0, 0, 0);
;
return x_18;
}
}
}
}
obj* _l_s4_lean_s14_constant__info_s5_hints(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s4_lean_s14_constant__info_s5_hints_s6___main(x_0);
return x_1;
}
}
void _l_initialize__l_s4_init_s4_lean_s4_expr();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s11_declaration() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_lean_s4_expr();
}
