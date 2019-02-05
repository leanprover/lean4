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
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_lean_constant__info_lparams(obj*);
obj* l_lean_constant__info_hints(obj*);
obj* l_lean_constant__info_id(obj*);
obj* l_lean_constant__info_type(obj*);
obj* l_lean_constant__info_to__constant__val___main(obj*);
obj* l_lean_constant__info_value___main(obj*);
obj* l_lean_constant__info_value(obj*);
obj* l_lean_constant__info_to__constant__val(obj*);
obj* l_task_get___rarg(obj*);
obj* l_lean_constant__info_hints___main(obj*);
obj* l_lean_constant__info_to__constant__val___main(obj* x_0) {
_start:
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
obj* l_lean_constant__info_to__constant__val(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_constant__info_to__constant__val___main(x_0);
return x_1;
}
}
obj* l_lean_constant__info_id(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_constant__info_to__constant__val___main(x_0);
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_constant__info_lparams(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_constant__info_to__constant__val___main(x_0);
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_constant__info_type(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_constant__info_to__constant__val___main(x_0);
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_constant__info_value___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
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
obj* x_10; obj* x_13; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = l_task_get___rarg(x_13);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
case 3:
{
obj* x_19; 
lean::dec(x_0);
x_19 = lean::box(0);
return x_19;
}
case 4:
{
obj* x_21; 
lean::dec(x_0);
x_21 = lean::box(0);
return x_21;
}
case 5:
{
obj* x_23; 
lean::dec(x_0);
x_23 = lean::box(0);
return x_23;
}
default:
{
obj* x_25; 
lean::dec(x_0);
x_25 = lean::box(0);
return x_25;
}
}
}
}
obj* l_lean_constant__info_value(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_constant__info_value___main(x_0);
return x_1;
}
}
obj* l_lean_constant__info_hints___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
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
x_10 = lean::box(0);
return x_10;
}
case 3:
{
obj* x_12; 
lean::dec(x_0);
x_12 = lean::box(0);
return x_12;
}
case 4:
{
obj* x_14; 
lean::dec(x_0);
x_14 = lean::box(0);
return x_14;
}
case 5:
{
obj* x_16; 
lean::dec(x_0);
x_16 = lean::box(0);
return x_16;
}
default:
{
obj* x_18; 
lean::dec(x_0);
x_18 = lean::box(0);
return x_18;
}
}
}
}
obj* l_lean_constant__info_hints(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_constant__info_hints___main(x_0);
return x_1;
}
}
void initialize_init_lean_expr();
static bool _G_initialized = false;
void initialize_init_lean_declaration() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_expr();
}
