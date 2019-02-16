// Lean compiler output
// Module: init.lean.declaration
// Imports: init.lean.expr
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
case 1:
{
obj* x_1; obj* x_4; obj* x_7; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_4);
return x_7;
}
case 2:
{
obj* x_8; obj* x_11; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = l_task_get___rarg(x_11);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
default:
{
obj* x_17; 
lean::dec(x_0);
x_17 = lean::box(0);
return x_17;
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
case 1:
{
obj* x_1; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
return x_4;
}
default:
{
obj* x_8; 
lean::dec(x_0);
x_8 = lean::box(0);
return x_8;
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
