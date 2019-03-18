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
obj* l_lean_constant__info_id___boxed(obj*);
obj* l_lean_constant__info_value___main(obj*);
obj* l_lean_constant__info_to__constant__val___main___boxed(obj*);
obj* l_lean_constant__info_hints___boxed(obj*);
obj* l_lean_constant__info_lparams___boxed(obj*);
obj* l_lean_constant__info_hints___main___boxed(obj*);
obj* l_lean_constant__info_to__constant__val___boxed(obj*);
obj* l_lean_constant__info_value(obj*);
obj* l_lean_constant__info_type___boxed(obj*);
obj* l_lean_constant__info_to__constant__val(obj*);
obj* l_lean_constant__info_hints___main(obj*);
obj* l_lean_constant__info_to__constant__val___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* l_lean_constant__info_to__constant__val___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_constant__info_to__constant__val___main(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_lean_constant__info_to__constant__val___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_constant__info_to__constant__val(x_0);
lean::dec(x_0);
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
obj* l_lean_constant__info_id___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_constant__info_id(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_lean_constant__info_lparams___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_constant__info_lparams(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_lean_constant__info_type___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_constant__info_type(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_8; obj* x_11; obj* x_14; obj* x_16; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::task_get(x_11);
lean::dec(x_11);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_14);
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
obj* x_1; obj* x_2; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
return x_2;
}
default:
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
}
}
}
obj* l_lean_constant__info_hints___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_constant__info_hints___main(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_lean_constant__info_hints___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_constant__info_hints(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* initialize_init_lean_expr(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_declaration(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_expr(w);
return w;
}
