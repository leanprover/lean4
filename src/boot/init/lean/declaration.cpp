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
obj* l_lean_constant__info_value___boxed(obj*);
obj* l_lean_constant__info_type(obj*);
obj* l_lean_constant__info_to__constant__val___main(obj*);
obj* l_lean_constant__info_id___boxed(obj*);
obj* l_lean_constant__info_value___main___boxed(obj*);
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
obj* x_1; obj* x_2; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_2);
return x_4;
}
case 2:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_5, 1);
x_7 = lean::task_get(x_6);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
default:
{
obj* x_9; 
x_9 = lean::box(0);
return x_9;
}
}
}
}
obj* l_lean_constant__info_value___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_constant__info_value___main(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_lean_constant__info_value___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_constant__info_value(x_0);
lean::dec(x_0);
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
void initialize_init_lean_expr();
static bool _G_initialized = false;
void initialize_init_lean_declaration() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_expr();
}
