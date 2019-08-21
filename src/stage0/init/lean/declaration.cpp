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
obj* l_Lean_ConstantInfo_name(obj*);
obj* l_Task_get(obj*, obj*);
obj* l_Lean_ConstantInfo_name___boxed(obj*);
obj* l_Lean_ConstantInfo_toConstantVal(obj*);
obj* l_Lean_ConstantInfo_value___boxed(obj*);
obj* l_Lean_ConstantInfo_value(obj*);
obj* l_Lean_ConstantInfo_lparams(obj*);
uint8 l_Lean_ConstantInfo_hasValue(obj*);
obj* l_Lean_ConstantInfo_hints___boxed(obj*);
obj* l_Lean_ConstantInfo_hints(obj*);
obj* l_Lean_ConstantInfo_toConstantVal___boxed(obj*);
obj* l_Lean_ConstantInfo_type(obj*);
obj* l_Lean_ConstantInfo_type___boxed(obj*);
obj* l_Lean_ConstantInfo_lparams___boxed(obj*);
obj* l_Lean_ConstantInfo_hasValue___boxed(obj*);
obj* l_Lean_ConstantInfo_toConstantVal(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
return x_3;
}
}
obj* l_Lean_ConstantInfo_toConstantVal___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_ConstantInfo_toConstantVal(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_ConstantInfo_name(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_ConstantInfo_toConstantVal(x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_ConstantInfo_name___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_ConstantInfo_name(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_ConstantInfo_lparams(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_ConstantInfo_toConstantVal(x_1);
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_ConstantInfo_lparams___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_ConstantInfo_lparams(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_ConstantInfo_type(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_ConstantInfo_toConstantVal(x_1);
x_3 = lean::cnstr_get(x_2, 2);
lean::inc(x_3);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_ConstantInfo_type___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_ConstantInfo_type(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_ConstantInfo_value(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
case 2:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
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
obj* l_Lean_ConstantInfo_value___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_ConstantInfo_value(x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Lean_ConstantInfo_hasValue(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
case 2:
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
default: 
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
}
}
}
obj* l_Lean_ConstantInfo_hasValue___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_ConstantInfo_hasValue(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_Lean_ConstantInfo_hints(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_2, 2);
lean::inc(x_3);
return x_3;
}
else
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
}
}
obj* l_Lean_ConstantInfo_hints___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_ConstantInfo_hints(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_lean_expr(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_declaration(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_expr(w);
if (lean::io_result_is_error(w)) return w;
return w;
}
