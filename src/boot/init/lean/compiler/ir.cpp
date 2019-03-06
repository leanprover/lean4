// Lean compiler output
// Module: init.lean.compiler.ir
// Imports: init.default init.lean.name init.lean.kvmap
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
obj* l_lean_ir_alts_is__pure(obj*);
obj* l_lean_ir_jpid;
uint8 l_lean_ir_expr_is__pure___main(obj*);
uint8 l_lean_ir_expr_is__pure(obj*);
obj* l_lean_ir_alts_is__pure___boxed(obj*);
obj* l_lean_ir_fnbody_is__pure(obj*);
obj* l_lean_ir_alt_is__pure___main___boxed(obj*);
obj* l_lean_ir_fnbody_is__pure___main___boxed(obj*);
obj* l_lean_ir_alts_is__pure___main(obj*);
obj* l_lean_ir_fnbody_is__pure___main(obj*);
obj* l_lean_ir_fnbody_is__pure___boxed(obj*);
obj* l_lean_ir_fid;
obj* l_lean_ir_varid;
obj* l_lean_ir_alt_is__pure___boxed(obj*);
obj* l_lean_ir_alt_is__pure(obj*);
obj* l_lean_ir_expr_is__pure___main___boxed(obj*);
obj* l_lean_ir_alts_is__pure___main___boxed(obj*);
obj* l_lean_ir_alt_is__pure___main(obj*);
obj* l_lean_ir_expr_is__pure___boxed(obj*);
obj* _init_l_lean_ir_varid() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_fid() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_jpid() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint8 l_lean_ir_expr_is__pure___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
case 2:
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
case 9:
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
case 10:
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
case 12:
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
case 13:
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
default:
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* l_lean_ir_expr_is__pure___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_expr_is__pure___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_lean_ir_expr_is__pure(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_lean_ir_expr_is__pure___main(x_0);
return x_1;
}
}
obj* l_lean_ir_expr_is__pure___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_expr_is__pure(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_ir_fnbody_is__pure___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::cnstr_get(x_0, 1);
x_2 = lean::cnstr_get(x_0, 2);
x_3 = l_lean_ir_expr_is__pure___main(x_1);
if (x_3 == 0)
{
obj* x_4; 
x_4 = lean::box(x_3);
return x_4;
}
else
{
x_0 = x_2;
goto _start;
}
}
case 1:
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_0, 2);
x_7 = lean::cnstr_get(x_0, 3);
x_8 = l_lean_ir_expr_is__pure___main(x_6);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::box(x_8);
return x_9;
}
else
{
x_0 = x_7;
goto _start;
}
}
case 3:
{
obj* x_11; 
x_11 = lean::cnstr_get(x_0, 3);
x_0 = x_11;
goto _start;
}
case 4:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_0, 4);
x_0 = x_13;
goto _start;
}
case 10:
{
obj* x_15; 
x_15 = lean::cnstr_get(x_0, 1);
x_0 = x_15;
goto _start;
}
case 11:
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_0, 1);
x_18 = l_lean_ir_alts_is__pure___main(x_17);
return x_18;
}
case 12:
{
uint8 x_19; obj* x_20; 
x_19 = 1;
x_20 = lean::box(x_19);
return x_20;
}
case 13:
{
uint8 x_21; obj* x_22; 
x_21 = 1;
x_22 = lean::box(x_21);
return x_22;
}
default:
{
uint8 x_23; obj* x_24; 
x_23 = 0;
x_24 = lean::box(x_23);
return x_24;
}
}
}
}
obj* l_lean_ir_alts_is__pure___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; obj* x_2; 
x_1 = 1;
x_2 = lean::box(x_1);
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = l_lean_ir_alt_is__pure___main(x_3);
x_6 = lean::unbox(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
x_0 = x_4;
goto _start;
}
}
}
}
obj* l_lean_ir_alt_is__pure___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_2; 
x_1 = lean::cnstr_get(x_0, 1);
x_2 = l_lean_ir_fnbody_is__pure___main(x_1);
return x_2;
}
else
{
uint8 x_3; obj* x_4; 
x_3 = 0;
x_4 = lean::box(x_3);
return x_4;
}
}
}
obj* l_lean_ir_fnbody_is__pure___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_fnbody_is__pure___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_alts_is__pure___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_alts_is__pure___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_alt_is__pure___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_alt_is__pure___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_fnbody_is__pure(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_fnbody_is__pure___main(x_0);
return x_1;
}
}
obj* l_lean_ir_fnbody_is__pure___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_fnbody_is__pure(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_alts_is__pure(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_alts_is__pure___main(x_0);
return x_1;
}
}
obj* l_lean_ir_alts_is__pure___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_alts_is__pure(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_alt_is__pure(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_alt_is__pure___main(x_0);
return x_1;
}
}
obj* l_lean_ir_alt_is__pure___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_alt_is__pure(x_0);
lean::dec(x_0);
return x_1;
}
}
void initialize_init_default();
void initialize_init_lean_name();
void initialize_init_lean_kvmap();
static bool _G_initialized = false;
void initialize_init_lean_compiler_ir() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_default();
 initialize_init_lean_name();
 initialize_init_lean_kvmap();
 l_lean_ir_varid = _init_l_lean_ir_varid();
lean::mark_persistent(l_lean_ir_varid);
 l_lean_ir_fid = _init_l_lean_ir_fid();
lean::mark_persistent(l_lean_ir_fid);
 l_lean_ir_jpid = _init_l_lean_ir_jpid();
lean::mark_persistent(l_lean_ir_jpid);
}
