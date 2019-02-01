// Lean compiler output
// Module: init.lean.ir.ir
// Imports: init.data.rbmap.default init.data.int.default init.control.state init.control.except init.control.combinators init.lean.name
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s4_lean_s2_ir_s4_decl_s14_is__definition_s6___main_s7___boxed(obj*);
obj* _l_s4_lean_s2_ir_s4_fnid;
obj* _l_s4_lean_s2_ir_s4_decl_s4_name(obj*);
obj* _l_s4_lean_s2_ir_s3_var;
unsigned char _l_s4_lean_s2_ir_s4_decl_s14_is__definition(obj*);
obj* _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(obj*);
unsigned char _l_s4_lean_s2_ir_s4_decl_s14_is__definition_s6___main(obj*);
obj* _l_s4_lean_s2_ir_s11_environment;
obj* _l_s4_lean_s2_ir_s4_decl_s14_is__definition_s7___boxed(obj*);
obj* _l_s4_lean_s2_ir_s7_blockid;
obj* _l_s4_lean_s2_ir_s4_decl_s6_header(obj*);
obj* _l_s4_lean_s2_ir_s3_tag;
obj* _init__l_s4_lean_s2_ir_s3_tag() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_var() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s4_fnid() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s7_blockid() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
unsigned char _l_s4_lean_s2_ir_s4_decl_s14_is__definition_s6___main(obj* x_0) {
{

if (lean::obj_tag(x_0) == 0)
{
unsigned char x_2; 
lean::dec(x_0);
x_2 = 0;
return x_2;
}
else
{
unsigned char x_4; 
lean::dec(x_0);
x_4 = 1;
return x_4;
}
}
}
obj* _l_s4_lean_s2_ir_s4_decl_s14_is__definition_s6___main_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = _l_s4_lean_s2_ir_s4_decl_s14_is__definition_s6___main(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
unsigned char _l_s4_lean_s2_ir_s4_decl_s14_is__definition(obj* x_0) {
{
unsigned char x_1; 
x_1 = _l_s4_lean_s2_ir_s4_decl_s14_is__definition_s6___main(x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s4_decl_s14_is__definition_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = _l_s4_lean_s2_ir_s4_decl_s14_is__definition(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(obj* x_0) {
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s4_decl_s6_header(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s4_decl_s4_name(obj* x_0) {
{
obj* x_1; obj* x_2; 
x_1 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_0);
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
return x_2;
}
}
obj* _init__l_s4_lean_s2_ir_s11_environment() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
void _l_initialize__l_s4_init_s4_data_s5_rbmap_s7_default();
void _l_initialize__l_s4_init_s4_data_s3_int_s7_default();
void _l_initialize__l_s4_init_s7_control_s5_state();
void _l_initialize__l_s4_init_s7_control_s6_except();
void _l_initialize__l_s4_init_s7_control_s11_combinators();
void _l_initialize__l_s4_init_s4_lean_s4_name();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s2_ir_s2_ir() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s5_rbmap_s7_default();
 _l_initialize__l_s4_init_s4_data_s3_int_s7_default();
 _l_initialize__l_s4_init_s7_control_s5_state();
 _l_initialize__l_s4_init_s7_control_s6_except();
 _l_initialize__l_s4_init_s7_control_s11_combinators();
 _l_initialize__l_s4_init_s4_lean_s4_name();
 _l_s4_lean_s2_ir_s3_tag = _init__l_s4_lean_s2_ir_s3_tag();
 _l_s4_lean_s2_ir_s3_var = _init__l_s4_lean_s2_ir_s3_var();
 _l_s4_lean_s2_ir_s4_fnid = _init__l_s4_lean_s2_ir_s4_fnid();
 _l_s4_lean_s2_ir_s7_blockid = _init__l_s4_lean_s2_ir_s7_blockid();
 _l_s4_lean_s2_ir_s11_environment = _init__l_s4_lean_s2_ir_s11_environment();
}
