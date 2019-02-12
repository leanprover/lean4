// Lean compiler output
// Module: init.lean.ir.ir
// Imports: init.data.rbmap.default init.data.int.default init.control.state init.control.except init.control.combinators init.lean.name
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
obj* l_lean_ir_decl_is__definition___boxed(obj*);
obj* l_lean_ir_var;
uint8 l_lean_ir_decl_is__definition___main(obj*);
obj* l_lean_ir_decl_is__definition___main___boxed(obj*);
obj* l_lean_ir_environment;
obj* l_lean_ir_decl_header___main(obj*);
obj* l_lean_ir_decl_header(obj*);
obj* l_lean_ir_blockid;
obj* l_lean_ir_tag;
uint8 l_lean_ir_decl_is__definition(obj*);
obj* l_lean_ir_decl_name(obj*);
obj* l_lean_ir_fnid;
obj* _init_l_lean_ir_tag() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_ir_var() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_ir_fnid() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_ir_blockid() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
uint8 l_lean_ir_decl_is__definition___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_2; 
lean::dec(x_0);
x_2 = 0;
return x_2;
}
else
{
uint8 x_4; 
lean::dec(x_0);
x_4 = 1;
return x_4;
}
}
}
obj* l_lean_ir_decl_is__definition___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_decl_is__definition___main(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
uint8 l_lean_ir_decl_is__definition(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_lean_ir_decl_is__definition___main(x_0);
return x_1;
}
}
obj* l_lean_ir_decl_is__definition___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_decl_is__definition(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_lean_ir_decl_header___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_decl_header(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_decl_header___main(x_0);
return x_1;
}
}
obj* l_lean_ir_decl_name(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_ir_decl_header___main(x_0);
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_ir_environment() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
void initialize_init_data_rbmap_default();
void initialize_init_data_int_default();
void initialize_init_control_state();
void initialize_init_control_except();
void initialize_init_control_combinators();
void initialize_init_lean_name();
static bool _G_initialized = false;
void initialize_init_lean_ir_ir() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_rbmap_default();
 initialize_init_data_int_default();
 initialize_init_control_state();
 initialize_init_control_except();
 initialize_init_control_combinators();
 initialize_init_lean_name();
 l_lean_ir_tag = _init_l_lean_ir_tag();
 l_lean_ir_var = _init_l_lean_ir_var();
 l_lean_ir_fnid = _init_l_lean_ir_fnid();
 l_lean_ir_blockid = _init_l_lean_ir_blockid();
 l_lean_ir_environment = _init_l_lean_ir_environment();
}
