// Lean compiler output
// Module: init.control.alternative
// Imports: init.core init.control.applicative
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s6_guardb_s6___rarg(obj*, unsigned char);
obj* _l_s6_guardb_s6___main_s6___rarg_s7___boxed(obj*, obj*);
obj* _l_s6_guardb(obj*);
obj* _l_s6_guardb_s6___rarg_s7___boxed(obj*, obj*);
obj* _l_s7_failure_s6___rarg(obj*, obj*);
obj* _l_s8_optional_s6___rarg_s11___closed__1;
obj* _l_s5_guard_s6___rarg(obj*, obj*, obj*);
obj* _l_s6_assert(obj*);
obj* _l_s7_failure(obj*);
obj* _l_s6_guardb_s6___main_s6___rarg(obj*, unsigned char);
obj* _l_s6_assert_s6___rarg(obj*, obj*, obj*);
obj* _l_s8_optional_s6___rarg_s11___lambda__1(obj*);
obj* _l_s6_guardb_s6___main(obj*);
obj* _l_s8_optional_s6___rarg(obj*, obj*, obj*);
obj* _l_s8_optional(obj*);
obj* _l_s5_guard(obj*);
obj* _l_s7_failure_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_3; obj* x_6; 
lean::dec(x_1);
x_3 = lean::cnstr_get(x_0, 2);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::apply_1(x_3, lean::box(0));
return x_6;
}
}
obj* _l_s7_failure(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s7_failure_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_guard_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{

lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_8; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::apply_1(x_5, lean::box(0));
return x_8;
}
else
{
obj* x_10; obj* x_13; unsigned char x_16; obj* x_17; obj* x_18; 
lean::dec(x_2);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = 0;
x_17 = lean::box(x_16);
x_18 = lean::apply_2(x_13, lean::box(0), x_17);
return x_18;
}
}
}
obj* _l_s5_guard(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_guard_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s6_assert_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{

lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_8; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::apply_1(x_5, lean::box(0));
return x_8;
}
else
{
obj* x_10; obj* x_13; obj* x_16; 
lean::dec(x_2);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::apply_2(x_13, lean::box(0), lean::box(0));
return x_16;
}
}
}
obj* _l_s6_assert(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_assert_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s6_guardb_s6___main_s6___rarg(obj* x_0, unsigned char x_1) {
{

if (x_1 == 0)
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 2);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::apply_1(x_2, lean::box(0));
return x_5;
}
else
{
obj* x_6; obj* x_9; unsigned char x_12; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = 0;
x_13 = lean::box(x_12);
x_14 = lean::apply_2(x_9, lean::box(0), x_13);
return x_14;
}
}
}
obj* _l_s6_guardb_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_guardb_s6___main_s6___rarg_s7___boxed), 2, 0);
return x_2;
}
}
obj* _l_s6_guardb_s6___main_s6___rarg_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = _l_s6_guardb_s6___main_s6___rarg(x_0, x_2);
return x_3;
}
}
obj* _l_s6_guardb_s6___rarg(obj* x_0, unsigned char x_1) {
{
obj* x_2; 
x_2 = _l_s6_guardb_s6___main_s6___rarg(x_0, x_1);
return x_2;
}
}
obj* _l_s6_guardb(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_guardb_s6___rarg_s7___boxed), 2, 0);
return x_2;
}
}
obj* _l_s6_guardb_s6___rarg_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = _l_s6_guardb_s6___rarg(x_0, x_2);
return x_3;
}
}
obj* _l_s8_optional_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_17; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_14 = _l_s8_optional_s6___rarg_s11___closed__1;
lean::inc(x_14);
x_16 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_14, x_2);
x_17 = lean::cnstr_get(x_6, 1);
lean::inc(x_17);
lean::dec(x_6);
x_20 = lean::box(0);
x_21 = lean::apply_2(x_17, lean::box(0), x_20);
x_22 = lean::apply_3(x_4, lean::box(0), x_16, x_21);
return x_22;
}
}
obj* _init__l_s8_optional_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_optional_s6___rarg_s11___lambda__1), 1, 0);
return x_0;
}
}
obj* _l_s8_optional_s6___rarg_s11___lambda__1(obj* x_0) {
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s8_optional(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_optional_s6___rarg), 3, 0);
return x_2;
}
}
void _l_initialize__l_s4_init_s4_core();
void _l_initialize__l_s4_init_s7_control_s11_applicative();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s7_control_s11_alternative() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_core();
 _l_initialize__l_s4_init_s7_control_s11_applicative();
 _l_s8_optional_s6___rarg_s11___closed__1 = _init__l_s8_optional_s6___rarg_s11___closed__1();
}
