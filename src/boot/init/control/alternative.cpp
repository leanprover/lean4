// Lean compiler output
// Module: init.control.alternative
// Imports: init.core init.control.applicative
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
obj* l_guard___boxed(obj*);
obj* l_guardb___rarg___boxed(obj*, obj*);
obj* l_failure___boxed(obj*);
obj* l_guard(obj*);
obj* l_guardb___main(obj*);
obj* l_guardb___main___boxed(obj*);
obj* l_assert___rarg(obj*, obj*, uint8);
obj* l_guardb___main___rarg___boxed(obj*, obj*);
obj* l_optional___rarg___lambda__1(obj*);
obj* l_guard___rarg(obj*, obj*, uint8);
obj* l_optional___rarg___lambda__1___boxed(obj*);
obj* l_assert___boxed(obj*);
obj* l_assert(obj*);
obj* l_optional___boxed(obj*);
obj* l_guard___rarg___boxed(obj*, obj*, obj*);
obj* l_failure___rarg___boxed(obj*, obj*);
obj* l_guardb___main___rarg(obj*, uint8);
obj* l_assert___rarg___boxed(obj*, obj*, obj*);
obj* l_guardb___boxed(obj*);
obj* l_optional___rarg(obj*, obj*, obj*);
obj* l_failure___rarg(obj*, obj*);
obj* l_failure(obj*);
obj* l_guardb(obj*);
obj* l_optional___rarg___boxed(obj*, obj*, obj*);
obj* l_optional(obj*);
obj* l_optional___rarg___closed__1;
obj* l_guardb___rarg(obj*, uint8);
obj* l_failure___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 2);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::apply_1(x_2, lean::box(0));
return x_5;
}
}
obj* l_failure(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_failure___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_failure___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_failure___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_failure___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_failure(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_guard___rarg(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
if (x_2 == 0)
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 2);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::apply_1(x_3, lean::box(0));
return x_6;
}
else
{
obj* x_7; obj* x_10; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::box(0);
x_14 = lean::apply_2(x_10, lean::box(0), x_13);
return x_14;
}
}
}
obj* l_guard(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_guard___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_guard___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_guard___rarg(x_0, x_1, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_guard___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_guard(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_assert___rarg(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
if (x_2 == 0)
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 2);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::apply_1(x_3, lean::box(0));
return x_6;
}
else
{
obj* x_7; obj* x_10; obj* x_13; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::apply_2(x_10, lean::box(0), lean::box(0));
return x_13;
}
}
}
obj* l_assert(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_assert___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_assert___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_assert___rarg(x_0, x_1, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_assert___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_assert(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_guardb___main___rarg(obj* x_0, uint8 x_1) {
_start:
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
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
}
}
obj* l_guardb___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_guardb___main___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_guardb___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = l_guardb___main___rarg(x_0, x_2);
return x_3;
}
}
obj* l_guardb___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_guardb___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_guardb___rarg(obj* x_0, uint8 x_1) {
_start:
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
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
}
}
obj* l_guardb(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_guardb___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_guardb___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = l_guardb___rarg(x_0, x_2);
return x_3;
}
}
obj* l_guardb___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_guardb(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_optional___rarg___lambda__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
return x_2;
}
}
obj* _init_l_optional___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_optional___rarg___lambda__1___boxed), 1, 0);
return x_0;
}
}
obj* l_optional___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_18; obj* x_19; obj* x_20; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_13 = l_optional___rarg___closed__1;
x_14 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_13, x_2);
x_15 = lean::cnstr_get(x_5, 1);
lean::inc(x_15);
lean::dec(x_5);
x_18 = lean::box(0);
x_19 = lean::apply_2(x_15, lean::box(0), x_18);
x_20 = lean::apply_3(x_3, lean::box(0), x_14, x_19);
return x_20;
}
}
obj* l_optional(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_optional___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_optional___rarg___lambda__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_optional___rarg___lambda__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_optional___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_optional___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_optional___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_optional(x_0);
lean::dec(x_0);
return x_1;
}
}
void initialize_init_core();
void initialize_init_control_applicative();
static bool _G_initialized = false;
void initialize_init_control_alternative() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_core();
 initialize_init_control_applicative();
 l_optional___rarg___closed__1 = _init_l_optional___rarg___closed__1();
lean::mark_persistent(l_optional___rarg___closed__1);
}
