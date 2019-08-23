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
extern "C" {
obj* l_guard___boxed(obj*);
obj* l_guardb___rarg___boxed(obj*, obj*);
obj* l_alternativeHasOrelse___rarg(obj*);
obj* l_failure___boxed(obj*);
obj* l_guard(obj*);
obj* l_assert___rarg(obj*, obj*, uint8);
obj* l_optional___rarg___lambda__1(obj*);
obj* l_guard___rarg(obj*, obj*, uint8);
obj* l_assert___boxed(obj*);
obj* l_assert(obj*);
obj* l_optional___boxed(obj*);
obj* l_guard___rarg___boxed(obj*, obj*, obj*);
obj* l_assert___rarg___boxed(obj*, obj*, obj*);
obj* l_guardb___boxed(obj*);
obj* l_optional___rarg(obj*, obj*, obj*);
obj* l_failure___rarg(obj*, obj*);
obj* l_failure(obj*);
obj* l_guardb(obj*);
obj* l_optional(obj*);
obj* l_optional___rarg___closed__1;
obj* l_alternativeHasOrelse(obj*, obj*);
obj* l_guardb___rarg(obj*, uint8);
obj* l_alternativeHasOrelse___boxed(obj*, obj*);
obj* l_alternativeHasOrelse___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
lean::dec(x_1);
x_3 = lean::apply_1(x_2, lean::box(0));
return x_3;
}
}
obj* l_alternativeHasOrelse(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_alternativeHasOrelse___rarg), 1, 0);
return x_3;
}
}
obj* l_alternativeHasOrelse___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_alternativeHasOrelse(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_failure___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::apply_1(x_3, lean::box(0));
return x_4;
}
}
obj* l_failure(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_failure___rarg), 2, 0);
return x_2;
}
}
obj* l_failure___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_failure(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_guard___rarg(obj* x_1, obj* x_2, uint8 x_3) {
_start:
{
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::apply_1(x_4, lean::box(0));
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::box(0);
x_9 = lean::apply_2(x_7, lean::box(0), x_8);
return x_9;
}
}
}
obj* l_guard(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_guard___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_guard___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
lean::dec(x_3);
x_5 = l_guard___rarg(x_1, x_2, x_4);
return x_5;
}
}
obj* l_guard___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_guard(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_assert___rarg(obj* x_1, obj* x_2, uint8 x_3) {
_start:
{
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::apply_1(x_4, lean::box(0));
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::apply_2(x_7, lean::box(0), lean::box(0));
return x_8;
}
}
}
obj* l_assert(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_assert___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_assert___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
lean::dec(x_3);
x_5 = l_assert___rarg(x_1, x_2, x_4);
return x_5;
}
}
obj* l_assert___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_assert(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_guardb___rarg(obj* x_1, uint8 x_2) {
_start:
{
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::apply_1(x_3, lean::box(0));
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::box(0);
x_8 = lean::apply_2(x_6, lean::box(0), x_7);
return x_8;
}
}
}
obj* l_guardb(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_guardb___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_guardb___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
lean::dec(x_2);
x_4 = l_guardb___rarg(x_1, x_3);
return x_4;
}
}
obj* l_guardb___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_guardb(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_optional___rarg___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_optional___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_optional___rarg___lambda__1), 1, 0);
return x_1;
}
}
obj* l_optional___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_8 = l_optional___rarg___closed__1;
x_9 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_8, x_3);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::box(0);
x_12 = lean::apply_2(x_10, lean::box(0), x_11);
x_13 = lean::apply_3(x_4, lean::box(0), x_9, x_12);
return x_13;
}
}
obj* l_optional(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_optional___rarg), 3, 0);
return x_2;
}
}
obj* l_optional___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_optional(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_core(obj*);
obj* initialize_init_control_applicative(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_alternative(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_core(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_applicative(w);
if (lean::io_result_is_error(w)) return w;
l_optional___rarg___closed__1 = _init_l_optional___rarg___closed__1();
lean::mark_persistent(l_optional___rarg___closed__1);
return w;
}
}
