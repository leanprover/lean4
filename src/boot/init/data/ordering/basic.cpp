// Lean compiler output
// Module: init.data.ordering.basic
// Imports: init.data.repr
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
unsigned char _l_s8_ordering_s8_or__else(unsigned char, unsigned char);
obj* _l_s8_ordering_s9_has__repr_s7___boxed(obj*);
obj* _l_s8_ordering_s4_swap_s6___main_s7___boxed(obj*);
unsigned char _l_s8_ordering_s8_or__else_s6___main(unsigned char, unsigned char);
unsigned char _l_s8_ordering_s4_swap(unsigned char);
unsigned char _l_s8_ordering_s4_swap_s6___main(unsigned char);
obj* _l_s3_cmp(obj*, obj*);
obj* _l_s10_cmp__using(obj*, obj*);
obj* _l_s8_ordering_s9_has__repr_s11___closed__3;
obj* _l_s8_ordering_s8_or__else_s6___main_s7___boxed(obj*, obj*);
obj* _l_s10_cmp__using_s6___rarg_s7___boxed(obj*, obj*, obj*);
unsigned char _l_s3_cmp_s6___rarg(obj*, obj*, obj*);
obj* _l_s8_ordering_s9_has__repr(unsigned char);
obj* _l_s8_ordering_s4_swap_s7___boxed(obj*);
obj* _l_s8_ordering_s13_decidable__eq(unsigned char, unsigned char);
obj* _l_s8_ordering_s8_or__else_s7___boxed(obj*, obj*);
obj* _l_s8_ordering_s9_has__repr_s11___closed__1;
obj* _l_s8_ordering_s9_has__repr_s11___closed__2;
unsigned char _l_s10_cmp__using_s6___rarg(obj*, obj*, obj*);
obj* _l_s8_ordering_s13_decidable__eq_s7___boxed(obj*, obj*);
obj* _l_s3_cmp_s6___rarg_s7___boxed(obj*, obj*, obj*);
obj* _l_s8_ordering_s9_has__repr(unsigned char x_0) {
_start:
{
switch (x_0) {
case 0:
{
obj* x_1; 
x_1 = _l_s8_ordering_s9_has__repr_s11___closed__1;
lean::inc(x_1);
return x_1;
}
case 1:
{
obj* x_3; 
x_3 = _l_s8_ordering_s9_has__repr_s11___closed__2;
lean::inc(x_3);
return x_3;
}
default:
{
obj* x_5; 
x_5 = _l_s8_ordering_s9_has__repr_s11___closed__3;
lean::inc(x_5);
return x_5;
}
}
}
}
obj* _init__l_s8_ordering_s9_has__repr_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lt");
return x_0;
}
}
obj* _init__l_s8_ordering_s9_has__repr_s11___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("eq");
return x_0;
}
}
obj* _init__l_s8_ordering_s9_has__repr_s11___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("gt");
return x_0;
}
}
obj* _l_s8_ordering_s9_has__repr_s7___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = _l_s8_ordering_s9_has__repr(x_1);
return x_2;
}
}
unsigned char _l_s8_ordering_s4_swap_s6___main(unsigned char x_0) {
_start:
{
switch (x_0) {
case 0:
{
unsigned char x_1; 
x_1 = 2;
return x_1;
}
case 1:
{
return x_0;
}
default:
{
unsigned char x_2; 
x_2 = 0;
return x_2;
}
}
}
}
obj* _l_s8_ordering_s4_swap_s6___main_s7___boxed(obj* x_0) {
_start:
{
unsigned char x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = _l_s8_ordering_s4_swap_s6___main(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s8_ordering_s4_swap(unsigned char x_0) {
_start:
{
unsigned char x_1; 
x_1 = _l_s8_ordering_s4_swap_s6___main(x_0);
return x_1;
}
}
obj* _l_s8_ordering_s4_swap_s7___boxed(obj* x_0) {
_start:
{
unsigned char x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = _l_s8_ordering_s4_swap(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s8_ordering_s8_or__else_s6___main(unsigned char x_0, unsigned char x_1) {
_start:
{
switch (x_0) {
case 0:
{
return x_0;
}
case 1:
{
return x_1;
}
default:
{
return x_0;
}
}
}
}
obj* _l_s8_ordering_s8_or__else_s6___main_s7___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; unsigned char x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s8_ordering_s8_or__else_s6___main(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
unsigned char _l_s8_ordering_s8_or__else(unsigned char x_0, unsigned char x_1) {
_start:
{
unsigned char x_2; 
x_2 = _l_s8_ordering_s8_or__else_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s8_ordering_s8_or__else_s7___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; unsigned char x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s8_ordering_s8_or__else(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
unsigned char _l_s10_cmp__using_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_6 = lean::apply_2(x_0, x_1, x_2);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; 
lean::dec(x_6);
x_8 = lean::apply_2(x_0, x_2, x_1);
if (lean::obj_tag(x_8) == 0)
{
unsigned char x_10; 
lean::dec(x_8);
x_10 = 1;
return x_10;
}
else
{
unsigned char x_12; 
lean::dec(x_8);
x_12 = 2;
return x_12;
}
}
else
{
unsigned char x_17; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_6);
x_17 = 0;
return x_17;
}
}
}
obj* _l_s10_cmp__using(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s10_cmp__using_s6___rarg_s7___boxed), 3, 0);
return x_4;
}
}
obj* _l_s10_cmp__using_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = _l_s10_cmp__using_s6___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
unsigned char _l_s3_cmp_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_6 = lean::apply_2(x_0, x_1, x_2);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; 
lean::dec(x_6);
x_8 = lean::apply_2(x_0, x_2, x_1);
if (lean::obj_tag(x_8) == 0)
{
unsigned char x_10; 
lean::dec(x_8);
x_10 = 1;
return x_10;
}
else
{
unsigned char x_12; 
lean::dec(x_8);
x_12 = 2;
return x_12;
}
}
else
{
unsigned char x_17; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_6);
x_17 = 0;
return x_17;
}
}
}
obj* _l_s3_cmp(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_cmp_s6___rarg_s7___boxed), 3, 0);
return x_4;
}
}
obj* _l_s3_cmp_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = _l_s3_cmp_s6___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _l_s8_ordering_s13_decidable__eq(unsigned char x_0, unsigned char x_1) {
_start:
{
switch (x_0) {
case 0:
{
switch (x_1) {
case 0:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 0, 0);
;
return x_2;
}
case 1:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(0, 0, 0);
;
return x_3;
}
default:
{
obj* x_4; 
x_4 = lean::alloc_cnstr(0, 0, 0);
;
return x_4;
}
}
}
case 1:
{
switch (x_1) {
case 0:
{
obj* x_5; 
x_5 = lean::alloc_cnstr(0, 0, 0);
;
return x_5;
}
case 1:
{
obj* x_6; 
x_6 = lean::alloc_cnstr(1, 0, 0);
;
return x_6;
}
default:
{
obj* x_7; 
x_7 = lean::alloc_cnstr(0, 0, 0);
;
return x_7;
}
}
}
default:
{
switch (x_1) {
case 0:
{
obj* x_8; 
x_8 = lean::alloc_cnstr(0, 0, 0);
;
return x_8;
}
case 1:
{
obj* x_9; 
x_9 = lean::alloc_cnstr(0, 0, 0);
;
return x_9;
}
default:
{
obj* x_10; 
x_10 = lean::alloc_cnstr(1, 0, 0);
;
return x_10;
}
}
}
}
}
}
obj* _l_s8_ordering_s13_decidable__eq_s7___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s8_ordering_s13_decidable__eq(x_2, x_3);
return x_4;
}
}
void _l_initialize__l_s4_init_s4_data_s4_repr();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s8_ordering_s5_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s4_repr();
 _l_s8_ordering_s9_has__repr_s11___closed__1 = _init__l_s8_ordering_s9_has__repr_s11___closed__1();
 _l_s8_ordering_s9_has__repr_s11___closed__2 = _init__l_s8_ordering_s9_has__repr_s11___closed__2();
 _l_s8_ordering_s9_has__repr_s11___closed__3 = _init__l_s8_ordering_s9_has__repr_s11___closed__3();
}
