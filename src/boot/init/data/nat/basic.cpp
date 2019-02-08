// Lean compiler output
// Module: init.data.nat.basic
// Imports: init.core
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
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
obj* l_nat_mul___main(obj*, obj*);
obj* l_nat_has__sub;
obj* l_nat_max(obj*, obj*);
obj* l_nat_le__refl;
obj* l_nat_beq___main(obj*, obj*);
obj* l_nat_repeat___rarg(obj*, obj*, obj*);
obj* l_nat_repeat__core___rarg(obj*, obj*, obj*, obj*);
obj* l_nat_decidable__eq;
obj* l_nat_succ__pos;
obj* l_nat_sub___main(obj*, obj*);
obj* l_nat_lt_step;
obj* l_nat_repeat(obj*);
obj* l_nat_pred___main(obj*);
obj* l_nat_has__pow;
obj* l_nat_ble(obj*, obj*);
obj* l_nat_repeat__core___main(obj*);
obj* l_nat_dec__eq___boxed(obj*, obj*);
obj* l_nat_has__lt;
obj* l_nat_has__mul;
obj* l_nat_lt_base;
obj* l_nat_lt;
obj* l_nat_pow___main(obj*, obj*);
obj* l_nat_pow(obj*, obj*);
obj* l_nat_repeat__core___main___rarg(obj*, obj*, obj*, obj*);
obj* l_nat_dec__le___boxed(obj*, obj*);
obj* l_nat_beq(obj*, obj*);
obj* l_nat_repeat__core(obj*);
obj* l_nat_pred(obj*);
obj* l_nat_has__le;
obj* l_nat_le;
obj* l_nat_ble___main(obj*, obj*);
obj* l_nat_le__refl___main;
obj* l_nat_dec__lt___boxed(obj*, obj*);
obj* l_nat_beq___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (x_4 == 0)
{
obj* x_6; obj* x_7; obj* x_9; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_0, x_6);
lean::dec(x_0);
x_9 = lean::nat_sub(x_1, x_6);
lean::dec(x_6);
lean::dec(x_1);
x_0 = x_7;
x_1 = x_9;
goto _start;
}
else
{
uint8 x_15; obj* x_16; 
lean::dec(x_1);
lean::dec(x_0);
x_15 = 0;
x_16 = lean::box(x_15);
return x_16;
}
}
else
{
uint8 x_18; 
lean::dec(x_0);
x_18 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
if (x_18 == 0)
{
uint8 x_21; obj* x_22; 
x_21 = 0;
x_22 = lean::box(x_21);
return x_22;
}
else
{
uint8 x_23; obj* x_24; 
x_23 = 1;
x_24 = lean::box(x_23);
return x_24;
}
}
}
}
obj* l_nat_beq(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_nat_beq___main(x_0, x_1);
return x_2;
}
}
obj* l_nat_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::nat_dec_eq(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_nat_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_dec__eq___boxed), 2, 0);
return x_0;
}
}
obj* l_nat_ble___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (x_4 == 0)
{
obj* x_6; obj* x_7; obj* x_9; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_0, x_6);
lean::dec(x_0);
x_9 = lean::nat_sub(x_1, x_6);
lean::dec(x_6);
lean::dec(x_1);
x_0 = x_7;
x_1 = x_9;
goto _start;
}
else
{
uint8 x_15; obj* x_16; 
lean::dec(x_1);
lean::dec(x_0);
x_15 = 0;
x_16 = lean::box(x_15);
return x_16;
}
}
else
{
uint8 x_20; obj* x_21; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_20 = 1;
x_21 = lean::box(x_20);
return x_21;
}
}
}
obj* l_nat_ble(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_nat_ble___main(x_0, x_1);
return x_2;
}
}
obj* _init_l_nat_le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_nat_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_nat_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_nat_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_nat_pred___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
lean::dec(x_1);
if (x_2 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_0, x_4);
lean::dec(x_4);
lean::dec(x_0);
return x_5;
}
else
{
obj* x_9; 
lean::dec(x_0);
x_9 = lean::mk_nat_obj(0u);
return x_9;
}
}
}
obj* l_nat_pred(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_nat_pred___main(x_0);
return x_1;
}
}
obj* l_nat_sub___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
x_9 = l_nat_sub___main(x_0, x_6);
x_10 = l_nat_pred___main(x_9);
return x_10;
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
obj* l_nat_mul___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; obj* x_6; obj* x_10; obj* x_11; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
lean::inc(x_0);
x_10 = l_nat_mul___main(x_0, x_6);
x_11 = lean::nat_add(x_10, x_0);
lean::dec(x_0);
lean::dec(x_10);
return x_11;
}
else
{
obj* x_16; 
lean::dec(x_1);
lean::dec(x_0);
x_16 = lean::mk_nat_obj(0u);
return x_16;
}
}
}
obj* _init_l_nat_has__sub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::nat_sub), 2, 0);
return x_0;
}
}
obj* _init_l_nat_has__mul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::nat_mul), 2, 0);
return x_0;
}
}
obj* l_nat_repeat__core___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_13; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_7);
x_10 = lean::nat_sub(x_1, x_2);
lean::dec(x_2);
lean::inc(x_0);
x_13 = lean::apply_2(x_0, x_10, x_3);
x_2 = x_8;
x_3 = x_13;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
}
obj* l_nat_repeat__core___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_repeat__core___main___rarg), 4, 0);
return x_2;
}
}
obj* l_nat_repeat__core___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_nat_repeat__core___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_nat_repeat__core(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_repeat__core___rarg), 4, 0);
return x_2;
}
}
obj* l_nat_repeat___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_1);
x_4 = l_nat_repeat__core___main___rarg(x_0, x_1, x_1, x_2);
return x_4;
}
}
obj* l_nat_repeat(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_repeat___rarg), 3, 0);
return x_2;
}
}
obj* l_nat_pow___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; obj* x_6; obj* x_10; obj* x_11; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
lean::inc(x_0);
x_10 = l_nat_pow___main(x_0, x_6);
x_11 = lean::nat_mul(x_10, x_0);
lean::dec(x_0);
lean::dec(x_10);
return x_11;
}
else
{
obj* x_16; 
lean::dec(x_1);
lean::dec(x_0);
x_16 = lean::mk_nat_obj(1u);
return x_16;
}
}
}
obj* l_nat_pow(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_nat_pow___main(x_0, x_1);
return x_2;
}
}
obj* _init_l_nat_has__pow() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_pow), 2, 0);
return x_0;
}
}
obj* _init_l_nat_le__refl___main() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_nat_le__refl() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_nat_succ__pos() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_nat_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::nat_dec_le(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_nat_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::nat_dec_lt(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_nat_lt_step() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_nat_lt_base() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_nat_max(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_le(x_0, x_1);
if (x_2 == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
void initialize_init_core();
static bool _G_initialized = false;
void initialize_init_data_nat_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_core();
 l_nat_decidable__eq = _init_l_nat_decidable__eq();
 l_nat_le = _init_l_nat_le();
 l_nat_has__le = _init_l_nat_has__le();
 l_nat_lt = _init_l_nat_lt();
 l_nat_has__lt = _init_l_nat_has__lt();
 l_nat_has__sub = _init_l_nat_has__sub();
 l_nat_has__mul = _init_l_nat_has__mul();
 l_nat_has__pow = _init_l_nat_has__pow();
 l_nat_le__refl___main = _init_l_nat_le__refl___main();
 l_nat_le__refl = _init_l_nat_le__refl();
 l_nat_succ__pos = _init_l_nat_succ__pos();
 l_nat_lt_step = _init_l_nat_lt_step();
 l_nat_lt_base = _init_l_nat_lt_base();
}
