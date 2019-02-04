// Lean compiler output
// Module: init.data.nat.basic
// Imports: init.core
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* _l_s3_nat_s3_pow_s6___main(obj*, obj*);
obj* _l_s3_nat_s2_lt_s4_base;
obj* _l_s3_nat_s8_has__sub;
obj* _l_s3_nat_s3_pow(obj*, obj*);
obj* _l_s3_nat_s4_pred(obj*);
obj* _l_s3_nat_s8_le__refl;
obj* _l_s3_nat_s6_repeat(obj*);
obj* _l_s3_nat_s2_lt;
obj* _l_s3_nat_s7_has__le;
obj* _l_s3_nat_s3_max(obj*, obj*);
obj* _l_s3_nat_s4_pred_s6___main(obj*);
obj* _l_s3_nat_s6_repeat_s6___main_s6___rarg(obj*, obj*, obj*);
obj* _l_s3_nat_s13_decidable__eq;
obj* _l_s3_nat_s2_le;
obj* _l_s3_nat_s9_succ__pos;
obj* _l_s3_nat_s3_ble_s6___main(obj*, obj*);
obj* _l_s3_nat_s7_has__lt;
obj* _l_s3_nat_s6_repeat_s6___rarg(obj*, obj*, obj*);
obj* _l_s3_nat_s8_le__refl_s6___main;
obj* _l_s3_nat_s8_has__mul;
obj* _l_s3_nat_s3_ble(obj*, obj*);
obj* _l_s3_nat_s3_beq_s6___main(obj*, obj*);
obj* _l_s3_nat_s8_has__pow;
obj* _l_s3_nat_s2_lt_s4_step;
obj* _l_s3_nat_s3_mul_s6___main(obj*, obj*);
obj* _l_s3_nat_s6_repeat_s6___main(obj*);
obj* _l_s3_nat_s3_sub_s6___main(obj*, obj*);
obj* _l_s3_nat_s3_beq(obj*, obj*);
obj* _l_s3_nat_s3_beq_s6___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_3);
x_5 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_9; obj* x_11; 
lean::dec(x_5);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_0, x_8);
lean::dec(x_0);
x_11 = lean::nat_sub(x_1, x_8);
lean::dec(x_8);
lean::dec(x_1);
x_0 = x_9;
x_1 = x_11;
goto _start;
}
else
{
unsigned char x_18; obj* x_19; 
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_1);
x_18 = 0;
x_19 = lean::box(x_18);
return x_19;
}
}
else
{
obj* x_22; 
lean::dec(x_0);
lean::dec(x_3);
x_22 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_22) == 0)
{
unsigned char x_26; obj* x_27; 
lean::dec(x_22);
x_26 = 0;
x_27 = lean::box(x_26);
return x_27;
}
else
{
unsigned char x_29; obj* x_30; 
lean::dec(x_22);
x_29 = 1;
x_30 = lean::box(x_29);
return x_30;
}
}
}
}
obj* _l_s3_nat_s3_beq(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s3_nat_s3_beq_s6___main(x_0, x_1);
return x_2;
}
}
obj* _init__l_s3_nat_s13_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::nat_dec_eq), 2, 0);
return x_0;
}
}
obj* _l_s3_nat_s3_ble_s6___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_3);
x_5 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_9; obj* x_11; 
lean::dec(x_5);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_0, x_8);
lean::dec(x_0);
x_11 = lean::nat_sub(x_1, x_8);
lean::dec(x_8);
lean::dec(x_1);
x_0 = x_9;
x_1 = x_11;
goto _start;
}
else
{
unsigned char x_18; obj* x_19; 
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_1);
x_18 = 0;
x_19 = lean::box(x_18);
return x_19;
}
}
else
{
unsigned char x_24; obj* x_25; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_24 = 1;
x_25 = lean::box(x_24);
return x_25;
}
}
}
obj* _l_s3_nat_s3_ble(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s3_nat_s3_ble_s6___main(x_0, x_1);
return x_2;
}
}
obj* _init__l_s3_nat_s2_le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s3_nat_s7_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s3_nat_s2_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s3_nat_s7_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _l_s3_nat_s4_pred_s6___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
lean::dec(x_5);
lean::dec(x_0);
return x_6;
}
else
{
obj* x_11; 
lean::dec(x_0);
lean::dec(x_2);
x_11 = lean::mk_nat_obj(0u);
return x_11;
}
}
}
obj* _l_s3_nat_s4_pred(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = _l_s3_nat_s4_pred_s6___main(x_0);
return x_1;
}
}
obj* _l_s3_nat_s3_sub_s6___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_6);
lean::dec(x_1);
x_10 = _l_s3_nat_s3_sub_s6___main(x_0, x_7);
x_11 = _l_s3_nat_s4_pred_s6___main(x_10);
return x_11;
}
else
{
lean::dec(x_1);
lean::dec(x_3);
return x_0;
}
}
}
obj* _l_s3_nat_s3_mul_s6___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_7; obj* x_11; obj* x_12; 
lean::dec(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_6);
lean::dec(x_1);
lean::inc(x_0);
x_11 = _l_s3_nat_s3_mul_s6___main(x_0, x_7);
x_12 = lean::nat_add(x_11, x_0);
lean::dec(x_0);
lean::dec(x_11);
return x_12;
}
else
{
obj* x_18; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
x_18 = lean::mk_nat_obj(0u);
return x_18;
}
}
}
obj* _init__l_s3_nat_s8_has__sub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::nat_sub), 2, 0);
return x_0;
}
}
obj* _init__l_s3_nat_s8_has__mul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::nat_mul), 2, 0);
return x_0;
}
}
obj* _l_s3_nat_s6_repeat_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_8; obj* x_13; obj* x_14; 
lean::dec(x_4);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
lean::dec(x_7);
lean::dec(x_1);
lean::inc(x_8);
lean::inc(x_0);
x_13 = _l_s3_nat_s6_repeat_s6___main_s6___rarg(x_0, x_8, x_2);
x_14 = lean::apply_2(x_0, x_8, x_13);
return x_14;
}
else
{
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
}
obj* _l_s3_nat_s6_repeat_s6___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_nat_s6_repeat_s6___main_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s3_nat_s6_repeat_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = _l_s3_nat_s6_repeat_s6___main_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s3_nat_s6_repeat(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_nat_s6_repeat_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s3_nat_s3_pow_s6___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_7; obj* x_11; obj* x_12; 
lean::dec(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_6);
lean::dec(x_1);
lean::inc(x_0);
x_11 = _l_s3_nat_s3_pow_s6___main(x_0, x_7);
x_12 = lean::nat_mul(x_11, x_0);
lean::dec(x_0);
lean::dec(x_11);
return x_12;
}
else
{
obj* x_18; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
x_18 = lean::mk_nat_obj(1u);
return x_18;
}
}
}
obj* _l_s3_nat_s3_pow(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s3_nat_s3_pow_s6___main(x_0, x_1);
return x_2;
}
}
obj* _init__l_s3_nat_s8_has__pow() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_nat_s3_pow), 2, 0);
return x_0;
}
}
obj* _init__l_s3_nat_s8_le__refl_s6___main() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s3_nat_s8_le__refl() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s3_nat_s9_succ__pos() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s3_nat_s2_lt_s4_step() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s3_nat_s2_lt_s4_base() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s3_nat_s3_max(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::nat_dec_le(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_0;
}
else
{
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
}
}
void _l_initialize__l_s4_init_s4_core();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_core();
 _l_s3_nat_s13_decidable__eq = _init__l_s3_nat_s13_decidable__eq();
 _l_s3_nat_s2_le = _init__l_s3_nat_s2_le();
 _l_s3_nat_s7_has__le = _init__l_s3_nat_s7_has__le();
 _l_s3_nat_s2_lt = _init__l_s3_nat_s2_lt();
 _l_s3_nat_s7_has__lt = _init__l_s3_nat_s7_has__lt();
 _l_s3_nat_s8_has__sub = _init__l_s3_nat_s8_has__sub();
 _l_s3_nat_s8_has__mul = _init__l_s3_nat_s8_has__mul();
 _l_s3_nat_s8_has__pow = _init__l_s3_nat_s8_has__pow();
 _l_s3_nat_s8_le__refl_s6___main = _init__l_s3_nat_s8_le__refl_s6___main();
 _l_s3_nat_s8_le__refl = _init__l_s3_nat_s8_le__refl();
 _l_s3_nat_s9_succ__pos = _init__l_s3_nat_s9_succ__pos();
 _l_s3_nat_s2_lt_s4_step = _init__l_s3_nat_s2_lt_s4_step();
 _l_s3_nat_s2_lt_s4_base = _init__l_s3_nat_s2_lt_s4_base();
}
