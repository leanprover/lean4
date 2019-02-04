// Lean compiler output
// Module: init.function
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
obj* _l_s8_function_s18_has__left__inverse;
obj* _l_s8_function_s4_comp_s6___rarg(obj*, obj*, obj*);
obj* _l_s8_function_s13_left__inverse;
obj* _l_s8_function_s5_curry(obj*, obj*, obj*);
obj* _l_s8_function_s5_dcomp_s6___rarg(obj*, obj*, obj*);
obj* _l_s8_function_s3_app(obj*, obj*);
obj* _l_s8_function_s7_on__fun_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s8_function_s5_curry_s6___rarg(obj*, obj*, obj*);
obj* _l_s8_function_s5_const(obj*, obj*);
obj* _l_s8_function_s14_right__inverse;
obj* _l_s8_function_s5_const_s6___rarg(obj*, obj*);
obj* _l_s8_function_s7_uncurry_s6___rarg(obj*, obj*);
obj* _l_s8_function_s4_swap(obj*, obj*, obj*);
obj* _l_s8_function_s7_uncurry(obj*, obj*, obj*);
obj* _l_s8_function_s10_comp__left_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s8_function_s10_comp__left(obj*, obj*);
obj* _l_s8_function_s7_combine_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s8_function_s11_comp__right_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s8_function_s11_comp__right(obj*, obj*);
obj* _l_s8_function_s4_swap_s6___rarg(obj*, obj*, obj*);
obj* _l_s8_function_s5_dcomp(obj*, obj*, obj*);
obj* _l_s8_function_s4_comp(obj*, obj*, obj*);
obj* _l_s8_function_s22_id__of__right__inverse;
obj* _l_s8_function_s7_combine(obj*, obj*, obj*, obj*, obj*);
obj* _l_s8_function_s19_has__right__inverse;
obj* _l_s8_function_s9_injective;
obj* _l_s8_function_s9_bijective;
obj* _l_s8_function_s3_app_s6___rarg(obj*, obj*);
obj* _l_s8_function_s7_on__fun(obj*, obj*, obj*);
obj* _l_s8_function_s10_surjective;
obj* _l_s8_function_s21_id__of__left__inverse;
obj* _l_s8_function_s4_comp_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_1, x_2);
x_4 = lean::apply_1(x_0, x_3);
return x_4;
}
}
obj* _l_s8_function_s4_comp(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s8_function_s5_dcomp_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_2);
x_4 = lean::apply_1(x_1, x_2);
x_5 = lean::apply_2(x_0, x_2, x_4);
return x_5;
}
}
obj* _l_s8_function_s5_dcomp(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s5_dcomp_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s8_function_s11_comp__right_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::apply_2(x_0, x_2, x_4);
return x_5;
}
}
obj* _l_s8_function_s11_comp__right(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s11_comp__right_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s8_function_s10_comp__left_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_2);
x_5 = lean::apply_2(x_0, x_4, x_3);
return x_5;
}
}
obj* _l_s8_function_s10_comp__left(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s10_comp__left_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s8_function_s7_on__fun_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_5 = lean::apply_1(x_1, x_2);
x_6 = lean::apply_1(x_1, x_3);
x_7 = lean::apply_2(x_0, x_5, x_6);
return x_7;
}
}
obj* _l_s8_function_s7_on__fun(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s7_on__fun_s6___rarg), 4, 0);
return x_6;
}
}
obj* _l_s8_function_s7_combine_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_4);
lean::inc(x_3);
x_7 = lean::apply_2(x_0, x_3, x_4);
x_8 = lean::apply_2(x_2, x_3, x_4);
x_9 = lean::apply_2(x_1, x_7, x_8);
return x_9;
}
}
obj* _l_s8_function_s7_combine(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s7_combine_s6___rarg), 5, 0);
return x_10;
}
}
obj* _l_s8_function_s5_const_s6___rarg(obj* x_0, obj* x_1) {
_start:
{
lean::dec(x_1);
return x_0;
}
}
obj* _l_s8_function_s5_const(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s5_const_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s8_function_s4_swap_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_0, x_2, x_1);
return x_3;
}
}
obj* _l_s8_function_s4_swap(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_swap_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s8_function_s3_app_s6___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* _l_s8_function_s3_app(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s3_app_s6___rarg), 2, 0);
return x_4;
}
}
obj* _init__l_s8_function_s9_injective() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s8_function_s10_surjective() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s8_function_s9_bijective() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s8_function_s13_left__inverse() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s8_function_s18_has__left__inverse() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s8_function_s14_right__inverse() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s8_function_s19_has__right__inverse() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s8_function_s5_curry_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::apply_1(x_0, x_3);
return x_4;
}
}
obj* _l_s8_function_s5_curry(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s5_curry_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s8_function_s7_uncurry_s6___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::apply_2(x_0, x_2, x_4);
return x_7;
}
}
obj* _l_s8_function_s7_uncurry(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s7_uncurry_s6___rarg), 2, 0);
return x_6;
}
}
obj* _init__l_s8_function_s21_id__of__left__inverse() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s8_function_s22_id__of__right__inverse() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
void _l_initialize__l_s4_init_s4_core();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s8_function() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_core();
 _l_s8_function_s9_injective = _init__l_s8_function_s9_injective();
 _l_s8_function_s10_surjective = _init__l_s8_function_s10_surjective();
 _l_s8_function_s9_bijective = _init__l_s8_function_s9_bijective();
 _l_s8_function_s13_left__inverse = _init__l_s8_function_s13_left__inverse();
 _l_s8_function_s18_has__left__inverse = _init__l_s8_function_s18_has__left__inverse();
 _l_s8_function_s14_right__inverse = _init__l_s8_function_s14_right__inverse();
 _l_s8_function_s19_has__right__inverse = _init__l_s8_function_s19_has__right__inverse();
 _l_s8_function_s21_id__of__left__inverse = _init__l_s8_function_s21_id__of__left__inverse();
 _l_s8_function_s22_id__of__right__inverse = _init__l_s8_function_s22_id__of__right__inverse();
}
