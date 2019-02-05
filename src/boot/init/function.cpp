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
obj* l_function_has__right__inverse;
obj* l_function_app(obj*, obj*);
obj* l_function_combine___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_function_injective;
obj* l_function_surjective;
obj* l_function_on__fun___rarg(obj*, obj*, obj*, obj*);
obj* l_function_dcomp(obj*, obj*, obj*);
obj* l_function_id__of__left__inverse;
obj* l_function_comp__right(obj*, obj*);
obj* l_function_swap(obj*, obj*, obj*);
obj* l_function_const___rarg(obj*, obj*);
obj* l_function_curry(obj*, obj*, obj*);
obj* l_function_comp(obj*, obj*, obj*);
obj* l_function_comp__left___rarg(obj*, obj*, obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_function_curry___rarg(obj*, obj*, obj*);
obj* l_function_uncurry___rarg(obj*, obj*);
obj* l_function_const(obj*, obj*);
obj* l_function_right__inverse;
obj* l_function_swap___rarg(obj*, obj*, obj*);
obj* l_function_comp__right___rarg(obj*, obj*, obj*, obj*);
obj* l_function_app___rarg(obj*, obj*);
obj* l_function_dcomp___rarg(obj*, obj*, obj*);
obj* l_function_has__left__inverse;
obj* l_function_bijective;
obj* l_function_id__of__right__inverse;
obj* l_function_on__fun(obj*, obj*, obj*);
obj* l_function_left__inverse;
obj* l_function_combine(obj*, obj*, obj*, obj*, obj*);
obj* l_function_uncurry(obj*, obj*, obj*);
obj* l_function_comp__left(obj*, obj*);
obj* l_function_comp___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_1, x_2);
x_4 = lean::apply_1(x_0, x_3);
return x_4;
}
}
obj* l_function_comp(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 0);
return x_6;
}
}
obj* l_function_dcomp___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_2);
x_4 = lean::apply_1(x_1, x_2);
x_5 = lean::apply_2(x_0, x_2, x_4);
return x_5;
}
}
obj* l_function_dcomp(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_function_dcomp___rarg), 3, 0);
return x_6;
}
}
obj* l_function_comp__right___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::apply_2(x_0, x_2, x_4);
return x_5;
}
}
obj* l_function_comp__right(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp__right___rarg), 4, 0);
return x_4;
}
}
obj* l_function_comp__left___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_2);
x_5 = lean::apply_2(x_0, x_4, x_3);
return x_5;
}
}
obj* l_function_comp__left(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp__left___rarg), 4, 0);
return x_4;
}
}
obj* l_function_on__fun___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* l_function_on__fun(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_function_on__fun___rarg), 4, 0);
return x_6;
}
}
obj* l_function_combine___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* l_function_combine(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_function_combine___rarg), 5, 0);
return x_10;
}
}
obj* l_function_const___rarg(obj* x_0, obj* x_1) {
_start:
{
lean::dec(x_1);
return x_0;
}
}
obj* l_function_const(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_function_const___rarg), 2, 0);
return x_4;
}
}
obj* l_function_swap___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_0, x_2, x_1);
return x_3;
}
}
obj* l_function_swap(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_function_swap___rarg), 3, 0);
return x_6;
}
}
obj* l_function_app___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_function_app(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_function_app___rarg), 2, 0);
return x_4;
}
}
obj* _init_l_function_injective() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_function_surjective() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_function_bijective() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_function_left__inverse() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_function_has__left__inverse() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_function_right__inverse() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_function_has__right__inverse() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_function_curry___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_function_curry(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_function_curry___rarg), 3, 0);
return x_6;
}
}
obj* l_function_uncurry___rarg(obj* x_0, obj* x_1) {
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
obj* l_function_uncurry(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_function_uncurry___rarg), 2, 0);
return x_6;
}
}
obj* _init_l_function_id__of__left__inverse() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_function_id__of__right__inverse() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
void initialize_init_core();
static bool _G_initialized = false;
void initialize_init_function() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_core();
 l_function_injective = _init_l_function_injective();
 l_function_surjective = _init_l_function_surjective();
 l_function_bijective = _init_l_function_bijective();
 l_function_left__inverse = _init_l_function_left__inverse();
 l_function_has__left__inverse = _init_l_function_has__left__inverse();
 l_function_right__inverse = _init_l_function_right__inverse();
 l_function_has__right__inverse = _init_l_function_has__right__inverse();
 l_function_id__of__left__inverse = _init_l_function_id__of__left__inverse();
 l_function_id__of__right__inverse = _init_l_function_id__of__right__inverse();
}
