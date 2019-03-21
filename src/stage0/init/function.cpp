// Lean compiler output
// Module: init.function
// Imports: init.core
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
obj* l_Function_uncurry(obj*, obj*, obj*);
obj* l_Function_onFun(obj*, obj*, obj*);
obj* l_Function_curry___rarg(obj*, obj*, obj*);
obj* l_Function_dcomp___boxed(obj*, obj*, obj*);
obj* l_Function_compLeft___boxed(obj*, obj*);
obj* l_Function_onFun___boxed(obj*, obj*, obj*);
obj* l_Function_app(obj*, obj*);
obj* l_Function_dcomp___rarg(obj*, obj*, obj*);
obj* l_Function_onFun___rarg(obj*, obj*, obj*, obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Function_curry___boxed(obj*, obj*, obj*);
obj* l_Function_uncurry___rarg(obj*, obj*);
obj* l_Function_comp___boxed(obj*, obj*, obj*);
obj* l_Function_dcomp(obj*, obj*, obj*);
obj* l_Function_uncurry___boxed(obj*, obj*, obj*);
obj* l_Function_compRight___rarg(obj*, obj*, obj*, obj*);
obj* l_Function_const___rarg___boxed(obj*, obj*);
obj* l_Function_const___boxed(obj*, obj*);
obj* l_Function_combine___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Function_swap(obj*, obj*, obj*);
obj* l_Function_compLeft(obj*, obj*);
obj* l_Function_compRight(obj*, obj*);
obj* l_Function_swap___boxed(obj*, obj*, obj*);
obj* l_Function_combine___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Function_const___rarg(obj*, obj*);
obj* l_Function_app___boxed(obj*, obj*);
obj* l_Function_app___rarg(obj*, obj*);
obj* l_Function_curry(obj*, obj*, obj*);
obj* l_Function_comp(obj*, obj*, obj*);
obj* l_Function_combine(obj*, obj*, obj*, obj*, obj*);
obj* l_Function_compRight___boxed(obj*, obj*);
obj* l_Function_swap___rarg(obj*, obj*, obj*);
obj* l_Function_const(obj*, obj*);
obj* l_Function_compLeft___rarg(obj*, obj*, obj*, obj*);
obj* l_Function_comp___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_1, x_2);
x_4 = lean::apply_1(x_0, x_3);
return x_4;
}
}
obj* l_Function_comp(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 0);
return x_3;
}
}
obj* l_Function_comp___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Function_comp(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Function_dcomp___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_2);
x_4 = lean::apply_1(x_1, x_2);
x_5 = lean::apply_2(x_0, x_2, x_4);
return x_5;
}
}
obj* l_Function_dcomp(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_dcomp___rarg), 3, 0);
return x_3;
}
}
obj* l_Function_dcomp___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Function_dcomp(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Function_compRight___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::apply_2(x_0, x_2, x_4);
return x_5;
}
}
obj* l_Function_compRight(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_compRight___rarg), 4, 0);
return x_2;
}
}
obj* l_Function_compRight___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Function_compRight(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Function_compLeft___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_2);
x_5 = lean::apply_2(x_0, x_4, x_3);
return x_5;
}
}
obj* l_Function_compLeft(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_compLeft___rarg), 4, 0);
return x_2;
}
}
obj* l_Function_compLeft___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Function_compLeft(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Function_onFun___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* l_Function_onFun(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_onFun___rarg), 4, 0);
return x_3;
}
}
obj* l_Function_onFun___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Function_onFun(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Function_combine___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* l_Function_combine(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_combine___rarg), 5, 0);
return x_5;
}
}
obj* l_Function_combine___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Function_combine(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_Function_const___rarg(obj* x_0, obj* x_1) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_Function_const(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_const___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Function_const___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Function_const___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Function_const___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Function_const(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Function_swap___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_0, x_2, x_1);
return x_3;
}
}
obj* l_Function_swap(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_swap___rarg), 3, 0);
return x_3;
}
}
obj* l_Function_swap___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Function_swap(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Function_app___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_Function_app(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_app___rarg), 2, 0);
return x_2;
}
}
obj* l_Function_app___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Function_app(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Function_curry___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_Function_curry(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_curry___rarg), 3, 0);
return x_3;
}
}
obj* l_Function_curry___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Function_curry(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Function_uncurry___rarg(obj* x_0, obj* x_1) {
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
obj* l_Function_uncurry(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_uncurry___rarg), 2, 0);
return x_3;
}
}
obj* l_Function_uncurry___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Function_uncurry(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* initialize_init_core(obj*);
static bool _G_initialized = false;
obj* initialize_init_function(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_core(w);
return w;
}
