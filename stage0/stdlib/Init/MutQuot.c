// Lean compiler output
// Module: Init.MutQuot
// Imports: Init.Core
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_MutQuot_liftSubsingleton(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mutquot_get(lean_object*);
lean_object* l_MutQuot_lift___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mutquot_mk(lean_object*);
lean_object* l_MutQuot_indep___rarg(lean_object*, lean_object*);
lean_object* l_MutQuot_dlift___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_MutQuot_liftUpdate(lean_object*, lean_object*, lean_object*);
lean_object* l_MutQuot_indep(lean_object*, lean_object*, lean_object*);
lean_object* l_MutQuot_dlift(lean_object*, lean_object*, lean_object*);
lean_object* l_MutQuot_val___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_MutQuot_lift(lean_object*, lean_object*, lean_object*);
lean_object* l_MutQuot_liftUpdate___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_MutQuot_mkAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_MutQuot_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_MutQuot_mk___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_MutQuot_liftUpdateUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* lean_mutquot_mk(lean_object*);
lean_object* l_MutQuot_liftSubsingleton___rarg(lean_object*, lean_object*);
lean_object* l_MutQuot_liftUpdateUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mutquot_set(lean_object*, lean_object*, lean_object*);
lean_object* l_MutQuot_mkAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_mutquot_mk(x_3);
return x_4;
}
}
lean_object* l_MutQuot_val___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_mutquot_get(x_3);
return x_4;
}
}
lean_object* l_MutQuot_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_mutquot_mk(x_3);
return x_4;
}
}
lean_object* l_MutQuot_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_mutquot_set(x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_MutQuot_liftUpdateUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_mutquot_set(x_4, x_7, x_6);
return x_8;
}
}
lean_object* l_MutQuot_liftUpdateUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_MutQuot_liftUpdateUnsafe___rarg), 4, 0);
return x_4;
}
}
lean_object* l_MutQuot_liftUpdate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_MutQuot_liftUpdate(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_MutQuot_liftUpdate___rarg), 4, 0);
return x_4;
}
}
lean_object* l_MutQuot_lift___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
lean_object* l_MutQuot_lift(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_MutQuot_lift___rarg), 3, 0);
return x_4;
}
}
lean_object* l_MutQuot_indep___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_2);
x_3 = lean_mutquot_mk(x_2);
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
lean_object* l_MutQuot_indep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_MutQuot_indep___rarg), 2, 0);
return x_4;
}
}
lean_object* l_MutQuot_dlift___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
lean_object* l_MutQuot_dlift(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_MutQuot_dlift___rarg), 3, 0);
return x_4;
}
}
lean_object* l_MutQuot_liftSubsingleton___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_MutQuot_liftSubsingleton(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_MutQuot_liftSubsingleton___rarg), 2, 0);
return x_5;
}
}
lean_object* initialize_Init_Core(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_MutQuot(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
