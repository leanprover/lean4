// Lean compiler output
// Module: Std.Do.SPred.SPred
// Imports: Init.Ext Std.Do.SPred.SVal
#include <lean/lean.h>
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
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_iff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_pure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_forall___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_entails_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_or(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_or___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_imp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_entails_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_not___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_pure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_forall(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_forall___redArg(lean_object*, lean_object*);
lean_object* l_Std_Do_SVal_curry___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_conjunction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_not(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_imp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_and___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_and(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_iff___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_pure___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Do_SVal_curry___redArg(x_1, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_pure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Do_SVal_curry___redArg(x_1, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_entails_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_2(x_4, lean_box(0), lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_5, lean_box(0), x_7, x_2, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_entails_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_entails_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_and___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_apply_1(x_2, x_4);
x_7 = l_Std_Do_SPred_and(x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_and(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return lean_box(0);
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_Std_Do_SPred_and___lam__0), 4, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_or___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_apply_1(x_2, x_4);
x_7 = l_Std_Do_SPred_or(x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_or(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return lean_box(0);
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_Std_Do_SPred_or___lam__0), 4, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_not___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = l_Std_Do_SPred_not(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_not(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
return lean_box(0);
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Do_SPred_not___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_imp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_apply_1(x_2, x_4);
x_7 = l_Std_Do_SPred_imp(x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_imp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return lean_box(0);
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_Std_Do_SPred_imp___lam__0), 4, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_iff___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_apply_1(x_2, x_4);
x_7 = l_Std_Do_SPred_iff(x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_iff(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return lean_box(0);
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_Std_Do_SPred_iff___lam__0), 4, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Std_Do_SPred_exists___redArg___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Std_Do_SPred_exists___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
return lean_box(0);
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Do_SPred_exists___redArg___lam__1), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Do_SPred_exists___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_forall___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Std_Do_SPred_exists___redArg___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Std_Do_SPred_forall___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_forall___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
return lean_box(0);
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Do_SPred_forall___redArg___lam__1), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_forall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Do_SPred_forall___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_conjunction(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Std_Do_SVal_curry___redArg(x_1, lean_box(0));
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = l_Std_Do_SPred_conjunction(x_1, x_5);
x_7 = l_Std_Do_SPred_and(x_1, x_4, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Init_Ext(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Do_SPred_SVal(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_SPred_SPred(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Ext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_SPred_SVal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
