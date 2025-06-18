// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Producers.Monadic.List
// Imports: Init.Data.Iterators.Consumers Init.Data.Iterators.Lemmas.Consumers.Monadic Init.Data.Iterators.Internal.LawfulMonadLiftFunction Std.Data.Iterators.Producers.Monadic.List Std.Data.Iterators.Lemmas.Equivalence.Basic
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_IterM_DefaultConsumers_toArrayMapped__eq__match__step_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_IterM_DefaultConsumers_toArrayMapped__eq__match__step_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__List_step__iterM_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_IterM_DefaultConsumers_toArrayMapped__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__3_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__List_step__iterM_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__List_step__iterM_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__3_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__3_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__3_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__3_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__3_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__3_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_IterM_DefaultConsumers_toArrayMapped__eq__match__step_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_3(x_2, x_5, x_6, lean_box(0));
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_8, lean_box(0));
return x_9;
}
default: 
{
lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_apply_1(x_4, lean_box(0));
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_IterM_DefaultConsumers_toArrayMapped__eq__match__step_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_IterM_DefaultConsumers_toArrayMapped__eq__match__step_match__1_splitter___rarg), 4, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_IterM_DefaultConsumers_toArrayMapped__eq__match__step_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_IterM_DefaultConsumers_toArrayMapped__eq__match__step_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__List_step__iterM_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__List_step__iterM_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__List_step__iterM_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__List_step__iterM_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__List_step__iterM_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
default: 
{
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__1_splitter___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_instIteratorListIteratorOfPure_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_Iterators_Consumers(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Producers_Monadic_List(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Monadic_List(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
