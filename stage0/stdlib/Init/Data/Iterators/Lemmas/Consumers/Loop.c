// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Consumers.Loop
// Imports: Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop Init.Data.Iterators.Consumers.Loop
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_forIn_x27__eq__match__step_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_IterM_forIn_x27__eq__match__step_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_forIn_x27__eq__match__step_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_IterM_forIn_x27__eq__match__step_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_forIn_x27__eq__match__step_match__3_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_forIn_x27__eq__match__step_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_toArray__eq__match__step_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_toArray__eq__match__step_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___rarg), 4, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_IterM_forIn_x27__eq__match__step_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_IterM_forIn_x27__eq__match__step_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_IterM_forIn_x27__eq__match__step_match__1_splitter___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_forIn_x27__eq__match__step_match__3_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_forIn_x27__eq__match__step_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_forIn_x27__eq__match__step_match__3_splitter___rarg), 4, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_forIn_x27__eq__match__step_match__3_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_forIn_x27__eq__match__step_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_forIn_x27__eq__match__step_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_forIn_x27__eq__match__step_match__1_splitter___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_toArray__eq__match__step_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_toArray__eq__match__step_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_toArray__eq__match__step_match__1_splitter___rarg), 4, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_toArray__eq__match__step_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iterators_Iter_toArray__eq__match__step_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
