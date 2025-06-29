// Lean compiler output
// Module: Std.Data.Iterators.Producers.Repeat
// Imports: Init.Data.Iterators.Consumers.Monadic Init.Data.Iterators.Internal.Termination
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
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorCollect(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMappedPartial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_repeat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorLoopPartial___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorCollect___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorRepeatIteratorId___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorCollect___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorCollectPartial(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorRepeatIteratorId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_repeat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_repeat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorRepeatIteratorId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorLoopPartial(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_repeat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_RepeatIterator_instProductivenessRelation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_RepeatIterator_instProductivenessRelation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorLoop___redArg(lean_object*, lean_object*);
static lean_object* l_Std_Iterators_RepeatIterator_instIteratorCollect___redArg___lam__0___closed__0;
lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_IterM_DefaultConsumers_forInPartial___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorLoopPartial___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorCollectPartial___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorRepeatIteratorId___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorRepeatIteratorId___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorRepeatIteratorId___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorRepeatIteratorId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorRepeatIteratorId___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_repeat___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_repeat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_repeat___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Iterators_Iter_repeat___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_repeat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Iterators_Iter_repeat(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_RepeatIterator_instProductivenessRelation(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_RepeatIterator_instProductivenessRelation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_RepeatIterator_instProductivenessRelation(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorLoop___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_1, x_2, x_3, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorLoop___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorRepeatIteratorId___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Iterators_RepeatIterator_instIteratorLoop___redArg___lam__0), 9, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_RepeatIterator_instIteratorLoop___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorLoopPartial___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Iterators_IterM_DefaultConsumers_forInPartial___redArg(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorLoopPartial___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorRepeatIteratorId___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Iterators_RepeatIterator_instIteratorLoopPartial___redArg___lam__0), 7, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorLoopPartial(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_RepeatIterator_instIteratorLoopPartial___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_Iterators_RepeatIterator_instIteratorCollect___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorCollect___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_Iterators_RepeatIterator_instIteratorCollect___redArg___lam__0___closed__0;
x_9 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_1, x_4, x_6, x_2, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorCollect___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorRepeatIteratorId___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Iterators_RepeatIterator_instIteratorCollect___redArg___lam__0), 7, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorCollect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_RepeatIterator_instIteratorCollect___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorCollectPartial___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorRepeatIteratorId___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Iterators_IterM_DefaultConsumers_toArrayMappedPartial), 10, 6);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, lean_box(0));
lean_closure_set(x_4, 3, lean_box(0));
lean_closure_set(x_4, 4, x_2);
lean_closure_set(x_4, 5, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_RepeatIterator_instIteratorCollectPartial(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_RepeatIterator_instIteratorCollectPartial___redArg(x_2, x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Internal_Termination(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Producers_Repeat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Monadic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Internal_Termination(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Iterators_RepeatIterator_instIteratorCollect___redArg___lam__0___closed__0 = _init_l_Std_Iterators_RepeatIterator_instIteratorCollect___redArg___lam__0___closed__0();
lean_mark_persistent(l_Std_Iterators_RepeatIterator_instIteratorCollect___redArg___lam__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
