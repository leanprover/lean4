// Lean compiler output
// Module: Init.Control.Except
// Imports: Init.Control.Alternative Init.Control.Lift Init.Data.ToString Init.Control.MonadFail
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
lean_object* l_Except_MonadExcept___closed__2;
lean_object* l_ExceptT_HasMonadLift___boxed(lean_object*, lean_object*);
lean_object* l_finally___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_lift___rarg___closed__1;
lean_object* l_Except_repr___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_finally___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_MonadExceptAdapter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_exceptTOfExcept(lean_object*, lean_object*);
lean_object* l_Except_toOption___rarg___boxed(lean_object*);
lean_object* l_ExceptT_pure___boxed(lean_object*, lean_object*);
lean_object* l_Except_Monad___closed__9;
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_toOption(lean_object*, lean_object*);
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_ExceptT_MonadFail(lean_object*);
lean_object* l_Except_return(lean_object*, lean_object*);
lean_object* l_MonadExcept_liftExcept___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_run___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1(lean_object*, lean_object*);
lean_object* l_Except_repr(lean_object*, lean_object*);
lean_object* l_ExceptT_mk___rarg(lean_object*);
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_mapError(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_Monad___rarg___lambda__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_Monad___closed__6;
lean_object* l_Except_toOption___rarg(lean_object*);
lean_object* l_ExceptT_MonadExcept(lean_object*, lean_object*);
lean_object* l_ExceptT_adapt(lean_object*, lean_object*);
lean_object* l_MonadExcept_orelse_x27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_Monad___rarg___lambda__6(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_HasMonadLift(lean_object*, lean_object*);
lean_object* l_ExceptT_run___rarg___boxed(lean_object*);
lean_object* l_ExceptT_catch___boxed(lean_object*, lean_object*);
lean_object* l_Except_HasToString(lean_object*, lean_object*);
lean_object* l_MonadExcept_orelse_x27___boxed(lean_object*, lean_object*);
lean_object* l_ExceptT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_mk___rarg___boxed(lean_object*);
lean_object* l_Except_MonadExcept(lean_object*);
lean_object* l_MonadExcept_liftExcept(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_Monad___closed__10;
lean_object* l_ExceptT_lift___rarg___lambda__1(lean_object*);
lean_object* l_ExceptT_catch(lean_object*, lean_object*);
lean_object* l_Except_toBool___rarg___boxed(lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_mk___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_MonadExcept_orelse___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_Monad___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_MonadExcept___rarg(lean_object*);
lean_object* l_MonadExcept_orelse_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_finally___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_adapt___boxed(lean_object*, lean_object*);
lean_object* l_Except_Monad___closed__7;
lean_object* l_finally___rarg___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_MonadFunctor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_MonadExcept___lambda__1(lean_object*, lean_object*);
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4(lean_object*, lean_object*);
lean_object* l_Except_bind___rarg(lean_object*, lean_object*);
lean_object* l_ExceptT_MonadExcept___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_Monad___closed__4;
lean_object* l_ExceptT_Monad___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_toString___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_toString___rarg___closed__2;
lean_object* l_Except_Monad___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_exceptTOfExcept___boxed(lean_object*, lean_object*);
lean_object* l_ExceptT_bindCont(lean_object*, lean_object*);
lean_object* l_ExceptT_catch___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map___rarg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Except_HasRepr(lean_object*, lean_object*);
lean_object* l_monadExceptAdapterTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_bind(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_pure___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Except_toBool___rarg(lean_object*);
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_ExceptT_Monad___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_finally___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_MonadExceptAdapter(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_return___rarg(lean_object*);
lean_object* l_ExceptT_pure(lean_object*, lean_object*);
lean_object* l_Except_HasToString___rarg(lean_object*, lean_object*);
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Except_toBool(lean_object*, lean_object*);
lean_object* l_ExceptT_map(lean_object*, lean_object*);
lean_object* l_ExceptT_HasMonadLift___rarg(lean_object*);
lean_object* l_ExceptT_Monad___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_MonadFunctor___rarg(lean_object*, lean_object*);
lean_object* l_ExceptT_mk(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_Monad___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_run___rarg(lean_object*);
lean_object* l_ExceptT_map___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_Monad___rarg___lambda__8___boxed(lean_object*, lean_object*);
lean_object* l_ExceptT_MonadExcept___boxed(lean_object*, lean_object*);
lean_object* l_ExceptT_map___boxed(lean_object*, lean_object*);
lean_object* l_MonadExcept_orelse_x27___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_MonadExcept_orelse_x27(lean_object*, lean_object*);
lean_object* l_ExceptT_MonadFunctor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_exceptTOfExcept___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_Monad___rarg___lambda__8(lean_object*, lean_object*);
lean_object* l_MonadExcept_orelse_x27___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_adapt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_catch___rarg(lean_object*, lean_object*);
lean_object* l_Except_Inhabited___rarg(lean_object*);
lean_object* l_Except_Monad___closed__3;
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3(lean_object*, lean_object*);
lean_object* l_Except_Inhabited(lean_object*, lean_object*);
lean_object* l_ExceptT_MonadRun(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_MonadRun___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_Monad___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2(lean_object*, lean_object*);
lean_object* l_ExceptT_MonadFail___boxed(lean_object*);
lean_object* l_monadExceptAdapterTrans___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_bindCont___boxed(lean_object*, lean_object*);
lean_object* l_ExceptT_lift___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_lift(lean_object*, lean_object*);
lean_object* l_Except_Monad___closed__5;
lean_object* l_ExceptT_bind(lean_object*, lean_object*);
lean_object* l_Except_MonadExcept___closed__3;
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_Monad(lean_object*);
lean_object* l_ExceptT_MonadRun___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_bindCont___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_catch___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_MonadExcept_orelse___boxed(lean_object*, lean_object*);
lean_object* l_MonadExcept_orelse_x27___rarg___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_MonadFail___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_lift___boxed(lean_object*, lean_object*);
lean_object* l_Except_toString(lean_object*, lean_object*);
lean_object* l_ExceptT_Monad___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_Monad___rarg(lean_object*);
lean_object* l_MonadExcept_orelse_x27___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_Monad___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_finally___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_catch(lean_object*, lean_object*);
lean_object* l_MonadExcept_orelse(lean_object*, lean_object*);
lean_object* l_Except_Monad___closed__8;
lean_object* l_Except_Monad___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_finally___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_HasRepr___rarg(lean_object*, lean_object*);
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_ExceptT_Monad(lean_object*, lean_object*);
lean_object* l_Except_Monad___closed__1;
lean_object* l_monadExceptAdapterTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_Monad___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_finally(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_Monad___closed__2;
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_map___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_Monad___boxed(lean_object*, lean_object*);
lean_object* l_Except_MonadExcept___closed__1;
lean_object* l_Except_mapError___rarg(lean_object*, lean_object*);
lean_object* l_ExceptT_MonadExceptAdapter___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_toString___rarg___closed__1;
lean_object* l_monadFunctorTTrans___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_run(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_Monad___rarg___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_bind___boxed(lean_object*, lean_object*);
lean_object* l_MonadExcept_liftExcept___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_finally___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_Inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Except_Inhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_Inhabited___rarg), 1, 0);
return x_3;
}
}
lean_object* _init_l_Except_toString___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(error ");
return x_1;
}
}
lean_object* _init_l_Except_toString___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(ok ");
return x_1;
}
}
lean_object* l_Except_toString___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_Except_toString___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Option_HasRepr___rarg___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_apply_1(x_2, x_10);
x_12 = l_Except_toString___rarg___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Option_HasRepr___rarg___closed__3;
x_15 = lean_string_append(x_13, x_14);
return x_15;
}
}
}
lean_object* l_Except_toString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_toString___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Except_repr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_Except_toString___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Option_HasRepr___rarg___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_apply_1(x_2, x_10);
x_12 = l_Except_toString___rarg___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Option_HasRepr___rarg___closed__3;
x_15 = lean_string_append(x_13, x_14);
return x_15;
}
}
}
lean_object* l_Except_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_repr___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Except_HasToString___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_toString___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Except_HasToString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_HasToString___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Except_HasRepr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_repr___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Except_HasRepr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_HasRepr___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Except_return___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Except_return(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_return___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Except_map___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_apply_1(x_1, x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
lean_object* l_Except_map(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Except_mapError___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
lean_object* l_Except_mapError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Except_mapError___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Except_bind___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
lean_dec(x_2);
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Except_bind(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Except_bind___rarg), 2, 0);
return x_4;
}
}
uint8_t l_Except_toBool___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
lean_object* l_Except_toBool(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_toBool___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_Except_toBool___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Except_toBool___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Except_toOption___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
lean_object* l_Except_toOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_toOption___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_Except_toOption___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Except_toOption___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Except_catch___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Except_catch(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_catch___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Except_Monad___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
}
}
}
lean_object* l_Except_Monad___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_apply_1(x_11, x_13);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_apply_1(x_11, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
lean_object* l_Except_Monad___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
}
lean_object* l_Except_Monad___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_dec(x_3);
lean_inc(x_4);
return x_4;
}
}
}
lean_object* _init_l_Except_Monad___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_map), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
lean_object* _init_l_Except_Monad___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_Monad___lambda__1), 4, 0);
return x_1;
}
}
lean_object* _init_l_Except_Monad___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Except_Monad___closed__1;
x_2 = l_Except_Monad___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Except_Monad___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_return), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
lean_object* _init_l_Except_Monad___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_Monad___lambda__2), 4, 0);
return x_1;
}
}
lean_object* _init_l_Except_Monad___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_Monad___lambda__3), 4, 0);
return x_1;
}
}
lean_object* _init_l_Except_Monad___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_Monad___lambda__4___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Except_Monad___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Except_Monad___closed__3;
x_2 = l_Except_Monad___closed__4;
x_3 = l_Except_Monad___closed__5;
x_4 = l_Except_Monad___closed__6;
x_5 = l_Except_Monad___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
lean_object* _init_l_Except_Monad___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_bind), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
lean_object* _init_l_Except_Monad___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Except_Monad___closed__8;
x_2 = l_Except_Monad___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Except_Monad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Except_Monad___closed__10;
return x_2;
}
}
lean_object* l_Except_Monad___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Except_Monad___lambda__4(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_ExceptT_mk___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_ExceptT_mk(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ExceptT_mk___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_ExceptT_mk___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ExceptT_mk___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_ExceptT_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ExceptT_mk(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_ExceptT_run___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_ExceptT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ExceptT_run___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_ExceptT_run___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ExceptT_run___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_ExceptT_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ExceptT_run(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_ExceptT_pure___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_ExceptT_pure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_pure___rarg), 3, 0);
return x_3;
}
}
lean_object* l_ExceptT_pure___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_pure(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ExceptT_bindCont___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
}
}
lean_object* l_ExceptT_bindCont(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_bindCont___rarg), 5, 0);
return x_3;
}
}
lean_object* l_ExceptT_bindCont___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_bindCont(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ExceptT_bind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_ExceptT_bindCont___rarg), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, lean_box(0));
lean_closure_set(x_7, 3, x_5);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_4, x_7);
return x_8;
}
}
lean_object* l_ExceptT_bind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_bind___rarg), 5, 0);
return x_3;
}
}
lean_object* l_ExceptT_bind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_bind(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ExceptT_map___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_1(x_2, x_14);
lean_ctor_set(x_3, 0, x_17);
x_18 = lean_apply_2(x_16, lean_box(0), x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_1(x_2, x_19);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_apply_2(x_21, lean_box(0), x_23);
return x_24;
}
}
}
}
lean_object* l_ExceptT_map___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_ExceptT_map___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_5, x_7);
return x_8;
}
}
lean_object* l_ExceptT_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_map___rarg), 5, 0);
return x_3;
}
}
lean_object* l_ExceptT_map___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_map(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ExceptT_lift___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_ExceptT_lift___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ExceptT_lift___rarg___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_ExceptT_lift___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_ExceptT_lift___rarg___closed__1;
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_3);
return x_8;
}
}
lean_object* l_ExceptT_lift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_lift___rarg), 3, 0);
return x_3;
}
}
lean_object* l_ExceptT_lift___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_lift(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ExceptT_exceptTOfExcept___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_3);
return x_6;
}
}
lean_object* l_ExceptT_exceptTOfExcept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_exceptTOfExcept___rarg), 3, 0);
return x_3;
}
}
lean_object* l_ExceptT_exceptTOfExcept___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_exceptTOfExcept(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ExceptT_HasMonadLift___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ExceptT_lift___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_ExceptT_HasMonadLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_HasMonadLift___rarg), 1, 0);
return x_3;
}
}
lean_object* l_ExceptT_HasMonadLift___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_HasMonadLift(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ExceptT_catch___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_3);
return x_8;
}
}
}
lean_object* l_ExceptT_catch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_ExceptT_catch___rarg___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_3, x_6);
return x_7;
}
}
lean_object* l_ExceptT_catch(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_catch___rarg), 4, 0);
return x_3;
}
}
lean_object* l_ExceptT_catch___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_catch(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ExceptT_MonadFunctor___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_ExceptT_MonadFunctor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_ExceptT_MonadFunctor___rarg), 2, 0);
return x_7;
}
}
lean_object* l_ExceptT_MonadFunctor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ExceptT_MonadFunctor(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
}
}
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg), 5, 0);
return x_3;
}
}
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
}
}
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg), 5, 0);
return x_3;
}
}
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
}
}
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg), 5, 0);
return x_3;
}
}
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
}
}
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg), 5, 0);
return x_3;
}
}
lean_object* l_ExceptT_Monad___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_ctor_set(x_3, 0, x_2);
x_17 = lean_apply_2(x_16, lean_box(0), x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
return x_21;
}
}
}
}
lean_object* l_ExceptT_Monad___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_ExceptT_Monad___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_5, x_7);
return x_8;
}
}
lean_object* l_ExceptT_Monad___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_ExceptT_map___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_2, x_5);
return x_6;
}
}
lean_object* l_ExceptT_Monad___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_ExceptT_Monad___rarg___lambda__3), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, lean_box(0));
lean_closure_set(x_8, 3, x_6);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_4, x_8);
return x_9;
}
}
lean_object* l_ExceptT_Monad___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_ExceptT_Monad___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_ExceptT_Monad___rarg___lambda__5___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, lean_box(0));
lean_closure_set(x_6, 3, x_4);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_2, x_6);
return x_7;
}
}
lean_object* l_ExceptT_Monad___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_ExceptT_Monad___rarg___lambda__6), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, lean_box(0));
lean_closure_set(x_8, 3, x_6);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_4, x_8);
return x_9;
}
}
lean_object* l_ExceptT_Monad___rarg___lambda__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_ExceptT_Monad___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_ExceptT_Monad___rarg___lambda__8___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, lean_box(0));
lean_closure_set(x_8, 3, x_6);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_4, x_8);
return x_9;
}
}
lean_object* l_ExceptT_Monad___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_ExceptT_map___rarg), 5, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_ExceptT_Monad___rarg___lambda__2), 5, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_ExceptT_pure___rarg), 3, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_ExceptT_Monad___rarg___lambda__4), 5, 1);
lean_closure_set(x_6, 0, x_1);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_ExceptT_Monad___rarg___lambda__7), 5, 1);
lean_closure_set(x_7, 0, x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_ExceptT_Monad___rarg___lambda__9), 5, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_8);
x_10 = lean_alloc_closure((void*)(l_ExceptT_bind___rarg), 5, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
lean_object* l_ExceptT_Monad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_Monad___rarg), 1, 0);
return x_3;
}
}
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ExceptT_Monad___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ExceptT_Monad___rarg___lambda__5(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_ExceptT_Monad___rarg___lambda__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_Monad___rarg___lambda__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_ExceptT_Monad___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_Monad(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ExceptT_adapt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_Except_mapError___rarg), 2, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_5);
return x_10;
}
}
lean_object* l_ExceptT_adapt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_adapt___rarg), 5, 0);
return x_3;
}
}
lean_object* l_ExceptT_adapt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_adapt(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_MonadExcept_orelse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_ExceptT_Monad___rarg___lambda__8___boxed), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_apply_3(x_5, lean_box(0), x_3, x_6);
return x_7;
}
}
lean_object* l_MonadExcept_orelse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_MonadExcept_orelse___rarg), 4, 0);
return x_3;
}
}
lean_object* l_MonadExcept_orelse___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_orelse(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_MonadExcept_orelse_x27___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_2 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_7, lean_box(0), x_3);
return x_8;
}
}
}
lean_object* l_MonadExcept_orelse_x27___rarg___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(x_2);
x_7 = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_5);
x_8 = lean_apply_3(x_3, lean_box(0), x_4, x_7);
return x_8;
}
}
lean_object* l_MonadExcept_orelse_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_box(x_5);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_4);
x_9 = lean_apply_3(x_6, lean_box(0), x_3, x_8);
return x_9;
}
}
lean_object* l_MonadExcept_orelse_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_MonadExcept_orelse_x27___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_MonadExcept_orelse_x27___rarg___lambda__1(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_MonadExcept_orelse_x27___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_MonadExcept_orelse_x27___rarg___lambda__2(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_MonadExcept_orelse_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_MonadExcept_orelse_x27___rarg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
lean_object* l_MonadExcept_orelse_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_orelse_x27(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_MonadExcept_liftExcept___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_2, x_6);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_12, lean_box(0), x_10);
return x_13;
}
}
}
lean_object* l_MonadExcept_liftExcept(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_MonadExcept_liftExcept___rarg), 5, 0);
return x_4;
}
}
lean_object* l_MonadExcept_liftExcept___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_MonadExcept_liftExcept(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_ExceptT_MonadExcept___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_ExceptT_MonadExcept___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_ExceptT_MonadExcept___rarg___lambda__1), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_ExceptT_catch___rarg), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_ExceptT_MonadExcept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_MonadExcept___rarg), 1, 0);
return x_3;
}
}
lean_object* l_ExceptT_MonadExcept___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_MonadExcept(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Except_MonadExcept___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* _init_l_Except_MonadExcept___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_catch), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
lean_object* _init_l_Except_MonadExcept___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_MonadExcept___lambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Except_MonadExcept___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Except_MonadExcept___closed__2;
x_2 = l_Except_MonadExcept___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Except_MonadExcept(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Except_MonadExcept___closed__3;
return x_2;
}
}
lean_object* l_monadExceptAdapterTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_monadFunctorTTrans___rarg___lambda__1), 4, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_3(x_1, lean_box(0), x_6, x_5);
return x_7;
}
}
lean_object* l_monadExceptAdapterTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_monadExceptAdapterTrans___rarg), 5, 0);
return x_7;
}
}
lean_object* l_monadExceptAdapterTrans___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_monadExceptAdapterTrans(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_ExceptT_MonadExceptAdapter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Except_mapError___rarg), 2, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_4);
return x_9;
}
}
lean_object* l_ExceptT_MonadExceptAdapter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ExceptT_MonadExceptAdapter___rarg), 4, 0);
return x_4;
}
}
lean_object* l_ExceptT_MonadExceptAdapter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ExceptT_MonadExceptAdapter(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_ExceptT_MonadRun___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_ExceptT_MonadRun(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ExceptT_MonadRun___rarg), 3, 0);
return x_4;
}
}
lean_object* l_ExceptT_MonadRun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ExceptT_MonadRun(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_ExceptT_MonadFail___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_ExceptT_MonadFail(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ExceptT_MonadFail___rarg), 3, 0);
return x_2;
}
}
lean_object* l_ExceptT_MonadFail___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ExceptT_MonadFail(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_finally___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
}
lean_object* l_finally___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_finally___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_3, x_5);
return x_6;
}
}
lean_object* l_finally___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_2);
return x_5;
}
}
lean_object* l_finally___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_finally___rarg___lambda__3___boxed), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_3, x_5);
return x_6;
}
}
lean_object* l_finally___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_finally___rarg___lambda__2), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_4);
lean_inc(x_6);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_3, x_7);
x_9 = lean_alloc_closure((void*)(l_finally___rarg___lambda__4), 4, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_4);
x_10 = lean_apply_3(x_5, lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_finally(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_finally___rarg), 4, 0);
return x_5;
}
}
lean_object* l_finally___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_finally___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_finally___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_finally___rarg___lambda__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_finally___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_finally(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* initialize_Init_Control_Alternative(lean_object*);
lean_object* initialize_Init_Control_Lift(lean_object*);
lean_object* initialize_Init_Data_ToString(lean_object*);
lean_object* initialize_Init_Control_MonadFail(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Control_Except(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Alternative(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Lift(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_MonadFail(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Except_toString___rarg___closed__1 = _init_l_Except_toString___rarg___closed__1();
lean_mark_persistent(l_Except_toString___rarg___closed__1);
l_Except_toString___rarg___closed__2 = _init_l_Except_toString___rarg___closed__2();
lean_mark_persistent(l_Except_toString___rarg___closed__2);
l_Except_Monad___closed__1 = _init_l_Except_Monad___closed__1();
lean_mark_persistent(l_Except_Monad___closed__1);
l_Except_Monad___closed__2 = _init_l_Except_Monad___closed__2();
lean_mark_persistent(l_Except_Monad___closed__2);
l_Except_Monad___closed__3 = _init_l_Except_Monad___closed__3();
lean_mark_persistent(l_Except_Monad___closed__3);
l_Except_Monad___closed__4 = _init_l_Except_Monad___closed__4();
lean_mark_persistent(l_Except_Monad___closed__4);
l_Except_Monad___closed__5 = _init_l_Except_Monad___closed__5();
lean_mark_persistent(l_Except_Monad___closed__5);
l_Except_Monad___closed__6 = _init_l_Except_Monad___closed__6();
lean_mark_persistent(l_Except_Monad___closed__6);
l_Except_Monad___closed__7 = _init_l_Except_Monad___closed__7();
lean_mark_persistent(l_Except_Monad___closed__7);
l_Except_Monad___closed__8 = _init_l_Except_Monad___closed__8();
lean_mark_persistent(l_Except_Monad___closed__8);
l_Except_Monad___closed__9 = _init_l_Except_Monad___closed__9();
lean_mark_persistent(l_Except_Monad___closed__9);
l_Except_Monad___closed__10 = _init_l_Except_Monad___closed__10();
lean_mark_persistent(l_Except_Monad___closed__10);
l_ExceptT_lift___rarg___closed__1 = _init_l_ExceptT_lift___rarg___closed__1();
lean_mark_persistent(l_ExceptT_lift___rarg___closed__1);
l_Except_MonadExcept___closed__1 = _init_l_Except_MonadExcept___closed__1();
lean_mark_persistent(l_Except_MonadExcept___closed__1);
l_Except_MonadExcept___closed__2 = _init_l_Except_MonadExcept___closed__2();
lean_mark_persistent(l_Except_MonadExcept___closed__2);
l_Except_MonadExcept___closed__3 = _init_l_Except_MonadExcept___closed__3();
lean_mark_persistent(l_Except_MonadExcept___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
