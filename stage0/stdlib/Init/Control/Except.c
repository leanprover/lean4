// Lean compiler output
// Module: Init.Control.Except
// Imports: Init.Control.Basic Init.Control.Id Init.Coe
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
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_tryFinally___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Id_finally(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_lift___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_pure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_lift___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_adapt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_tryFinally___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_toOption___rarg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Except_instMonadExcept___closed__7;
LEAN_EXPORT lean_object* l_Except_instMonadExcept(lean_object*);
LEAN_EXPORT lean_object* l_observing___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_orElseLazy___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_toOption___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExceptExceptT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_bind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlExceptT___rarg___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_tryFinally___rarg___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Except_toBool___rarg___boxed(lean_object*);
static lean_object* l_instMonadControlExceptT___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Except_pure___rarg(lean_object*);
LEAN_EXPORT lean_object* l_observing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctorExceptT___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ExceptT_lift___rarg___closed__1;
LEAN_EXPORT lean_object* l_observing___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___rarg___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_finally___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_adapt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExceptT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Except_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_tryFinally(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_instMonadExcept___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_ExceptT_finally___rarg___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont(lean_object*, lean_object*);
static lean_object* l_instMonadExceptOfExcept___closed__3;
LEAN_EXPORT lean_object* l_Except_mapError___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_toBool(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctorExceptT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlExceptT___rarg___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_instMonadExcept___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_map(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Except_instMonadExcept___closed__10;
LEAN_EXPORT lean_object* l_instMonadControlExceptT___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Except_toBool___rarg(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedExceptT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedExceptT___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_pure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_lift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_tryCatch___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlExceptT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_pure___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_finally(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_tryCatch___rarg(lean_object*, lean_object*);
static lean_object* l_Except_instMonadExcept___closed__8;
LEAN_EXPORT lean_object* l_ExceptT_finally___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Except_instMonadExcept___closed__4;
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_map___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_tryFinally___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_mapError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_instMonadExcept___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_mk___rarg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_mk___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Except_tryCatch(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_instMonadExcept___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_tryCatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept(lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExceptExceptT___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_orElseLazy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_tryCatch(lean_object*, lean_object*);
static lean_object* l_Except_instMonadExcept___closed__5;
LEAN_EXPORT lean_object* l_ExceptT_mk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_bind___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instMonadExceptOfExcept___closed__2;
LEAN_EXPORT lean_object* l_tryFinally___rarg___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_map(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT(lean_object*, lean_object*);
static lean_object* l_instMonadControlExceptT___rarg___closed__1;
static lean_object* l_Except_instMonadExcept___closed__6;
static lean_object* l_instMonadExceptOfExcept___closed__1;
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_run___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_toOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Except_instMonadExcept___closed__9;
LEAN_EXPORT lean_object* l_ExceptT_run___rarg(lean_object*);
static lean_object* l_Except_instMonadExcept___closed__1;
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExceptT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__8(lean_object*, lean_object*);
static lean_object* l_Except_instMonadExcept___closed__2;
LEAN_EXPORT lean_object* l_Id_finally___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_map___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_tryFinally___rarg___closed__1;
static lean_object* l_Except_instMonadExcept___closed__3;
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_observing___rarg___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlExceptT___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_pure___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Except_pure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_pure___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Except_map___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Except_map(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Except_mapError___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Except_mapError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Except_mapError___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Except_bind___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Except_bind(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Except_bind___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Except_toBool___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Except_toBool(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_toBool___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Except_toBool___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Except_toBool___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Except_toOption___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Except_toOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_toOption___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Except_toOption___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Except_toOption___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Except_tryCatch___rarg(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_tryCatch(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_tryCatch___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Except_orElseLazy___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_orElseLazy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Except_orElseLazy___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Except_instMonadExcept___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Except_instMonadExcept___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_apply_1(x_8, x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_apply_1(x_8, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_instMonadExcept___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_16; 
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_8);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_instMonadExcept___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_4, x_8);
return x_9;
}
}
}
static lean_object* _init_l_Except_instMonadExcept___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_map), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Except_instMonadExcept___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_instMonadExcept___lambda__1), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Except_instMonadExcept___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Except_instMonadExcept___closed__1;
x_2 = l_Except_instMonadExcept___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Except_instMonadExcept___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_pure), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Except_instMonadExcept___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_instMonadExcept___lambda__2), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Except_instMonadExcept___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_instMonadExcept___lambda__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Except_instMonadExcept___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_instMonadExcept___lambda__4), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Except_instMonadExcept___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Except_instMonadExcept___closed__3;
x_2 = l_Except_instMonadExcept___closed__4;
x_3 = l_Except_instMonadExcept___closed__5;
x_4 = l_Except_instMonadExcept___closed__6;
x_5 = l_Except_instMonadExcept___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Except_instMonadExcept___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_bind), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Except_instMonadExcept___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Except_instMonadExcept___closed__8;
x_2 = l_Except_instMonadExcept___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Except_instMonadExcept(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Except_instMonadExcept___closed__10;
return x_2;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ExceptT_mk___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ExceptT_mk___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ExceptT_run___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ExceptT_run___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ExceptT_pure___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_ExceptT_pure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_pure___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_ExceptT_bindCont(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_bindCont___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_ExceptT_bind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_bind___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_map___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_ExceptT_map___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_ExceptT_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_map___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_lift___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_ExceptT_lift___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ExceptT_lift___rarg___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ExceptT_lift___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_ExceptT_lift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_lift___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExceptExceptT___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExceptExceptT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_instMonadLiftExceptExceptT___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExceptT___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ExceptT_lift___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExceptT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_instMonadLiftExceptT___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_ExceptT_tryCatch___rarg___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_tryCatch___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctorExceptT___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctorExceptT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ExceptT_instMonadFunctorExceptT___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__1___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__2___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__3___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__4___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_ExceptT_instMonadExceptT___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_box(0);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_ExceptT_map___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_ExceptT_instMonadExceptT___rarg___lambda__3), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__1___rarg), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, lean_box(0));
lean_closure_set(x_8, 3, x_6);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_4, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_box(0);
x_5 = lean_apply_1(x_1, x_4);
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_ExceptT_instMonadExceptT___rarg___lambda__5___boxed), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__2___rarg), 5, 4);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, lean_box(0));
lean_closure_set(x_8, 3, x_6);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_ExceptT_instMonadExceptT___rarg___lambda__6), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__3___rarg), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, lean_box(0));
lean_closure_set(x_8, 3, x_6);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_4, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_ExceptT_instMonadExceptT___rarg___lambda__8___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_ExceptT_instMonadExceptT___spec__4___rarg), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, lean_box(0));
lean_closure_set(x_8, 3, x_6);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_4, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_ExceptT_map___rarg), 5, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_ExceptT_instMonadExceptT___rarg___lambda__2), 5, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_ExceptT_pure___rarg), 3, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_ExceptT_instMonadExceptT___rarg___lambda__4), 5, 1);
lean_closure_set(x_6, 0, x_1);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_ExceptT_instMonadExceptT___rarg___lambda__7), 5, 1);
lean_closure_set(x_7, 0, x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_ExceptT_instMonadExceptT___rarg___lambda__9), 5, 1);
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
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_instMonadExceptT___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ExceptT_instMonadExceptT___rarg___lambda__5(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadExceptT___rarg___lambda__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ExceptT_instMonadExceptT___rarg___lambda__8(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_adapt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_ExceptT_adapt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_adapt___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_5, lean_box(0), x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___rarg___lambda__1), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___rarg___lambda__2), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instMonadExceptOfExceptT(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT__1___rarg___lambda__1), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_ExceptT_tryCatch___rarg), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT__1___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instInhabitedExceptT___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instInhabitedExceptT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instInhabitedExceptT___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_instMonadExceptOfExcept___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_tryCatch), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_instMonadExceptOfExcept___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadExceptOfExcept___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadExceptOfExcept___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instMonadExceptOfExcept___closed__2;
x_2 = l_instMonadExceptOfExcept___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadExceptOfExcept___closed__3;
return x_2;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___rarg___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
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
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_MonadExcept_orelse_x27___rarg___lambda__1(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_MonadExcept_orelse_x27___rarg___lambda__2(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_MonadExcept_orelse_x27___rarg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_observing___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_observing___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_observing___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_observing___rarg___lambda__1), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_3, x_6);
x_8 = lean_alloc_closure((void*)(l_observing___rarg___lambda__2), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_apply_3(x_4, lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_observing(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_observing___rarg), 3, 0);
return x_4;
}
}
static lean_object* _init_l_instMonadControlExceptT___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ExceptT_run), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptT___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_instMonadControlExceptT___rarg___lambda__1___closed__1;
x_5 = lean_apply_1(x_3, x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_ExceptT_lift___rarg___closed__1;
x_10 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptT___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_instMonadControlExceptT___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadControlExceptT___rarg___lambda__2___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptT___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_instMonadControlExceptT___rarg___lambda__1), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_instMonadControlExceptT___rarg___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instMonadControlExceptT___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptT___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instMonadControlExceptT___rarg___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_tryFinally___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_tryFinally___rarg___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_tryFinally___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_tryFinally___rarg___lambda__2___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_tryFinally___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_alloc_closure((void*)(l_tryFinally___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_3, x_5);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_tryFinally___rarg___closed__1;
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_tryFinally(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_tryFinally___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_tryFinally___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_tryFinally___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_tryFinally___rarg___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_tryFinally___rarg___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Id_finally___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Id_finally(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Id_finally___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_free_object(x_2);
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
lean_ctor_set(x_2, 0, x_9);
x_10 = lean_apply_1(x_1, x_2);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_11);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_apply_1(x_1, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_16);
x_19 = lean_apply_2(x_18, lean_box(0), x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_24 = lean_apply_2(x_22, lean_box(0), x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 0);
lean_dec(x_27);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_28; 
lean_free_object(x_2);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_apply_2(x_30, lean_box(0), x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_36 = lean_apply_2(x_34, lean_box(0), x_35);
return x_36;
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_3, 0);
lean_inc(x_37);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
lean_ctor_set(x_2, 1, x_39);
lean_ctor_set(x_2, 0, x_37);
lean_ctor_set(x_26, 0, x_2);
x_42 = lean_apply_2(x_41, lean_box(0), x_26);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_26, 0);
lean_inc(x_43);
lean_dec(x_26);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
lean_ctor_set(x_2, 1, x_43);
lean_ctor_set(x_2, 0, x_37);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_2);
x_47 = lean_apply_2(x_45, lean_box(0), x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_dec(x_2);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_3);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
lean_dec(x_1);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_49);
x_54 = lean_apply_2(x_52, lean_box(0), x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_3, 0);
lean_inc(x_55);
lean_dec(x_3);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_57 = x_48;
} else {
 lean_dec_ref(x_48);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
lean_dec(x_1);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_56);
if (lean_is_scalar(x_57)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_57;
}
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_apply_2(x_59, lean_box(0), x_61);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_ExceptT_finally___rarg___lambda__1), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_5, x_8);
x_10 = lean_alloc_closure((void*)(l_ExceptT_finally___rarg___lambda__2), 2, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_finally___rarg), 6, 0);
return x_3;
}
}
lean_object* initialize_Init_Control_Basic(lean_object*);
lean_object* initialize_Init_Control_Id(lean_object*);
lean_object* initialize_Init_Coe(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_Except(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Id(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Coe(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Except_instMonadExcept___closed__1 = _init_l_Except_instMonadExcept___closed__1();
lean_mark_persistent(l_Except_instMonadExcept___closed__1);
l_Except_instMonadExcept___closed__2 = _init_l_Except_instMonadExcept___closed__2();
lean_mark_persistent(l_Except_instMonadExcept___closed__2);
l_Except_instMonadExcept___closed__3 = _init_l_Except_instMonadExcept___closed__3();
lean_mark_persistent(l_Except_instMonadExcept___closed__3);
l_Except_instMonadExcept___closed__4 = _init_l_Except_instMonadExcept___closed__4();
lean_mark_persistent(l_Except_instMonadExcept___closed__4);
l_Except_instMonadExcept___closed__5 = _init_l_Except_instMonadExcept___closed__5();
lean_mark_persistent(l_Except_instMonadExcept___closed__5);
l_Except_instMonadExcept___closed__6 = _init_l_Except_instMonadExcept___closed__6();
lean_mark_persistent(l_Except_instMonadExcept___closed__6);
l_Except_instMonadExcept___closed__7 = _init_l_Except_instMonadExcept___closed__7();
lean_mark_persistent(l_Except_instMonadExcept___closed__7);
l_Except_instMonadExcept___closed__8 = _init_l_Except_instMonadExcept___closed__8();
lean_mark_persistent(l_Except_instMonadExcept___closed__8);
l_Except_instMonadExcept___closed__9 = _init_l_Except_instMonadExcept___closed__9();
lean_mark_persistent(l_Except_instMonadExcept___closed__9);
l_Except_instMonadExcept___closed__10 = _init_l_Except_instMonadExcept___closed__10();
lean_mark_persistent(l_Except_instMonadExcept___closed__10);
l_ExceptT_lift___rarg___closed__1 = _init_l_ExceptT_lift___rarg___closed__1();
lean_mark_persistent(l_ExceptT_lift___rarg___closed__1);
l_instMonadExceptOfExcept___closed__1 = _init_l_instMonadExceptOfExcept___closed__1();
lean_mark_persistent(l_instMonadExceptOfExcept___closed__1);
l_instMonadExceptOfExcept___closed__2 = _init_l_instMonadExceptOfExcept___closed__2();
lean_mark_persistent(l_instMonadExceptOfExcept___closed__2);
l_instMonadExceptOfExcept___closed__3 = _init_l_instMonadExceptOfExcept___closed__3();
lean_mark_persistent(l_instMonadExceptOfExcept___closed__3);
l_instMonadControlExceptT___rarg___lambda__1___closed__1 = _init_l_instMonadControlExceptT___rarg___lambda__1___closed__1();
lean_mark_persistent(l_instMonadControlExceptT___rarg___lambda__1___closed__1);
l_instMonadControlExceptT___rarg___closed__1 = _init_l_instMonadControlExceptT___rarg___closed__1();
lean_mark_persistent(l_instMonadControlExceptT___rarg___closed__1);
l_tryFinally___rarg___closed__1 = _init_l_tryFinally___rarg___closed__1();
lean_mark_persistent(l_tryFinally___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
