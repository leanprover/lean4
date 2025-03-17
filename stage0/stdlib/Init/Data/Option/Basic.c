// Lean compiler output
// Module: Init.Data.Option.Basic
// Imports: Init.Control.Basic
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
LEAN_EXPORT lean_object* l_Option_isNone(lean_object*);
static lean_object* l_instAlternativeOption___closed__1;
LEAN_EXPORT lean_object* l_instLEOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_tryCatch___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_guard___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq(lean_object*);
LEAN_EXPORT lean_object* l_Option_guard(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instAlternativeOption;
LEAN_EXPORT lean_object* l_instMonadOption___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_max(lean_object*);
LEAN_EXPORT lean_object* l_Option_instOrElse___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_mapM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instMin___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Option_mapA___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableEq(lean_object*);
LEAN_EXPORT lean_object* l_Option_liftOrGet___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadOption___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getM___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instAlternativeOption___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instOrElse(lean_object*);
LEAN_EXPORT lean_object* l_Option_filter___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toList(lean_object*);
LEAN_EXPORT lean_object* l_Option_mapA(lean_object*);
LEAN_EXPORT lean_object* l_Option_isNone___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Option_any(lean_object*);
LEAN_EXPORT lean_object* l_Option_orElse(lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfUnitOption___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toArray(lean_object*);
static lean_object* l_instMonadOption___closed__2;
LEAN_EXPORT lean_object* l_instMonadExceptOfUnitOption___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfUnitOption___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_min___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_isEqSome(lean_object*);
LEAN_EXPORT uint8_t l_Option_isNone___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Option_bind(lean_object*, lean_object*);
static lean_object* l_instAlternativeOption___closed__3;
LEAN_EXPORT lean_object* l_instFunctorOption;
LEAN_EXPORT lean_object* l_Option_or___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_bind___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instFunctorOption___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instMonadOption___closed__6;
LEAN_EXPORT lean_object* l_Option_instMin(lean_object*);
LEAN_EXPORT lean_object* l_Option_max___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_merge(lean_object*);
LEAN_EXPORT lean_object* l_Option_instMax(lean_object*);
static lean_object* l_instMonadOption___closed__7;
LEAN_EXPORT lean_object* l_Option_or(lean_object*);
LEAN_EXPORT lean_object* l_instLTOption(lean_object*, lean_object*);
static lean_object* l_instMonadOption___closed__4;
LEAN_EXPORT lean_object* l_Option_isEqSome___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_join(lean_object*);
static lean_object* l_instMonadOption___closed__1;
LEAN_EXPORT lean_object* l_Option_all(lean_object*);
LEAN_EXPORT lean_object* l_instMonadOption;
LEAN_EXPORT lean_object* l_instMonadOption___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_elimM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4_(lean_object*);
LEAN_EXPORT lean_object* l_Option_bindM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instFunctorOption___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_mapA___rarg___closed__1;
LEAN_EXPORT lean_object* l_Option_sequence(lean_object*);
LEAN_EXPORT lean_object* l_Option_filter(lean_object*);
LEAN_EXPORT uint8_t l_Option_isSome___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Option_elimM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getDM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_elim___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_get(lean_object*);
LEAN_EXPORT lean_object* l_Option_any___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toList___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Option_bindM___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_instFunctorOption___closed__3;
LEAN_EXPORT lean_object* l_Option_instMax___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_instMonadOption___closed__3;
LEAN_EXPORT lean_object* l_Option_join___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Option_sequence___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_instAlternativeOption___closed__2;
LEAN_EXPORT lean_object* l_Option_tryCatch(lean_object*);
static lean_object* l_instMonadExceptOfUnitOption___closed__3;
LEAN_EXPORT lean_object* l_Option_mapM___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getDM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toList___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Option_all___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadOption___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_or___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_elimM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadOption___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_elim___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_mapM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instAlternativeOption___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_instMonadOption___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instLEOption___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159_(lean_object*);
LEAN_EXPORT lean_object* l_liftOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instLTOption___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_tryCatch___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_instMonadOption___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instMonadExceptOfUnitOption___closed__2;
LEAN_EXPORT lean_object* l_Option_mapA___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_isSome(lean_object*);
static lean_object* l_instFunctorOption___closed__2;
LEAN_EXPORT lean_object* l_Option_min(lean_object*);
LEAN_EXPORT lean_object* l_Option_toArray___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfUnitOption;
LEAN_EXPORT lean_object* l_Option_elim(lean_object*, lean_object*);
static lean_object* l_instMonadExceptOfUnitOption___closed__1;
LEAN_EXPORT lean_object* l_Option_getDM___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_orElse___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Option_get___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_elimM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_join___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Option_isSome___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Option_liftOrGet(lean_object*);
static lean_object* l_Option_toArray___rarg___closed__1;
LEAN_EXPORT lean_object* l_Option_merge___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftOption___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfUnitOption___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_instMonadOption___closed__5;
LEAN_EXPORT lean_object* l_Option_get___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_bindM___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_instFunctorOption___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = lean_box(x_4);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = 0;
x_7 = lean_box(x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_box(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_apply_2(x_1, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_instDecidableEq___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = lean_box(x_4);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = 0;
x_7 = lean_box(x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_box(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_apply_2(x_1, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_instBEq___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_instBEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_instBEq___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_getM___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Option_getM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_getM___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Option_isSome___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Option_isSome(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_isSome___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_isSome___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Option_isSome___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Option_isNone___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Option_isNone(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_isNone___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_isNone___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Option_isNone___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_isEqSome___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = 0;
x_5 = lean_box(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_2(x_1, x_6, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Option_isEqSome(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_isEqSome___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_bind___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Option_bind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_bind___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_bindM___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_2(x_4, lean_box(0), x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Option_bindM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_apply_1(x_2, x_8);
x_11 = lean_alloc_closure((void*)(l_Option_bindM___rarg___lambda__1), 2, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Option_bindM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Option_bindM___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_mapM___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Option_mapM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_apply_1(x_2, x_8);
x_11 = lean_alloc_closure((void*)(l_Option_mapM___rarg___lambda__1), 2, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Option_mapM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Option_mapM___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_filter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_free_object(x_2);
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
return x_2;
}
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_9);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_filter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_filter___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_all___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = 1;
x_4 = lean_box(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_1(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Option_all(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_all___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_any___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = 0;
x_4 = lean_box(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_1(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Option_any(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_any___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_orElse___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
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
LEAN_EXPORT lean_object* l_Option_orElse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_orElse___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
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
LEAN_EXPORT lean_object* l_Option_instOrElse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_instOrElse___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_or___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
uint8_t x_3; 
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
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_or(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_or___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_or___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_or___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_box(x_4);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = 1;
x_7 = lean_box(x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_box(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_apply_2(x_1, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Option_instDecidableRelLt___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_merge___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
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
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_apply_2(x_1, x_11, x_13);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_apply_2(x_1, x_11, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_merge(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_merge___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_elim___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Option_elim(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_elim___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_elim___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Option_elim___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_get___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_get(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_get___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_get___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_get___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_guard___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unbox(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Option_guard(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_guard___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_toList___rarg(lean_object* x_1) {
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(0);
lean_inc(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Option_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_toList___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_toList___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_toList___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Option_toArray___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_toArray___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_toArray___rarg___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(0);
lean_inc(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_array_mk(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Option_toArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_toArray___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_toArray___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_toArray___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_liftOrGet___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
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
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_apply_2(x_1, x_11, x_13);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_apply_2(x_1, x_11, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_liftOrGet(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_liftOrGet___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_join___rarg(lean_object* x_1) {
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
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Option_join(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_join___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_join___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_join___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_mapA___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Option_mapA___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Option_mapA___rarg___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Option_mapA___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_1(x_4, x_9);
x_13 = l_Option_mapA___rarg___closed__1;
x_14 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Option_mapA(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_mapA___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_sequence___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Option_mapA___rarg___closed__1;
x_13 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Option_sequence(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_sequence___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_elimM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Option_elimM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Option_elimM___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Option_elimM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Option_elimM___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_elimM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Option_elimM___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_getDM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Option_getDM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_getDM___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_getDM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Option_getDM___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_min___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_apply_2(x_1, x_6, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_apply_2(x_1, x_6, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_min(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_min___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_instMin___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_min___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_instMin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_instMin___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_max___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
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
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_apply_2(x_1, x_11, x_13);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_apply_2(x_1, x_11, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_max(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_max___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_instMax___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_max___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_instMax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_instMax___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instLTOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instLTOption___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instLTOption(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instLEOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instLEOption___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instLEOption(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instFunctorOption___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_apply_1(x_3, x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_apply_1(x_3, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_instFunctorOption___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
}
}
}
static lean_object* _init_l_instFunctorOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instFunctorOption___lambda__1), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instFunctorOption___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instFunctorOption___lambda__2), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instFunctorOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instFunctorOption___closed__1;
x_2 = l_instFunctorOption___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_instFunctorOption() {
_start:
{
lean_object* x_1; 
x_1 = l_instFunctorOption___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_apply_1(x_6, x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_apply_1(x_6, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_inc(x_6);
lean_ctor_set(x_8, 0, x_6);
return x_8;
}
else
{
lean_object* x_12; 
lean_dec(x_8);
lean_inc(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
}
}
static lean_object* _init_l_instMonadOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadOption___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadOption___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadOption___lambda__2), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadOption___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadOption___lambda__3___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadOption___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadOption___lambda__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadOption___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_instFunctorOption;
x_2 = l_instMonadOption___closed__1;
x_3 = l_instMonadOption___closed__2;
x_4 = l_instMonadOption___closed__3;
x_5 = l_instMonadOption___closed__4;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_instMonadOption___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadOption___lambda__5), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadOption___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instMonadOption___closed__5;
x_2 = l_instMonadOption___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_instMonadOption() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadOption___closed__7;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instMonadOption___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instMonadOption___lambda__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instAlternativeOption___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instAlternativeOption___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
static lean_object* _init_l_instAlternativeOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instAlternativeOption___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instAlternativeOption___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instAlternativeOption___lambda__2), 3, 0);
return x_1;
}
}
static lean_object* _init_l_instAlternativeOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_instMonadOption;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_instAlternativeOption___closed__1;
x_4 = l_instAlternativeOption___closed__2;
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_instAlternativeOption() {
_start:
{
lean_object* x_1; 
x_1 = l_instAlternativeOption___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_liftOption___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_liftOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_liftOption___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_tryCatch___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_tryCatch___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfUnitOption___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfUnitOption___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
static lean_object* _init_l_instMonadExceptOfUnitOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadExceptOfUnitOption___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadExceptOfUnitOption___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadExceptOfUnitOption___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadExceptOfUnitOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instMonadExceptOfUnitOption___closed__1;
x_2 = l_instMonadExceptOfUnitOption___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_instMonadExceptOfUnitOption() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadExceptOfUnitOption___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfUnitOption___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instMonadExceptOfUnitOption___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfUnitOption___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instMonadExceptOfUnitOption___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Control_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Option_toArray___rarg___closed__1 = _init_l_Option_toArray___rarg___closed__1();
lean_mark_persistent(l_Option_toArray___rarg___closed__1);
l_Option_mapA___rarg___closed__1 = _init_l_Option_mapA___rarg___closed__1();
lean_mark_persistent(l_Option_mapA___rarg___closed__1);
l_instFunctorOption___closed__1 = _init_l_instFunctorOption___closed__1();
lean_mark_persistent(l_instFunctorOption___closed__1);
l_instFunctorOption___closed__2 = _init_l_instFunctorOption___closed__2();
lean_mark_persistent(l_instFunctorOption___closed__2);
l_instFunctorOption___closed__3 = _init_l_instFunctorOption___closed__3();
lean_mark_persistent(l_instFunctorOption___closed__3);
l_instFunctorOption = _init_l_instFunctorOption();
lean_mark_persistent(l_instFunctorOption);
l_instMonadOption___closed__1 = _init_l_instMonadOption___closed__1();
lean_mark_persistent(l_instMonadOption___closed__1);
l_instMonadOption___closed__2 = _init_l_instMonadOption___closed__2();
lean_mark_persistent(l_instMonadOption___closed__2);
l_instMonadOption___closed__3 = _init_l_instMonadOption___closed__3();
lean_mark_persistent(l_instMonadOption___closed__3);
l_instMonadOption___closed__4 = _init_l_instMonadOption___closed__4();
lean_mark_persistent(l_instMonadOption___closed__4);
l_instMonadOption___closed__5 = _init_l_instMonadOption___closed__5();
lean_mark_persistent(l_instMonadOption___closed__5);
l_instMonadOption___closed__6 = _init_l_instMonadOption___closed__6();
lean_mark_persistent(l_instMonadOption___closed__6);
l_instMonadOption___closed__7 = _init_l_instMonadOption___closed__7();
lean_mark_persistent(l_instMonadOption___closed__7);
l_instMonadOption = _init_l_instMonadOption();
lean_mark_persistent(l_instMonadOption);
l_instAlternativeOption___closed__1 = _init_l_instAlternativeOption___closed__1();
lean_mark_persistent(l_instAlternativeOption___closed__1);
l_instAlternativeOption___closed__2 = _init_l_instAlternativeOption___closed__2();
lean_mark_persistent(l_instAlternativeOption___closed__2);
l_instAlternativeOption___closed__3 = _init_l_instAlternativeOption___closed__3();
lean_mark_persistent(l_instAlternativeOption___closed__3);
l_instAlternativeOption = _init_l_instAlternativeOption();
lean_mark_persistent(l_instAlternativeOption);
l_instMonadExceptOfUnitOption___closed__1 = _init_l_instMonadExceptOfUnitOption___closed__1();
lean_mark_persistent(l_instMonadExceptOfUnitOption___closed__1);
l_instMonadExceptOfUnitOption___closed__2 = _init_l_instMonadExceptOfUnitOption___closed__2();
lean_mark_persistent(l_instMonadExceptOfUnitOption___closed__2);
l_instMonadExceptOfUnitOption___closed__3 = _init_l_instMonadExceptOfUnitOption___closed__3();
lean_mark_persistent(l_instMonadExceptOfUnitOption___closed__3);
l_instMonadExceptOfUnitOption = _init_l_instMonadExceptOfUnitOption();
lean_mark_persistent(l_instMonadExceptOfUnitOption);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
