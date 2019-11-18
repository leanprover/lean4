// Lean compiler output
// Module: Init.Lean.Meta.WHNF
// Imports: Init.Lean.AuxRecursor Init.Lean.WHNF Init.Lean.Meta.Basic
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
lean_object* l_Lean_Meta_unfoldDefinitionAux(lean_object*);
extern lean_object* l_EIO_Monad___closed__1;
extern lean_object* l_Lean_noConfusionExt;
lean_object* l_Lean_Meta_whnfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinitionAux___rarg___closed__2;
lean_object* l_ReaderT_Monad___rarg(lean_object*);
lean_object* l_Lean_Meta_unfoldDefinitionAux___rarg___closed__1;
lean_object* l_Lean_Meta_unfoldDefinitionAux___rarg___closed__4;
extern lean_object* l_Lean_auxRecExt;
lean_object* l_Lean_Meta_unfoldDefinitionAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinitionAux___rarg___closed__3;
lean_object* l_Lean_Meta_getConstNoEx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinitionAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinitionAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_unfoldDefinitionAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfCore___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfAux___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinitionAux___rarg___closed__5;
lean_object* l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_auxRecExt;
x_6 = l_Lean_TagDeclarationExtension_isTagged(x_5, x_4, x_1);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_noConfusionExt;
x_8 = l_Lean_TagDeclarationExtension_isTagged(x_7, x_4, x_1);
lean_dec(x_4);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
lean_object* l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_unfoldDefinitionAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_unfoldDefinitionAux___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EIO_Monad___closed__1;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_unfoldDefinitionAux___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getConstNoEx___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_unfoldDefinitionAux___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_unfoldDefinitionAux___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_unfoldDefinitionAux___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getExprMVarAssignment___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_unfoldDefinitionAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_10, 0, x_6);
x_11 = l_Lean_Meta_unfoldDefinitionAux___rarg___closed__1;
x_12 = l_Lean_Meta_unfoldDefinitionAux___rarg___closed__2;
x_13 = l_Lean_Meta_unfoldDefinitionAux___rarg___closed__3;
x_14 = l_Lean_Meta_unfoldDefinitionAux___rarg___closed__4;
x_15 = l_Lean_Meta_unfoldDefinitionAux___rarg___closed__5;
x_16 = l_Lean_unfoldDefinitionAux___rarg(x_11, x_12, x_13, x_1, x_2, x_3, x_4, x_14, x_15, x_5, x_10, x_7);
x_17 = lean_apply_2(x_16, x_8, x_9);
return x_17;
}
}
lean_object* l_Lean_Meta_unfoldDefinitionAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_unfoldDefinitionAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_unfoldDefinitionAux___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Meta_whnfAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_whnfAux___main), 6, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
x_10 = l_Lean_Meta_unfoldDefinitionAux___rarg___closed__2;
x_11 = l_Lean_Meta_unfoldDefinitionAux___rarg___closed__3;
x_12 = l_Lean_Meta_unfoldDefinitionAux___rarg___closed__4;
x_13 = l_Lean_Meta_unfoldDefinitionAux___rarg___closed__5;
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_9);
x_14 = l_Lean_whnfCore___main___rarg(x_4, x_10, x_11, x_9, x_1, x_2, x_12, x_13, x_6);
lean_inc(x_7);
x_15 = lean_apply_2(x_14, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_16);
x_18 = lean_alloc_closure((void*)(l_ReaderT_pure___rarg___boxed), 4, 3);
lean_closure_set(x_18, 0, x_5);
lean_closure_set(x_18, 1, lean_box(0));
lean_closure_set(x_18, 2, x_16);
lean_inc(x_9);
x_19 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_9, x_1, x_2, x_3, x_16, x_18, x_9, x_7, x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l_Lean_Meta_whnfAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_Meta_unfoldDefinitionAux___rarg___closed__1;
x_8 = l_EIO_Monad___closed__1;
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_whnfAux___main___lambda__1), 8, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_7);
lean_closure_set(x_9, 4, x_8);
x_10 = l_Lean_Meta_unfoldDefinitionAux___rarg___closed__4;
x_11 = l_Lean_Meta_unfoldDefinitionAux___rarg___closed__5;
x_12 = l_Lean_whnfEasyCases___main___rarg(x_7, x_10, x_11, x_4, x_9);
x_13 = lean_apply_2(x_12, x_5, x_6);
return x_13;
}
}
lean_object* l_Lean_Meta_whnfAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_whnfAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Init_Lean_AuxRecursor(lean_object*);
lean_object* initialize_Init_Lean_WHNF(lean_object*);
lean_object* initialize_Init_Lean_Meta_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_WHNF(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_AuxRecursor(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_WHNF(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_unfoldDefinitionAux___rarg___closed__1 = _init_l_Lean_Meta_unfoldDefinitionAux___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_unfoldDefinitionAux___rarg___closed__1);
l_Lean_Meta_unfoldDefinitionAux___rarg___closed__2 = _init_l_Lean_Meta_unfoldDefinitionAux___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_unfoldDefinitionAux___rarg___closed__2);
l_Lean_Meta_unfoldDefinitionAux___rarg___closed__3 = _init_l_Lean_Meta_unfoldDefinitionAux___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_unfoldDefinitionAux___rarg___closed__3);
l_Lean_Meta_unfoldDefinitionAux___rarg___closed__4 = _init_l_Lean_Meta_unfoldDefinitionAux___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_unfoldDefinitionAux___rarg___closed__4);
l_Lean_Meta_unfoldDefinitionAux___rarg___closed__5 = _init_l_Lean_Meta_unfoldDefinitionAux___rarg___closed__5();
lean_mark_persistent(l_Lean_Meta_unfoldDefinitionAux___rarg___closed__5);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
