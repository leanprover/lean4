// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Preprocess
// Imports: Init Lean.Meta.Transform Lean.Elab.RecAppSyntax
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
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_preprocess___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
extern lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_preprocess___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t l_Lean_KVMap_contains(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isConstOf(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 0;
x_4 = l_Lean_Expr_isHeadBetaTarget(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lambda__1___boxed), 2, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_Lean_Expr_getAppFn(x_1);
x_8 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = 1;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Structural_preprocess___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = l_Lean_Elab_Structural_preprocess___lambda__1___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Expr_headBeta(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 10)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey;
x_10 = l_Lean_KVMap_contains(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_13 = l_Lean_Expr_app___override(x_8, x_6);
x_14 = l_Lean_Expr_mdata___override(x_7, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_preprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_preprocess___lambda__2___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_preprocess___lambda__1___boxed), 5, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_Lean_Elab_Structural_preprocess___closed__1;
x_8 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_1, x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Structural_preprocess___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Structural_preprocess___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_RecAppSyntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_Preprocess(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_RecAppSyntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Structural_preprocess___lambda__1___closed__1 = _init_l_Lean_Elab_Structural_preprocess___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_preprocess___lambda__1___closed__1);
l_Lean_Elab_Structural_preprocess___closed__1 = _init_l_Lean_Elab_Structural_preprocess___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_preprocess___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
