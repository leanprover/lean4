// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Preprocess
// Imports: Init Lean.Meta.Transform
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_preprocess___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
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
uint8_t x_3; 
x_3 = l_Lean_Expr_isHeadBetaTarget(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Lean_Expr_getAppFn(x_1);
x_7 = 8192;
x_8 = l_Lean_Expr_FindImpl_initCache;
x_9 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_5, x_7, x_6, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = 1;
return x_12;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
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
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Transform(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_Preprocess(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Structural_preprocess___closed__1 = _init_l_Lean_Elab_Structural_preprocess___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_preprocess___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
