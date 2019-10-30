// Lean compiler output
// Module: Init.Lean.TypeInference
// Imports: Init.Control.Reader Init.Lean.NameGenerator Init.Lean.Environment Init.Lean.AbstractMetavarContext Init.Lean.Trace
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
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___closed__1;
lean_object* l_Lean_TypeInferenceState_backtrackable___lambda__1(lean_object*);
lean_object* l___private_Init_Lean_TypeInference_1__getOptions___rarg(lean_object*, lean_object*);
lean_object* l_Lean_TypeInference_tracer___closed__3;
lean_object* l_Lean_TypeInference_tracer___closed__1;
lean_object* l_Lean_TypeInferenceState_backtrackable___closed__2;
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeInference_2__getTraceState___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__1(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_TypeInference_tracer___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeInference_1__getOptions(lean_object*, lean_object*);
lean_object* l_Lean_TypeInferenceState_backtrackable___closed__3;
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___closed__2;
lean_object* l_Lean_TypeInference_tracer(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeInference_1__getOptions___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeInferenceState_backtrackable(lean_object*, lean_object*);
lean_object* l_Lean_TypeInferenceState_backtrackable___lambda__2(lean_object*, lean_object*);
lean_object* l_Lean_TypeInference_tracer___closed__4;
lean_object* l_Lean_TypeInference_tracer___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeInference_2__getTraceState___rarg(lean_object*);
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___closed__3;
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache;
lean_object* l_Lean_TypeInferenceState_backtrackable___lambda__1___boxed(lean_object*);
lean_object* l_Lean_TypeInference_tracer___closed__2;
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeInference_2__getTraceState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeInferenceState_backtrackable___closed__1;
lean_object* l_Lean_TypeInferenceState_backtrackable___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_TypeInferenceState_backtrackable___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
return x_10;
}
}
}
lean_object* _init_l_Lean_TypeInferenceState_backtrackable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TypeInferenceState_backtrackable___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_TypeInferenceState_backtrackable___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TypeInferenceState_backtrackable___lambda__2), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_TypeInferenceState_backtrackable___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_TypeInferenceState_backtrackable___closed__1;
x_2 = l_Lean_TypeInferenceState_backtrackable___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_TypeInferenceState_backtrackable(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeInferenceState_backtrackable___closed__3;
return x_3;
}
}
lean_object* l_Lean_TypeInferenceState_backtrackable___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TypeInferenceState_backtrackable___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_TypeInference_1__getOptions___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l___private_Init_Lean_TypeInference_1__getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeInference_1__getOptions___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeInference_1__getOptions___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_TypeInference_1__getOptions___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeInference_2__getTraceState___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeInference_2__getTraceState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeInference_2__getTraceState___rarg), 1, 0);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeInference_2__getTraceState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_TypeInference_2__getTraceState(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_TypeInference_tracer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 3);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_3, 3, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*5);
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_15 = lean_apply_1(x_1, x_12);
x_16 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_13);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* _init_l_Lean_TypeInference_tracer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeInference_2__getTraceState___boxed), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
lean_object* _init_l_Lean_TypeInference_tracer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeInference_1__getOptions___rarg___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_TypeInference_tracer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TypeInference_tracer___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_TypeInference_tracer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_TypeInference_tracer___closed__2;
x_2 = l_Lean_TypeInference_tracer___closed__3;
x_3 = l_Lean_TypeInference_tracer___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_TypeInference_tracer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeInference_tracer___closed__4;
return x_3;
}
}
lean_object* l_Lean_TypeInference_tracer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeInference_tracer___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* _init_l_Lean_typeContextNoCacheIsAbstractTCCache___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_typeContextNoCacheIsAbstractTCCache___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__2___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_typeContextNoCacheIsAbstractTCCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_typeContextNoCacheIsAbstractTCCache___closed__1;
x_2 = l_Lean_typeContextNoCacheIsAbstractTCCache___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_typeContextNoCacheIsAbstractTCCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_typeContextNoCacheIsAbstractTCCache___closed__3;
return x_1;
}
}
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__2(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Lean_NameGenerator(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_AbstractMetavarContext(lean_object*);
lean_object* initialize_Init_Lean_Trace(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_TypeInference(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_NameGenerator(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_AbstractMetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Trace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_TypeInferenceState_backtrackable___closed__1 = _init_l_Lean_TypeInferenceState_backtrackable___closed__1();
lean_mark_persistent(l_Lean_TypeInferenceState_backtrackable___closed__1);
l_Lean_TypeInferenceState_backtrackable___closed__2 = _init_l_Lean_TypeInferenceState_backtrackable___closed__2();
lean_mark_persistent(l_Lean_TypeInferenceState_backtrackable___closed__2);
l_Lean_TypeInferenceState_backtrackable___closed__3 = _init_l_Lean_TypeInferenceState_backtrackable___closed__3();
lean_mark_persistent(l_Lean_TypeInferenceState_backtrackable___closed__3);
l_Lean_TypeInference_tracer___closed__1 = _init_l_Lean_TypeInference_tracer___closed__1();
lean_mark_persistent(l_Lean_TypeInference_tracer___closed__1);
l_Lean_TypeInference_tracer___closed__2 = _init_l_Lean_TypeInference_tracer___closed__2();
lean_mark_persistent(l_Lean_TypeInference_tracer___closed__2);
l_Lean_TypeInference_tracer___closed__3 = _init_l_Lean_TypeInference_tracer___closed__3();
lean_mark_persistent(l_Lean_TypeInference_tracer___closed__3);
l_Lean_TypeInference_tracer___closed__4 = _init_l_Lean_TypeInference_tracer___closed__4();
lean_mark_persistent(l_Lean_TypeInference_tracer___closed__4);
l_Lean_typeContextNoCacheIsAbstractTCCache___closed__1 = _init_l_Lean_typeContextNoCacheIsAbstractTCCache___closed__1();
lean_mark_persistent(l_Lean_typeContextNoCacheIsAbstractTCCache___closed__1);
l_Lean_typeContextNoCacheIsAbstractTCCache___closed__2 = _init_l_Lean_typeContextNoCacheIsAbstractTCCache___closed__2();
lean_mark_persistent(l_Lean_typeContextNoCacheIsAbstractTCCache___closed__2);
l_Lean_typeContextNoCacheIsAbstractTCCache___closed__3 = _init_l_Lean_typeContextNoCacheIsAbstractTCCache___closed__3();
lean_mark_persistent(l_Lean_typeContextNoCacheIsAbstractTCCache___closed__3);
l_Lean_typeContextNoCacheIsAbstractTCCache = _init_l_Lean_typeContextNoCacheIsAbstractTCCache();
lean_mark_persistent(l_Lean_typeContextNoCacheIsAbstractTCCache);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
