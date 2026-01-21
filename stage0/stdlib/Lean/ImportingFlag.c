// Lean compiler output
// Module: Lean.ImportingFlag
// Imports: public import Init.System.IO
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
LEAN_EXPORT lean_object* l_Lean_enableInitializersExecution___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInitializerExecutionEnabled();
LEAN_EXPORT lean_object* l_Lean_withImporting(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initializing();
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
LEAN_EXPORT lean_object* lean_enable_initializer_execution();
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2____boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_importingRef;
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_io_initializing();
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInitializerExecutionEnabled___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initializing___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_() {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_st_mk_ref(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_() {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_st_mk_ref(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* lean_enable_initializer_execution() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_st_ref_set(x_2, x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_enableInitializersExecution___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_enable_initializer_execution();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_isInitializerExecutionEnabled() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
x_3 = lean_st_ref_get(x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isInitializerExecutionEnabled___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_isInitializerExecutionEnabled();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initializing() {
_start:
{
uint8_t x_2; 
x_2 = lean_io_initializing();
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l___private_Lean_ImportingFlag_0__Lean_importingRef;
x_4 = lean_st_ref_get(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initializing___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initializing();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_box(x_2);
x_6 = lean_st_ref_set(x_1, x_5);
x_7 = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
x_8 = lean_box(x_2);
x_9 = lean_st_ref_set(x_7, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_withImporting___redArg___lam__0(x_1, x_5, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_3 = l___private_Lean_ImportingFlag_0__Lean_importingRef;
x_4 = 1;
x_5 = lean_box(x_4);
x_6 = lean_st_ref_set(x_3, x_5);
x_7 = 0;
x_8 = lean_apply_1(x_1, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_ctor_set_tag(x_8, 1);
x_11 = l_Lean_withImporting___redArg___lam__0(x_3, x_7, x_8);
lean_dec_ref(x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_10);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_withImporting___redArg___lam__0(x_3, x_7, x_16);
lean_dec_ref(x_16);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_18 = x_17;
} else {
 lean_dec_ref(x_17);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec_ref(x_8);
x_21 = lean_box(0);
x_22 = l_Lean_withImporting___redArg___lam__0(x_3, x_7, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; 
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_withImporting___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_withImporting___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_withImporting(x_1, x_2);
return x_4;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ImportingFlag(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ImportingFlag_0__Lean_importingRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ImportingFlag_0__Lean_importingRef);
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ImportingFlag_0__Lean_runInitializersRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ImportingFlag_0__Lean_runInitializersRef);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
