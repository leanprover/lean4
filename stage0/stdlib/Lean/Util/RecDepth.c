// Lean compiler output
// Module: Lean.Util.RecDepth
// Imports: public import Lean.Data.Options
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_;
extern lean_object* l_Lean_defaultMaxRecDepth;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_maxRecDepth;
static lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_;
static lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4____boxed(lean_object*);
static lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_;
static lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_;
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_6);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_7);
lean_inc(x_1);
x_10 = lean_register_option(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_17);
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_18);
lean_inc(x_1);
x_21 = lean_register_option(x_1, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_22 = x_21;
} else {
 lean_dec_ref(x_21);
 x_22 = lean_box(0);
}
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_17);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
lean_dec(x_1);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_26 = x_21;
} else {
 lean_dec_ref(x_21);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4__spec__0(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__2_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum recursion depth for many Lean procedures", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__2_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_;
x_2 = l_Lean_defaultMaxRecDepth;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__4_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_;
x_2 = l_Lean_initFn___closed__4_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_;
x_3 = l_Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_;
x_4 = l_Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_;
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_();
return x_2;
}
}
lean_object* initialize_Lean_Data_Options(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_RecDepth(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_ = _init_l_Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_);
l_Lean_initFn___closed__1_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_ = _init_l_Lean_initFn___closed__1_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__1_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_);
l_Lean_initFn___closed__2_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_ = _init_l_Lean_initFn___closed__2_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__2_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_);
l_Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_ = _init_l_Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_);
l_Lean_initFn___closed__4_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_ = _init_l_Lean_initFn___closed__4_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__4_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_);
l_Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_ = _init_l_Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_initFn_00___x40_Lean_Util_RecDepth_171279117____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_maxRecDepth = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_maxRecDepth);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
