// Lean compiler output
// Module: Lean.Compiler.Options
// Imports: public import Lean.Util.Trace
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
static lean_object* l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
static lean_object* l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4____boxed(lean_object*);
static lean_object* l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_checkMeta;
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_check;
static lean_object* l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4____boxed(lean_object*);
static lean_object* l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_alloc_ctor(1, 0, 1);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, 0, x_9);
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_7);
lean_inc(x_1);
x_11 = lean_register_option(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 0, 1);
x_21 = lean_unbox(x_18);
lean_ctor_set_uint8(x_20, 0, x_21);
lean_inc(x_1);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_19);
lean_inc(x_1);
x_23 = lean_register_option(x_1, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_24 = x_23;
} else {
 lean_dec_ref(x_23);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_18);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_1);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_28 = x_23;
} else {
 lean_dec_ref(x_23);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("check", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
x_2 = l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type check code after each compiler step (this is useful for debugging purses)", 78, 78);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
x_2 = l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
x_3 = l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
x_4 = l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
x_3 = l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
x_4 = l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
x_5 = l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkMeta", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
x_2 = l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Check that `meta` declarations only refer to other `meta` declarations and ditto for non-`meta` declarations. Disabling this option may lead to delayed compiler errors and is\n    intended only for debugging purposes.", 216, 216);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
x_2 = l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
x_3 = l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
x_4 = l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
x_3 = l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
x_4 = l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
x_5 = l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
return x_2;
}
}
lean_object* initialize_Lean_Util_Trace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Options(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_check = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_check);
lean_dec_ref(res);
}l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_checkMeta = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_checkMeta);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
