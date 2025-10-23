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
static lean_object* l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Compiler_initFn____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_(lean_object*);
static lean_object* l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_checkMeta;
static lean_object* l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_check;
static lean_object* l_Lean_Compiler_initFn___closed__6____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Compiler_initFn____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn___closed__7____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
static lean_object* l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Compiler_initFn____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_alloc_ctor(1, 0, 1);
x_9 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, 0, x_9);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_inc(x_1);
x_11 = lean_register_option(x_1, x_10, x_4);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_inc(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("check", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_2 = l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type check code after each compiler step (this is useful for debugging purses)", 78, 78);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_2 = l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_3 = 0;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__6____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__7____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_2 = l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_3 = l_Lean_Compiler_initFn___closed__6____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_4 = l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_3 = l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_4 = l_Lean_Compiler_initFn___closed__7____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_5 = l_Lean_Option_register___at___Lean_Compiler_initFn____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Compiler_initFn____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___Lean_Compiler_initFn____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4__spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkMeta", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
x_2 = l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Check that `meta` declarations only refer to other `meta` declarations and ditto for non-`meta` declarations. Disabling this option may lead to delayed compiler errors and is\n    intended only for debugging purposes.", 216, 216);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
x_2 = l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
x_2 = l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_3 = l_Lean_Compiler_initFn___closed__6____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_4 = l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
x_3 = l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
x_4 = l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
x_5 = l_Lean_Option_register___at___Lean_Compiler_initFn____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Util_Trace(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Options(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__6____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__6____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__6____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__7____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__7____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__7____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options_1537036116____hygCtx___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_check = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_check);
lean_dec_ref(res);
}l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_);
l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = _init_l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_checkMeta = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_checkMeta);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
