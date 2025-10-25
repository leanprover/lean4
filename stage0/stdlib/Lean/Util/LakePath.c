// Lean compiler output
// Module: Lean.Util.LakePath
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
LEAN_EXPORT lean_object* l_Lean_determineLakePath();
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lean_determineLakePath___closed__1;
lean_object* lean_io_getenv(lean_object*);
static lean_object* l_Lean_determineLakePath___closed__3;
lean_object* l_IO_appDir();
static lean_object* l_Lean_determineLakePath___closed__2;
static lean_object* l_Lean_determineLakePath___closed__0;
LEAN_EXPORT lean_object* l_Lean_determineLakePath___boxed(lean_object*);
static lean_object* _init_l_Lean_determineLakePath___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_determineLakePath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_SYSROOT", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_determineLakePath___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_determineLakePath___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bin", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_determineLakePath() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_determineLakePath___closed__0;
x_3 = lean_io_getenv(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_determineLakePath___closed__1;
x_5 = lean_io_getenv(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_IO_appDir();
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_determineLakePath___closed__2;
x_10 = l_System_FilePath_join(x_8, x_9);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l_Lean_determineLakePath___closed__2;
x_13 = l_System_FilePath_join(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
return x_6;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = l_Lean_determineLakePath___closed__3;
x_18 = l_System_FilePath_join(x_16, x_17);
x_19 = l_Lean_determineLakePath___closed__2;
x_20 = l_System_FilePath_join(x_18, x_19);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_5, 0);
lean_inc(x_21);
lean_dec(x_5);
x_22 = l_Lean_determineLakePath___closed__3;
x_23 = l_System_FilePath_join(x_21, x_22);
x_24 = l_Lean_determineLakePath___closed__2;
x_25 = l_System_FilePath_join(x_23, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_determineLakePath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_determineLakePath();
return x_2;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_LakePath(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_determineLakePath___closed__0 = _init_l_Lean_determineLakePath___closed__0();
lean_mark_persistent(l_Lean_determineLakePath___closed__0);
l_Lean_determineLakePath___closed__1 = _init_l_Lean_determineLakePath___closed__1();
lean_mark_persistent(l_Lean_determineLakePath___closed__1);
l_Lean_determineLakePath___closed__2 = _init_l_Lean_determineLakePath___closed__2();
lean_mark_persistent(l_Lean_determineLakePath___closed__2);
l_Lean_determineLakePath___closed__3 = _init_l_Lean_determineLakePath___closed__3();
lean_mark_persistent(l_Lean_determineLakePath___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
