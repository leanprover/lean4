// Lean compiler output
// Module: Lean.Util.LakePath
// Imports: Init.System.IO
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
LEAN_EXPORT lean_object* l_Lean_determineLakePath(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lean_determineLakePath___closed__1;
lean_object* lean_io_getenv(lean_object*, lean_object*);
static lean_object* l_Lean_determineLakePath___closed__3;
lean_object* l_IO_appDir(lean_object*);
static lean_object* l_Lean_determineLakePath___closed__2;
static lean_object* l_Lean_determineLakePath___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_determineLakePath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_determineLakePath___closed__0;
x_3 = lean_io_getenv(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_determineLakePath___closed__1;
x_7 = lean_io_getenv(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_IO_appDir(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_determineLakePath___closed__2;
x_14 = l_System_FilePath_join(x_12, x_13);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = l_Lean_determineLakePath___closed__2;
x_18 = l_System_FilePath_join(x_15, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
return x_10;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_7, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
lean_dec(x_8);
x_23 = l_Lean_determineLakePath___closed__3;
x_24 = l_System_FilePath_join(x_22, x_23);
x_25 = l_Lean_determineLakePath___closed__2;
x_26 = l_System_FilePath_join(x_24, x_25);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
lean_dec(x_8);
x_29 = l_Lean_determineLakePath___closed__3;
x_30 = l_System_FilePath_join(x_28, x_29);
x_31 = l_Lean_determineLakePath___closed__2;
x_32 = l_System_FilePath_join(x_30, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_3, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
lean_dec(x_4);
lean_ctor_set(x_3, 0, x_36);
return x_3;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_dec(x_3);
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
lean_dec(x_4);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_LakePath(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
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
