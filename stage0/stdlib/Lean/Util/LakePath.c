// Lean compiler output
// Module: Lean.Util.LakePath
// Imports: Init
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
static lean_object* l_Lean_determineLakePath___lambda__1___closed__2;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lean_determineLakePath___closed__1;
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_determineLakePath___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_IO_appDir(lean_object*);
static lean_object* l_Lean_determineLakePath___closed__2;
static lean_object* l_Lean_determineLakePath___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_determineLakePath___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_determineLakePath___lambda__1___closed__1;
static lean_object* _init_l_Lean_determineLakePath___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LEAN_SYSROOT", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_determineLakePath___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lake", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_determineLakePath___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("bin", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_determineLakePath___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_determineLakePath___lambda__1___closed__1;
x_4 = lean_io_getenv(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_appDir(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_determineLakePath___lambda__1___closed__2;
x_11 = l_System_FilePath_join(x_9, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = l_Lean_determineLakePath___lambda__1___closed__2;
x_15 = l_System_FilePath_join(x_12, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_4, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
x_24 = l_Lean_determineLakePath___lambda__1___closed__3;
x_25 = l_System_FilePath_join(x_23, x_24);
x_26 = l_Lean_determineLakePath___lambda__1___closed__2;
x_27 = l_System_FilePath_join(x_25, x_26);
lean_ctor_set(x_4, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
lean_dec(x_5);
x_30 = l_Lean_determineLakePath___lambda__1___closed__3;
x_31 = l_System_FilePath_join(x_29, x_30);
x_32 = l_Lean_determineLakePath___lambda__1___closed__2;
x_33 = l_System_FilePath_join(x_31, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_determineLakePath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LAKE", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_determineLakePath___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_determineLakePath___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_determineLakePath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_determineLakePath___closed__1;
x_3 = lean_io_getenv(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_determineLakePath___closed__2;
x_7 = lean_box(0);
x_8 = lean_apply_2(x_6, x_7, x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_determineLakePath___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_determineLakePath___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_LakePath(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_determineLakePath___lambda__1___closed__1 = _init_l_Lean_determineLakePath___lambda__1___closed__1();
lean_mark_persistent(l_Lean_determineLakePath___lambda__1___closed__1);
l_Lean_determineLakePath___lambda__1___closed__2 = _init_l_Lean_determineLakePath___lambda__1___closed__2();
lean_mark_persistent(l_Lean_determineLakePath___lambda__1___closed__2);
l_Lean_determineLakePath___lambda__1___closed__3 = _init_l_Lean_determineLakePath___lambda__1___closed__3();
lean_mark_persistent(l_Lean_determineLakePath___lambda__1___closed__3);
l_Lean_determineLakePath___closed__1 = _init_l_Lean_determineLakePath___closed__1();
lean_mark_persistent(l_Lean_determineLakePath___closed__1);
l_Lean_determineLakePath___closed__2 = _init_l_Lean_determineLakePath___closed__2();
lean_mark_persistent(l_Lean_determineLakePath___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
