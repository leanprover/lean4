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
static const lean_string_object l_Lean_determineLakePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LAKE"};
static const lean_object* l_Lean_determineLakePath___closed__0 = (const lean_object*)&l_Lean_determineLakePath___closed__0_value;
static const lean_string_object l_Lean_determineLakePath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LEAN_SYSROOT"};
static const lean_object* l_Lean_determineLakePath___closed__1 = (const lean_object*)&l_Lean_determineLakePath___closed__1_value;
static const lean_string_object l_Lean_determineLakePath___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l_Lean_determineLakePath___closed__2 = (const lean_object*)&l_Lean_determineLakePath___closed__2_value;
static const lean_string_object l_Lean_determineLakePath___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bin"};
static const lean_object* l_Lean_determineLakePath___closed__3 = (const lean_object*)&l_Lean_determineLakePath___closed__3_value;
lean_object* lean_io_getenv(lean_object*);
lean_object* l_IO_appDir();
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_determineLakePath();
LEAN_EXPORT lean_object* l_Lean_determineLakePath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_determineLakePath() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_determineLakePath___closed__0));
x_3 = lean_io_getenv(x_2);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 0);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = ((lean_object*)(l_Lean_determineLakePath___closed__1));
x_13 = lean_io_getenv(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = l_IO_appDir();
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_15 = lean_ctor_get(x_14, 0);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
x_16 = x_14;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = ((lean_object*)(l_Lean_determineLakePath___closed__2));
x_19 = l_System_FilePath_join(x_15, x_18);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_19);
x_20 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
return x_14;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_36; 
x_25 = lean_ctor_get(x_13, 0);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
x_26 = x_13;
x_27 = x_36;
goto block_35;
}
else
{
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_box(0);
x_27 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = ((lean_object*)(l_Lean_determineLakePath___closed__3));
x_29 = l_System_FilePath_join(x_25, x_28);
x_30 = ((lean_object*)(l_Lean_determineLakePath___closed__2));
x_31 = l_System_FilePath_join(x_29, x_30);
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 0, x_31);
x_32 = x_26;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
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
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_LakePath(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_IO(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_LakePath(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_LakePath(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_LakePath(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_LakePath(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_LakePath(builtin);
}
#ifdef __cplusplus
}
#endif
