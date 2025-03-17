// Lean compiler output
// Module: Lean.Data.Json.Stream
// Imports: Init.System.IO Lean.Data.Json.Parser Lean.Data.Json.Printer Lean.Data.Json.FromToJson
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
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l_IO_FS_Stream_readJson___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readJson___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readJson(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readJson___closed__2;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_IO_FS_Stream_readJson___spec__1(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
static lean_object* l_IO_FS_Stream_readJson___closed__3;
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_any(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_IO_FS_Stream_readJson___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
lean_ctor_set_tag(x_1, 18);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
}
static lean_object* _init_l_IO_FS_Stream_readJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8", 13, 13);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readJson___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readJson___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readJson___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readJson(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_usize_of_nat(x_2);
x_6 = lean_box_usize(x_5);
x_7 = lean_apply_2(x_4, x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_string_validate_utf8(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = l_IO_FS_Stream_readJson___closed__2;
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_7);
x_13 = lean_string_from_utf8_unchecked(x_9);
lean_dec(x_9);
x_14 = l_IO_FS_Stream_readJson___closed__3;
x_15 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_14, x_13);
x_16 = l_IO_ofExcept___at_IO_FS_Stream_readJson___spec__1(x_15, x_10);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_string_validate_utf8(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
x_20 = l_IO_FS_Stream_readJson___closed__2;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_string_from_utf8_unchecked(x_17);
lean_dec(x_17);
x_23 = l_IO_FS_Stream_readJson___closed__3;
x_24 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_23, x_22);
x_25 = l_IO_ofExcept___at_IO_FS_Stream_readJson___spec__1(x_24, x_18);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
return x_7;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readJson___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_readJson(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeJson(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = l_Lean_Json_compress(x_2);
x_6 = lean_apply_2(x_4, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_8, x_7);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_Parser(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_Printer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_FromToJson(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_Stream(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Parser(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Printer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_FromToJson(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_IO_FS_Stream_readJson___closed__1 = _init_l_IO_FS_Stream_readJson___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readJson___closed__1);
l_IO_FS_Stream_readJson___closed__2 = _init_l_IO_FS_Stream_readJson___closed__2();
lean_mark_persistent(l_IO_FS_Stream_readJson___closed__2);
l_IO_FS_Stream_readJson___closed__3 = _init_l_IO_FS_Stream_readJson___closed__3();
lean_mark_persistent(l_IO_FS_Stream_readJson___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
