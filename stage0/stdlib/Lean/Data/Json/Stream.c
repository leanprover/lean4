// Lean compiler output
// Module: Lean.Data.Json.Stream
// Imports: public import Lean.Data.Json.Parser public import Lean.Data.Json.Printer
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
static const lean_string_object l_IO_FS_Stream_readUTF8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invalid UTF-8"};
static const lean_object* l_IO_FS_Stream_readUTF8___closed__0 = (const lean_object*)&l_IO_FS_Stream_readUTF8___closed__0_value;
lean_object* lean_mk_io_user_error(lean_object*);
static lean_once_cell_t l_IO_FS_Stream_readUTF8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_readUTF8___closed__1;
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readUTF8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readUTF8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readJson___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeJson___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_IO_FS_Stream_readUTF8___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_IO_FS_Stream_readUTF8___closed__0));
x_2 = lean_mk_io_user_error(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readUTF8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_usize_of_nat(x_2);
x_6 = lean_box_usize(x_5);
x_7 = lean_apply_2(x_4, x_6, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_21; 
x_8 = lean_ctor_get(x_7, 0);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
x_9 = x_7;
x_10 = x_21;
goto block_20;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_21;
goto block_20;
}
block_20:
{
uint8_t x_11; 
x_11 = lean_string_validate_utf8(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
x_12 = lean_obj_once(&l_IO_FS_Stream_readUTF8___closed__1, &l_IO_FS_Stream_readUTF8___closed__1_once, _init_l_IO_FS_Stream_readUTF8___closed__1);
if (x_10 == 0)
{
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
x_13 = x_9;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_string_from_utf8_unchecked(x_8);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_16);
x_17 = x_9;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
x_22 = lean_ctor_get(x_7, 0);
x_29 = !lean_is_exclusive(x_7);
if (x_29 == 0)
{
x_23 = x_7;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readUTF8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_readUTF8(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
x_4 = x_1;
x_5 = x_11;
goto block_10;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_io_user_error(x_3);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_6);
x_7 = x_4;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
x_13 = x_1;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readJson(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_usize_of_nat(x_2);
x_6 = lean_box_usize(x_5);
x_7 = lean_apply_2(x_4, x_6, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_20; 
x_8 = lean_ctor_get(x_7, 0);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
x_9 = x_7;
x_10 = x_20;
goto block_19;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_20;
goto block_19;
}
block_19:
{
uint8_t x_11; 
x_11 = lean_string_validate_utf8(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
x_12 = lean_obj_once(&l_IO_FS_Stream_readUTF8___closed__1, &l_IO_FS_Stream_readUTF8___closed__1_once, _init_l_IO_FS_Stream_readUTF8___closed__1);
if (x_10 == 0)
{
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
x_13 = x_9;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_del_object(x_9);
x_16 = lean_string_from_utf8_unchecked(x_8);
x_17 = l_Lean_Json_parse(x_16);
x_18 = l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg(x_17);
return x_18;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_21 = lean_ctor_get(x_7, 0);
x_28 = !lean_is_exclusive(x_7);
if (x_28 == 0)
{
x_22 = x_7;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readJson___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_readJson(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeJson(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = l_Lean_Json_compress(x_2);
x_7 = lean_apply_2(x_5, x_6, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec_ref(x_7);
x_8 = lean_apply_1(x_4, lean_box(0));
return x_8;
}
else
{
lean_dec_ref(x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeJson___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeJson(x_1, x_2);
return x_4;
}
}
lean_object* runtime_initialize_Lean_Data_Json_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json_Printer(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Json_Stream(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Json_Parser(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_Printer(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Json_Stream(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json_Parser(uint8_t builtin);
lean_object* initialize_Lean_Data_Json_Printer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_Stream(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_Parser(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Printer(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_Stream(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Json_Stream(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Json_Stream(builtin);
}
#ifdef __cplusplus
}
#endif
