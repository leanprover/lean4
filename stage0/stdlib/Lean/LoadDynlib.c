// Lean compiler output
// Module: Lean.LoadDynlib
// Imports: public import Init.System.IO import Init.Data.String.TakeDrop import Init.Data.ToString.Macro
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
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_DynlibImpl;
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___boxed(lean_object*);
lean_object* lean_dynlib_load(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Dynlib_load___boxed(lean_object*, lean_object*);
lean_object* lean_dynlib_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Dynlib_get_x3f___boxed(lean_object*, lean_object*);
lean_object* lean_dynlib_symbol_run_as_init(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Dynlib_Symbol_runAsInit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_runtime_mark_persistent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_load_dynlib(lean_object*);
LEAN_EXPORT lean_object* l_Lean_loadDynlib___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_shared"};
static const lean_object* l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0 = (const lean_object*)&l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_once_cell_t l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(lean_object*);
static const lean_string_object l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00Lean_loadPlugin_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_loadPlugin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "initialize_"};
static const lean_object* l_Lean_loadPlugin___closed__0 = (const lean_object*)&l_Lean_loadPlugin___closed__0_value;
static const lean_string_object l_Lean_loadPlugin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "error loading plugin, initializer not found '"};
static const lean_object* l_Lean_loadPlugin___closed__1 = (const lean_object*)&l_Lean_loadPlugin___closed__1_value;
static const lean_string_object l_Lean_loadPlugin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_loadPlugin___closed__2 = (const lean_object*)&l_Lean_loadPlugin___closed__2_value;
static const lean_string_object l_Lean_loadPlugin___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "error, plugin has invalid file name '"};
static const lean_object* l_Lean_loadPlugin___closed__3 = (const lean_object*)&l_Lean_loadPlugin___closed__3_value;
lean_object* lean_io_realpath(lean_object*);
lean_object* l_System_FilePath_fileStem(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* lean_load_plugin(lean_object*);
LEAN_EXPORT lean_object* l_Lean_loadPlugin___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___boxed(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_LoadDynlib_0__Lean_DynlibImpl(void) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_load___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_dynlib_load(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_get_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_dynlib_get(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_Symbol_runAsInit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_dynlib_symbol_run_as_init(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_runtime_mark_persistent(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_load_dynlib(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_dynlib_load(x_1);
lean_dec_ref(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
x_5 = x_3;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_runtime_mark_persistent(x_4);
lean_dec(x_7);
x_8 = lean_box(0);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = lean_ctor_get(x_3, 0);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
x_15 = x_3;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
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
}
LEAN_EXPORT lean_object* l_Lean_loadDynlib___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_load_dynlib(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_runtime_mark_persistent(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_dynlib_symbol_run_as_init(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0));
x_6 = lean_obj_once(&l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1, &l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1_once, _init_l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1);
x_7 = lean_nat_sub(x_4, x_3);
x_8 = lean_nat_dec_le(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_sub(x_7, x_6);
lean_dec(x_7);
x_11 = lean_nat_add(x_3, x_10);
x_12 = lean_string_memcmp(x_2, x_5, x_11, x_9, x_6);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_21; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_13 = l_String_Slice_pos_x21(x_1, x_10);
lean_dec(x_10);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_1, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_14 = x_1;
x_15 = x_21;
goto block_20;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_nat_add(x_3, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_ctor_set(x_14, 2, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_16);
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
}
}
static lean_object* _init_l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = ((lean_object*)(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0));
x_6 = lean_obj_once(&l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1, &l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1_once, _init_l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1);
x_7 = lean_nat_sub(x_4, x_3);
x_8 = lean_nat_dec_le(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
return x_1;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_memcmp(x_2, x_5, x_3, x_9, x_6);
if (x_10 == 0)
{
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_11 = l_String_Slice_pos_x21(x_1, x_6);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_1, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_12 = x_1;
x_13 = x_19;
goto block_18;
}
else
{
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_nat_add(x_3, x_11);
lean_dec(x_11);
lean_dec(x_3);
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_4);
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
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00Lean_loadPlugin_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_load_plugin(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_realpath(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_50; 
x_4 = lean_ctor_get(x_3, 0);
x_50 = !lean_is_exclusive(x_3);
if (x_50 == 0)
{
x_5 = x_3;
x_6 = x_50;
goto block_49;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = l_System_FilePath_fileStem(x_4);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_del_object(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_dynlib_load(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_32; 
x_10 = lean_ctor_get(x_9, 0);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
x_11 = x_9;
x_12 = x_32;
goto block_31;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = ((lean_object*)(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0));
x_14 = l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(x_8, x_13);
x_15 = l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(x_14);
x_16 = ((lean_object*)(l_Lean_loadPlugin___closed__0));
x_17 = l_String_Slice_toString(x_15);
lean_dec_ref(x_15);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = lean_dynlib_get(x_10, x_18);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_18);
lean_del_object(x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc(x_10);
x_21 = lean_runtime_mark_persistent(x_10);
lean_dec(x_21);
x_22 = lean_dynlib_symbol_run_as_init(x_10, x_20);
lean_dec(x_20);
lean_dec(x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_19);
lean_dec(x_10);
x_23 = ((lean_object*)(l_Lean_loadPlugin___closed__1));
x_24 = lean_string_append(x_23, x_18);
lean_dec_ref(x_18);
x_25 = ((lean_object*)(l_Lean_loadPlugin___closed__2));
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_mk_io_user_error(x_26);
if (x_12 == 0)
{
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_27);
x_28 = x_11;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_8);
x_33 = lean_ctor_get(x_9, 0);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
x_34 = x_9;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_9);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_7);
x_41 = ((lean_object*)(l_Lean_loadPlugin___closed__3));
x_42 = lean_string_append(x_41, x_4);
lean_dec(x_4);
x_43 = ((lean_object*)(l_Lean_loadPlugin___closed__2));
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_mk_io_user_error(x_44);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_45);
x_46 = x_5;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
x_51 = lean_ctor_get(x_3, 0);
x_58 = !lean_is_exclusive(x_3);
if (x_58 == 0)
{
x_52 = x_3;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_3);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_loadPlugin___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_load_plugin(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LoadDynlib(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_IO(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_LoadDynlib_0__Lean_DynlibImpl = _init_l___private_Lean_LoadDynlib_0__Lean_DynlibImpl();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_LoadDynlib(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LoadDynlib(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LoadDynlib(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_LoadDynlib(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_LoadDynlib(builtin);
}
#ifdef __cplusplus
}
#endif
