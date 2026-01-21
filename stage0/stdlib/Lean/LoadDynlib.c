// Lean compiler output
// Module: Lean.LoadDynlib
// Imports: public import Init.System.IO import Init.Data.String.TakeDrop
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
LEAN_EXPORT lean_object* l_Lean_Dynlib_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Dynlib_Symbol_runAsInit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00Lean_loadPlugin_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1(lean_object*);
lean_object* lean_dynlib_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_DynlibImpl;
LEAN_EXPORT lean_object* l_Lean_loadPlugin___boxed(lean_object*, lean_object*);
static lean_object* l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_System_FilePath_fileStem(lean_object*);
static lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(lean_object*);
lean_object* lean_dynlib_symbol_run_as_init(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Dynlib_load___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_loadPlugin___closed__3;
static lean_object* l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0;
LEAN_EXPORT lean_object* lean_load_plugin(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_io_realpath(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(lean_object*);
static lean_object* l_Lean_loadPlugin___closed__2;
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_loadPlugin___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_loadPlugin___closed__0;
LEAN_EXPORT lean_object* lean_load_dynlib(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_runtime_mark_persistent(lean_object*);
lean_object* lean_dynlib_load(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_loadDynlib___boxed(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_LoadDynlib_0__Lean_DynlibImpl() {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_runtime_mark_persistent(x_5);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_runtime_mark_persistent(x_8);
lean_dec(x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
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
static lean_object* _init_l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_shared", 7, 7);
return x_1;
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0;
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
x_5 = l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0;
x_6 = l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1;
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
lean_object* x_13; uint8_t x_14; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_13 = l_String_Slice_pos_x21(x_1, x_10);
lean_dec(x_10);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_18 = lean_nat_add(x_3, x_13);
lean_dec(x_13);
lean_ctor_set(x_1, 2, x_18);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_nat_add(x_3, x_13);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
}
}
}
static lean_object* _init_l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lib", 3, 3);
return x_1;
}
}
static lean_object* _init_l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0;
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
x_5 = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0;
x_6 = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1;
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
lean_object* x_11; uint8_t x_12; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_11 = l_String_Slice_pos_x21(x_1, x_6);
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
x_16 = lean_nat_add(x_3, x_11);
lean_dec(x_11);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_16);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_nat_add(x_3, x_11);
lean_dec(x_11);
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_4);
return x_18;
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
static lean_object* _init_l_Lean_loadPlugin___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initialize_", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error loading plugin, initializer not found '", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_loadPlugin___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error, plugin has invalid file name '", 37, 37);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_load_plugin(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_realpath(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = l_System_FilePath_fileStem(x_5);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_free_object(x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_dynlib_load(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0;
x_12 = l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(x_7, x_11);
x_13 = l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(x_12);
x_14 = l_Lean_loadPlugin___closed__0;
x_15 = l_String_Slice_toString(x_13);
lean_dec_ref(x_13);
x_16 = lean_string_append(x_14, x_15);
lean_dec_ref(x_15);
x_17 = lean_dynlib_get(x_10, x_16);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_16);
lean_free_object(x_8);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc(x_10);
x_19 = lean_runtime_mark_persistent(x_10);
lean_dec(x_19);
x_20 = lean_dynlib_symbol_run_as_init(x_10, x_18);
lean_dec(x_18);
lean_dec(x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
lean_dec(x_10);
x_21 = l_Lean_loadPlugin___closed__1;
x_22 = lean_string_append(x_21, x_16);
lean_dec_ref(x_16);
x_23 = l_Lean_loadPlugin___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_mk_io_user_error(x_24);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_8, 0);
lean_inc(x_26);
lean_dec(x_8);
x_27 = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0;
x_28 = l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(x_7, x_27);
x_29 = l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(x_28);
x_30 = l_Lean_loadPlugin___closed__0;
x_31 = l_String_Slice_toString(x_29);
lean_dec_ref(x_29);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = lean_dynlib_get(x_26, x_32);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
lean_inc(x_26);
x_35 = lean_runtime_mark_persistent(x_26);
lean_dec(x_35);
x_36 = lean_dynlib_symbol_run_as_init(x_26, x_34);
lean_dec(x_34);
lean_dec(x_26);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_33);
lean_dec(x_26);
x_37 = l_Lean_loadPlugin___closed__1;
x_38 = lean_string_append(x_37, x_32);
lean_dec_ref(x_32);
x_39 = l_Lean_loadPlugin___closed__2;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_mk_io_user_error(x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_7);
x_43 = !lean_is_exclusive(x_8);
if (x_43 == 0)
{
return x_8;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_8, 0);
lean_inc(x_44);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_6);
x_46 = l_Lean_loadPlugin___closed__3;
x_47 = lean_string_append(x_46, x_5);
lean_dec(x_5);
x_48 = l_Lean_loadPlugin___closed__2;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_mk_io_user_error(x_49);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_50);
return x_3;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
lean_dec(x_3);
lean_inc(x_51);
x_52 = l_System_FilePath_fileStem(x_51);
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_dynlib_load(x_51);
lean_dec(x_51);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0;
x_58 = l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(x_53, x_57);
x_59 = l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(x_58);
x_60 = l_Lean_loadPlugin___closed__0;
x_61 = l_String_Slice_toString(x_59);
lean_dec_ref(x_59);
x_62 = lean_string_append(x_60, x_61);
lean_dec_ref(x_61);
x_63 = lean_dynlib_get(x_55, x_62);
if (lean_obj_tag(x_63) == 1)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_62);
lean_dec(x_56);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
lean_inc(x_55);
x_65 = lean_runtime_mark_persistent(x_55);
lean_dec(x_65);
x_66 = lean_dynlib_symbol_run_as_init(x_55, x_64);
lean_dec(x_64);
lean_dec(x_55);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_63);
lean_dec(x_55);
x_67 = l_Lean_loadPlugin___closed__1;
x_68 = lean_string_append(x_67, x_62);
lean_dec_ref(x_62);
x_69 = l_Lean_loadPlugin___closed__2;
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_mk_io_user_error(x_70);
if (lean_is_scalar(x_56)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_56;
 lean_ctor_set_tag(x_72, 1);
}
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_53);
x_73 = lean_ctor_get(x_54, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_74 = x_54;
} else {
 lean_dec_ref(x_54);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_52);
x_76 = l_Lean_loadPlugin___closed__3;
x_77 = lean_string_append(x_76, x_51);
lean_dec(x_51);
x_78 = l_Lean_loadPlugin___closed__2;
x_79 = lean_string_append(x_77, x_78);
x_80 = lean_mk_io_user_error(x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_3);
if (x_82 == 0)
{
return x_3;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
lean_dec(x_3);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
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
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LoadDynlib(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_LoadDynlib_0__Lean_DynlibImpl = _init_l___private_Lean_LoadDynlib_0__Lean_DynlibImpl();
l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0 = _init_l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0();
lean_mark_persistent(l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0);
l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1 = _init_l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1();
lean_mark_persistent(l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1);
l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0 = _init_l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0);
l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1 = _init_l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1);
l_Lean_loadPlugin___closed__0 = _init_l_Lean_loadPlugin___closed__0();
lean_mark_persistent(l_Lean_loadPlugin___closed__0);
l_Lean_loadPlugin___closed__1 = _init_l_Lean_loadPlugin___closed__1();
lean_mark_persistent(l_Lean_loadPlugin___closed__1);
l_Lean_loadPlugin___closed__2 = _init_l_Lean_loadPlugin___closed__2();
lean_mark_persistent(l_Lean_loadPlugin___closed__2);
l_Lean_loadPlugin___closed__3 = _init_l_Lean_loadPlugin___closed__3();
lean_mark_persistent(l_Lean_loadPlugin___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
