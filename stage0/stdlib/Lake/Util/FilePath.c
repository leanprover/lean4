// Lean compiler output
// Module: Lake.Util.FilePath
// Imports: public import Lean.Data.Json import Init.Data.String.TakeDrop import Init.Data.String.Modify
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonFilePath__lake;
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_modOfFilePath_spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_instHDivFilePathString__lake;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_relPathFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_mkRelPathString_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_System_FilePath_components(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instToJsonFilePath__lake___closed__0;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___boxed(lean_object*, lean_object*);
extern uint32_t l_System_FilePath_pathSeparator;
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg(lean_object*);
static lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_instToJsonFilePath__lake___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_relPathFrom___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_modOfFilePath(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDivFilePath__lake;
static lean_object* l_Lake_joinRelative___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Char_utf8Size(uint32_t);
LEAN_EXPORT lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_instDivFilePath__lake___closed__0;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0(lean_object*, lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_nat_dec_le(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_memcmp(x_2, x_1, x_7, x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_2);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_3);
x_11 = l_String_Slice_pos_x21(x_10, x_4);
lean_dec_ref(x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_relPathFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_2);
x_3 = l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec_ref(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_String_Slice_Pos_nextn(x_4, x_9, x_8);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
x_15 = lean_nat_add(x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
lean_ctor_set(x_4, 1, x_15);
x_16 = l_String_Slice_toString(x_4);
lean_dec_ref(x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_17 = lean_nat_add(x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_7);
x_19 = l_String_Slice_toString(x_18);
lean_dec_ref(x_18);
return x_19;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lake_relPathFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_relPathFrom(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_mkRelPathString_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_9; uint8_t x_10; 
x_9 = lean_string_utf8_byte_size(x_1);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get_fast(x_1, x_2);
x_12 = 92;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
x_3 = x_11;
goto block_8;
}
else
{
uint32_t x_14; 
x_14 = 47;
x_3 = x_14;
goto block_8;
}
}
else
{
lean_dec(x_2);
return x_1;
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
x_4 = lean_string_utf8_set(x_1, x_2, x_3);
x_5 = l_Char_utf8Size(x_3);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_5);
lean_dec(x_2);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkRelPathString(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isWindows;
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_mapAux___at___00Lake_mkRelPathString_spec__0(x_1, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonFilePath__lake___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_mkRelPathString(x_1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToJsonFilePath__lake___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToJsonFilePath__lake___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToJsonFilePath__lake() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToJsonFilePath__lake___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_joinRelative___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_joinRelative(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lake_joinRelative___closed__0;
x_4 = lean_string_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_string_dec_eq(x_1, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_System_FilePath_join(x_1, x_2);
return x_6;
}
else
{
lean_dec_ref(x_1);
return x_2;
}
}
else
{
lean_dec_ref(x_2);
return x_1;
}
}
}
static lean_object* _init_l_Lake_instDivFilePath__lake___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_joinRelative), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instDivFilePath__lake() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instDivFilePath__lake___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_instHDivFilePathString__lake() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instDivFilePath__lake___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_6 = lean_string_utf8_prev(x_1, x_2);
lean_dec(x_2);
x_7 = lean_string_utf8_get(x_1, x_6);
x_8 = l_System_FilePath_pathSeparator;
x_9 = lean_uint32_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 46;
x_11 = lean_uint32_dec_eq(x_7, x_10);
if (x_11 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_3);
lean_inc(x_6);
x_2 = x_6;
x_3 = x_6;
goto _start;
}
}
else
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = lean_string_utf8_extract(x_1, x_4, x_3);
lean_dec(x_3);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_string_utf8_extract(x_1, x_4, x_3);
lean_dec(x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_pathSeparator;
x_2 = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1;
x_6 = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_modOfFilePath_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Name_str___override(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_modOfFilePath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_System_FilePath_normalize(x_1);
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts(x_2, x_3, x_3);
lean_dec_ref(x_2);
x_5 = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1;
x_6 = l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_box(0);
x_11 = lean_string_utf8_extract(x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_12 = l_System_FilePath_components(x_11);
x_13 = l_List_foldl___at___00Lake_modOfFilePath_spec__1(x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_FilePath(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instToJsonFilePath__lake___closed__0 = _init_l_Lake_instToJsonFilePath__lake___closed__0();
lean_mark_persistent(l_Lake_instToJsonFilePath__lake___closed__0);
l_Lake_instToJsonFilePath__lake = _init_l_Lake_instToJsonFilePath__lake();
lean_mark_persistent(l_Lake_instToJsonFilePath__lake);
l_Lake_joinRelative___closed__0 = _init_l_Lake_joinRelative___closed__0();
lean_mark_persistent(l_Lake_joinRelative___closed__0);
l_Lake_instDivFilePath__lake___closed__0 = _init_l_Lake_instDivFilePath__lake___closed__0();
lean_mark_persistent(l_Lake_instDivFilePath__lake___closed__0);
l_Lake_instDivFilePath__lake = _init_l_Lake_instDivFilePath__lake();
lean_mark_persistent(l_Lake_instDivFilePath__lake);
l_Lake_instHDivFilePathString__lake = _init_l_Lake_instHDivFilePathString__lake();
lean_mark_persistent(l_Lake_instHDivFilePathString__lake);
l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0 = _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0);
l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1 = _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1);
l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2 = _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
