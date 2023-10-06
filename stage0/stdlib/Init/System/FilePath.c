// Lean compiler output
// Module: Init.System.FilePath
// Imports: Init.System.Platform Init.Data.String.Basic Init.Data.Repr Init.Data.ToString.Basic
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
LEAN_EXPORT lean_object* l_System_FilePath_pathSeparators;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___at_System_SearchPath_parse___spec__1(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at_System_FilePath_normalize___spec__2(lean_object*, lean_object*);
static lean_object* l_System_FilePath_pathSeparators___closed__2;
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_normalize___lambda__2___boxed(lean_object*, lean_object*);
static lean_object* l_System_FilePath_normalize___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at_System_SearchPath_parse___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_System_instToStringFilePath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_System_SearchPath_toString___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object*);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_System_instReprFilePath(lean_object*, lean_object*);
static uint32_t l_System_SearchPath_separator___closed__1;
LEAN_EXPORT lean_object* l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_String_Iterator_next(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_exeExtension;
LEAN_EXPORT lean_object* l_System_FilePath_instHDivFilePathString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___at_System_SearchPath_parse___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_contains___at___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_String_revFind(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_System_instInhabitedFilePath___closed__1;
lean_object* lean_string_push(lean_object*, uint32_t);
uint32_t l_String_Iterator_curr(lean_object*);
uint8_t l_String_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_System_FilePath_normalize___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_System_instReprFilePath___closed__1;
static lean_object* l_System_FilePath_instDivFilePath___closed__1;
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath(lean_object*);
lean_object* l_Char_toUpper(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object*);
static uint8_t l_System_FilePath_normalize___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_hashFilePath____x40_Init_System_FilePath___hyg_116____boxed(lean_object*);
static lean_object* l_System_FilePath_pathSeparators___closed__1;
static lean_object* l_System_FilePath_fileName___closed__1;
LEAN_EXPORT lean_object* l_String_splitAux___at_System_SearchPath_parse___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_System_FilePath_extension___closed__1;
LEAN_EXPORT uint32_t l_System_FilePath_extSeparator;
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_parent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object*);
static lean_object* l_System_FilePath_exeExtension___closed__1;
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object*);
LEAN_EXPORT lean_object* l_System_instToStringFilePath(lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_System_FilePath_normalize___spec__1(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withFileName___boxed(lean_object*, lean_object*);
static lean_object* l_System_FilePath_normalize___closed__1;
static uint32_t l_System_FilePath_pathSeparator___closed__1;
LEAN_EXPORT lean_object* l_System_instReprFilePath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_System_FilePath_pathSeparator;
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object*);
lean_object* l_String_revPosOf(lean_object*, uint32_t);
lean_object* l_String_csize(uint32_t);
LEAN_EXPORT lean_object* l_System_FilePath_instDivFilePath;
static lean_object* l_System_FilePath_fileName___closed__3;
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object*);
LEAN_EXPORT lean_object* l_System_instHashableFilePath;
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object*);
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_System_FilePath_pathSeparators___closed__3;
LEAN_EXPORT lean_object* l_System_instInhabitedFilePath;
static lean_object* l_System_FilePath_exeExtension___closed__2;
static lean_object* l_System_instHashableFilePath___closed__1;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l_System_FilePath_join___closed__1;
LEAN_EXPORT uint32_t l_System_SearchPath_separator;
LEAN_EXPORT uint8_t l_List_contains___at___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___spec__1(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_System_FilePath_normalize___lambda__2(lean_object*, lean_object*);
static lean_object* l_System_SearchPath_toString___closed__1;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT uint64_t l___private_Init_System_FilePath_0__System_hashFilePath____x40_Init_System_FilePath___hyg_116_(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_normalize___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_pathSeparators___closed__2___boxed__const__1;
static lean_object* l_System_FilePath_normalize___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_System_SearchPath_parse___spec__3(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_normalize___lambda__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_System_FilePath_fileName___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_System_FilePath_0__System_decEqFilePath____x40_Init_System_FilePath___hyg_24_(lean_object*, lean_object*);
static lean_object* l_System_instReprFilePath___closed__2;
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_decEqFilePath____x40_Init_System_FilePath___hyg_24____boxed(lean_object*, lean_object*);
uint8_t l_Char_isLower(uint32_t);
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object*);
lean_object* l_String_splitOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___boxed(lean_object*);
static lean_object* _init_l_System_instInhabitedFilePath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_System_instInhabitedFilePath() {
_start:
{
lean_object* x_1; 
x_1 = l_System_instInhabitedFilePath___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_System_FilePath_0__System_decEqFilePath____x40_Init_System_FilePath___hyg_24_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_decEqFilePath____x40_Init_System_FilePath___hyg_24____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_System_FilePath_0__System_decEqFilePath____x40_Init_System_FilePath___hyg_24_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_System_instDecidableEqFilePath(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l___private_Init_System_FilePath_0__System_hashFilePath____x40_Init_System_FilePath___hyg_116_(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; 
x_2 = 0;
x_3 = lean_string_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_hashFilePath____x40_Init_System_FilePath___hyg_116____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Init_System_FilePath_0__System_hashFilePath____x40_Init_System_FilePath___hyg_116_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_System_instHashableFilePath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_FilePath_0__System_hashFilePath____x40_Init_System_FilePath___hyg_116____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_System_instHashableFilePath() {
_start:
{
lean_object* x_1; 
x_1 = l_System_instHashableFilePath___closed__1;
return x_1;
}
}
static lean_object* _init_l_System_instReprFilePath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("FilePath.mk ", 12);
return x_1;
}
}
static lean_object* _init_l_System_instReprFilePath___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_System_instReprFilePath___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_instReprFilePath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_String_quote(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_System_instReprFilePath___closed__2;
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Repr_addAppParen(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_System_instReprFilePath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_instReprFilePath(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_instToStringFilePath(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_instToStringFilePath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_instToStringFilePath(x_1);
lean_dec(x_1);
return x_2;
}
}
static uint32_t _init_l_System_FilePath_pathSeparator___closed__1() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
uint32_t x_2; 
x_2 = 47;
return x_2;
}
else
{
uint32_t x_3; 
x_3 = 92;
return x_3;
}
}
}
static uint32_t _init_l_System_FilePath_pathSeparator() {
_start:
{
uint32_t x_1; 
x_1 = l_System_FilePath_pathSeparator___closed__1;
return x_1;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_pathSeparators___closed__1;
x_2 = l_System_FilePath_pathSeparators___closed__2___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__3() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_System_FilePath_pathSeparators___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_System_FilePath_pathSeparators___closed__2;
return x_3;
}
}
}
static lean_object* _init_l_System_FilePath_pathSeparators() {
_start:
{
lean_object* x_1; 
x_1 = l_System_FilePath_pathSeparators___closed__3;
return x_1;
}
}
static uint32_t _init_l_System_FilePath_extSeparator() {
_start:
{
uint32_t x_1; 
x_1 = 46;
return x_1;
}
}
static lean_object* _init_l_System_FilePath_exeExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("exe", 3);
return x_1;
}
}
static lean_object* _init_l_System_FilePath_exeExtension___closed__2() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_System_instInhabitedFilePath___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_System_FilePath_exeExtension___closed__1;
return x_3;
}
}
}
static lean_object* _init_l_System_FilePath_exeExtension() {
_start:
{
lean_object* x_1; 
x_1 = l_System_FilePath_exeExtension___closed__2;
return x_1;
}
}
LEAN_EXPORT uint8_t l_List_elem___at_System_FilePath_normalize___spec__1(uint32_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_7 = lean_uint32_dec_eq(x_1, x_6);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_5);
x_9 = 1;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at_System_FilePath_normalize___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_utf8_at_end(x_2, x_1);
if (x_3 == 0)
{
uint32_t x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_string_utf8_get(x_2, x_1);
x_5 = l_System_FilePath_pathSeparators;
x_6 = l_List_elem___at_System_FilePath_normalize___spec__1(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_string_utf8_set(x_2, x_1, x_4);
x_8 = lean_string_utf8_next(x_7, x_1);
lean_dec(x_1);
x_1 = x_8;
x_2 = x_7;
goto _start;
}
else
{
uint32_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_System_FilePath_pathSeparator;
x_11 = lean_string_utf8_set(x_2, x_1, x_10);
x_12 = lean_string_utf8_next(x_11, x_1);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_11;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_System_FilePath_normalize___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_FilePath_normalize___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_System_FilePath_normalize___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_pathSeparators;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_List_lengthTRAux___rarg(x_1, x_2);
return x_3;
}
}
static uint8_t _init_l_System_FilePath_normalize___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_System_FilePath_normalize___lambda__2___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_System_FilePath_normalize___lambda__2___closed__1;
x_4 = l_System_FilePath_normalize___lambda__2___closed__3;
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_String_mapAux___at_System_FilePath_normalize___spec__2(x_5, x_1);
x_7 = lean_box(0);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_apply_2(x_3, x_1, x_9);
return x_10;
}
}
}
static lean_object* _init_l_System_FilePath_normalize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_FilePath_normalize___lambda__2___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_System_FilePath_normalize___closed__1;
x_3 = l_System_Platform_isWindows;
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_apply_2(x_2, x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_string_length(x_1);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_dec_le(x_7, x_6);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_apply_2(x_2, x_1, x_9);
return x_10;
}
else
{
lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_get(x_1, x_11);
x_13 = l_Char_isLower(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_apply_2(x_2, x_1, x_14);
return x_15;
}
else
{
lean_object* x_16; uint32_t x_17; uint32_t x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_string_utf8_get(x_1, x_16);
x_18 = 58;
x_19 = lean_uint32_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = lean_apply_2(x_2, x_1, x_20);
return x_21;
}
else
{
lean_object* x_22; uint32_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = l_Char_toUpper(x_12);
x_23 = lean_unbox_uint32(x_22);
lean_dec(x_22);
x_24 = lean_string_utf8_set(x_1, x_11, x_23);
x_25 = lean_box(0);
x_26 = lean_apply_2(x_2, x_24, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at_System_FilePath_normalize___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_List_elem___at_System_FilePath_normalize___spec__1(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_normalize___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_normalize___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = l_System_FilePath_pathSeparators;
x_5 = l_List_elem___at_System_FilePath_normalize___spec__1(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_System_Platform_isWindows;
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_string_length(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_lt(x_9, x_8);
lean_dec(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = 0;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint32_t x_14; uint32_t x_15; uint8_t x_16; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
x_13 = l_String_Iterator_next(x_12);
x_14 = l_String_Iterator_curr(x_13);
lean_dec(x_13);
x_15 = 58;
x_16 = lean_uint32_dec_eq(x_14, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_System_FilePath_isAbsolute(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_FilePath_isAbsolute(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_System_FilePath_isRelative(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_System_FilePath_join___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; 
x_1 = l_System_instInhabitedFilePath___closed__1;
x_2 = l_System_FilePath_pathSeparator;
x_3 = lean_string_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_2);
x_3 = l_System_FilePath_isAbsolute(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_System_FilePath_join___closed__1;
x_5 = lean_string_append(x_1, x_4);
x_6 = lean_string_append(x_5, x_2);
lean_dec(x_2);
return x_6;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
static lean_object* _init_l_System_FilePath_instDivFilePath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_FilePath_join), 2, 0);
return x_1;
}
}
static lean_object* _init_l_System_FilePath_instDivFilePath() {
_start:
{
lean_object* x_1; 
x_1 = l_System_FilePath_instDivFilePath___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_instHDivFilePathString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_join(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_contains___at___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___spec__1(lean_object* x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_List_elem___at_System_FilePath_normalize___spec__1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_System_FilePath_pathSeparators;
x_3 = lean_alloc_closure((void*)(l_List_contains___at___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___spec__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_String_revFind(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_contains___at___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_List_contains___at___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___spec__1(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_string_utf8_extract(x_1, x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_utf8_extract(x_1, x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_parent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_parent(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_System_FilePath_fileName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l_System_FilePath_fileName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("..", 2);
return x_1;
}
}
static lean_object* _init_l_System_FilePath_fileName___closed__3() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = l_String_csize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = l_String_isEmpty(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_System_FilePath_fileName___closed__1;
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_System_FilePath_fileName___closed__2;
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_box(0);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_System_FilePath_fileName___closed__3;
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_13);
x_16 = lean_string_utf8_byte_size(x_1);
x_17 = lean_string_utf8_extract(x_1, x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
x_18 = l_String_isEmpty(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_System_FilePath_fileName___closed__1;
x_20 = lean_string_dec_eq(x_17, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_System_FilePath_fileName___closed__2;
x_22 = lean_string_dec_eq(x_17, x_21);
if (x_22 == 0)
{
lean_ctor_set(x_2, 0, x_17);
return x_2;
}
else
{
lean_object* x_23; 
lean_dec(x_17);
lean_free_object(x_2);
x_23 = lean_box(0);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_17);
lean_free_object(x_2);
x_24 = lean_box(0);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_17);
lean_free_object(x_2);
x_25 = lean_box(0);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = l_System_FilePath_fileName___closed__3;
x_28 = lean_nat_add(x_26, x_27);
lean_dec(x_26);
x_29 = lean_string_utf8_byte_size(x_1);
x_30 = lean_string_utf8_extract(x_1, x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
x_31 = l_String_isEmpty(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_System_FilePath_fileName___closed__1;
x_33 = lean_string_dec_eq(x_30, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_System_FilePath_fileName___closed__2;
x_35 = lean_string_dec_eq(x_30, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_30);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_30);
x_37 = lean_box(0);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_30);
x_38 = lean_box(0);
return x_38;
}
}
else
{
lean_object* x_39; 
lean_dec(x_30);
x_39 = lean_box(0);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_fileName(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = 46;
x_7 = l_String_revPosOf(x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
return x_2;
}
else
{
uint8_t x_8; 
lean_free_object(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_string_utf8_extract(x_5, x_10, x_9);
lean_dec(x_9);
lean_dec(x_5);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_string_utf8_extract(x_5, x_14, x_13);
lean_dec(x_13);
lean_dec(x_5);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_13);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
}
}
}
else
{
lean_object* x_19; uint32_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = 46;
x_21 = l_String_revPosOf(x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_23, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_string_utf8_extract(x_19, x_25, x_23);
lean_dec(x_23);
lean_dec(x_19);
if (lean_is_scalar(x_24)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_24;
}
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_23);
if (lean_is_scalar(x_24)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_24;
}
lean_ctor_set(x_29, 0, x_19);
return x_29;
}
}
}
}
}
}
static lean_object* _init_l_System_FilePath_extension___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 46;
x_2 = l_String_csize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_fileName(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = 46;
x_6 = l_String_revPosOf(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_System_FilePath_extension___closed__1;
x_13 = lean_nat_add(x_9, x_12);
lean_dec(x_9);
x_14 = lean_string_utf8_byte_size(x_4);
x_15 = lean_string_utf8_extract(x_4, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
else
{
lean_object* x_16; 
lean_free_object(x_6);
lean_dec(x_9);
lean_dec(x_4);
x_16 = lean_box(0);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_System_FilePath_extension___closed__1;
x_21 = lean_nat_add(x_17, x_20);
lean_dec(x_17);
x_22 = lean_string_utf8_byte_size(x_4);
x_23 = lean_string_utf8_extract(x_4, x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_4);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_17);
lean_dec(x_4);
x_25 = lean_box(0);
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_parent(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_System_FilePath_join(x_4, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withFileName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_withFileName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_System_FilePath_fileStem(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_String_isEmpty(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_System_FilePath_fileName___closed__1;
x_7 = lean_string_append(x_4, x_6);
x_8 = lean_string_append(x_7, x_2);
x_9 = l_System_FilePath_withFileName(x_1, x_8);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_System_FilePath_withFileName(x_1, x_4);
lean_dec(x_1);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_withExtension(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_System_FilePath_normalize(x_1);
x_3 = l_System_FilePath_join___closed__1;
x_4 = l_String_splitOn(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_System_FilePath_join___closed__1;
x_3 = l_String_intercalate(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_instCoeStringFilePath(x_1);
lean_dec(x_1);
return x_2;
}
}
static uint32_t _init_l_System_SearchPath_separator___closed__1() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
uint32_t x_2; 
x_2 = 58;
return x_2;
}
else
{
uint32_t x_3; 
x_3 = 59;
return x_3;
}
}
}
static uint32_t _init_l_System_SearchPath_separator() {
_start:
{
uint32_t x_1; 
x_1 = l_System_SearchPath_separator___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at_System_SearchPath_parse___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = l_System_SearchPath_separator;
x_8 = lean_uint32_dec_eq(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_string_utf8_next(x_1, x_3);
x_12 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
lean_inc(x_11);
x_2 = x_11;
x_3 = x_11;
x_4 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = l_List_reverse___rarg(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_split___at_System_SearchPath_parse___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_splitAux___at_System_SearchPath_parse___spec__2(x_1, x_3, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_System_SearchPath_parse___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_String_split___at_System_SearchPath_parse___spec__1(x_1);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at_System_SearchPath_parse___spec__3(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at_System_SearchPath_parse___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at_System_SearchPath_parse___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___at_System_SearchPath_parse___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at_System_SearchPath_parse___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_System_SearchPath_toString___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
static lean_object* _init_l_System_SearchPath_toString___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; 
x_1 = l_System_instInhabitedFilePath___closed__1;
x_2 = l_System_SearchPath_separator;
x_3 = lean_string_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at_System_SearchPath_toString___spec__1(x_1, x_2);
x_4 = l_System_SearchPath_toString___closed__1;
x_5 = l_String_intercalate(x_4, x_3);
return x_5;
}
}
lean_object* initialize_Init_System_Platform(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Repr(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_FilePath(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Platform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Repr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_System_instInhabitedFilePath___closed__1 = _init_l_System_instInhabitedFilePath___closed__1();
lean_mark_persistent(l_System_instInhabitedFilePath___closed__1);
l_System_instInhabitedFilePath = _init_l_System_instInhabitedFilePath();
lean_mark_persistent(l_System_instInhabitedFilePath);
l_System_instHashableFilePath___closed__1 = _init_l_System_instHashableFilePath___closed__1();
lean_mark_persistent(l_System_instHashableFilePath___closed__1);
l_System_instHashableFilePath = _init_l_System_instHashableFilePath();
lean_mark_persistent(l_System_instHashableFilePath);
l_System_instReprFilePath___closed__1 = _init_l_System_instReprFilePath___closed__1();
lean_mark_persistent(l_System_instReprFilePath___closed__1);
l_System_instReprFilePath___closed__2 = _init_l_System_instReprFilePath___closed__2();
lean_mark_persistent(l_System_instReprFilePath___closed__2);
l_System_FilePath_pathSeparator___closed__1 = _init_l_System_FilePath_pathSeparator___closed__1();
l_System_FilePath_pathSeparator = _init_l_System_FilePath_pathSeparator();
l_System_FilePath_pathSeparators___closed__1___boxed__const__1 = _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__1___boxed__const__1);
l_System_FilePath_pathSeparators___closed__1 = _init_l_System_FilePath_pathSeparators___closed__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__1);
l_System_FilePath_pathSeparators___closed__2___boxed__const__1 = _init_l_System_FilePath_pathSeparators___closed__2___boxed__const__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__2___boxed__const__1);
l_System_FilePath_pathSeparators___closed__2 = _init_l_System_FilePath_pathSeparators___closed__2();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__2);
l_System_FilePath_pathSeparators___closed__3 = _init_l_System_FilePath_pathSeparators___closed__3();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__3);
l_System_FilePath_pathSeparators = _init_l_System_FilePath_pathSeparators();
lean_mark_persistent(l_System_FilePath_pathSeparators);
l_System_FilePath_extSeparator = _init_l_System_FilePath_extSeparator();
l_System_FilePath_exeExtension___closed__1 = _init_l_System_FilePath_exeExtension___closed__1();
lean_mark_persistent(l_System_FilePath_exeExtension___closed__1);
l_System_FilePath_exeExtension___closed__2 = _init_l_System_FilePath_exeExtension___closed__2();
lean_mark_persistent(l_System_FilePath_exeExtension___closed__2);
l_System_FilePath_exeExtension = _init_l_System_FilePath_exeExtension();
lean_mark_persistent(l_System_FilePath_exeExtension);
l_System_FilePath_normalize___lambda__2___closed__1 = _init_l_System_FilePath_normalize___lambda__2___closed__1();
lean_mark_persistent(l_System_FilePath_normalize___lambda__2___closed__1);
l_System_FilePath_normalize___lambda__2___closed__2 = _init_l_System_FilePath_normalize___lambda__2___closed__2();
lean_mark_persistent(l_System_FilePath_normalize___lambda__2___closed__2);
l_System_FilePath_normalize___lambda__2___closed__3 = _init_l_System_FilePath_normalize___lambda__2___closed__3();
l_System_FilePath_normalize___closed__1 = _init_l_System_FilePath_normalize___closed__1();
lean_mark_persistent(l_System_FilePath_normalize___closed__1);
l_System_FilePath_join___closed__1 = _init_l_System_FilePath_join___closed__1();
lean_mark_persistent(l_System_FilePath_join___closed__1);
l_System_FilePath_instDivFilePath___closed__1 = _init_l_System_FilePath_instDivFilePath___closed__1();
lean_mark_persistent(l_System_FilePath_instDivFilePath___closed__1);
l_System_FilePath_instDivFilePath = _init_l_System_FilePath_instDivFilePath();
lean_mark_persistent(l_System_FilePath_instDivFilePath);
l_System_FilePath_fileName___closed__1 = _init_l_System_FilePath_fileName___closed__1();
lean_mark_persistent(l_System_FilePath_fileName___closed__1);
l_System_FilePath_fileName___closed__2 = _init_l_System_FilePath_fileName___closed__2();
lean_mark_persistent(l_System_FilePath_fileName___closed__2);
l_System_FilePath_fileName___closed__3 = _init_l_System_FilePath_fileName___closed__3();
lean_mark_persistent(l_System_FilePath_fileName___closed__3);
l_System_FilePath_extension___closed__1 = _init_l_System_FilePath_extension___closed__1();
lean_mark_persistent(l_System_FilePath_extension___closed__1);
l_System_SearchPath_separator___closed__1 = _init_l_System_SearchPath_separator___closed__1();
l_System_SearchPath_separator = _init_l_System_SearchPath_separator();
l_System_SearchPath_toString___closed__1 = _init_l_System_SearchPath_toString___closed__1();
lean_mark_persistent(l_System_SearchPath_toString___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
