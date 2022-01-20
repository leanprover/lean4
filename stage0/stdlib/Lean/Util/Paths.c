// Lean compiler output
// Module: Lean.Util.Paths
// Imports: Init Lean.Data.Json Lean.Util.Path
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
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_instFromJsonLeanPaths___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonLeanPaths;
LEAN_EXPORT lean_object* l_Lean_initSrcSearchPath(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1(lean_object*, lean_object*);
lean_object* l_List_join___rarg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__2(size_t, size_t, lean_object*);
lean_object* l_IO_appDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initSrcSearchPath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24_(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonLeanPaths;
LEAN_EXPORT lean_object* l_Lean_initSrcSearchPath___rarg(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initSrcSearchPath___rarg___closed__5;
static lean_object* l_Lean_initSrcSearchPath___rarg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64_(lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1___closed__1;
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1___closed__2;
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_initSrcSearchPath___rarg___closed__4;
lean_object* l_System_SearchPath_parse(lean_object*);
static lean_object* l_Lean_initSrcSearchPath___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_initSrcSearchPath___rarg___closed__3;
static lean_object* l_Lean_initSrcSearchPath___rarg___closed__1;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____closed__2;
static lean_object* l_Lean_instToJsonLeanPaths___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("oleanPath");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("srcPath");
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_List_redLength___rarg(x_2);
x_4 = lean_mk_empty_array_with_capacity(x_3);
lean_dec(x_3);
x_5 = l_List_toArrayAux___rarg(x_2, x_4);
x_6 = lean_array_get_size(x_5);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____spec__1(x_7, x_8, x_5);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_List_redLength___rarg(x_15);
x_17 = lean_mk_empty_array_with_capacity(x_16);
lean_dec(x_16);
x_18 = l_List_toArrayAux___rarg(x_15, x_17);
x_19 = lean_array_get_size(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____spec__1(x_20, x_8, x_18);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____closed__2;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_List_join___rarg(x_27);
x_29 = l_Lean_Json_mkObj(x_28);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instToJsonLeanPaths___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToJsonLeanPaths() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToJsonLeanPaths___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l_Lean_Json_getStr_x3f(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected JSON array, got '");
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__2(x_6, x_7, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_array_to_list(lean_box(0), x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_array_to_list(lean_box(0), x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_unsigned_to_nat(80u);
x_19 = l_Lean_Json_pretty(x_3, x_18);
x_20 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____closed__2;
x_9 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instFromJsonLeanPaths___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instFromJsonLeanPaths() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instFromJsonLeanPaths___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_initSrcSearchPath___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("LEAN_SRC_PATH");
return x_1;
}
}
static lean_object* _init_l_Lean_initSrcSearchPath___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("..");
return x_1;
}
}
static lean_object* _init_l_Lean_initSrcSearchPath___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lib");
return x_1;
}
}
static lean_object* _init_l_Lean_initSrcSearchPath___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean");
return x_1;
}
}
static lean_object* _init_l_Lean_initSrcSearchPath___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("src");
return x_1;
}
}
static lean_object* _init_l_Lean_initSrcSearchPath___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lake");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_initSrcSearchPath___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_initSrcSearchPath___rarg___closed__1;
x_3 = lean_io_getenv(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_IO_appDir(x_5);
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_box(0);
x_10 = l_Lean_initSrcSearchPath___rarg___closed__2;
x_11 = l_System_FilePath_join(x_8, x_10);
x_12 = l_Lean_initSrcSearchPath___rarg___closed__3;
x_13 = l_System_FilePath_join(x_11, x_12);
x_14 = l_Lean_initSrcSearchPath___rarg___closed__4;
x_15 = l_System_FilePath_join(x_13, x_14);
x_16 = l_Lean_initSrcSearchPath___rarg___closed__5;
x_17 = l_System_FilePath_join(x_15, x_16);
x_18 = l_Lean_initSrcSearchPath___rarg___closed__6;
lean_inc(x_17);
x_19 = l_System_FilePath_join(x_17, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_List_appendTR___rarg(x_9, x_21);
lean_ctor_set(x_6, 0, x_22);
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_box(0);
x_26 = l_Lean_initSrcSearchPath___rarg___closed__2;
x_27 = l_System_FilePath_join(x_23, x_26);
x_28 = l_Lean_initSrcSearchPath___rarg___closed__3;
x_29 = l_System_FilePath_join(x_27, x_28);
x_30 = l_Lean_initSrcSearchPath___rarg___closed__4;
x_31 = l_System_FilePath_join(x_29, x_30);
x_32 = l_Lean_initSrcSearchPath___rarg___closed__5;
x_33 = l_System_FilePath_join(x_31, x_32);
x_34 = l_Lean_initSrcSearchPath___rarg___closed__6;
lean_inc(x_33);
x_35 = l_System_FilePath_join(x_33, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_25);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_List_appendTR___rarg(x_25, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_24);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_6);
if (x_40 == 0)
{
return x_6;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_6, 0);
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_6);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_4, 0);
lean_inc(x_44);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_46 = lean_ctor_get(x_6, 0);
x_47 = l_System_SearchPath_parse(x_44);
x_48 = l_Lean_initSrcSearchPath___rarg___closed__2;
x_49 = l_System_FilePath_join(x_46, x_48);
x_50 = l_Lean_initSrcSearchPath___rarg___closed__3;
x_51 = l_System_FilePath_join(x_49, x_50);
x_52 = l_Lean_initSrcSearchPath___rarg___closed__4;
x_53 = l_System_FilePath_join(x_51, x_52);
x_54 = l_Lean_initSrcSearchPath___rarg___closed__5;
x_55 = l_System_FilePath_join(x_53, x_54);
x_56 = l_Lean_initSrcSearchPath___rarg___closed__6;
lean_inc(x_55);
x_57 = l_System_FilePath_join(x_55, x_56);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_List_appendTR___rarg(x_47, x_60);
lean_ctor_set(x_6, 0, x_61);
return x_6;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_62 = lean_ctor_get(x_6, 0);
x_63 = lean_ctor_get(x_6, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_6);
x_64 = l_System_SearchPath_parse(x_44);
x_65 = l_Lean_initSrcSearchPath___rarg___closed__2;
x_66 = l_System_FilePath_join(x_62, x_65);
x_67 = l_Lean_initSrcSearchPath___rarg___closed__3;
x_68 = l_System_FilePath_join(x_66, x_67);
x_69 = l_Lean_initSrcSearchPath___rarg___closed__4;
x_70 = l_System_FilePath_join(x_68, x_69);
x_71 = l_Lean_initSrcSearchPath___rarg___closed__5;
x_72 = l_System_FilePath_join(x_70, x_71);
x_73 = l_Lean_initSrcSearchPath___rarg___closed__6;
lean_inc(x_72);
x_74 = l_System_FilePath_join(x_72, x_73);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_List_appendTR___rarg(x_64, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_63);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_6);
if (x_80 == 0)
{
return x_6;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_6, 0);
x_82 = lean_ctor_get(x_6, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_6);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initSrcSearchPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_initSrcSearchPath___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initSrcSearchPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_initSrcSearchPath(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Path(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Paths(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____closed__1 = _init_l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____closed__1();
lean_mark_persistent(l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____closed__1);
l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____closed__2 = _init_l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____closed__2();
lean_mark_persistent(l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_24____closed__2);
l_Lean_instToJsonLeanPaths___closed__1 = _init_l_Lean_instToJsonLeanPaths___closed__1();
lean_mark_persistent(l_Lean_instToJsonLeanPaths___closed__1);
l_Lean_instToJsonLeanPaths = _init_l_Lean_instToJsonLeanPaths();
lean_mark_persistent(l_Lean_instToJsonLeanPaths);
l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1___closed__1 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1___closed__1();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1___closed__1);
l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1___closed__2 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1___closed__2();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_64____spec__1___closed__2);
l_Lean_instFromJsonLeanPaths___closed__1 = _init_l_Lean_instFromJsonLeanPaths___closed__1();
lean_mark_persistent(l_Lean_instFromJsonLeanPaths___closed__1);
l_Lean_instFromJsonLeanPaths = _init_l_Lean_instFromJsonLeanPaths();
lean_mark_persistent(l_Lean_instFromJsonLeanPaths);
l_Lean_initSrcSearchPath___rarg___closed__1 = _init_l_Lean_initSrcSearchPath___rarg___closed__1();
lean_mark_persistent(l_Lean_initSrcSearchPath___rarg___closed__1);
l_Lean_initSrcSearchPath___rarg___closed__2 = _init_l_Lean_initSrcSearchPath___rarg___closed__2();
lean_mark_persistent(l_Lean_initSrcSearchPath___rarg___closed__2);
l_Lean_initSrcSearchPath___rarg___closed__3 = _init_l_Lean_initSrcSearchPath___rarg___closed__3();
lean_mark_persistent(l_Lean_initSrcSearchPath___rarg___closed__3);
l_Lean_initSrcSearchPath___rarg___closed__4 = _init_l_Lean_initSrcSearchPath___rarg___closed__4();
lean_mark_persistent(l_Lean_initSrcSearchPath___rarg___closed__4);
l_Lean_initSrcSearchPath___rarg___closed__5 = _init_l_Lean_initSrcSearchPath___rarg___closed__5();
lean_mark_persistent(l_Lean_initSrcSearchPath___rarg___closed__5);
l_Lean_initSrcSearchPath___rarg___closed__6 = _init_l_Lean_initSrcSearchPath___rarg___closed__6();
lean_mark_persistent(l_Lean_initSrcSearchPath___rarg___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
