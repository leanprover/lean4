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
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_instFromJsonLeanPaths___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____closed__1;
LEAN_EXPORT lean_object* l_Lean_instFromJsonLeanPaths;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1(lean_object*, lean_object*);
lean_object* l_List_join___rarg(lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23_(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonLeanPaths;
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1___closed__2;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63_(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____spec__1(size_t, size_t, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____closed__2;
static lean_object* l_Lean_instToJsonLeanPaths___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("oleanPath");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("srcPath");
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
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
x_9 = x_5;
x_10 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____spec__1(x_7, x_8, x_9);
x_11 = x_10;
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_List_redLength___rarg(x_17);
x_19 = lean_mk_empty_array_with_capacity(x_18);
lean_dec(x_18);
x_20 = l_List_toArrayAux___rarg(x_17, x_19);
x_21 = lean_array_get_size(x_20);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = x_20;
x_24 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____spec__1(x_22, x_8, x_23);
x_25 = x_24;
x_26 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____closed__2;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_List_join___rarg(x_31);
x_33 = l_Lean_Json_mkObj(x_32);
return x_33;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instToJsonLeanPaths___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23_), 1, 0);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = x_3;
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Json_getStr_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = 1;
x_17 = x_2 + x_16;
x_18 = x_15;
x_19 = lean_array_uset(x_9, x_2, x_18);
x_2 = x_17;
x_3 = x_19;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected JSON array, got '");
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = x_4;
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__2(x_6, x_7, x_8);
x_10 = x_9;
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_array_to_list(lean_box(0), x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_array_to_list(lean_box(0), x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_unsigned_to_nat(80u);
x_21 = l_Lean_Json_pretty(x_3, x_20);
x_22 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1(x_1, x_2);
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
x_8 = l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____closed__2;
x_9 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1(x_1, x_8);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instFromJsonLeanPaths___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____boxed), 1, 0);
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Json(lean_object*);
lean_object* initialize_Lean_Util_Path(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Paths(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____closed__1 = _init_l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____closed__1();
lean_mark_persistent(l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____closed__1);
l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____closed__2 = _init_l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____closed__2();
lean_mark_persistent(l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_23____closed__2);
l_Lean_instToJsonLeanPaths___closed__1 = _init_l_Lean_instToJsonLeanPaths___closed__1();
lean_mark_persistent(l_Lean_instToJsonLeanPaths___closed__1);
l_Lean_instToJsonLeanPaths = _init_l_Lean_instToJsonLeanPaths();
lean_mark_persistent(l_Lean_instToJsonLeanPaths);
l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1___closed__1 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1___closed__1();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1___closed__1);
l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1___closed__2 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1___closed__2();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_63____spec__1___closed__2);
l_Lean_instFromJsonLeanPaths___closed__1 = _init_l_Lean_instFromJsonLeanPaths___closed__1();
lean_mark_persistent(l_Lean_instFromJsonLeanPaths___closed__1);
l_Lean_instFromJsonLeanPaths = _init_l_Lean_instFromJsonLeanPaths();
lean_mark_persistent(l_Lean_instFromJsonLeanPaths);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
