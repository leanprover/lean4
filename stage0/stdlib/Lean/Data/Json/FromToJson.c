// Lean compiler output
// Module: Lean.Data.Json.FromToJson
// Imports: Init Lean.Data.Json.Basic
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
lean_object* l_Lean_instToJsonJson;
lean_object* l_Lean_instToJsonArray(lean_object*);
static lean_object* l_Lean_instFromJsonOption___rarg___closed__1;
lean_object* l_Lean_instToJsonBool___boxed(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_instToJsonOption___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Json_instToJsonStructured_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonNat;
lean_object* l_Lean_instToJsonArray___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Json_getInt_x3f___boxed(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Json_getNum_x3f___boxed(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f___boxed(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f(lean_object*);
lean_object* l_Lean_instFromJsonString;
lean_object* l_Lean_Json_toStructured_x3f___rarg(lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
static lean_object* l_Lean_instFromJsonString___closed__1;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_instFromJsonBool___closed__1;
lean_object* l_Lean_Json_instToJsonStructured_match__1(lean_object*);
static lean_object* l_Lean_instToJsonJson___closed__1;
lean_object* l_Lean_instFromJsonArray_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonOption_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_opt(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_instToJsonArray___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_instToJsonNat(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_instFromJsonArray___spec__1(lean_object*);
static lean_object* l_Lean_instFromJsonJsonNumber___closed__1;
lean_object* l_Lean_instFromJsonOption___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_instFromJsonNat___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_instFromJsonArray___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_instToJsonInt(lean_object*);
static lean_object* l_Lean_instFromJsonInt___closed__1;
lean_object* l_Lean_instFromJsonInt;
lean_object* l_Lean_instFromJsonJson(lean_object*);
lean_object* l_Lean_instFromJsonBool;
lean_object* l_Lean_Json_getNat_x3f___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Json_instToJsonStructured(lean_object*);
lean_object* l_Lean_instToJsonOption_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonOption_match__1(lean_object*);
lean_object* l_Lean_Json_opt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonOption(lean_object*);
lean_object* l_Lean_instToJsonString(lean_object*);
lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
lean_object* l_Lean_instToJsonJsonNumber(lean_object*);
lean_object* l_Lean_instFromJsonArray(lean_object*);
lean_object* l_Lean_instToJsonOption_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_instFromJsonStructured_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_instFromJsonArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToJsonBool(uint8_t);
lean_object* l_Lean_Json_instToJsonStructured___boxed(lean_object*);
lean_object* l_Lean_Json_instFromJsonStructured_match__1(lean_object*);
lean_object* l_Lean_instFromJsonArray___rarg(lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonJsonNumber;
lean_object* l_Array_mapMUnsafe_map___at_Lean_instToJsonArray___spec__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_instToJsonArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonArray_match__1(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToJsonOption(lean_object*);
lean_object* l_Lean_Json_instFromJsonStructured(lean_object*);
lean_object* l_Lean_Json_instFromJsonStructured___boxed(lean_object*);
lean_object* l_Lean_instFromJsonJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToJsonJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToJsonJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToJsonJson___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_instFromJsonJsonNumber___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_getNum_x3f___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instFromJsonJsonNumber() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instFromJsonJsonNumber___closed__1;
return x_1;
}
}
lean_object* l_Lean_instToJsonJsonNumber(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instFromJsonBool___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_getBool_x3f___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instFromJsonBool() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instFromJsonBool___closed__1;
return x_1;
}
}
lean_object* l_Lean_instToJsonBool(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_instToJsonBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToJsonBool(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_getNat_x3f___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instFromJsonNat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instFromJsonNat___closed__1;
return x_1;
}
}
lean_object* l_Lean_instToJsonNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonNumber_fromNat(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_getInt_x3f___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instFromJsonInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instFromJsonInt___closed__1;
return x_1;
}
}
lean_object* l_Lean_instToJsonInt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instFromJsonString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_getStr_x3f___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instFromJsonString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instFromJsonString___closed__1;
return x_1;
}
}
lean_object* l_Lean_instToJsonString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_instFromJsonArray_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_instFromJsonArray_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instFromJsonArray_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_instFromJsonArray___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = x_4;
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_uget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_4, x_3, x_9);
x_11 = x_8;
lean_inc(x_1);
x_12 = lean_apply_1(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_1);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = x_3 + x_15;
x_17 = x_14;
x_18 = lean_array_uset(x_10, x_3, x_17);
x_3 = x_16;
x_4 = x_18;
goto _start;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_instFromJsonArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_instFromJsonArray___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_instFromJsonArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = x_3;
x_8 = l_Array_mapMUnsafe_map___at_Lean_instFromJsonArray___spec__1___rarg(x_1, x_5, x_6, x_7);
x_9 = x_8;
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
}
}
lean_object* l_Lean_instFromJsonArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instFromJsonArray___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_instFromJsonArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_instFromJsonArray___spec__1___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_instToJsonArray___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_10);
x_12 = 1;
x_13 = x_3 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_9, x_3, x_14);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_instToJsonArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_instToJsonArray___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_instToJsonArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
x_6 = x_2;
x_7 = l_Array_mapMUnsafe_map___at_Lean_instToJsonArray___spec__1___rarg(x_1, x_4, x_5, x_6);
x_8 = x_7;
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
lean_object* l_Lean_instToJsonArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToJsonArray___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_instToJsonArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_instToJsonArray___spec__1___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_instFromJsonOption_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_instFromJsonOption_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instFromJsonOption_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_instFromJsonOption___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_instFromJsonOption___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l_Lean_instFromJsonOption___rarg___closed__1;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
}
lean_object* l_Lean_instFromJsonOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instFromJsonOption___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_instToJsonOption_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_instToJsonOption_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instToJsonOption_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_instToJsonOption___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
}
lean_object* l_Lean_instToJsonOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToJsonOption___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Json_instFromJsonStructured_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 5:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_apply_1(x_4, x_1);
return x_9;
}
}
}
}
lean_object* l_Lean_Json_instFromJsonStructured_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Json_instFromJsonStructured_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Json_instFromJsonStructured(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
case 5:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
}
lean_object* l_Lean_Json_instFromJsonStructured___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_instFromJsonStructured(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_instToJsonStructured_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Json_instToJsonStructured_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Json_instToJsonStructured_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Json_instToJsonStructured(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Json_instToJsonStructured___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_instToJsonStructured(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_toStructured_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
switch (lean_obj_tag(x_3)) {
case 4:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
case 5:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
default: 
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_box(0);
return x_10;
}
}
}
}
lean_object* l_Lean_Json_toStructured_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Json_toStructured_x3f___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Json_getObjValD(x_1, x_4);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Json_getObjValAs_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Json_opt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Json_opt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Json_opt___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Json_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_Json_FromToJson(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instToJsonJson___closed__1 = _init_l_Lean_instToJsonJson___closed__1();
lean_mark_persistent(l_Lean_instToJsonJson___closed__1);
l_Lean_instToJsonJson = _init_l_Lean_instToJsonJson();
lean_mark_persistent(l_Lean_instToJsonJson);
l_Lean_instFromJsonJsonNumber___closed__1 = _init_l_Lean_instFromJsonJsonNumber___closed__1();
lean_mark_persistent(l_Lean_instFromJsonJsonNumber___closed__1);
l_Lean_instFromJsonJsonNumber = _init_l_Lean_instFromJsonJsonNumber();
lean_mark_persistent(l_Lean_instFromJsonJsonNumber);
l_Lean_instFromJsonBool___closed__1 = _init_l_Lean_instFromJsonBool___closed__1();
lean_mark_persistent(l_Lean_instFromJsonBool___closed__1);
l_Lean_instFromJsonBool = _init_l_Lean_instFromJsonBool();
lean_mark_persistent(l_Lean_instFromJsonBool);
l_Lean_instFromJsonNat___closed__1 = _init_l_Lean_instFromJsonNat___closed__1();
lean_mark_persistent(l_Lean_instFromJsonNat___closed__1);
l_Lean_instFromJsonNat = _init_l_Lean_instFromJsonNat();
lean_mark_persistent(l_Lean_instFromJsonNat);
l_Lean_instFromJsonInt___closed__1 = _init_l_Lean_instFromJsonInt___closed__1();
lean_mark_persistent(l_Lean_instFromJsonInt___closed__1);
l_Lean_instFromJsonInt = _init_l_Lean_instFromJsonInt();
lean_mark_persistent(l_Lean_instFromJsonInt);
l_Lean_instFromJsonString___closed__1 = _init_l_Lean_instFromJsonString___closed__1();
lean_mark_persistent(l_Lean_instFromJsonString___closed__1);
l_Lean_instFromJsonString = _init_l_Lean_instFromJsonString();
lean_mark_persistent(l_Lean_instFromJsonString);
l_Lean_instFromJsonOption___rarg___closed__1 = _init_l_Lean_instFromJsonOption___rarg___closed__1();
lean_mark_persistent(l_Lean_instFromJsonOption___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
