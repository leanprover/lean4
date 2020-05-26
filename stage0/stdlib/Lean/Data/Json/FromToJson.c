// Lean compiler output
// Module: Lean.Data.Json.FromToJson
// Imports: Lean.Data.Json.Basic Init.Data.List.Control
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
lean_object* l_Lean_String_hasFromJson___closed__1;
lean_object* l_Lean_Json_HasToJson;
lean_object* l_Lean_Json_getInt_x3f___boxed(lean_object*);
lean_object* l_Lean_Json_getNum_x3f___boxed(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f___boxed(lean_object*);
lean_object* l_Lean_JsonNumber_hasToJson(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Int_hasFromJson___closed__1;
lean_object* l_Lean_JsonNumber_hasFromJson;
lean_object* l_Lean_Int_hasToJson(lean_object*);
lean_object* l_Lean_String_hasFromJson;
extern lean_object* l_Nat_HasOfNat___closed__1;
lean_object* l_Lean_String_hasToJson(lean_object*);
lean_object* l_Lean_Int_hasFromJson;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Array_hasFromJson(lean_object*);
lean_object* l_Lean_Nat_hasFromJson___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_List_hasToJson___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_List_hasToJson___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Json_hasFromJson(lean_object*);
lean_object* l_Lean_Json_getNat_x3f___boxed(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Array_hasFromJson___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Nat_hasToJson(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_List_hasToJson___spec__1(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Bool_hasToJson___boxed(lean_object*);
lean_object* l_Lean_List_hasToJson(lean_object*);
lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
lean_object* l_Lean_Bool_hasFromJson___closed__1;
lean_object* l_Lean_JsonNumber_hasFromJson___closed__1;
lean_object* l_Lean_Bool_hasFromJson;
lean_object* l_Lean_Array_hasFromJson___rarg(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Bool_hasToJson(uint8_t);
lean_object* l_Lean_Nat_hasFromJson;
lean_object* l_Lean_Json_getObjValAs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Array_hasFromJson___spec__1(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Json_hasFromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Json_HasToJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_HasOfNat___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_JsonNumber_hasFromJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_getNum_x3f___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_JsonNumber_hasFromJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonNumber_hasFromJson___closed__1;
return x_1;
}
}
lean_object* l_Lean_JsonNumber_hasToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Bool_hasFromJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_getBool_x3f___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Bool_hasFromJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Bool_hasFromJson___closed__1;
return x_1;
}
}
lean_object* l_Lean_Bool_hasToJson(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Bool_hasToJson___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Bool_hasToJson(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Nat_hasFromJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_getNat_x3f___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Nat_hasFromJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Nat_hasFromJson___closed__1;
return x_1;
}
}
lean_object* l_Lean_Nat_hasToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonNumber_fromNat(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Int_hasFromJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_getInt_x3f___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Int_hasFromJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Int_hasFromJson___closed__1;
return x_1;
}
}
lean_object* l_Lean_Int_hasToJson(lean_object* x_1) {
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
lean_object* _init_l_Lean_String_hasFromJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_getStr_x3f___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_String_hasFromJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_String_hasFromJson___closed__1;
return x_1;
}
}
lean_object* l_Lean_String_hasToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Array_hasFromJson___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_3, x_2, x_9);
x_11 = x_8;
lean_inc(x_1);
x_12 = lean_apply_1(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
x_17 = x_14;
x_18 = lean_array_fset(x_10, x_2, x_17);
lean_dec(x_2);
x_2 = x_16;
x_3 = x_18;
goto _start;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Array_hasFromJson___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Array_hasFromJson___spec__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Array_hasFromJson___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = x_3;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_Lean_Array_hasFromJson___spec__1___rarg(x_1, x_5, x_4);
x_7 = x_6;
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
}
}
lean_object* l_Lean_Array_hasFromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Array_hasFromJson___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_List_hasToJson___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_List_hasToJson___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_List_hasToJson___spec__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_List_hasToJson___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = x_2;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_umapMAux___main___at_Lean_List_hasToJson___spec__1___rarg(x_1, x_4, x_3);
x_6 = x_5;
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
lean_object* l_Lean_List_hasToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_List_hasToJson___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Json_getObjVal_x3f(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
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
lean_object* initialize_Lean_Data_Json_Basic(lean_object*);
lean_object* initialize_Init_Data_List_Control(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_Json_FromToJson(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Json_HasToJson = _init_l_Lean_Json_HasToJson();
lean_mark_persistent(l_Lean_Json_HasToJson);
l_Lean_JsonNumber_hasFromJson___closed__1 = _init_l_Lean_JsonNumber_hasFromJson___closed__1();
lean_mark_persistent(l_Lean_JsonNumber_hasFromJson___closed__1);
l_Lean_JsonNumber_hasFromJson = _init_l_Lean_JsonNumber_hasFromJson();
lean_mark_persistent(l_Lean_JsonNumber_hasFromJson);
l_Lean_Bool_hasFromJson___closed__1 = _init_l_Lean_Bool_hasFromJson___closed__1();
lean_mark_persistent(l_Lean_Bool_hasFromJson___closed__1);
l_Lean_Bool_hasFromJson = _init_l_Lean_Bool_hasFromJson();
lean_mark_persistent(l_Lean_Bool_hasFromJson);
l_Lean_Nat_hasFromJson___closed__1 = _init_l_Lean_Nat_hasFromJson___closed__1();
lean_mark_persistent(l_Lean_Nat_hasFromJson___closed__1);
l_Lean_Nat_hasFromJson = _init_l_Lean_Nat_hasFromJson();
lean_mark_persistent(l_Lean_Nat_hasFromJson);
l_Lean_Int_hasFromJson___closed__1 = _init_l_Lean_Int_hasFromJson___closed__1();
lean_mark_persistent(l_Lean_Int_hasFromJson___closed__1);
l_Lean_Int_hasFromJson = _init_l_Lean_Int_hasFromJson();
lean_mark_persistent(l_Lean_Int_hasFromJson);
l_Lean_String_hasFromJson___closed__1 = _init_l_Lean_String_hasFromJson___closed__1();
lean_mark_persistent(l_Lean_String_hasFromJson___closed__1);
l_Lean_String_hasFromJson = _init_l_Lean_String_hasFromJson();
lean_mark_persistent(l_Lean_String_hasFromJson);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
