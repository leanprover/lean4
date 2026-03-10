// Lean compiler output
// Module: Std.Internal.Http.Data.Extensions
// Imports: public import Init.Dynamic public import Init.Data.String public import Std.Data.TreeMap
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
LEAN_EXPORT uint8_t l_Std_Http_Extensions_compareName(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedExtensions_default;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedExtensions;
LEAN_EXPORT lean_object* l_Std_Http_Extensions_empty;
static const lean_closure_object l_Std_Http_Extensions_get___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Extensions_compareName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Extensions_get___redArg___closed__0 = (const lean_object*)&l_Std_Http_Extensions_get___redArg___closed__0_value;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_insert(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_remove___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_remove(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Extensions_contains___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_contains___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Extensions_contains(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_contains___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Extensions_compareName(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
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
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Std_Http_Extensions_compareName(x_6, x_8);
if (x_10 == 1)
{
uint8_t x_11; 
x_11 = lean_string_dec_lt(x_7, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_string_dec_eq(x_7, x_9);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 2;
return x_13;
}
else
{
return x_10;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
else
{
return x_10;
}
}
default: 
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = l_Std_Http_Extensions_compareName(x_16, x_18);
if (x_20 == 1)
{
uint8_t x_21; 
x_21 = lean_nat_dec_lt(x_17, x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_17, x_19);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = 2;
return x_23;
}
else
{
return x_20;
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
else
{
return x_20;
}
}
else
{
uint8_t x_25; 
x_25 = 2;
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Http_Extensions_compareName(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Http_instInhabitedExtensions_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
static lean_object* _init_l_Std_Http_instInhabitedExtensions(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
static lean_object* _init_l_Std_Http_Extensions_empty(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_get___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
lean_inc(x_2);
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(x_3, x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_6, x_2);
lean_dec(x_2);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_get(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
lean_inc(x_3);
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(x_4, x_1, x_3);
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
lean_dec_ref(x_5);
x_8 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_7, x_3);
lean_dec(x_3);
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
x_6 = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(x_4);
x_7 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_5, x_6, x_4, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
x_7 = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(x_5);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_6, x_7, x_5, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_remove___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
x_4 = l_Std_DTreeMap_Internal_Impl_erase___redArg(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_remove(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
x_5 = l_Std_DTreeMap_Internal_Impl_erase___redArg(x_4, x_3, x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Extensions_contains___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
x_4 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_contains___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Http_Extensions_contains___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Extensions_contains(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
x_5 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_4, x_3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_contains___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Http_Extensions_contains(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* runtime_initialize_Init_Dynamic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_Extensions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Dynamic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_instInhabitedExtensions_default = _init_l_Std_Http_instInhabitedExtensions_default();
lean_mark_persistent(l_Std_Http_instInhabitedExtensions_default);
l_Std_Http_instInhabitedExtensions = _init_l_Std_Http_instInhabitedExtensions();
lean_mark_persistent(l_Std_Http_instInhabitedExtensions);
l_Std_Http_Extensions_empty = _init_l_Std_Http_Extensions_empty();
lean_mark_persistent(l_Std_Http_Extensions_empty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Data_Extensions(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Dynamic(uint8_t builtin);
lean_object* initialize_Init_Data_String(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_Extensions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Dynamic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Extensions(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Data_Extensions(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Data_Extensions(builtin);
}
#ifdef __cplusplus
}
#endif
