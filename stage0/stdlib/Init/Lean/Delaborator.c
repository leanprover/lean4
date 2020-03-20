// Lean compiler output
// Module: Init.Lean.Delaborator
// Imports: Init.Lean.KeyedDeclsAttribute
#include "runtime/lean.h"
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
lean_object* l_Lean_Delaborator_mkDelabAttribute___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_empty___at_Lean_Delaborator_delabAttribute___spec__3;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__3;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__10;
lean_object* l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1;
lean_object* l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__1;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__2;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__7;
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__5;
lean_object* l_Lean_Delaborator_delabAttribute___closed__2;
lean_object* l_Lean_Delaborator_mkDelabAttribute___lambda__1(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_attrParamSyntaxToIdentifier(lean_object*);
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__4;
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Delaborator_delabAttribute___closed__4;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__6;
lean_object* l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__1;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__13;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__2;
lean_object* l_Lean_Delaborator_delabAttribute___closed__1;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__1;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__8;
lean_object* l_Lean_Delaborator_mkDelabAttribute(lean_object*);
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__12;
lean_object* l_Lean_Delaborator_delabAttribute;
lean_object* l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__2;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__11;
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabAttribute___closed__5;
lean_object* l_Lean_Delaborator_delabAttribute___closed__3;
extern lean_object* l_Lean_mkAppStx___closed__2;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__9;
lean_object* l_mkHashMap___at_Lean_Delaborator_delabAttribute___spec__2(lean_object*);
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid attribute argument, expected identifier");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Delaborator_mkDelabAttribute___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_attrParamSyntaxToIdentifier(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__2;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinDelab");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Delaborator_mkDelabAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("delab");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Delaborator_mkDelabAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Delaborator");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Delaborator_mkDelabAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Delab");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_mkDelabAttribute___closed__6;
x_2 = l_Lean_Delaborator_mkDelabAttribute___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("delaborator");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_mkDelabAttribute___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Delaborator_mkDelabAttribute___closed__2;
x_2 = l_Lean_Delaborator_mkDelabAttribute___closed__4;
x_3 = l_Lean_Delaborator_mkDelabAttribute___closed__9;
x_4 = l_Lean_Delaborator_mkDelabAttribute___closed__8;
x_5 = l_Lean_Delaborator_mkDelabAttribute___closed__10;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("delabAttribute");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_mkDelabAttribute___closed__6;
x_2 = l_Lean_Delaborator_mkDelabAttribute___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Delaborator_mkDelabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Delaborator_mkDelabAttribute___closed__11;
x_3 = l_Lean_Delaborator_mkDelabAttribute___closed__13;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Delaborator_mkDelabAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Delaborator_mkDelabAttribute___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_mkHashMap___at_Lean_Delaborator_delabAttribute___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_PersistentHashMap_empty___at_Lean_Delaborator_delabAttribute___spec__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__1;
x_3 = l_PersistentHashMap_empty___at_Lean_Delaborator_delabAttribute___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_delabAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Delaborator_delabAttribute___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_Delaborator_delabAttribute___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Delaborator_delabAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Delaborator_delabAttribute___closed__3;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_6 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Delaborator_delabAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Delaborator_delabAttribute___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* initialize_Init_Lean_KeyedDeclsAttribute(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Delaborator(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_KeyedDeclsAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__1 = _init_l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__1);
l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__2 = _init_l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__2);
l_Lean_Delaborator_mkDelabAttribute___closed__1 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__1();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__1);
l_Lean_Delaborator_mkDelabAttribute___closed__2 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__2();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__2);
l_Lean_Delaborator_mkDelabAttribute___closed__3 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__3();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__3);
l_Lean_Delaborator_mkDelabAttribute___closed__4 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__4();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__4);
l_Lean_Delaborator_mkDelabAttribute___closed__5 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__5();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__5);
l_Lean_Delaborator_mkDelabAttribute___closed__6 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__6();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__6);
l_Lean_Delaborator_mkDelabAttribute___closed__7 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__7();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__7);
l_Lean_Delaborator_mkDelabAttribute___closed__8 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__8();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__8);
l_Lean_Delaborator_mkDelabAttribute___closed__9 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__9();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__9);
l_Lean_Delaborator_mkDelabAttribute___closed__10 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__10();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__10);
l_Lean_Delaborator_mkDelabAttribute___closed__11 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__11();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__11);
l_Lean_Delaborator_mkDelabAttribute___closed__12 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__12();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__12);
l_Lean_Delaborator_mkDelabAttribute___closed__13 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__13();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__13);
l_PersistentHashMap_empty___at_Lean_Delaborator_delabAttribute___spec__3 = _init_l_PersistentHashMap_empty___at_Lean_Delaborator_delabAttribute___spec__3();
lean_mark_persistent(l_PersistentHashMap_empty___at_Lean_Delaborator_delabAttribute___spec__3);
l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1 = _init_l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1);
l_Lean_Delaborator_delabAttribute___closed__1 = _init_l_Lean_Delaborator_delabAttribute___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabAttribute___closed__1);
l_Lean_Delaborator_delabAttribute___closed__2 = _init_l_Lean_Delaborator_delabAttribute___closed__2();
lean_mark_persistent(l_Lean_Delaborator_delabAttribute___closed__2);
l_Lean_Delaborator_delabAttribute___closed__3 = _init_l_Lean_Delaborator_delabAttribute___closed__3();
lean_mark_persistent(l_Lean_Delaborator_delabAttribute___closed__3);
l_Lean_Delaborator_delabAttribute___closed__4 = _init_l_Lean_Delaborator_delabAttribute___closed__4();
lean_mark_persistent(l_Lean_Delaborator_delabAttribute___closed__4);
l_Lean_Delaborator_delabAttribute___closed__5 = _init_l_Lean_Delaborator_delabAttribute___closed__5();
lean_mark_persistent(l_Lean_Delaborator_delabAttribute___closed__5);
res = l_Lean_Delaborator_mkDelabAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Delaborator_delabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Delaborator_delabAttribute);
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
