// Lean compiler output
// Module: Lean.Data.OpenDecl
// Imports: Init Lean.Data.Name
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
LEAN_EXPORT lean_object* l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_rootNamespace;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_rootNamespace___closed__1;
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3(uint8_t, lean_object*);
static lean_object* l_Lean_rootNamespace___closed__2;
LEAN_EXPORT lean_object* l_Lean_removeRoot(lean_object*);
static lean_object* l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___closed__1;
static lean_object* l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___closed__2;
static lean_object* l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_OpenDecl_instInhabitedOpenDecl;
LEAN_EXPORT lean_object* l_Lean_OpenDecl_instToStringOpenDecl(lean_object*);
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_OpenDecl_instToStringOpenDecl___closed__1;
static lean_object* l_Lean_OpenDecl_instToStringOpenDecl___closed__2;
static lean_object* l_Lean_OpenDecl_instInhabitedOpenDecl___closed__1;
static lean_object* l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__3;
LEAN_EXPORT uint8_t l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_OpenDecl_instInhabitedOpenDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_OpenDecl_instInhabitedOpenDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_OpenDecl_instInhabitedOpenDecl___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_name_eq(x_6, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
static lean_object* _init_l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 1;
x_7 = l_Lean_Name_toString(x_4, x_6);
x_8 = l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___closed__2;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = 0;
x_11 = l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3(x_10, x_5);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
return x_12;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___closed__1;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = 1;
x_17 = l_Lean_Name_toString(x_14, x_16);
x_18 = 0;
x_19 = l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3(x_18, x_15);
x_20 = lean_string_append(x_17, x_19);
lean_dec(x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[]");
return x_1;
}
}
static lean_object* _init_l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = 1;
x_5 = l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3(x_4, x_1);
x_6 = l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 1;
x_14 = l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3(x_13, x_12);
x_15 = l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__2;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__3;
x_18 = lean_string_append(x_16, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_OpenDecl_instToStringOpenDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" hiding ");
return x_1;
}
}
static lean_object* _init_l_Lean_OpenDecl_instToStringOpenDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" → ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_instToStringOpenDecl(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = 1;
x_5 = l_Lean_Name_toString(x_2, x_4);
x_6 = lean_box(0);
x_7 = l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2(x_3);
x_9 = l_Lean_OpenDecl_instToStringOpenDecl___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_5, x_10);
lean_dec(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___closed__1;
x_13 = lean_string_append(x_5, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = 1;
x_17 = l_Lean_Name_toString(x_14, x_16);
x_18 = l_Lean_OpenDecl_instToStringOpenDecl___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_Name_toString(x_15, x_16);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_rootNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_root_");
return x_1;
}
}
static lean_object* _init_l_Lean_rootNamespace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_rootNamespace___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_rootNamespace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_rootNamespace___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_removeRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_rootNamespace;
x_3 = lean_box(0);
x_4 = l_Lean_Name_replacePrefix(x_1, x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Name(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_OpenDecl(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_OpenDecl_instInhabitedOpenDecl___closed__1 = _init_l_Lean_OpenDecl_instInhabitedOpenDecl___closed__1();
lean_mark_persistent(l_Lean_OpenDecl_instInhabitedOpenDecl___closed__1);
l_Lean_OpenDecl_instInhabitedOpenDecl = _init_l_Lean_OpenDecl_instInhabitedOpenDecl();
lean_mark_persistent(l_Lean_OpenDecl_instInhabitedOpenDecl);
l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___closed__1 = _init_l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___closed__1();
lean_mark_persistent(l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___closed__1);
l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___closed__2 = _init_l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___closed__2();
lean_mark_persistent(l_List_toStringAux___at_Lean_OpenDecl_instToStringOpenDecl___spec__3___closed__2);
l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__1 = _init_l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__1();
lean_mark_persistent(l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__1);
l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__2 = _init_l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__2();
lean_mark_persistent(l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__2);
l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__3 = _init_l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__3();
lean_mark_persistent(l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2___closed__3);
l_Lean_OpenDecl_instToStringOpenDecl___closed__1 = _init_l_Lean_OpenDecl_instToStringOpenDecl___closed__1();
lean_mark_persistent(l_Lean_OpenDecl_instToStringOpenDecl___closed__1);
l_Lean_OpenDecl_instToStringOpenDecl___closed__2 = _init_l_Lean_OpenDecl_instToStringOpenDecl___closed__2();
lean_mark_persistent(l_Lean_OpenDecl_instToStringOpenDecl___closed__2);
l_Lean_rootNamespace___closed__1 = _init_l_Lean_rootNamespace___closed__1();
lean_mark_persistent(l_Lean_rootNamespace___closed__1);
l_Lean_rootNamespace___closed__2 = _init_l_Lean_rootNamespace___closed__2();
lean_mark_persistent(l_Lean_rootNamespace___closed__2);
l_Lean_rootNamespace = _init_l_Lean_rootNamespace();
lean_mark_persistent(l_Lean_rootNamespace);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
