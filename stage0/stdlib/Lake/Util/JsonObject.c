// Lean compiler output
// Module: Lake.Util.JsonObject
// Imports: Lean.Data.Json
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
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_instToJson;
lean_object* l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_getJson_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_insertSome(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_get___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_JsonObject_get___rarg___closed__2;
lean_object* l_Lean_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_mk___boxed(lean_object*);
lean_object* l_Lean_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_getD(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_get_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_appendTrees___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_getD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_erase___boxed(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_instFromJson;
static lean_object* l_Lake_JsonObject_get___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lake_JsonObject_getD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_JsonObject_get_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_JsonObject_insertSome___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_JsonObject_get___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_JsonObject_insert(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_get_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lake_JsonObject_erase___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_instCoeJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_get_x3f(lean_object*);
uint8_t l_Lean_RBNode_isBlack___rarg(lean_object*);
static lean_object* l_Lake_JsonObject_instToJson___closed__1;
LEAN_EXPORT lean_object* l_Lake_JsonObject_mk(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_JsonObject_instFromJson___closed__1;
lean_object* l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_get___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lake_JsonObject_erase___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_get(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_mk(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_mk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_JsonObject_mk(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_instCoeJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_JsonObject_instToJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_JsonObject_toJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_JsonObject_instToJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_JsonObject_instToJson___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getObj_x3f(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_JsonObject_instFromJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_JsonObject_fromJson_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_JsonObject_instFromJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_JsonObject_instFromJson___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_JsonObject_insert___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_insertSome___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_1, x_5);
x_7 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_2, x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_insertSome(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_JsonObject_insertSome___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lake_JsonObject_erase___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_string_dec_lt(x_1, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_string_dec_eq(x_1, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_RBNode_isBlack___rarg(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_RBNode_del___at_Lake_JsonObject_erase___spec__1(x_1, x_8);
x_13 = 0;
lean_ctor_set(x_2, 3, x_12);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_2);
x_14 = l_Lean_RBNode_del___at_Lake_JsonObject_erase___spec__1(x_1, x_8);
x_15 = l_Lean_RBNode_balRight___rarg(x_5, x_6, x_7, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
x_16 = l_Lean_RBNode_appendTrees___rarg(x_5, x_8);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = l_Lean_RBNode_isBlack___rarg(x_5);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_RBNode_del___at_Lake_JsonObject_erase___spec__1(x_1, x_5);
x_19 = 0;
lean_ctor_set(x_2, 0, x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_2);
x_20 = l_Lean_RBNode_del___at_Lake_JsonObject_erase___spec__1(x_1, x_5);
x_21 = l_Lean_RBNode_balLeft___rarg(x_20, x_6, x_7, x_8);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_26 = lean_string_dec_lt(x_1, x_23);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = lean_string_dec_eq(x_1, x_23);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_RBNode_isBlack___rarg(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Lean_RBNode_del___at_Lake_JsonObject_erase___spec__1(x_1, x_25);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_RBNode_del___at_Lake_JsonObject_erase___spec__1(x_1, x_25);
x_33 = l_Lean_RBNode_balRight___rarg(x_22, x_23, x_24, x_32);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_23);
x_34 = l_Lean_RBNode_appendTrees___rarg(x_22, x_25);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = l_Lean_RBNode_isBlack___rarg(x_22);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = l_Lean_RBNode_del___at_Lake_JsonObject_erase___spec__1(x_1, x_22);
x_37 = 0;
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 3, x_25);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_RBNode_del___at_Lake_JsonObject_erase___spec__1(x_1, x_22);
x_40 = l_Lean_RBNode_balLeft___rarg(x_39, x_23, x_24, x_25);
return x_40;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at_Lake_JsonObject_erase___spec__1(x_2, x_1);
x_4 = l_Lean_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lake_JsonObject_erase___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_del___at_Lake_JsonObject_erase___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_erase___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JsonObject_erase(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_getJson_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_getJson_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JsonObject_getJson_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_JsonObject_get___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_JsonObject_get___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_JsonObject_get___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_get___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_5 = l_Lake_JsonObject_get___rarg___closed__1;
x_6 = lean_string_append(x_5, x_3);
x_7 = l_Lake_JsonObject_get___rarg___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_apply_1(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lake_JsonObject_get___rarg___closed__2;
x_15 = lean_string_append(x_14, x_3);
x_16 = l_Lake_JsonObject_get___rarg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_13);
lean_dec(x_13);
x_19 = lean_string_append(x_18, x_14);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = l_Lake_JsonObject_get___rarg___closed__2;
x_22 = lean_string_append(x_21, x_3);
x_23 = l_Lake_JsonObject_get___rarg___closed__3;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_20);
lean_dec(x_20);
x_26 = lean_string_append(x_25, x_21);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_11, 0);
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_get(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_JsonObject_get___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_get___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_JsonObject_get___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_JsonObject_get_x3f___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_get_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_13; 
x_13 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = l_Lake_JsonObject_get_x3f___rarg___closed__1;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_free_object(x_13);
lean_dec(x_1);
x_17 = l_Lake_JsonObject_get_x3f___rarg___closed__1;
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_apply_1(x_1, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_free_object(x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_4 = x_19;
goto block_12;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_13, 0, x_21);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
lean_ctor_set(x_13, 0, x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_13);
return x_23;
}
}
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = l_Lake_JsonObject_get_x3f___rarg___closed__1;
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_apply_1(x_1, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_4 = x_27;
goto block_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(1, 1, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
block_12:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lake_JsonObject_get___rarg___closed__2;
x_6 = lean_string_append(x_5, x_3);
x_7 = l_Lake_JsonObject_get___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_string_append(x_8, x_4);
lean_dec(x_4);
x_10 = lean_string_append(x_9, x_5);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_get_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_JsonObject_get_x3f___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_get_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_JsonObject_get_x3f___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_getD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_11; lean_object* x_20; 
x_20 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_2, x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_box(0);
x_5 = x_21;
goto block_10;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 0);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_free_object(x_20);
lean_dec(x_1);
x_24 = lean_box(0);
x_5 = x_24;
goto block_10;
}
else
{
lean_object* x_25; 
x_25 = lean_apply_1(x_1, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_free_object(x_20);
lean_dec(x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_11 = x_26;
goto block_19;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_ctor_set(x_20, 0, x_27);
x_5 = x_20;
goto block_10;
}
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_dec(x_1);
x_29 = lean_box(0);
x_5 = x_29;
goto block_10;
}
else
{
lean_object* x_30; 
x_30 = lean_apply_1(x_1, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_11 = x_31;
goto block_19;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_5 = x_33;
goto block_10;
}
}
}
}
block_10:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
block_19:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = l_Lake_JsonObject_get___rarg___closed__2;
x_13 = lean_string_append(x_12, x_3);
x_14 = l_Lake_JsonObject_get___rarg___closed__3;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_11);
lean_dec(x_11);
x_17 = lean_string_append(x_16, x_12);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_getD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_JsonObject_getD___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_getD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_JsonObject_getD___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_JsonObject_instToJson___closed__1 = _init_l_Lake_JsonObject_instToJson___closed__1();
lean_mark_persistent(l_Lake_JsonObject_instToJson___closed__1);
l_Lake_JsonObject_instToJson = _init_l_Lake_JsonObject_instToJson();
lean_mark_persistent(l_Lake_JsonObject_instToJson);
l_Lake_JsonObject_instFromJson___closed__1 = _init_l_Lake_JsonObject_instFromJson___closed__1();
lean_mark_persistent(l_Lake_JsonObject_instFromJson___closed__1);
l_Lake_JsonObject_instFromJson = _init_l_Lake_JsonObject_instFromJson();
lean_mark_persistent(l_Lake_JsonObject_instFromJson);
l_Lake_JsonObject_get___rarg___closed__1 = _init_l_Lake_JsonObject_get___rarg___closed__1();
lean_mark_persistent(l_Lake_JsonObject_get___rarg___closed__1);
l_Lake_JsonObject_get___rarg___closed__2 = _init_l_Lake_JsonObject_get___rarg___closed__2();
lean_mark_persistent(l_Lake_JsonObject_get___rarg___closed__2);
l_Lake_JsonObject_get___rarg___closed__3 = _init_l_Lake_JsonObject_get___rarg___closed__3();
lean_mark_persistent(l_Lake_JsonObject_get___rarg___closed__3);
l_Lake_JsonObject_get_x3f___rarg___closed__1 = _init_l_Lake_JsonObject_get_x3f___rarg___closed__1();
lean_mark_persistent(l_Lake_JsonObject_get_x3f___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
