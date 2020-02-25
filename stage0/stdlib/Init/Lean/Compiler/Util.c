// Lean compiler output
// Module: Init.Lean.Compiler.Util
// Imports: Init.Lean.Environment
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
lean_object* l_Lean_Compiler_atMostOnce___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_objectType___closed__3;
lean_object* l_Lean_Compiler_atMostOnce_visit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_voidType;
lean_object* l_Lean_Compiler_neutralExpr___closed__1;
lean_object* l_List_map___main___at___private_Init_Lean_Compiler_Util_1__getDeclNamesForCodeGen___spec__1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLcProof___closed__3;
lean_object* l_Lean_Compiler_objectType;
lean_object* l_Lean_Compiler_objectType___closed__2;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLcProof___closed__2;
lean_object* l_Lean_Compiler_atMostOnce_visit___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_neutralExpr___closed__2;
lean_object* l_Lean_Compiler_checkIsDefinition___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLcProof___closed__1;
lean_object* l_Lean_Compiler_neutralExpr;
lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(lean_object*);
lean_object* l_Lean_Compiler_atMostOnce_visit___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_is_eager_lambda_lifting_name(lean_object*);
lean_object* l_Lean_Compiler_atMostOnce_visit___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_voidType___closed__3;
lean_object* lean_get_decl_names_for_code_gen(lean_object*);
lean_object* l_Lean_Compiler_atMostOnce_HasAndthen___closed__1;
lean_object* l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1;
lean_object* l_Lean_Compiler_atMostOnce_skip___boxed(lean_object*);
lean_object* l_Lean_Compiler_neutralExpr___closed__3;
lean_object* l_Lean_Compiler_voidType___closed__2;
lean_object* l_Nat_repr(lean_object*);
uint8_t l_Lean_Compiler_isEagerLambdaLiftingName___main(lean_object*);
lean_object* l_Lean_Compiler_atMostOnce___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLcProof(lean_object*);
lean_object* l_Lean_Compiler_atMostOnce_visitFVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_atMostOnce_HasAndthen;
lean_object* l_Lean_Compiler_checkIsDefinition(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_voidType___closed__1;
lean_object* l_Lean_Compiler_unreachableExpr;
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___main___boxed(lean_object*);
lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___main___closed__1;
lean_object* l_Lean_Compiler_atMostOnce_seq(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_objectType___closed__1;
lean_object* l_Lean_Compiler_checkIsDefinition___closed__4;
lean_object* l_Lean_Compiler_checkIsDefinition___closed__1;
lean_object* l_Lean_Compiler_atMostOnce_visitFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_checkIsDefinition___closed__5;
lean_object* l_Lean_Compiler_unreachableExpr___closed__2;
lean_object* l_Lean_Compiler_atMostOnce_skip(lean_object*);
lean_object* l_Lean_Compiler_checkIsDefinition___closed__2;
lean_object* lean_mk_eager_lambda_lifting_name(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t lean_at_most_once(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_unreachableExpr___closed__1;
lean_object* l_Lean_Compiler_unreachableExpr___closed__3;
lean_object* _init_l_Lean_Compiler_neutralExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_neutral");
return x_1;
}
}
lean_object* _init_l_Lean_Compiler_neutralExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_neutralExpr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Compiler_neutralExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_neutralExpr___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Compiler_neutralExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_neutralExpr___closed__3;
return x_1;
}
}
lean_object* _init_l_Lean_Compiler_unreachableExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_unreachable");
return x_1;
}
}
lean_object* _init_l_Lean_Compiler_unreachableExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_unreachableExpr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Compiler_unreachableExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_unreachableExpr___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Compiler_unreachableExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_unreachableExpr___closed__3;
return x_1;
}
}
lean_object* _init_l_Lean_Compiler_objectType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_obj");
return x_1;
}
}
lean_object* _init_l_Lean_Compiler_objectType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_objectType___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Compiler_objectType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_objectType___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Compiler_objectType() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_objectType___closed__3;
return x_1;
}
}
lean_object* _init_l_Lean_Compiler_voidType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_void");
return x_1;
}
}
lean_object* _init_l_Lean_Compiler_voidType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_voidType___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Compiler_voidType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_voidType___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Compiler_voidType() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_voidType___closed__3;
return x_1;
}
}
lean_object* _init_l_Lean_Compiler_mkLcProof___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lcProof");
return x_1;
}
}
lean_object* _init_l_Lean_Compiler_mkLcProof___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkLcProof___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Compiler_mkLcProof___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkLcProof___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Compiler_mkLcProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_mkLcProof___closed__3;
x_3 = l_Lean_mkApp(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Compiler_atMostOnce_seq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_ctor_get_uint8(x_4, 7);
if (x_5 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_apply_1(x_2, x_4);
return x_6;
}
}
}
lean_object* _init_l_Lean_Compiler_atMostOnce_HasAndthen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_atMostOnce_seq), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Compiler_atMostOnce_HasAndthen() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_atMostOnce_HasAndthen___closed__1;
return x_1;
}
}
lean_object* l_Lean_Compiler_atMostOnce_skip(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Compiler_atMostOnce_skip___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_atMostOnce_skip(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_atMostOnce_visitFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_3, 6);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_3, 7);
if (x_6 == 0)
{
uint32_t x_7; uint16_t x_8; 
x_7 = 0;
x_8 = 0;
lean_ctor_set_uint8(x_3, 6, x_6);
lean_ctor_set_uint32(x_3, 0, x_7);
lean_ctor_set_uint16(x_3, 4, x_8);
return x_3;
}
else
{
uint8_t x_9; uint32_t x_10; uint16_t x_11; 
x_9 = lean_name_eq(x_1, x_2);
x_10 = 0;
x_11 = 0;
lean_ctor_set_uint8(x_3, 6, x_9);
lean_ctor_set_uint32(x_3, 0, x_10);
lean_ctor_set_uint16(x_3, 4, x_11);
return x_3;
}
}
else
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_3, 7);
lean_dec(x_3);
if (x_12 == 0)
{
uint32_t x_13; uint16_t x_14; lean_object* x_15; 
x_13 = 0;
x_14 = 0;
x_15 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_15, 6, x_12);
lean_ctor_set_uint8(x_15, 7, x_12);
lean_ctor_set_uint32(x_15, 0, x_13);
lean_ctor_set_uint16(x_15, 4, x_14);
return x_15;
}
else
{
uint8_t x_16; uint32_t x_17; uint16_t x_18; lean_object* x_19; 
x_16 = lean_name_eq(x_1, x_2);
x_17 = 0;
x_18 = 0;
x_19 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_19, 6, x_16);
lean_ctor_set_uint8(x_19, 7, x_12);
lean_ctor_set_uint32(x_19, 0, x_17);
lean_ctor_set_uint16(x_19, 4, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_3, 7);
if (x_20 == 0)
{
return x_3;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_name_eq(x_1, x_2);
if (x_22 == 0)
{
uint8_t x_23; uint32_t x_24; uint16_t x_25; 
x_23 = 1;
x_24 = 0;
x_25 = 0;
lean_ctor_set_uint8(x_3, 6, x_20);
lean_ctor_set_uint8(x_3, 7, x_23);
lean_ctor_set_uint32(x_3, 0, x_24);
lean_ctor_set_uint16(x_3, 4, x_25);
return x_3;
}
else
{
uint8_t x_26; uint32_t x_27; uint16_t x_28; 
x_26 = 0;
x_27 = 0;
x_28 = 0;
lean_ctor_set_uint8(x_3, 6, x_20);
lean_ctor_set_uint8(x_3, 7, x_26);
lean_ctor_set_uint32(x_3, 0, x_27);
lean_ctor_set_uint16(x_3, 4, x_28);
return x_3;
}
}
else
{
uint8_t x_29; 
lean_dec(x_3);
x_29 = lean_name_eq(x_1, x_2);
if (x_29 == 0)
{
uint8_t x_30; uint32_t x_31; uint16_t x_32; lean_object* x_33; 
x_30 = 1;
x_31 = 0;
x_32 = 0;
x_33 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_33, 6, x_20);
lean_ctor_set_uint8(x_33, 7, x_30);
lean_ctor_set_uint32(x_33, 0, x_31);
lean_ctor_set_uint16(x_33, 4, x_32);
return x_33;
}
else
{
uint8_t x_34; uint32_t x_35; uint16_t x_36; lean_object* x_37; 
x_34 = 0;
x_35 = 0;
x_36 = 0;
x_37 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_37, 6, x_20);
lean_ctor_set_uint8(x_37, 7, x_34);
lean_ctor_set_uint32(x_37, 0, x_35);
lean_ctor_set_uint16(x_37, 4, x_36);
return x_37;
}
}
}
}
}
}
lean_object* l_Lean_Compiler_atMostOnce_visitFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_atMostOnce_visitFVar(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Compiler_atMostOnce_visit___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_3, 6);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_3, 7);
if (x_6 == 0)
{
uint32_t x_7; uint16_t x_8; 
x_7 = 0;
x_8 = 0;
lean_ctor_set_uint8(x_3, 6, x_6);
lean_ctor_set_uint32(x_3, 0, x_7);
lean_ctor_set_uint16(x_3, 4, x_8);
return x_3;
}
else
{
lean_object* x_9; uint8_t x_10; uint32_t x_11; uint16_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_name_eq(x_9, x_1);
x_11 = 0;
x_12 = 0;
lean_ctor_set_uint8(x_3, 6, x_10);
lean_ctor_set_uint32(x_3, 0, x_11);
lean_ctor_set_uint16(x_3, 4, x_12);
return x_3;
}
}
else
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_3, 7);
lean_dec(x_3);
if (x_13 == 0)
{
uint32_t x_14; uint16_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = 0;
x_16 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_16, 6, x_13);
lean_ctor_set_uint8(x_16, 7, x_13);
lean_ctor_set_uint32(x_16, 0, x_14);
lean_ctor_set_uint16(x_16, 4, x_15);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; uint32_t x_19; uint16_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_name_eq(x_17, x_1);
x_19 = 0;
x_20 = 0;
x_21 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_21, 6, x_18);
lean_ctor_set_uint8(x_21, 7, x_13);
lean_ctor_set_uint32(x_21, 0, x_19);
lean_ctor_set_uint16(x_21, 4, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
x_22 = lean_ctor_get_uint8(x_3, 7);
if (x_22 == 0)
{
return x_3;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_name_eq(x_24, x_1);
if (x_25 == 0)
{
uint8_t x_26; uint32_t x_27; uint16_t x_28; 
x_26 = 1;
x_27 = 0;
x_28 = 0;
lean_ctor_set_uint8(x_3, 6, x_22);
lean_ctor_set_uint8(x_3, 7, x_26);
lean_ctor_set_uint32(x_3, 0, x_27);
lean_ctor_set_uint16(x_3, 4, x_28);
return x_3;
}
else
{
uint8_t x_29; uint32_t x_30; uint16_t x_31; 
x_29 = 0;
x_30 = 0;
x_31 = 0;
lean_ctor_set_uint8(x_3, 6, x_22);
lean_ctor_set_uint8(x_3, 7, x_29);
lean_ctor_set_uint32(x_3, 0, x_30);
lean_ctor_set_uint16(x_3, 4, x_31);
return x_3;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
lean_dec(x_3);
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_name_eq(x_32, x_1);
if (x_33 == 0)
{
uint8_t x_34; uint32_t x_35; uint16_t x_36; lean_object* x_37; 
x_34 = 1;
x_35 = 0;
x_36 = 0;
x_37 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_37, 6, x_22);
lean_ctor_set_uint8(x_37, 7, x_34);
lean_ctor_set_uint32(x_37, 0, x_35);
lean_ctor_set_uint16(x_37, 4, x_36);
return x_37;
}
else
{
uint8_t x_38; uint32_t x_39; uint16_t x_40; lean_object* x_41; 
x_38 = 0;
x_39 = 0;
x_40 = 0;
x_41 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_41, 6, x_22);
lean_ctor_set_uint8(x_41, 7, x_38);
lean_ctor_set_uint32(x_41, 0, x_39);
lean_ctor_set_uint16(x_41, 4, x_40);
return x_41;
}
}
}
}
}
case 5:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
x_44 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_43, x_3);
x_45 = lean_ctor_get_uint8(x_44, 7);
if (x_45 == 0)
{
return x_44;
}
else
{
x_2 = x_42;
x_3 = x_44;
goto _start;
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_2, 1);
x_48 = lean_ctor_get(x_2, 2);
x_49 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_47, x_3);
x_50 = lean_ctor_get_uint8(x_49, 7);
if (x_50 == 0)
{
return x_49;
}
else
{
x_2 = x_48;
x_3 = x_49;
goto _start;
}
}
case 7:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_2, 1);
x_53 = lean_ctor_get(x_2, 2);
x_54 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_52, x_3);
x_55 = lean_ctor_get_uint8(x_54, 7);
if (x_55 == 0)
{
return x_54;
}
else
{
x_2 = x_53;
x_3 = x_54;
goto _start;
}
}
case 8:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_2, 1);
x_58 = lean_ctor_get(x_2, 2);
x_59 = lean_ctor_get(x_2, 3);
x_60 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_57, x_3);
x_61 = lean_ctor_get_uint8(x_60, 7);
if (x_61 == 0)
{
return x_60;
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_58, x_60);
x_63 = lean_ctor_get_uint8(x_62, 7);
if (x_63 == 0)
{
return x_62;
}
else
{
x_2 = x_59;
x_3 = x_62;
goto _start;
}
}
}
case 10:
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_2, 1);
x_2 = x_65;
goto _start;
}
case 11:
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_2, 2);
x_2 = x_67;
goto _start;
}
default: 
{
return x_3;
}
}
}
}
lean_object* l_Lean_Compiler_atMostOnce_visit___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Compiler_atMostOnce_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Compiler_atMostOnce_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_atMostOnce_visit(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Compiler_atMostOnce___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint32_t x_3; uint16_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = 0;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_5, 6, x_1);
lean_ctor_set_uint8(x_5, 7, x_2);
lean_ctor_set_uint32(x_5, 0, x_3);
lean_ctor_set_uint16(x_5, 4, x_4);
return x_5;
}
}
uint8_t lean_at_most_once(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Compiler_atMostOnce___closed__1;
x_4 = l_Lean_Compiler_atMostOnce_visit___main(x_2, x_1, x_3);
lean_dec(x_1);
lean_dec(x_2);
x_5 = lean_ctor_get_uint8(x_4, 7);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_Compiler_atMostOnce___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_at_most_once(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_elambda_");
return x_1;
}
}
lean_object* lean_mk_eager_lambda_lifting_name(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Nat_repr(x_2);
x_4 = l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = lean_name_mk_string(x_1, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Compiler_isEagerLambdaLiftingName___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_elambda");
return x_1;
}
}
uint8_t l_Lean_Compiler_isEagerLambdaLiftingName___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Compiler_isEagerLambdaLiftingName___main___closed__1;
x_6 = l_String_isPrefixOf(x_5, x_4);
if (x_6 == 0)
{
x_1 = x_3;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
default: 
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 0);
x_1 = x_9;
goto _start;
}
}
}
}
lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_isEagerLambdaLiftingName___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t lean_is_eager_lambda_lifting_name(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Compiler_isEagerLambdaLiftingName___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_is_eager_lambda_lifting_name(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Compiler_Util_1__getDeclNamesForCodeGen___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_List_map___main___at___private_Init_Lean_Compiler_Util_1__getDeclNamesForCodeGen___spec__1(x_6);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = l_List_map___main___at___private_Init_Lean_Compiler_Util_1__getDeclNamesForCodeGen___spec__1(x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* lean_get_decl_names_for_code_gen(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
case 3:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
case 5:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_List_map___main___at___private_Init_Lean_Compiler_Util_1__getDeclNamesForCodeGen___spec__1(x_12);
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_box(0);
return x_14;
}
}
}
}
lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknow declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_checkIsDefinition___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declaration is not a definition");
return x_1;
}
}
lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_checkIsDefinition(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_checkIsDefinition___closed__2;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
lean_dec(x_5);
x_6 = l_Lean_Compiler_checkIsDefinition___closed__5;
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = l_Lean_Compiler_checkIsDefinition___closed__4;
return x_7;
}
}
}
}
lean_object* initialize_Init_Lean_Environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_Util(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_neutralExpr___closed__1 = _init_l_Lean_Compiler_neutralExpr___closed__1();
lean_mark_persistent(l_Lean_Compiler_neutralExpr___closed__1);
l_Lean_Compiler_neutralExpr___closed__2 = _init_l_Lean_Compiler_neutralExpr___closed__2();
lean_mark_persistent(l_Lean_Compiler_neutralExpr___closed__2);
l_Lean_Compiler_neutralExpr___closed__3 = _init_l_Lean_Compiler_neutralExpr___closed__3();
lean_mark_persistent(l_Lean_Compiler_neutralExpr___closed__3);
l_Lean_Compiler_neutralExpr = _init_l_Lean_Compiler_neutralExpr();
lean_mark_persistent(l_Lean_Compiler_neutralExpr);
l_Lean_Compiler_unreachableExpr___closed__1 = _init_l_Lean_Compiler_unreachableExpr___closed__1();
lean_mark_persistent(l_Lean_Compiler_unreachableExpr___closed__1);
l_Lean_Compiler_unreachableExpr___closed__2 = _init_l_Lean_Compiler_unreachableExpr___closed__2();
lean_mark_persistent(l_Lean_Compiler_unreachableExpr___closed__2);
l_Lean_Compiler_unreachableExpr___closed__3 = _init_l_Lean_Compiler_unreachableExpr___closed__3();
lean_mark_persistent(l_Lean_Compiler_unreachableExpr___closed__3);
l_Lean_Compiler_unreachableExpr = _init_l_Lean_Compiler_unreachableExpr();
lean_mark_persistent(l_Lean_Compiler_unreachableExpr);
l_Lean_Compiler_objectType___closed__1 = _init_l_Lean_Compiler_objectType___closed__1();
lean_mark_persistent(l_Lean_Compiler_objectType___closed__1);
l_Lean_Compiler_objectType___closed__2 = _init_l_Lean_Compiler_objectType___closed__2();
lean_mark_persistent(l_Lean_Compiler_objectType___closed__2);
l_Lean_Compiler_objectType___closed__3 = _init_l_Lean_Compiler_objectType___closed__3();
lean_mark_persistent(l_Lean_Compiler_objectType___closed__3);
l_Lean_Compiler_objectType = _init_l_Lean_Compiler_objectType();
lean_mark_persistent(l_Lean_Compiler_objectType);
l_Lean_Compiler_voidType___closed__1 = _init_l_Lean_Compiler_voidType___closed__1();
lean_mark_persistent(l_Lean_Compiler_voidType___closed__1);
l_Lean_Compiler_voidType___closed__2 = _init_l_Lean_Compiler_voidType___closed__2();
lean_mark_persistent(l_Lean_Compiler_voidType___closed__2);
l_Lean_Compiler_voidType___closed__3 = _init_l_Lean_Compiler_voidType___closed__3();
lean_mark_persistent(l_Lean_Compiler_voidType___closed__3);
l_Lean_Compiler_voidType = _init_l_Lean_Compiler_voidType();
lean_mark_persistent(l_Lean_Compiler_voidType);
l_Lean_Compiler_mkLcProof___closed__1 = _init_l_Lean_Compiler_mkLcProof___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkLcProof___closed__1);
l_Lean_Compiler_mkLcProof___closed__2 = _init_l_Lean_Compiler_mkLcProof___closed__2();
lean_mark_persistent(l_Lean_Compiler_mkLcProof___closed__2);
l_Lean_Compiler_mkLcProof___closed__3 = _init_l_Lean_Compiler_mkLcProof___closed__3();
lean_mark_persistent(l_Lean_Compiler_mkLcProof___closed__3);
l_Lean_Compiler_atMostOnce_HasAndthen___closed__1 = _init_l_Lean_Compiler_atMostOnce_HasAndthen___closed__1();
lean_mark_persistent(l_Lean_Compiler_atMostOnce_HasAndthen___closed__1);
l_Lean_Compiler_atMostOnce_HasAndthen = _init_l_Lean_Compiler_atMostOnce_HasAndthen();
lean_mark_persistent(l_Lean_Compiler_atMostOnce_HasAndthen);
l_Lean_Compiler_atMostOnce___closed__1 = _init_l_Lean_Compiler_atMostOnce___closed__1();
lean_mark_persistent(l_Lean_Compiler_atMostOnce___closed__1);
l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1 = _init_l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1);
l_Lean_Compiler_isEagerLambdaLiftingName___main___closed__1 = _init_l_Lean_Compiler_isEagerLambdaLiftingName___main___closed__1();
lean_mark_persistent(l_Lean_Compiler_isEagerLambdaLiftingName___main___closed__1);
l_Lean_Compiler_checkIsDefinition___closed__1 = _init_l_Lean_Compiler_checkIsDefinition___closed__1();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__1);
l_Lean_Compiler_checkIsDefinition___closed__2 = _init_l_Lean_Compiler_checkIsDefinition___closed__2();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__2);
l_Lean_Compiler_checkIsDefinition___closed__3 = _init_l_Lean_Compiler_checkIsDefinition___closed__3();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__3);
l_Lean_Compiler_checkIsDefinition___closed__4 = _init_l_Lean_Compiler_checkIsDefinition___closed__4();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__4);
l_Lean_Compiler_checkIsDefinition___closed__5 = _init_l_Lean_Compiler_checkIsDefinition___closed__5();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__5);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
