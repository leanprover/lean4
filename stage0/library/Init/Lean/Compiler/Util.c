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
uint8_t l_Lean_Name_beq___main(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_atMostOnce_HasAndthen;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_atMostOnce_seq(lean_object*, lean_object*, lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Compiler_Util_1__getDeclNamesForCodeGen___spec__1(lean_object*);
lean_object* l_Lean_Compiler_mkLcProof___closed__3;
uint8_t lean_at_most_once(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_atMostOnce_HasAndthen___closed__1;
lean_object* l_Lean_Compiler_atMostOnce_visit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_unreachableExpr___closed__2;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_isEagerLambdaLiftingName___main(lean_object*);
lean_object* l_Lean_Compiler_atMostOnce_visit___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_checkIsDefinition___closed__3;
lean_object* l_Lean_Compiler_mkLcProof(lean_object*);
lean_object* l_Lean_Compiler_objectType___closed__3;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Compiler_neutralExpr___closed__1;
lean_object* l_Lean_Compiler_objectType;
lean_object* l_Lean_Compiler_neutralExpr___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_atMostOnce___closed__1;
lean_object* l_Lean_Compiler_objectType___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_atMostOnce_visit___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_atMostOnce___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_objectType___closed__1;
lean_object* l_Lean_Compiler_atMostOnce_visit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_unreachableExpr___closed__3;
lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___main___closed__1;
lean_object* l_Lean_Compiler_atMostOnce_visitFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1;
lean_object* l_Lean_Compiler_voidType;
lean_object* l_Lean_Compiler_checkIsDefinition___closed__4;
lean_object* l_Lean_Compiler_neutralExpr___closed__2;
lean_object* l_Lean_Compiler_atMostOnce_skip(lean_object*);
lean_object* lean_get_decl_names_for_code_gen(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_atMostOnce_skip___boxed(lean_object*);
lean_object* l_Lean_Compiler_unreachableExpr___closed__1;
uint8_t lean_is_eager_lambda_lifting_name(lean_object*);
lean_object* l_Lean_Compiler_mkLcProof___closed__1;
lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(lean_object*);
lean_object* l_Lean_Compiler_voidType___closed__2;
lean_object* l_Lean_Compiler_checkIsDefinition___closed__1;
lean_object* l_Lean_Compiler_mkLcProof___closed__2;
lean_object* l_Lean_Compiler_checkIsDefinition___closed__2;
lean_object* l_Lean_Compiler_checkIsDefinition(lean_object*, lean_object*);
lean_object* lean_mk_eager_lambda_lifting_name(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_voidType___closed__1;
lean_object* l_Lean_Compiler_neutralExpr;
lean_object* l_Lean_Compiler_checkIsDefinition___closed__5;
lean_object* l_Lean_Compiler_atMostOnce_visitFVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_unreachableExpr;
lean_object* l_Lean_Compiler_voidType___closed__3;
lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___main___boxed(lean_object*);
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
x_5 = lean_ctor_get_uint8(x_4, 1);
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
x_4 = lean_ctor_get_uint8(x_3, 0);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_3, 1);
if (x_6 == 0)
{
lean_ctor_set_uint8(x_3, 0, x_6);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = l_Lean_Name_beq___main(x_1, x_2);
lean_ctor_set_uint8(x_3, 0, x_7);
return x_3;
}
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_3, 1);
lean_dec(x_3);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_9, 0, x_8);
lean_ctor_set_uint8(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; 
x_10 = l_Lean_Name_beq___main(x_1, x_2);
x_11 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_11, 0, x_10);
lean_ctor_set_uint8(x_11, 1, x_8);
return x_11;
}
}
}
else
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_3, 1);
if (x_12 == 0)
{
return x_3;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_beq___main(x_1, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = 1;
lean_ctor_set_uint8(x_3, 0, x_12);
lean_ctor_set_uint8(x_3, 1, x_15);
return x_3;
}
else
{
uint8_t x_16; 
x_16 = 0;
lean_ctor_set_uint8(x_3, 0, x_12);
lean_ctor_set_uint8(x_3, 1, x_16);
return x_3;
}
}
else
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = l_Lean_Name_beq___main(x_1, x_2);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
x_19 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_19, 0, x_12);
lean_ctor_set_uint8(x_19, 1, x_18);
return x_19;
}
else
{
uint8_t x_20; lean_object* x_21; 
x_20 = 0;
x_21 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_21, 0, x_12);
lean_ctor_set_uint8(x_21, 1, x_20);
return x_21;
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
x_4 = lean_ctor_get_uint8(x_3, 0);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_3, 1);
if (x_6 == 0)
{
lean_ctor_set_uint8(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_Name_beq___main(x_7, x_1);
lean_ctor_set_uint8(x_3, 0, x_8);
return x_3;
}
}
else
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_3, 1);
lean_dec(x_3);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_10, 0, x_9);
lean_ctor_set_uint8(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = l_Lean_Name_beq___main(x_11, x_1);
x_13 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, 1, x_9);
return x_13;
}
}
}
else
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_3, 1);
if (x_14 == 0)
{
return x_3;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = l_Lean_Name_beq___main(x_16, x_1);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = 1;
lean_ctor_set_uint8(x_3, 0, x_14);
lean_ctor_set_uint8(x_3, 1, x_18);
return x_3;
}
else
{
uint8_t x_19; 
x_19 = 0;
lean_ctor_set_uint8(x_3, 0, x_14);
lean_ctor_set_uint8(x_3, 1, x_19);
return x_3;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_3);
x_20 = lean_ctor_get(x_2, 0);
x_21 = l_Lean_Name_beq___main(x_20, x_1);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = 1;
x_23 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_23, 0, x_14);
lean_ctor_set_uint8(x_23, 1, x_22);
return x_23;
}
else
{
uint8_t x_24; lean_object* x_25; 
x_24 = 0;
x_25 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_25, 0, x_14);
lean_ctor_set_uint8(x_25, 1, x_24);
return x_25;
}
}
}
}
}
case 5:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_27, x_3);
x_29 = lean_ctor_get_uint8(x_28, 1);
if (x_29 == 0)
{
return x_28;
}
else
{
x_2 = x_26;
x_3 = x_28;
goto _start;
}
}
case 6:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ctor_get(x_2, 2);
x_33 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_31, x_3);
x_34 = lean_ctor_get_uint8(x_33, 1);
if (x_34 == 0)
{
return x_33;
}
else
{
x_2 = x_32;
x_3 = x_33;
goto _start;
}
}
case 7:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get(x_2, 2);
x_38 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_36, x_3);
x_39 = lean_ctor_get_uint8(x_38, 1);
if (x_39 == 0)
{
return x_38;
}
else
{
x_2 = x_37;
x_3 = x_38;
goto _start;
}
}
case 8:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_ctor_get(x_2, 2);
x_43 = lean_ctor_get(x_2, 3);
x_44 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_41, x_3);
x_45 = lean_ctor_get_uint8(x_44, 1);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Compiler_atMostOnce_visit___main(x_1, x_42, x_44);
x_47 = lean_ctor_get_uint8(x_46, 1);
if (x_47 == 0)
{
return x_46;
}
else
{
x_2 = x_43;
x_3 = x_46;
goto _start;
}
}
}
case 10:
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_2, 1);
x_2 = x_49;
goto _start;
}
case 11:
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_2, 2);
x_2 = x_51;
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
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 0;
x_2 = 1;
x_3 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_2);
return x_3;
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
x_5 = lean_ctor_get_uint8(x_4, 1);
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
case 5:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_List_map___main___at___private_Init_Lean_Compiler_Util_1__getDeclNamesForCodeGen___spec__1(x_7);
return x_8;
}
default: 
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
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
