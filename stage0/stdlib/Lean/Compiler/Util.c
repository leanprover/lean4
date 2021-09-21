// Lean compiler output
// Module: Lean.Compiler.Util
// Imports: Init Lean.Environment
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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_objectType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_voidType;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_neutralExpr___closed__1;
static lean_object* l_Lean_Compiler_mkLcProof___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_objectType;
static lean_object* l_Lean_Compiler_objectType___closed__2;
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkLcProof___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_neutralExpr___closed__2;
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_decl_names_for_code_gen(lean_object*);
static lean_object* l_Lean_Compiler_mkLcProof___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_neutralExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_is_eager_lambda_lifting_name(lean_object*);
static lean_object* l_Lean_Compiler_voidType___closed__3;
static lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___closed__1;
static lean_object* l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_skip___boxed(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_neutralExpr___closed__3;
static lean_object* l_Lean_Compiler_voidType___closed__2;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Compiler_atMostOnce___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcProof(lean_object*);
LEAN_EXPORT lean_object* lean_mk_unsafe_rec_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visitFVar___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_atMostOnce_visitFVar___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_voidType___closed__1;
static lean_object* l_Lean_Compiler_atMostOnce_visitFVar___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_unreachableExpr;
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_seq(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_objectType___closed__1;
LEAN_EXPORT lean_object* lean_is_unsafe_rec_name(lean_object*);
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__4;
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visitFVar(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_unreachableExpr___closed__2;
static lean_object* l_Lean_Compiler_mkUnsafeRecName___closed__1;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Compiler_Util_0__Lean_Compiler_getDeclNamesForCodeGen___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_skip(lean_object*);
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__2;
LEAN_EXPORT lean_object* lean_mk_eager_lambda_lifting_name(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_at_most_once(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_instAndThenVisitor(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_unreachableExpr___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_unreachableExpr___closed__3;
static lean_object* _init_l_Lean_Compiler_neutralExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_neutral");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_neutralExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_neutralExpr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_neutralExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_neutralExpr___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_neutralExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_neutralExpr___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_unreachableExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_unreachable");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_unreachableExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_unreachableExpr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unreachableExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_unreachableExpr___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unreachableExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_unreachableExpr___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_objectType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_obj");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_objectType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_objectType___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_objectType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_objectType___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_objectType() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_objectType___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_voidType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_void");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_voidType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_voidType___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_voidType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_voidType___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_voidType() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_voidType___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkLcProof___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lcProof");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkLcProof___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkLcProof___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkLcProof___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkLcProof___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_mkLcProof___closed__3;
x_3 = l_Lean_mkApp(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_seq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_ctor_get_uint8(x_4, 1);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
lean_ctor_set_uint8(x_4, 1, x_7);
return x_4;
}
else
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get_uint8(x_4, 0);
lean_dec(x_4);
x_9 = 0;
x_10 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, 1, x_9);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = lean_apply_1(x_2, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_instAndThenVisitor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_ctor_get_uint8(x_4, 1);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
lean_ctor_set_uint8(x_4, 1, x_7);
return x_4;
}
else
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get_uint8(x_4, 0);
lean_dec(x_4);
x_9 = 0;
x_10 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, 1, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_apply_2(x_2, x_11, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_skip(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_skip___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_atMostOnce_skip(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_atMostOnce_visitFVar___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_atMostOnce_visitFVar___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 1;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visitFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t x_7; uint8_t x_8; 
x_7 = lean_name_eq(x_1, x_2);
x_8 = 1;
lean_ctor_set_uint8(x_3, 0, x_7);
lean_ctor_set_uint8(x_3, 1, x_8);
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
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_name_eq(x_1, x_2);
x_12 = 1;
x_13 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, 1, x_12);
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
lean_dec(x_3);
x_15 = lean_name_eq(x_1, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Compiler_atMostOnce_visitFVar___closed__1;
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Compiler_atMostOnce_visitFVar___closed__2;
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visitFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_atMostOnce_visitFVar(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_name_eq(x_7, x_1);
x_9 = 1;
lean_ctor_set_uint8(x_3, 0, x_8);
lean_ctor_set_uint8(x_3, 1, x_9);
return x_3;
}
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_3, 1);
lean_dec(x_3);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_11, 0, x_10);
lean_ctor_set_uint8(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_name_eq(x_12, x_1);
x_14 = 1;
x_15 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, 1, x_14);
return x_15;
}
}
}
else
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_3, 1);
if (x_16 == 0)
{
return x_3;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_3);
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_name_eq(x_17, x_1);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Compiler_atMostOnce_visitFVar___closed__1;
return x_19;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Compiler_atMostOnce_visitFVar___closed__2;
return x_20;
}
}
}
}
case 5:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = l_Lean_Compiler_atMostOnce_visit(x_1, x_22, x_3);
x_24 = lean_ctor_get_uint8(x_23, 1);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = 0;
lean_ctor_set_uint8(x_23, 1, x_26);
return x_23;
}
else
{
uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get_uint8(x_23, 0);
lean_dec(x_23);
x_28 = 0;
x_29 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, 1, x_28);
return x_29;
}
}
else
{
x_2 = x_21;
x_3 = x_23;
goto _start;
}
}
case 6:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ctor_get(x_2, 2);
x_33 = l_Lean_Compiler_atMostOnce_visit(x_1, x_31, x_3);
x_34 = lean_ctor_get_uint8(x_33, 1);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = 0;
lean_ctor_set_uint8(x_33, 1, x_36);
return x_33;
}
else
{
uint8_t x_37; uint8_t x_38; lean_object* x_39; 
x_37 = lean_ctor_get_uint8(x_33, 0);
lean_dec(x_33);
x_38 = 0;
x_39 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, 1, x_38);
return x_39;
}
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
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_ctor_get(x_2, 2);
x_43 = l_Lean_Compiler_atMostOnce_visit(x_1, x_41, x_3);
x_44 = lean_ctor_get_uint8(x_43, 1);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = 0;
lean_ctor_set_uint8(x_43, 1, x_46);
return x_43;
}
else
{
uint8_t x_47; uint8_t x_48; lean_object* x_49; 
x_47 = lean_ctor_get_uint8(x_43, 0);
lean_dec(x_43);
x_48 = 0;
x_49 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, 1, x_48);
return x_49;
}
}
else
{
x_2 = x_42;
x_3 = x_43;
goto _start;
}
}
case 8:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_2, 1);
x_52 = lean_ctor_get(x_2, 2);
x_53 = lean_ctor_get(x_2, 3);
x_54 = l_Lean_Compiler_atMostOnce_visit(x_1, x_51, x_3);
x_55 = lean_ctor_get_uint8(x_54, 1);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = 0;
lean_ctor_set_uint8(x_54, 1, x_57);
return x_54;
}
else
{
uint8_t x_58; uint8_t x_59; lean_object* x_60; 
x_58 = lean_ctor_get_uint8(x_54, 0);
lean_dec(x_54);
x_59 = 0;
x_60 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = l_Lean_Compiler_atMostOnce_visit(x_1, x_52, x_54);
x_62 = lean_ctor_get_uint8(x_61, 1);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = 0;
lean_ctor_set_uint8(x_61, 1, x_64);
return x_61;
}
else
{
uint8_t x_65; uint8_t x_66; lean_object* x_67; 
x_65 = lean_ctor_get_uint8(x_61, 0);
lean_dec(x_61);
x_66 = 0;
x_67 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, 1, x_66);
return x_67;
}
}
else
{
x_2 = x_53;
x_3 = x_61;
goto _start;
}
}
}
case 10:
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_2, 1);
x_2 = x_69;
goto _start;
}
case 11:
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_2, 2);
x_2 = x_71;
goto _start;
}
default: 
{
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_atMostOnce_visit(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_atMostOnce___closed__1() {
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
LEAN_EXPORT uint8_t lean_at_most_once(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Compiler_atMostOnce___closed__1;
x_4 = l_Lean_Compiler_atMostOnce_visit(x_2, x_1, x_3);
lean_dec(x_1);
lean_dec(x_2);
x_5 = lean_ctor_get_uint8(x_4, 1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_at_most_once(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_elambda_");
return x_1;
}
}
LEAN_EXPORT lean_object* lean_mk_eager_lambda_lifting_name(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_elambda");
return x_1;
}
}
LEAN_EXPORT uint8_t lean_is_eager_lambda_lifting_name(lean_object* x_1) {
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
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Compiler_isEagerLambdaLiftingName___closed__1;
x_6 = l_String_isPrefixOf(x_5, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
x_1 = x_3;
goto _start;
}
else
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 1;
return x_8;
}
}
default: 
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_1 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_is_eager_lambda_lifting_name(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Compiler_Util_0__Lean_Compiler_getDeclNamesForCodeGen___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_9);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lean_get_decl_names_for_code_gen(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = lean_box(0);
return x_2;
}
case 4:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
case 5:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = l_List_mapTRAux___at___private_Lean_Compiler_Util_0__Lean_Compiler_getDeclNamesForCodeGen___spec__1(x_4, x_5);
return x_6;
}
case 6:
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
default: 
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknow declaration '");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declaration is not a definition '");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = 1;
x_5 = l_Lean_Name_toString(x_2, x_4);
x_6 = l_Lean_Compiler_checkIsDefinition___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_Compiler_checkIsDefinition___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
switch (lean_obj_tag(x_11)) {
case 1:
{
lean_object* x_12; 
lean_dec(x_11);
lean_dec(x_2);
x_12 = l_Lean_Compiler_checkIsDefinition___closed__4;
return x_12;
}
case 3:
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_2);
x_13 = l_Lean_Compiler_checkIsDefinition___closed__4;
return x_13;
}
default: 
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
x_14 = 1;
x_15 = l_Lean_Name_toString(x_2, x_14);
x_16 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_Compiler_checkIsDefinition___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_mkUnsafeRecName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_unsafe_rec");
return x_1;
}
}
LEAN_EXPORT lean_object* lean_mk_unsafe_rec_name(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_mkUnsafeRecName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_is_unsafe_rec_name(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Compiler_mkUnsafeRecName___closed__1;
x_5 = lean_string_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Util(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
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
l_Lean_Compiler_atMostOnce_visitFVar___closed__1 = _init_l_Lean_Compiler_atMostOnce_visitFVar___closed__1();
lean_mark_persistent(l_Lean_Compiler_atMostOnce_visitFVar___closed__1);
l_Lean_Compiler_atMostOnce_visitFVar___closed__2 = _init_l_Lean_Compiler_atMostOnce_visitFVar___closed__2();
lean_mark_persistent(l_Lean_Compiler_atMostOnce_visitFVar___closed__2);
l_Lean_Compiler_atMostOnce___closed__1 = _init_l_Lean_Compiler_atMostOnce___closed__1();
lean_mark_persistent(l_Lean_Compiler_atMostOnce___closed__1);
l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1 = _init_l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1);
l_Lean_Compiler_isEagerLambdaLiftingName___closed__1 = _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__1();
lean_mark_persistent(l_Lean_Compiler_isEagerLambdaLiftingName___closed__1);
l_Lean_Compiler_checkIsDefinition___closed__1 = _init_l_Lean_Compiler_checkIsDefinition___closed__1();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__1);
l_Lean_Compiler_checkIsDefinition___closed__2 = _init_l_Lean_Compiler_checkIsDefinition___closed__2();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__2);
l_Lean_Compiler_checkIsDefinition___closed__3 = _init_l_Lean_Compiler_checkIsDefinition___closed__3();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__3);
l_Lean_Compiler_checkIsDefinition___closed__4 = _init_l_Lean_Compiler_checkIsDefinition___closed__4();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__4);
l_Lean_Compiler_mkUnsafeRecName___closed__1 = _init_l_Lean_Compiler_mkUnsafeRecName___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkUnsafeRecName___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
