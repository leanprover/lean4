// Lean compiler output
// Module: Lean.Meta.Coe
// Imports: Init Lean.Meta.WHNF Lean.Meta.Transform
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
static lean_object* l_Lean_Meta_isCoeDecl___closed__9;
static lean_object* l_Lean_Meta_isCoeDecl___closed__1;
static lean_object* l_Lean_Meta_isCoeDecl___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_isCoeDecl___boxed(lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__2;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__8;
static lean_object* l_Lean_Meta_isCoeDecl___closed__25;
static lean_object* l_Lean_Meta_isCoeDecl___closed__5;
static lean_object* l_Lean_Meta_isCoeDecl___closed__14;
static lean_object* l_Lean_Meta_isCoeDecl___closed__28;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__29;
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__3;
static lean_object* l_Lean_Meta_isCoeDecl___closed__31;
static lean_object* l_Lean_Meta_isCoeDecl___closed__27;
static lean_object* l_Lean_Meta_isCoeDecl___closed__4;
static lean_object* l_Lean_Meta_isCoeDecl___closed__26;
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__34;
static lean_object* l_Lean_Meta_isCoeDecl___closed__15;
static lean_object* l_Lean_Meta_isCoeDecl___closed__30;
static lean_object* l_Lean_Meta_isCoeDecl___closed__18;
static lean_object* l_Lean_Meta_isCoeDecl___closed__13;
static lean_object* l_Lean_Meta_isCoeDecl___closed__23;
static lean_object* l_Lean_Meta_isCoeDecl___closed__24;
uint8_t l_Lean_Expr_isConst(lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__20;
static lean_object* l_Lean_Meta_isCoeDecl___closed__10;
static lean_object* l_Lean_Meta_isCoeDecl___closed__32;
static lean_object* l_Lean_Meta_isCoeDecl___closed__35;
static lean_object* l_Lean_Meta_isCoeDecl___closed__12;
static lean_object* l_Lean_Meta_isCoeDecl___closed__16;
static lean_object* l_Lean_Meta_isCoeDecl___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__36;
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_expandCoe___closed__2;
static lean_object* l_Lean_Meta_expandCoe___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_isCoeDecl(lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__21;
static lean_object* l_Lean_Meta_isCoeDecl___closed__19;
static lean_object* l_Lean_Meta_isCoeDecl___closed__11;
static lean_object* l_Lean_Meta_isCoeDecl___closed__33;
static lean_object* l_Lean_Meta_isCoeDecl___closed__22;
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__6;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Coe", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("coe", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__2;
x_2 = l_Lean_Meta_isCoeDecl___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeTC", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__6;
x_2 = l_Lean_Meta_isCoeDecl___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeHead", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__9;
x_2 = l_Lean_Meta_isCoeDecl___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeTail", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__12;
x_2 = l_Lean_Meta_isCoeDecl___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeHTCT", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__15;
x_2 = l_Lean_Meta_isCoeDecl___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeDep", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__18;
x_2 = l_Lean_Meta_isCoeDecl___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeT", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__20;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__21;
x_2 = l_Lean_Meta_isCoeDecl___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeFun", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__23;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__24;
x_2 = l_Lean_Meta_isCoeDecl___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeSort", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__26;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__27;
x_2 = l_Lean_Meta_isCoeDecl___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__29;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Internal", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__30;
x_2 = l_Lean_Meta_isCoeDecl___closed__31;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("liftCoeM", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__32;
x_2 = l_Lean_Meta_isCoeDecl___closed__33;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("coeM", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__32;
x_2 = l_Lean_Meta_isCoeDecl___closed__35;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isCoeDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_isCoeDecl___closed__4;
x_3 = lean_name_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_isCoeDecl___closed__7;
x_5 = lean_name_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Meta_isCoeDecl___closed__10;
x_7 = lean_name_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_isCoeDecl___closed__13;
x_9 = lean_name_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_isCoeDecl___closed__16;
x_11 = lean_name_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_isCoeDecl___closed__19;
x_13 = lean_name_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Meta_isCoeDecl___closed__22;
x_15 = lean_name_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Meta_isCoeDecl___closed__25;
x_17 = lean_name_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Meta_isCoeDecl___closed__28;
x_19 = lean_name_eq(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Meta_isCoeDecl___closed__34;
x_21 = lean_name_eq(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Meta_isCoeDecl___closed__36;
x_23 = lean_name_eq(x_1, x_22);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = 1;
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = 1;
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = 1;
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = 1;
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = 1;
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = 1;
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = 1;
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = 1;
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = 1;
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = 1;
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isCoeDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_isCoeDecl(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe_step(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Expr_getAppFn(x_1);
x_8 = l_Lean_Expr_isConst(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Expr_constName_x21(x_7);
lean_dec(x_7);
x_12 = l_Lean_Meta_isCoeDecl(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = l_Lean_Expr_headBeta(x_24);
x_1 = x_25;
x_6 = x_23;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_expandCoe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_expandCoe_step), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_expandCoe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_expandCoe___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = 3;
lean_ctor_set_uint8(x_8, 5, x_10);
x_11 = l_Lean_Meta_expandCoe___closed__1;
x_12 = l_Lean_Meta_expandCoe___closed__2;
x_13 = 0;
x_14 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_11, x_12, x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_23 = lean_ctor_get_uint8(x_8, 0);
x_24 = lean_ctor_get_uint8(x_8, 1);
x_25 = lean_ctor_get_uint8(x_8, 2);
x_26 = lean_ctor_get_uint8(x_8, 3);
x_27 = lean_ctor_get_uint8(x_8, 4);
x_28 = lean_ctor_get_uint8(x_8, 6);
x_29 = lean_ctor_get_uint8(x_8, 7);
x_30 = lean_ctor_get_uint8(x_8, 8);
x_31 = lean_ctor_get_uint8(x_8, 9);
x_32 = lean_ctor_get_uint8(x_8, 10);
x_33 = lean_ctor_get_uint8(x_8, 11);
x_34 = lean_ctor_get_uint8(x_8, 12);
x_35 = lean_ctor_get_uint8(x_8, 13);
lean_dec(x_8);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_37, 0, x_23);
lean_ctor_set_uint8(x_37, 1, x_24);
lean_ctor_set_uint8(x_37, 2, x_25);
lean_ctor_set_uint8(x_37, 3, x_26);
lean_ctor_set_uint8(x_37, 4, x_27);
lean_ctor_set_uint8(x_37, 5, x_36);
lean_ctor_set_uint8(x_37, 6, x_28);
lean_ctor_set_uint8(x_37, 7, x_29);
lean_ctor_set_uint8(x_37, 8, x_30);
lean_ctor_set_uint8(x_37, 9, x_31);
lean_ctor_set_uint8(x_37, 10, x_32);
lean_ctor_set_uint8(x_37, 11, x_33);
lean_ctor_set_uint8(x_37, 12, x_34);
lean_ctor_set_uint8(x_37, 13, x_35);
lean_ctor_set(x_2, 0, x_37);
x_38 = l_Lean_Meta_expandCoe___closed__1;
x_39 = l_Lean_Meta_expandCoe___closed__2;
x_40 = 0;
x_41 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_38, x_39, x_40, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_48 = x_41;
} else {
 lean_dec_ref(x_41);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_50 = lean_ctor_get(x_2, 0);
x_51 = lean_ctor_get(x_2, 1);
x_52 = lean_ctor_get(x_2, 2);
x_53 = lean_ctor_get(x_2, 3);
x_54 = lean_ctor_get(x_2, 4);
x_55 = lean_ctor_get(x_2, 5);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_2);
x_56 = lean_ctor_get_uint8(x_50, 0);
x_57 = lean_ctor_get_uint8(x_50, 1);
x_58 = lean_ctor_get_uint8(x_50, 2);
x_59 = lean_ctor_get_uint8(x_50, 3);
x_60 = lean_ctor_get_uint8(x_50, 4);
x_61 = lean_ctor_get_uint8(x_50, 6);
x_62 = lean_ctor_get_uint8(x_50, 7);
x_63 = lean_ctor_get_uint8(x_50, 8);
x_64 = lean_ctor_get_uint8(x_50, 9);
x_65 = lean_ctor_get_uint8(x_50, 10);
x_66 = lean_ctor_get_uint8(x_50, 11);
x_67 = lean_ctor_get_uint8(x_50, 12);
x_68 = lean_ctor_get_uint8(x_50, 13);
if (lean_is_exclusive(x_50)) {
 x_69 = x_50;
} else {
 lean_dec_ref(x_50);
 x_69 = lean_box(0);
}
x_70 = 3;
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 0, 14);
} else {
 x_71 = x_69;
}
lean_ctor_set_uint8(x_71, 0, x_56);
lean_ctor_set_uint8(x_71, 1, x_57);
lean_ctor_set_uint8(x_71, 2, x_58);
lean_ctor_set_uint8(x_71, 3, x_59);
lean_ctor_set_uint8(x_71, 4, x_60);
lean_ctor_set_uint8(x_71, 5, x_70);
lean_ctor_set_uint8(x_71, 6, x_61);
lean_ctor_set_uint8(x_71, 7, x_62);
lean_ctor_set_uint8(x_71, 8, x_63);
lean_ctor_set_uint8(x_71, 9, x_64);
lean_ctor_set_uint8(x_71, 10, x_65);
lean_ctor_set_uint8(x_71, 11, x_66);
lean_ctor_set_uint8(x_71, 12, x_67);
lean_ctor_set_uint8(x_71, 13, x_68);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_51);
lean_ctor_set(x_72, 2, x_52);
lean_ctor_set(x_72, 3, x_53);
lean_ctor_set(x_72, 4, x_54);
lean_ctor_set(x_72, 5, x_55);
x_73 = l_Lean_Meta_expandCoe___closed__1;
x_74 = l_Lean_Meta_expandCoe___closed__2;
x_75 = 0;
x_76 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_73, x_74, x_75, x_72, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_83 = x_76;
} else {
 lean_dec_ref(x_76);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_expandCoe___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Coe(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_isCoeDecl___closed__1 = _init_l_Lean_Meta_isCoeDecl___closed__1();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__1);
l_Lean_Meta_isCoeDecl___closed__2 = _init_l_Lean_Meta_isCoeDecl___closed__2();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__2);
l_Lean_Meta_isCoeDecl___closed__3 = _init_l_Lean_Meta_isCoeDecl___closed__3();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__3);
l_Lean_Meta_isCoeDecl___closed__4 = _init_l_Lean_Meta_isCoeDecl___closed__4();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__4);
l_Lean_Meta_isCoeDecl___closed__5 = _init_l_Lean_Meta_isCoeDecl___closed__5();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__5);
l_Lean_Meta_isCoeDecl___closed__6 = _init_l_Lean_Meta_isCoeDecl___closed__6();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__6);
l_Lean_Meta_isCoeDecl___closed__7 = _init_l_Lean_Meta_isCoeDecl___closed__7();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__7);
l_Lean_Meta_isCoeDecl___closed__8 = _init_l_Lean_Meta_isCoeDecl___closed__8();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__8);
l_Lean_Meta_isCoeDecl___closed__9 = _init_l_Lean_Meta_isCoeDecl___closed__9();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__9);
l_Lean_Meta_isCoeDecl___closed__10 = _init_l_Lean_Meta_isCoeDecl___closed__10();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__10);
l_Lean_Meta_isCoeDecl___closed__11 = _init_l_Lean_Meta_isCoeDecl___closed__11();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__11);
l_Lean_Meta_isCoeDecl___closed__12 = _init_l_Lean_Meta_isCoeDecl___closed__12();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__12);
l_Lean_Meta_isCoeDecl___closed__13 = _init_l_Lean_Meta_isCoeDecl___closed__13();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__13);
l_Lean_Meta_isCoeDecl___closed__14 = _init_l_Lean_Meta_isCoeDecl___closed__14();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__14);
l_Lean_Meta_isCoeDecl___closed__15 = _init_l_Lean_Meta_isCoeDecl___closed__15();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__15);
l_Lean_Meta_isCoeDecl___closed__16 = _init_l_Lean_Meta_isCoeDecl___closed__16();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__16);
l_Lean_Meta_isCoeDecl___closed__17 = _init_l_Lean_Meta_isCoeDecl___closed__17();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__17);
l_Lean_Meta_isCoeDecl___closed__18 = _init_l_Lean_Meta_isCoeDecl___closed__18();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__18);
l_Lean_Meta_isCoeDecl___closed__19 = _init_l_Lean_Meta_isCoeDecl___closed__19();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__19);
l_Lean_Meta_isCoeDecl___closed__20 = _init_l_Lean_Meta_isCoeDecl___closed__20();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__20);
l_Lean_Meta_isCoeDecl___closed__21 = _init_l_Lean_Meta_isCoeDecl___closed__21();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__21);
l_Lean_Meta_isCoeDecl___closed__22 = _init_l_Lean_Meta_isCoeDecl___closed__22();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__22);
l_Lean_Meta_isCoeDecl___closed__23 = _init_l_Lean_Meta_isCoeDecl___closed__23();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__23);
l_Lean_Meta_isCoeDecl___closed__24 = _init_l_Lean_Meta_isCoeDecl___closed__24();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__24);
l_Lean_Meta_isCoeDecl___closed__25 = _init_l_Lean_Meta_isCoeDecl___closed__25();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__25);
l_Lean_Meta_isCoeDecl___closed__26 = _init_l_Lean_Meta_isCoeDecl___closed__26();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__26);
l_Lean_Meta_isCoeDecl___closed__27 = _init_l_Lean_Meta_isCoeDecl___closed__27();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__27);
l_Lean_Meta_isCoeDecl___closed__28 = _init_l_Lean_Meta_isCoeDecl___closed__28();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__28);
l_Lean_Meta_isCoeDecl___closed__29 = _init_l_Lean_Meta_isCoeDecl___closed__29();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__29);
l_Lean_Meta_isCoeDecl___closed__30 = _init_l_Lean_Meta_isCoeDecl___closed__30();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__30);
l_Lean_Meta_isCoeDecl___closed__31 = _init_l_Lean_Meta_isCoeDecl___closed__31();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__31);
l_Lean_Meta_isCoeDecl___closed__32 = _init_l_Lean_Meta_isCoeDecl___closed__32();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__32);
l_Lean_Meta_isCoeDecl___closed__33 = _init_l_Lean_Meta_isCoeDecl___closed__33();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__33);
l_Lean_Meta_isCoeDecl___closed__34 = _init_l_Lean_Meta_isCoeDecl___closed__34();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__34);
l_Lean_Meta_isCoeDecl___closed__35 = _init_l_Lean_Meta_isCoeDecl___closed__35();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__35);
l_Lean_Meta_isCoeDecl___closed__36 = _init_l_Lean_Meta_isCoeDecl___closed__36();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__36);
l_Lean_Meta_expandCoe___closed__1 = _init_l_Lean_Meta_expandCoe___closed__1();
lean_mark_persistent(l_Lean_Meta_expandCoe___closed__1);
l_Lean_Meta_expandCoe___closed__2 = _init_l_Lean_Meta_expandCoe___closed__2();
lean_mark_persistent(l_Lean_Meta_expandCoe___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
