// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.IsRelevant
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Arith.Util import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
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
lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10;
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12;
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11;
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6;
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9;
uint8_t l_Lean_Meta_Grind_Arith_isIntType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; uint8_t x_50; 
x_50 = l_Lean_Meta_Grind_Arith_isNatType(x_1);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = l_Lean_Meta_Grind_Arith_isIntType(x_1);
x_12 = x_51;
goto block_49;
}
else
{
x_12 = x_50;
goto block_49;
}
block_49:
{
uint8_t x_13; 
x_13 = 1;
if (x_12 == 0)
{
lean_object* x_14; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_free_object(x_14);
x_17 = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_box(x_12);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; 
lean_dec_ref(x_19);
x_21 = lean_box(x_13);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(x_12);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_22);
x_25 = lean_box(x_13);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_30 = lean_box(x_13);
lean_ctor_set(x_14, 0, x_30);
return x_14;
}
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(x_12);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 1, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_33);
x_37 = lean_box(x_13);
if (lean_is_scalar(x_34)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_34;
}
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_31);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_42 = lean_box(x_13);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_14, 0);
lean_inc(x_45);
lean_dec(x_14);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_47 = lean_box(x_13);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_isSupportedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5;
x_2 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8;
x_2 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11;
x_2 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1;
x_22 = l_Lean_Expr_isConstOf(x_20, x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec_ref(x_19);
x_23 = l_Lean_Expr_isApp(x_20);
if (x_23 == 0)
{
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_28 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3;
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec_ref(x_26);
x_30 = l_Lean_Expr_isApp(x_27);
if (x_30 == 0)
{
lean_dec_ref(x_27);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_31);
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_33 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6;
x_34 = l_Lean_Expr_isConstOf(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9;
x_36 = l_Lean_Expr_isConstOf(x_32, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12;
x_38 = l_Lean_Expr_isConstOf(x_32, x_37);
lean_dec_ref(x_32);
if (x_38 == 0)
{
lean_dec_ref(x_31);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_39; 
x_39 = l_Lean_Meta_Grind_Arith_isSupportedType(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec_ref(x_32);
x_40 = l_Lean_Meta_Grind_Arith_isSupportedType(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec_ref(x_32);
x_41 = l_Lean_Meta_Grind_Arith_isSupportedType(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_41;
}
}
}
else
{
lean_object* x_42; 
lean_dec_ref(x_27);
x_42 = l_Lean_Meta_Grind_Arith_isSupportedType(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_42;
}
}
}
}
else
{
lean_dec_ref(x_20);
x_1 = x_19;
goto _start;
}
}
block_16:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_isRelevantPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_IsRelevant(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11);
l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12 = _init_l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
