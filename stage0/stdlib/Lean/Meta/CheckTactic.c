// Lean compiler output
// Module: Lean.Meta.CheckTactic
// Imports: Lean.Meta.Basic
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
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__5;
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4;
static lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
static lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__7;
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1;
static lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1;
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CheckTactic", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CheckGoalType", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1;
x_2 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2;
x_3 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3;
x_4 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__5;
x_14 = l_Lean_Expr_const___override(x_13, x_12);
x_15 = l_Lean_mkAppB(x_14, x_2, x_1);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__5;
x_21 = l_Lean_Expr_const___override(x_20, x_19);
x_22 = l_Lean_mkAppB(x_21, x_2, x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_CheckTactic_mkCheckGoalType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 5);
x_10 = l_Lean_replaceRef(x_1, x_9);
lean_dec(x_9);
lean_ctor_set(x_5, 5, x_10);
x_11 = l_Lean_throwError___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
x_21 = lean_ctor_get(x_5, 9);
x_22 = lean_ctor_get(x_5, 10);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*12);
x_24 = lean_ctor_get(x_5, 11);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*12 + 1);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_26 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_27 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_13);
lean_ctor_set(x_27, 2, x_14);
lean_ctor_set(x_27, 3, x_15);
lean_ctor_set(x_27, 4, x_16);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set(x_27, 6, x_18);
lean_ctor_set(x_27, 7, x_19);
lean_ctor_set(x_27, 8, x_20);
lean_ctor_set(x_27, 9, x_21);
lean_ctor_set(x_27, 10, x_22);
lean_ctor_set(x_27, 11, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*12, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*12 + 1, x_25);
x_28 = l_Lean_throwError___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__2(x_2, x_3, x_4, x_27, x_6, x_7);
lean_dec(x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Goal", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nis expected to match ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_12 = l_Lean_Expr_sort___override(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = 0;
x_15 = lean_box(0);
lean_inc(x_3);
x_16 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_13, x_14, x_15, x_3, x_4, x_5, x_6, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
lean_inc(x_3);
x_21 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_20, x_14, x_15, x_3, x_4, x_5, x_6, x_19);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_box(0);
lean_inc(x_10);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_25);
lean_ctor_set(x_21, 0, x_10);
x_26 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__5;
x_27 = l_Lean_Expr_const___override(x_26, x_21);
x_28 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1;
lean_inc(x_18);
x_29 = lean_array_push(x_28, x_18);
lean_inc(x_23);
x_30 = lean_array_push(x_29, x_23);
x_31 = l_Lean_mkAppN(x_27, x_30);
lean_dec(x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_31);
lean_inc(x_2);
x_32 = l_Lean_Meta_isExprDefEq(x_2, x_31, x_3, x_4, x_5, x_6, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = l_Lean_indentExpr(x_2);
x_37 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_36);
lean_ctor_set(x_16, 0, x_37);
x_38 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_38);
lean_ctor_set(x_8, 0, x_16);
x_39 = l_Lean_indentExpr(x_31);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_8);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__7;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwErrorAt___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__1(x_1, x_42, x_3, x_4, x_5, x_6, x_35);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_31);
lean_free_object(x_16);
lean_free_object(x_8);
lean_dec(x_2);
x_48 = lean_ctor_get(x_32, 1);
lean_inc(x_48);
lean_dec(x_32);
x_49 = lean_box(0);
x_50 = l_Lean_Meta_CheckTactic_matchCheckGoalType___lambda__1(x_18, x_10, x_23, x_49, x_3, x_4, x_5, x_6, x_48);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_31);
lean_dec(x_23);
lean_free_object(x_16);
lean_dec(x_18);
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_32);
if (x_51 == 0)
{
return x_32;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_32, 0);
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_32);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_55 = lean_ctor_get(x_21, 0);
x_56 = lean_ctor_get(x_21, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_21);
x_57 = lean_box(0);
lean_inc(x_10);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_10);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__5;
x_60 = l_Lean_Expr_const___override(x_59, x_58);
x_61 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1;
lean_inc(x_18);
x_62 = lean_array_push(x_61, x_18);
lean_inc(x_55);
x_63 = lean_array_push(x_62, x_55);
x_64 = l_Lean_mkAppN(x_60, x_63);
lean_dec(x_63);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_64);
lean_inc(x_2);
x_65 = l_Lean_Meta_isExprDefEq(x_2, x_64, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_55);
lean_dec(x_18);
lean_dec(x_10);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = l_Lean_indentExpr(x_2);
x_70 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_69);
lean_ctor_set(x_16, 0, x_70);
x_71 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_71);
lean_ctor_set(x_8, 0, x_16);
x_72 = l_Lean_indentExpr(x_64);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_8);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__7;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_throwErrorAt___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__1(x_1, x_75, x_3, x_4, x_5, x_6, x_68);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_64);
lean_free_object(x_16);
lean_free_object(x_8);
lean_dec(x_2);
x_81 = lean_ctor_get(x_65, 1);
lean_inc(x_81);
lean_dec(x_65);
x_82 = lean_box(0);
x_83 = l_Lean_Meta_CheckTactic_matchCheckGoalType___lambda__1(x_18, x_10, x_55, x_82, x_3, x_4, x_5, x_6, x_81);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_64);
lean_dec(x_55);
lean_free_object(x_16);
lean_dec(x_18);
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = lean_ctor_get(x_65, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_65, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_86 = x_65;
} else {
 lean_dec_ref(x_65);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_88 = lean_ctor_get(x_16, 0);
x_89 = lean_ctor_get(x_16, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_16);
lean_inc(x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_88);
lean_inc(x_3);
x_91 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_90, x_14, x_15, x_3, x_4, x_5, x_6, x_89);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_95 = lean_box(0);
lean_inc(x_10);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_94;
 lean_ctor_set_tag(x_96, 1);
}
lean_ctor_set(x_96, 0, x_10);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__5;
x_98 = l_Lean_Expr_const___override(x_97, x_96);
x_99 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1;
lean_inc(x_88);
x_100 = lean_array_push(x_99, x_88);
lean_inc(x_92);
x_101 = lean_array_push(x_100, x_92);
x_102 = l_Lean_mkAppN(x_98, x_101);
lean_dec(x_101);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_102);
lean_inc(x_2);
x_103 = l_Lean_Meta_isExprDefEq(x_2, x_102, x_3, x_4, x_5, x_6, x_93);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_10);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = l_Lean_indentExpr(x_2);
x_108 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3;
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_110);
lean_ctor_set(x_8, 0, x_109);
x_111 = l_Lean_indentExpr(x_102);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_8);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__7;
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_throwErrorAt___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__1(x_1, x_114, x_3, x_4, x_5, x_6, x_106);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_102);
lean_free_object(x_8);
lean_dec(x_2);
x_120 = lean_ctor_get(x_103, 1);
lean_inc(x_120);
lean_dec(x_103);
x_121 = lean_box(0);
x_122 = l_Lean_Meta_CheckTactic_matchCheckGoalType___lambda__1(x_88, x_10, x_92, x_121, x_3, x_4, x_5, x_6, x_120);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_102);
lean_dec(x_92);
lean_dec(x_88);
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = lean_ctor_get(x_103, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_103, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_125 = x_103;
} else {
 lean_dec_ref(x_103);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_127 = lean_ctor_get(x_8, 0);
x_128 = lean_ctor_get(x_8, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_8);
lean_inc(x_127);
x_129 = l_Lean_Expr_sort___override(x_127);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = 0;
x_132 = lean_box(0);
lean_inc(x_3);
x_133 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_130, x_131, x_132, x_3, x_4, x_5, x_6, x_128);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
lean_inc(x_134);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_134);
lean_inc(x_3);
x_138 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_137, x_131, x_132, x_3, x_4, x_5, x_6, x_135);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = lean_box(0);
lean_inc(x_127);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_141;
 lean_ctor_set_tag(x_143, 1);
}
lean_ctor_set(x_143, 0, x_127);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__5;
x_145 = l_Lean_Expr_const___override(x_144, x_143);
x_146 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1;
lean_inc(x_134);
x_147 = lean_array_push(x_146, x_134);
lean_inc(x_139);
x_148 = lean_array_push(x_147, x_139);
x_149 = l_Lean_mkAppN(x_145, x_148);
lean_dec(x_148);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_149);
lean_inc(x_2);
x_150 = l_Lean_Meta_isExprDefEq(x_2, x_149, x_3, x_4, x_5, x_6, x_140);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_139);
lean_dec(x_134);
lean_dec(x_127);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = l_Lean_indentExpr(x_2);
x_155 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3;
if (lean_is_scalar(x_136)) {
 x_156 = lean_alloc_ctor(7, 2, 0);
} else {
 x_156 = x_136;
 lean_ctor_set_tag(x_156, 7);
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5;
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_indentExpr(x_149);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__7;
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_throwErrorAt___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__1(x_1, x_162, x_3, x_4, x_5, x_6, x_153);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_149);
lean_dec(x_136);
lean_dec(x_2);
x_168 = lean_ctor_get(x_150, 1);
lean_inc(x_168);
lean_dec(x_150);
x_169 = lean_box(0);
x_170 = l_Lean_Meta_CheckTactic_matchCheckGoalType___lambda__1(x_134, x_127, x_139, x_169, x_3, x_4, x_5, x_6, x_168);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_149);
lean_dec(x_139);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_171 = lean_ctor_get(x_150, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_150, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_173 = x_150;
} else {
 lean_dec_ref(x_150);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwErrorAt___at_Lean_Meta_CheckTactic_matchCheckGoalType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_CheckTactic_matchCheckGoalType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CheckTactic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1 = _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1();
lean_mark_persistent(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1);
l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2 = _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2();
lean_mark_persistent(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2);
l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3 = _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3();
lean_mark_persistent(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3);
l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4 = _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4();
lean_mark_persistent(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4);
l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__5 = _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__5();
lean_mark_persistent(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__5);
l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1 = _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1();
lean_mark_persistent(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1);
l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2 = _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2();
lean_mark_persistent(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2);
l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3 = _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3();
lean_mark_persistent(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3);
l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4 = _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4();
lean_mark_persistent(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4);
l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5 = _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5();
lean_mark_persistent(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5);
l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6 = _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6();
lean_mark_persistent(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6);
l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__7 = _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__7();
lean_mark_persistent(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
