// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Offset.Util
// Imports: Lean.Expr Lean.Message Lean.Meta.Tactic.Grind.Arith.Util
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
static lean_object* l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__3;
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_toMessageData(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrExpr;
static lean_object* l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__5;
uint8_t l_Lean_Meta_Grind_Arith_isInstLENat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_isNatOffset_x3f(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Offset_instInhabitedCnstr___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_instInhabitedCnstr___rarg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__1;
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_toMessageData___at_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrExpr___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_instInhabitedCnstr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_Cnstr_neg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Offset_Cnstr_neg___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_Cnstr_neg___rarg(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__6;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_isNatOffset_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_isNatAdd_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_Meta_Grind_Arith_isNatNum_x3f(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_free_object(x_4);
lean_dec(x_6);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_ctor_set(x_4, 1, x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = l_Lean_Meta_Grind_Arith_isNatNum_x3f(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_18);
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(1, 1, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_instInhabitedCnstr___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_instInhabitedCnstr___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_Offset_instInhabitedCnstr___rarg___closed__1;
lean_inc(x_1);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_instInhabitedCnstr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Offset_instInhabitedCnstr___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_Cnstr_neg___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_Cnstr_neg___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_int_neg(x_5);
lean_dec(x_5);
x_7 = l_Lean_Meta_Grind_Arith_Offset_Cnstr_neg___rarg___closed__1;
x_8 = lean_int_sub(x_6, x_7);
lean_dec(x_6);
lean_ctor_set(x_1, 2, x_8);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_12 = lean_int_neg(x_11);
lean_dec(x_11);
x_13 = l_Lean_Meta_Grind_Arith_Offset_Cnstr_neg___rarg___closed__1;
x_14 = lean_int_sub(x_12, x_13);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_Cnstr_neg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Offset_Cnstr_neg___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ≤ ", 5, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" + ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = l_Lean_Meta_Grind_Arith_Offset_instInhabitedCnstr___rarg___closed__1;
x_5 = lean_int_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_nat_abs(x_3);
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
x_11 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__2;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__4;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_apply_1(x_1, x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__6;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_6);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_MessageData_ofFormat(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_6);
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
lean_inc(x_1);
x_26 = lean_apply_1(x_1, x_25);
x_27 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__2;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__4;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec(x_2);
x_32 = lean_apply_1(x_1, x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_35 = lean_nat_abs(x_3);
lean_dec(x_3);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_sub(x_35, x_36);
lean_dec(x_35);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
lean_inc(x_1);
x_39 = lean_apply_1(x_1, x_38);
x_40 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__2;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__6;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_nat_add(x_37, x_36);
lean_dec(x_37);
x_45 = l___private_Init_Data_Repr_0__Nat_reprFast(x_44);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_MessageData_ofFormat(x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__4;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
lean_dec(x_2);
x_52 = lean_apply_1(x_1, x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_40);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_toMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_toMessageData___at_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrExpr___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_3 = l_Lean_Meta_Grind_Arith_Offset_instInhabitedCnstr___rarg___closed__1;
x_4 = lean_int_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_nat_abs(x_2);
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l_Lean_MessageData_ofExpr(x_8);
x_10 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__2;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__4;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_MessageData_ofExpr(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__6;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_MessageData_ofFormat(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = l_Lean_MessageData_ofExpr(x_24);
x_26 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__2;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__4;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_Lean_MessageData_ofExpr(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_34 = lean_nat_abs(x_2);
lean_dec(x_2);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_sub(x_34, x_35);
lean_dec(x_34);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = l_Lean_MessageData_ofExpr(x_37);
x_39 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__2;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__6;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_nat_add(x_36, x_35);
lean_dec(x_36);
x_44 = l___private_Init_Data_Repr_0__Nat_reprFast(x_43);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_MessageData_ofFormat(x_45);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__4;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
lean_dec(x_1);
x_51 = l_Lean_MessageData_ofExpr(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_39);
return x_53;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Offset_toMessageData___at_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrExpr___spec__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrExpr___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Meta_Grind_Arith_Offset_isNatOffset_x3f(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_Grind_Arith_Offset_isNatOffset_x3f(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = l_Lean_Meta_Grind_Arith_isNatNum_x3f(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_inc(x_3);
x_7 = l_Lean_Meta_Grind_Arith_isNatNum_x3f(x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_8 = l_Lean_Meta_Grind_Arith_Offset_instInhabitedCnstr___rarg___closed__1;
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_nat_to_int(x_20);
x_22 = lean_int_neg(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_6, 0, x_23);
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_6, 0);
lean_inc(x_24);
lean_dec(x_6);
x_25 = lean_nat_to_int(x_24);
x_26 = lean_int_neg(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_nat_to_int(x_32);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_5, 0, x_34);
return x_5;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
lean_dec(x_5);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_nat_to_int(x_37);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_4);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_4, 0);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_nat_to_int(x_44);
x_46 = lean_int_neg(x_45);
lean_dec(x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_3);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_4, 0, x_47);
return x_4;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_4, 0);
lean_inc(x_48);
lean_dec(x_4);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_nat_to_int(x_50);
x_52 = lean_int_neg(x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Expr_cleanupAnnotations(x_1);
x_4 = l_Lean_Expr_isApp(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lean_Expr_appArg(x_3, lean_box(0));
x_7 = l_Lean_Expr_appFnCleanup(x_3, lean_box(0));
x_8 = l_Lean_Expr_isApp(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Expr_appArg(x_7, lean_box(0));
x_11 = l_Lean_Expr_appFnCleanup(x_7, lean_box(0));
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_2);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Expr_appArg(x_11, lean_box(0));
x_15 = l_Lean_Expr_appFnCleanup(x_11, lean_box(0));
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_2);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Expr_appFnCleanup(x_15, lean_box(0));
x_19 = l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__3;
x_20 = l_Lean_Expr_isConstOf(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_2);
x_21 = lean_box(0);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = l_Lean_Meta_Grind_Arith_isInstLENat(x_14);
lean_dec(x_14);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_2);
x_23 = lean_box(0);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f_go(x_2, x_10, x_6);
return x_24;
}
}
}
}
}
}
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Offset_Util(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Offset_instInhabitedCnstr___rarg___closed__1 = _init_l_Lean_Meta_Grind_Arith_Offset_instInhabitedCnstr___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_instInhabitedCnstr___rarg___closed__1);
l_Lean_Meta_Grind_Arith_Offset_Cnstr_neg___rarg___closed__1 = _init_l_Lean_Meta_Grind_Arith_Offset_Cnstr_neg___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_Cnstr_neg___rarg___closed__1);
l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__1 = _init_l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__1);
l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__2 = _init_l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__2);
l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__3 = _init_l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__3);
l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__4 = _init_l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__4);
l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__5 = _init_l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__5);
l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__6 = _init_l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_toMessageData___rarg___closed__6);
l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrExpr___closed__1 = _init_l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrExpr___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrExpr___closed__1);
l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrExpr = _init_l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrExpr();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrExpr);
l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__1 = _init_l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__1);
l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__2 = _init_l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__2);
l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__3 = _init_l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_isNatOffsetCnstr_x3f___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
