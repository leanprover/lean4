// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.Util
// Imports: Lean.Meta.Tactic.Grind.Order.OrderM Lean.Meta.Tactic.Grind.Arith.Util
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
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5;
lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_Grind_Order_instAddWeight___closed__0;
static lean_object* l_Lean_Meta_Grind_Order_instOrdWeight___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_compare(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instLEWeight;
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLTWeight___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instAddWeight;
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instLTWeight;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isZero___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_compare___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instOrdWeight;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object*);
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLEWeight___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isNeg___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLTWeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isZero(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6;
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1;
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3;
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__7;
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" + ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("≤", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = l_Lean_Meta_Grind_Order_getExpr(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = l_Lean_Meta_Grind_Order_getExpr(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_31; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
if (x_12 == 0)
{
lean_object* x_64; 
x_64 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6;
x_31 = x_64;
goto block_63;
}
else
{
lean_object* x_65; 
x_65 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__7;
x_31 = x_65;
goto block_63;
}
block_30:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofFormat(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
if (lean_is_scalar(x_23)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_23;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
block_63:
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_33 = lean_int_dec_eq(x_15, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_19);
x_34 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_17);
x_35 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_stringToMessageData(x_31);
lean_dec_ref(x_31);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
x_40 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_21);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_int_dec_lt(x_15, x_32);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_nat_abs(x_15);
x_46 = l_Nat_reprFast(x_45);
x_24 = x_43;
x_25 = x_46;
goto block_30;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_nat_abs(x_15);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_47, x_48);
lean_dec(x_47);
x_50 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_51 = lean_nat_add(x_49, x_48);
lean_dec(x_49);
x_52 = l_Nat_reprFast(x_51);
x_53 = lean_string_append(x_50, x_52);
lean_dec_ref(x_52);
x_24 = x_43;
x_25 = x_53;
goto block_30;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_23);
x_54 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_17);
x_55 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_stringToMessageData(x_31);
lean_dec_ref(x_31);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
x_60 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_21);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
if (lean_is_scalar(x_19)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_19;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_22);
return x_62;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_19);
lean_dec(x_17);
x_66 = !lean_is_exclusive(x_20);
if (x_66 == 0)
{
return x_20;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_20, 0);
x_68 = lean_ctor_get(x_20, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_20);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_16);
if (x_70 == 0)
{
return x_16;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_16, 0);
x_72 = lean_ctor_get(x_16, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_16);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Order_Cnstr_pp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_compare(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_11 = lean_int_dec_lt(x_3, x_5);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_int_dec_lt(x_5, x_3);
if (x_12 == 0)
{
if (x_4 == 0)
{
if (x_6 == 0)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
goto block_10;
}
}
else
{
if (x_6 == 0)
{
goto block_10;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = 2;
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
block_10:
{
if (x_4 == 0)
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
else
{
if (x_6 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 2;
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_compare___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_Order_Weight_compare(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instOrdWeight___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Order_Weight_compare___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instOrdWeight() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Order_instOrdWeight___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instLEWeight() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instLTWeight() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_3 = l_Lean_Meta_Grind_Order_Weight_compare(x_1, x_2);
x_4 = 2;
x_5 = l_instDecidableEqOrdering(x_3, x_4);
x_6 = l_instDecidableNot___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLEWeight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_Order_instDecidableLEWeight(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLTWeight(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Grind_Order_Weight_compare(x_1, x_2);
x_4 = 0;
x_5 = l_instDecidableEqOrdering(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLTWeight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_Order_instDecidableLTWeight(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_int_add(x_4, x_6);
lean_dec(x_6);
if (x_5 == 0)
{
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_ctor_set(x_2, 0, x_7);
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_5);
return x_2;
}
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_10);
lean_dec(x_2);
x_12 = lean_int_add(x_8, x_10);
lean_dec(x_10);
if (x_9 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_11);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_9);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Order_Weight_add(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instAddWeight___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Order_Weight_add___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instAddWeight() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Order_instAddWeight___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_5 = lean_int_dec_lt(x_2, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_int_dec_eq(x_2, x_4);
if (x_6 == 0)
{
return x_6;
}
else
{
return x_3;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isNeg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Order_Weight_isNeg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isZero(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_5 = lean_int_dec_eq(x_2, x_4);
if (x_5 == 0)
{
return x_5;
}
else
{
if (x_3 == 0)
{
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isZero___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Order_Weight_isZero(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-ε", 3, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_9 = lean_int_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_nat_abs(x_7);
x_11 = l_Nat_reprFast(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_nat_abs(x_7);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_16 = lean_nat_add(x_14, x_13);
lean_dec(x_14);
x_17 = l_Nat_reprFast(x_16);
x_18 = lean_string_append(x_15, x_17);
lean_dec_ref(x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_21 = lean_int_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_nat_abs(x_19);
x_23 = l_Nat_reprFast(x_22);
x_2 = x_23;
goto block_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_nat_abs(x_19);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_27 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_28 = lean_nat_add(x_26, x_25);
lean_dec(x_26);
x_29 = l_Nat_reprFast(x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec_ref(x_29);
x_2 = x_30;
goto block_5;
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
x_4 = lean_string_append(x_2, x_3);
return x_4;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instToStringWeight() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqTrue: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqFalse: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq: ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = l_Lean_Meta_Grind_Order_getExpr(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Lean_Meta_Grind_Order_getExpr(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
lean_dec(x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_31; lean_object* x_32; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_79; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_36 = lean_ctor_get(x_15, 0);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
lean_dec_ref(x_15);
x_38 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1;
x_39 = l_Lean_MessageData_ofExpr(x_12);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_MessageData_ofExpr(x_18);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
x_46 = l_Lean_MessageData_ofExpr(x_21);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
if (x_37 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_84 = lean_int_dec_lt(x_36, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_nat_abs(x_36);
lean_dec(x_36);
x_86 = l_Nat_reprFast(x_85);
x_49 = x_86;
goto block_78;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_nat_abs(x_36);
lean_dec(x_36);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_sub(x_87, x_88);
lean_dec(x_87);
x_90 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_91 = lean_nat_add(x_89, x_88);
lean_dec(x_89);
x_92 = l_Nat_reprFast(x_91);
x_93 = lean_string_append(x_90, x_92);
lean_dec_ref(x_92);
x_49 = x_93;
goto block_78;
}
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_95 = lean_int_dec_lt(x_36, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_nat_abs(x_36);
lean_dec(x_36);
x_97 = l_Nat_reprFast(x_96);
x_79 = x_97;
goto block_82;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_nat_abs(x_36);
lean_dec(x_36);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_sub(x_98, x_99);
lean_dec(x_98);
x_101 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_102 = lean_nat_add(x_100, x_99);
lean_dec(x_100);
x_103 = l_Nat_reprFast(x_102);
x_104 = lean_string_append(x_101, x_103);
lean_dec_ref(x_103);
x_79 = x_104;
goto block_82;
}
}
block_30:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofFormat(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
if (lean_is_scalar(x_23)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_23;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
x_34 = lean_string_append(x_32, x_33);
x_24 = x_31;
x_25 = x_34;
goto block_30;
}
block_78:
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_16, 0);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
lean_dec_ref(x_16);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_49);
x_53 = l_Lean_MessageData_ofFormat(x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_41);
if (x_51 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_57 = lean_int_dec_lt(x_50, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_nat_abs(x_50);
lean_dec(x_50);
x_59 = l_Nat_reprFast(x_58);
x_24 = x_55;
x_25 = x_59;
goto block_30;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_nat_abs(x_50);
lean_dec(x_50);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_sub(x_60, x_61);
lean_dec(x_60);
x_63 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_64 = lean_nat_add(x_62, x_61);
lean_dec(x_62);
x_65 = l_Nat_reprFast(x_64);
x_66 = lean_string_append(x_63, x_65);
lean_dec_ref(x_65);
x_24 = x_55;
x_25 = x_66;
goto block_30;
}
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_68 = lean_int_dec_lt(x_50, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_nat_abs(x_50);
lean_dec(x_50);
x_70 = l_Nat_reprFast(x_69);
x_31 = x_55;
x_32 = x_70;
goto block_35;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_nat_abs(x_50);
lean_dec(x_50);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_sub(x_71, x_72);
lean_dec(x_71);
x_74 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_75 = lean_nat_add(x_73, x_72);
lean_dec(x_73);
x_76 = l_Nat_reprFast(x_75);
x_77 = lean_string_append(x_74, x_76);
lean_dec_ref(x_76);
x_31 = x_55;
x_32 = x_77;
goto block_35;
}
}
}
block_82:
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
x_81 = lean_string_append(x_79, x_80);
x_49 = x_81;
goto block_78;
}
}
else
{
uint8_t x_105; 
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_12);
x_105 = !lean_is_exclusive(x_20);
if (x_105 == 0)
{
return x_20;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_20, 0);
x_107 = lean_ctor_get(x_20, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_20);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_12);
x_109 = !lean_is_exclusive(x_17);
if (x_109 == 0)
{
return x_17;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_17, 0);
x_111 = lean_ctor_get(x_17, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_17);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
case 1:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_1, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_1, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_117);
lean_dec_ref(x_1);
x_118 = l_Lean_Meta_Grind_Order_getExpr(x_114, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_114);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec_ref(x_118);
x_121 = l_Lean_Meta_Grind_Order_getExpr(x_115, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_120);
lean_dec(x_115);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_132; lean_object* x_133; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_180; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
x_137 = lean_ctor_get(x_116, 0);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_116, sizeof(void*)*1);
lean_dec_ref(x_116);
x_139 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5;
x_140 = l_Lean_MessageData_ofExpr(x_113);
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_MessageData_ofExpr(x_119);
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_142);
x_147 = l_Lean_MessageData_ofExpr(x_122);
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_142);
if (x_138 == 0)
{
lean_object* x_184; uint8_t x_185; 
x_184 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_185 = lean_int_dec_lt(x_137, x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_nat_abs(x_137);
lean_dec(x_137);
x_187 = l_Nat_reprFast(x_186);
x_150 = x_187;
goto block_179;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_188 = lean_nat_abs(x_137);
lean_dec(x_137);
x_189 = lean_unsigned_to_nat(1u);
x_190 = lean_nat_sub(x_188, x_189);
lean_dec(x_188);
x_191 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_192 = lean_nat_add(x_190, x_189);
lean_dec(x_190);
x_193 = l_Nat_reprFast(x_192);
x_194 = lean_string_append(x_191, x_193);
lean_dec_ref(x_193);
x_150 = x_194;
goto block_179;
}
}
else
{
lean_object* x_195; uint8_t x_196; 
x_195 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_196 = lean_int_dec_lt(x_137, x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_nat_abs(x_137);
lean_dec(x_137);
x_198 = l_Nat_reprFast(x_197);
x_180 = x_198;
goto block_183;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_199 = lean_nat_abs(x_137);
lean_dec(x_137);
x_200 = lean_unsigned_to_nat(1u);
x_201 = lean_nat_sub(x_199, x_200);
lean_dec(x_199);
x_202 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_203 = lean_nat_add(x_201, x_200);
lean_dec(x_201);
x_204 = l_Nat_reprFast(x_203);
x_205 = lean_string_append(x_202, x_204);
lean_dec_ref(x_204);
x_180 = x_205;
goto block_183;
}
}
block_131:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = l_Lean_MessageData_ofFormat(x_127);
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_128);
if (lean_is_scalar(x_124)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_124;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_123);
return x_130;
}
block_136:
{
lean_object* x_134; lean_object* x_135; 
x_134 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
x_135 = lean_string_append(x_133, x_134);
x_125 = x_132;
x_126 = x_135;
goto block_131;
}
block_179:
{
lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_151 = lean_ctor_get(x_117, 0);
lean_inc(x_151);
x_152 = lean_ctor_get_uint8(x_117, sizeof(void*)*1);
lean_dec_ref(x_117);
x_153 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_153, 0, x_150);
x_154 = l_Lean_MessageData_ofFormat(x_153);
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_149);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_142);
if (x_152 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_158 = lean_int_dec_lt(x_151, x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_nat_abs(x_151);
lean_dec(x_151);
x_160 = l_Nat_reprFast(x_159);
x_125 = x_156;
x_126 = x_160;
goto block_131;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_161 = lean_nat_abs(x_151);
lean_dec(x_151);
x_162 = lean_unsigned_to_nat(1u);
x_163 = lean_nat_sub(x_161, x_162);
lean_dec(x_161);
x_164 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_165 = lean_nat_add(x_163, x_162);
lean_dec(x_163);
x_166 = l_Nat_reprFast(x_165);
x_167 = lean_string_append(x_164, x_166);
lean_dec_ref(x_166);
x_125 = x_156;
x_126 = x_167;
goto block_131;
}
}
else
{
lean_object* x_168; uint8_t x_169; 
x_168 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_169 = lean_int_dec_lt(x_151, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_nat_abs(x_151);
lean_dec(x_151);
x_171 = l_Nat_reprFast(x_170);
x_132 = x_156;
x_133 = x_171;
goto block_136;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = lean_nat_abs(x_151);
lean_dec(x_151);
x_173 = lean_unsigned_to_nat(1u);
x_174 = lean_nat_sub(x_172, x_173);
lean_dec(x_172);
x_175 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_176 = lean_nat_add(x_174, x_173);
lean_dec(x_174);
x_177 = l_Nat_reprFast(x_176);
x_178 = lean_string_append(x_175, x_177);
lean_dec_ref(x_177);
x_132 = x_156;
x_133 = x_178;
goto block_136;
}
}
}
block_183:
{
lean_object* x_181; lean_object* x_182; 
x_181 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
x_182 = lean_string_append(x_180, x_181);
x_150 = x_182;
goto block_179;
}
}
else
{
uint8_t x_206; 
lean_dec(x_119);
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec_ref(x_113);
x_206 = !lean_is_exclusive(x_121);
if (x_206 == 0)
{
return x_121;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_121, 0);
x_208 = lean_ctor_get(x_121, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_121);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_113);
x_210 = !lean_is_exclusive(x_118);
if (x_210 == 0)
{
return x_118;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_118, 0);
x_212 = lean_ctor_get(x_118, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_118);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
default: 
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_1);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_1, 0);
x_216 = lean_ctor_get(x_1, 1);
x_217 = l_Lean_Meta_Grind_Order_getExpr(x_215, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_215);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec_ref(x_217);
x_220 = l_Lean_Meta_Grind_Order_getExpr(x_216, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_219);
lean_dec(x_216);
if (lean_obj_tag(x_220) == 0)
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_222 = lean_ctor_get(x_220, 0);
x_223 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7;
x_224 = l_Lean_MessageData_ofExpr(x_218);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_224);
lean_ctor_set(x_1, 0, x_223);
x_225 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_1);
lean_ctor_set(x_226, 1, x_225);
x_227 = l_Lean_MessageData_ofExpr(x_222);
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
lean_ctor_set(x_220, 0, x_228);
return x_220;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_229 = lean_ctor_get(x_220, 0);
x_230 = lean_ctor_get(x_220, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_220);
x_231 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7;
x_232 = l_Lean_MessageData_ofExpr(x_218);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_232);
lean_ctor_set(x_1, 0, x_231);
x_233 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_1);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Lean_MessageData_ofExpr(x_229);
x_236 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_230);
return x_237;
}
}
else
{
uint8_t x_238; 
lean_dec(x_218);
lean_free_object(x_1);
x_238 = !lean_is_exclusive(x_220);
if (x_238 == 0)
{
return x_220;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_220, 0);
x_240 = lean_ctor_get(x_220, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_220);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
else
{
uint8_t x_242; 
lean_free_object(x_1);
lean_dec(x_216);
x_242 = !lean_is_exclusive(x_217);
if (x_242 == 0)
{
return x_217;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_217, 0);
x_244 = lean_ctor_get(x_217, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_217);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_1, 0);
x_247 = lean_ctor_get(x_1, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_1);
x_248 = l_Lean_Meta_Grind_Order_getExpr(x_246, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_246);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec_ref(x_248);
x_251 = l_Lean_Meta_Grind_Order_getExpr(x_247, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_250);
lean_dec(x_247);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_254 = x_251;
} else {
 lean_dec_ref(x_251);
 x_254 = lean_box(0);
}
x_255 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7;
x_256 = l_Lean_MessageData_ofExpr(x_249);
x_257 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_259 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
x_260 = l_Lean_MessageData_ofExpr(x_252);
x_261 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
if (lean_is_scalar(x_254)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_254;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_253);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_249);
x_263 = lean_ctor_get(x_251, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_251, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_265 = x_251;
} else {
 lean_dec_ref(x_251);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_247);
x_267 = lean_ctor_get(x_248, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_248, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_269 = x_248;
} else {
 lean_dec_ref(x_248);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Order_ToPropagate_pp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = 0;
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = 1;
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Order_Cnstr_getWeight(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0 = _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1 = _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1);
l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2 = _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2);
l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3 = _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3);
l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4 = _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4);
l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5 = _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5);
l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6 = _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6);
l_Lean_Meta_Grind_Order_Cnstr_pp___closed__7 = _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__7);
l_Lean_Meta_Grind_Order_instOrdWeight___closed__0 = _init_l_Lean_Meta_Grind_Order_instOrdWeight___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instOrdWeight___closed__0);
l_Lean_Meta_Grind_Order_instOrdWeight = _init_l_Lean_Meta_Grind_Order_instOrdWeight();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instOrdWeight);
l_Lean_Meta_Grind_Order_instLEWeight = _init_l_Lean_Meta_Grind_Order_instLEWeight();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instLEWeight);
l_Lean_Meta_Grind_Order_instLTWeight = _init_l_Lean_Meta_Grind_Order_instLTWeight();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instLTWeight);
l_Lean_Meta_Grind_Order_instAddWeight___closed__0 = _init_l_Lean_Meta_Grind_Order_instAddWeight___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instAddWeight___closed__0);
l_Lean_Meta_Grind_Order_instAddWeight = _init_l_Lean_Meta_Grind_Order_instAddWeight();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instAddWeight);
l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0 = _init_l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0);
l_Lean_Meta_Grind_Order_instToStringWeight = _init_l_Lean_Meta_Grind_Order_instToStringWeight();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instToStringWeight);
l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0 = _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0);
l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1 = _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1);
l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2 = _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2);
l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3 = _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4 = _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4);
l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5 = _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5);
l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6 = _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6);
l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7 = _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
