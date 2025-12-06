// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.Util
// Imports: public import Lean.Meta.Tactic.Grind.Order.OrderM import Lean.Meta.Tactic.Grind.Arith.Util
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
lean_object* l_Lean_Meta_Grind_Order_getExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = l_Lean_Meta_Grind_Order_getExpr(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_18 = x_16;
} else {
 lean_dec_ref(x_16);
 x_18 = lean_box(0);
}
x_19 = l_Lean_Meta_Grind_Order_getExpr(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
if (x_12 == 0)
{
lean_object* x_62; 
x_62 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6;
x_29 = x_62;
goto block_61;
}
else
{
lean_object* x_63; 
x_63 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__7;
x_29 = x_63;
goto block_61;
}
block_28:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
if (lean_is_scalar(x_21)) {
 x_27 = lean_alloc_ctor(0, 1, 0);
} else {
 x_27 = x_21;
}
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
block_61:
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_31 = lean_int_dec_eq(x_15, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_18);
x_32 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_17);
x_33 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_stringToMessageData(x_29);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
x_38 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_20);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_int_dec_lt(x_15, x_30);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_nat_abs(x_15);
x_44 = l_Nat_reprFast(x_43);
x_22 = x_41;
x_23 = x_44;
goto block_28;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_nat_abs(x_15);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_sub(x_45, x_46);
lean_dec(x_45);
x_48 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_49 = lean_nat_add(x_47, x_46);
lean_dec(x_47);
x_50 = l_Nat_reprFast(x_49);
x_51 = lean_string_append(x_48, x_50);
lean_dec_ref(x_50);
x_22 = x_41;
x_23 = x_51;
goto block_28;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_21);
x_52 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_17);
x_53 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_stringToMessageData(x_29);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
x_58 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_20);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_18)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_18;
}
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_18);
lean_dec(x_17);
x_64 = !lean_is_exclusive(x_19);
if (x_64 == 0)
{
return x_19;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_19, 0);
lean_inc(x_65);
lean_dec(x_19);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_16);
if (x_67 == 0)
{
return x_16;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_16, 0);
lean_inc(x_68);
lean_dec(x_16);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Order_Cnstr_pp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Grind_Order_Weight_compare(x_1, x_2);
x_4 = 2;
x_5 = l_instDecidableEqOrdering(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_17 = l_Lean_Meta_Grind_Order_getExpr(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_Order_getExpr(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_29; lean_object* x_30; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_77; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
lean_dec_ref(x_15);
x_36 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1;
x_37 = l_Lean_MessageData_ofExpr(x_12);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_MessageData_ofExpr(x_18);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
x_44 = l_Lean_MessageData_ofExpr(x_20);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_39);
if (x_35 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_82 = lean_int_dec_lt(x_34, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_nat_abs(x_34);
lean_dec(x_34);
x_84 = l_Nat_reprFast(x_83);
x_47 = x_84;
goto block_76;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_nat_abs(x_34);
lean_dec(x_34);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_85, x_86);
lean_dec(x_85);
x_88 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_89 = lean_nat_add(x_87, x_86);
lean_dec(x_87);
x_90 = l_Nat_reprFast(x_89);
x_91 = lean_string_append(x_88, x_90);
lean_dec_ref(x_90);
x_47 = x_91;
goto block_76;
}
}
else
{
lean_object* x_92; uint8_t x_93; 
x_92 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_93 = lean_int_dec_lt(x_34, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_nat_abs(x_34);
lean_dec(x_34);
x_95 = l_Nat_reprFast(x_94);
x_77 = x_95;
goto block_80;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_nat_abs(x_34);
lean_dec(x_34);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_sub(x_96, x_97);
lean_dec(x_96);
x_99 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_100 = lean_nat_add(x_98, x_97);
lean_dec(x_98);
x_101 = l_Nat_reprFast(x_100);
x_102 = lean_string_append(x_99, x_101);
lean_dec_ref(x_101);
x_77 = x_102;
goto block_80;
}
}
block_28:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
if (lean_is_scalar(x_21)) {
 x_27 = lean_alloc_ctor(0, 1, 0);
} else {
 x_27 = x_21;
}
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
block_33:
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
x_32 = lean_string_append(x_30, x_31);
x_22 = x_29;
x_23 = x_32;
goto block_28;
}
block_76:
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
lean_dec_ref(x_16);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_47);
x_51 = l_Lean_MessageData_ofFormat(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_39);
if (x_49 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_55 = lean_int_dec_lt(x_48, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_nat_abs(x_48);
lean_dec(x_48);
x_57 = l_Nat_reprFast(x_56);
x_22 = x_53;
x_23 = x_57;
goto block_28;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_nat_abs(x_48);
lean_dec(x_48);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_sub(x_58, x_59);
lean_dec(x_58);
x_61 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_62 = lean_nat_add(x_60, x_59);
lean_dec(x_60);
x_63 = l_Nat_reprFast(x_62);
x_64 = lean_string_append(x_61, x_63);
lean_dec_ref(x_63);
x_22 = x_53;
x_23 = x_64;
goto block_28;
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_66 = lean_int_dec_lt(x_48, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_nat_abs(x_48);
lean_dec(x_48);
x_68 = l_Nat_reprFast(x_67);
x_29 = x_53;
x_30 = x_68;
goto block_33;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_nat_abs(x_48);
lean_dec(x_48);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_69, x_70);
lean_dec(x_69);
x_72 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_73 = lean_nat_add(x_71, x_70);
lean_dec(x_71);
x_74 = l_Nat_reprFast(x_73);
x_75 = lean_string_append(x_72, x_74);
lean_dec_ref(x_74);
x_29 = x_53;
x_30 = x_75;
goto block_33;
}
}
}
block_80:
{
lean_object* x_78; lean_object* x_79; 
x_78 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
x_79 = lean_string_append(x_77, x_78);
x_47 = x_79;
goto block_76;
}
}
else
{
uint8_t x_103; 
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_12);
x_103 = !lean_is_exclusive(x_19);
if (x_103 == 0)
{
return x_19;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_19, 0);
lean_inc(x_104);
lean_dec(x_19);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_12);
x_106 = !lean_is_exclusive(x_17);
if (x_106 == 0)
{
return x_17;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_17, 0);
lean_inc(x_107);
lean_dec(x_17);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
case 1:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_1, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_1, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_113);
lean_dec_ref(x_1);
x_114 = l_Lean_Meta_Grind_Order_getExpr(x_110, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_110);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = l_Lean_Meta_Grind_Order_getExpr(x_111, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_111);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_126; lean_object* x_127; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_174; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_131 = lean_ctor_get(x_112, 0);
lean_inc(x_131);
x_132 = lean_ctor_get_uint8(x_112, sizeof(void*)*1);
lean_dec_ref(x_112);
x_133 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5;
x_134 = l_Lean_MessageData_ofExpr(x_109);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_MessageData_ofExpr(x_115);
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_136);
x_141 = l_Lean_MessageData_ofExpr(x_117);
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_136);
if (x_132 == 0)
{
lean_object* x_178; uint8_t x_179; 
x_178 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_179 = lean_int_dec_lt(x_131, x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_nat_abs(x_131);
lean_dec(x_131);
x_181 = l_Nat_reprFast(x_180);
x_144 = x_181;
goto block_173;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_182 = lean_nat_abs(x_131);
lean_dec(x_131);
x_183 = lean_unsigned_to_nat(1u);
x_184 = lean_nat_sub(x_182, x_183);
lean_dec(x_182);
x_185 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_186 = lean_nat_add(x_184, x_183);
lean_dec(x_184);
x_187 = l_Nat_reprFast(x_186);
x_188 = lean_string_append(x_185, x_187);
lean_dec_ref(x_187);
x_144 = x_188;
goto block_173;
}
}
else
{
lean_object* x_189; uint8_t x_190; 
x_189 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_190 = lean_int_dec_lt(x_131, x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_nat_abs(x_131);
lean_dec(x_131);
x_192 = l_Nat_reprFast(x_191);
x_174 = x_192;
goto block_177;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_193 = lean_nat_abs(x_131);
lean_dec(x_131);
x_194 = lean_unsigned_to_nat(1u);
x_195 = lean_nat_sub(x_193, x_194);
lean_dec(x_193);
x_196 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_197 = lean_nat_add(x_195, x_194);
lean_dec(x_195);
x_198 = l_Nat_reprFast(x_197);
x_199 = lean_string_append(x_196, x_198);
lean_dec_ref(x_198);
x_174 = x_199;
goto block_177;
}
}
block_125:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = l_Lean_MessageData_ofFormat(x_121);
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_122);
if (lean_is_scalar(x_118)) {
 x_124 = lean_alloc_ctor(0, 1, 0);
} else {
 x_124 = x_118;
}
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
block_130:
{
lean_object* x_128; lean_object* x_129; 
x_128 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
x_129 = lean_string_append(x_127, x_128);
x_119 = x_126;
x_120 = x_129;
goto block_125;
}
block_173:
{
lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = lean_ctor_get(x_113, 0);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_113, sizeof(void*)*1);
lean_dec_ref(x_113);
x_147 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_147, 0, x_144);
x_148 = l_Lean_MessageData_ofFormat(x_147);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_143);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_136);
if (x_146 == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_152 = lean_int_dec_lt(x_145, x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_nat_abs(x_145);
lean_dec(x_145);
x_154 = l_Nat_reprFast(x_153);
x_119 = x_150;
x_120 = x_154;
goto block_125;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_155 = lean_nat_abs(x_145);
lean_dec(x_145);
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_nat_sub(x_155, x_156);
lean_dec(x_155);
x_158 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_159 = lean_nat_add(x_157, x_156);
lean_dec(x_157);
x_160 = l_Nat_reprFast(x_159);
x_161 = lean_string_append(x_158, x_160);
lean_dec_ref(x_160);
x_119 = x_150;
x_120 = x_161;
goto block_125;
}
}
else
{
lean_object* x_162; uint8_t x_163; 
x_162 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_163 = lean_int_dec_lt(x_145, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_nat_abs(x_145);
lean_dec(x_145);
x_165 = l_Nat_reprFast(x_164);
x_126 = x_150;
x_127 = x_165;
goto block_130;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_nat_abs(x_145);
lean_dec(x_145);
x_167 = lean_unsigned_to_nat(1u);
x_168 = lean_nat_sub(x_166, x_167);
lean_dec(x_166);
x_169 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_170 = lean_nat_add(x_168, x_167);
lean_dec(x_168);
x_171 = l_Nat_reprFast(x_170);
x_172 = lean_string_append(x_169, x_171);
lean_dec_ref(x_171);
x_126 = x_150;
x_127 = x_172;
goto block_130;
}
}
}
block_177:
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
x_176 = lean_string_append(x_174, x_175);
x_144 = x_176;
goto block_173;
}
}
else
{
uint8_t x_200; 
lean_dec(x_115);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_109);
x_200 = !lean_is_exclusive(x_116);
if (x_200 == 0)
{
return x_116;
}
else
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_116, 0);
lean_inc(x_201);
lean_dec(x_116);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_201);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_109);
x_203 = !lean_is_exclusive(x_114);
if (x_203 == 0)
{
return x_114;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_114, 0);
lean_inc(x_204);
lean_dec(x_114);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
}
}
default: 
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_1);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_1, 0);
x_208 = lean_ctor_get(x_1, 1);
x_209 = l_Lean_Meta_Grind_Order_getExpr(x_207, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_207);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec_ref(x_209);
x_211 = l_Lean_Meta_Grind_Order_getExpr(x_208, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_208);
if (lean_obj_tag(x_211) == 0)
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7;
x_215 = l_Lean_MessageData_ofExpr(x_210);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_215);
lean_ctor_set(x_1, 0, x_214);
x_216 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_217 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_217, 0, x_1);
lean_ctor_set(x_217, 1, x_216);
x_218 = l_Lean_MessageData_ofExpr(x_213);
x_219 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
lean_ctor_set(x_211, 0, x_219);
return x_211;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_220 = lean_ctor_get(x_211, 0);
lean_inc(x_220);
lean_dec(x_211);
x_221 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7;
x_222 = l_Lean_MessageData_ofExpr(x_210);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_222);
lean_ctor_set(x_1, 0, x_221);
x_223 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_224 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_224, 0, x_1);
lean_ctor_set(x_224, 1, x_223);
x_225 = l_Lean_MessageData_ofExpr(x_220);
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_227, 0, x_226);
return x_227;
}
}
else
{
uint8_t x_228; 
lean_dec(x_210);
lean_free_object(x_1);
x_228 = !lean_is_exclusive(x_211);
if (x_228 == 0)
{
return x_211;
}
else
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_211, 0);
lean_inc(x_229);
lean_dec(x_211);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_229);
return x_230;
}
}
}
else
{
uint8_t x_231; 
lean_free_object(x_1);
lean_dec(x_208);
x_231 = !lean_is_exclusive(x_209);
if (x_231 == 0)
{
return x_209;
}
else
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_209, 0);
lean_inc(x_232);
lean_dec(x_209);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_232);
return x_233;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_1, 0);
x_235 = lean_ctor_get(x_1, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_1);
x_236 = l_Lean_Meta_Grind_Order_getExpr(x_234, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_234);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec_ref(x_236);
x_238 = l_Lean_Meta_Grind_Order_getExpr(x_235, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_235);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 x_240 = x_238;
} else {
 lean_dec_ref(x_238);
 x_240 = lean_box(0);
}
x_241 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7;
x_242 = l_Lean_MessageData_ofExpr(x_237);
x_243 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_245 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = l_Lean_MessageData_ofExpr(x_239);
x_247 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
if (lean_is_scalar(x_240)) {
 x_248 = lean_alloc_ctor(0, 1, 0);
} else {
 x_248 = x_240;
}
lean_ctor_set(x_248, 0, x_247);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_237);
x_249 = lean_ctor_get(x_238, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 x_250 = x_238;
} else {
 lean_dec_ref(x_238);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 1, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_249);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_235);
x_252 = lean_ctor_get(x_236, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 x_253 = x_236;
} else {
 lean_dec_ref(x_236);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 1, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_252);
return x_254;
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
x_12 = l_Lean_Meta_Grind_Order_ToPropagate_pp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Order_Cnstr_getWeight(x_1, x_2);
lean_dec_ref(x_2);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
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
