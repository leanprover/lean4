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
lean_object* l_Lean_Meta_Grind_Order_getExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instLEWeight;
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___closed__0;
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
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = l_Lean_Meta_Grind_Order_getExpr(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_19 = x_17;
} else {
 lean_dec_ref(x_17);
 x_19 = lean_box(0);
}
x_20 = l_Lean_Meta_Grind_Order_getExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
if (x_13 == 0)
{
lean_object* x_63; 
x_63 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6;
x_30 = x_63;
goto block_62;
}
else
{
lean_object* x_64; 
x_64 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__7;
x_30 = x_64;
goto block_62;
}
block_29:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_MessageData_ofFormat(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
if (lean_is_scalar(x_22)) {
 x_28 = lean_alloc_ctor(0, 1, 0);
} else {
 x_28 = x_22;
}
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
block_62:
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_32 = lean_int_dec_eq(x_16, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_19);
x_33 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_18);
x_34 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_stringToMessageData(x_30);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
x_39 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_21);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_int_dec_lt(x_16, x_31);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_nat_abs(x_16);
x_45 = l_Nat_reprFast(x_44);
x_23 = x_42;
x_24 = x_45;
goto block_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_nat_abs(x_16);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_46, x_47);
lean_dec(x_46);
x_49 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_50 = lean_nat_add(x_48, x_47);
lean_dec(x_48);
x_51 = l_Nat_reprFast(x_50);
x_52 = lean_string_append(x_49, x_51);
lean_dec_ref(x_51);
x_23 = x_42;
x_24 = x_52;
goto block_29;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_22);
x_53 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_18);
x_54 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_stringToMessageData(x_30);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
x_59 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_21);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
if (lean_is_scalar(x_19)) {
 x_61 = lean_alloc_ctor(0, 1, 0);
} else {
 x_61 = x_19;
}
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_19);
lean_dec(x_18);
x_65 = !lean_is_exclusive(x_20);
if (x_65 == 0)
{
return x_20;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_20, 0);
lean_inc(x_66);
lean_dec(x_20);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_17);
if (x_68 == 0)
{
return x_17;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_17, 0);
lean_inc(x_69);
lean_dec(x_17);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Order_Cnstr_pp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
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
static lean_object* _init_l_Lean_Meta_Grind_Order_instToStringWeight___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instToStringWeight() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Order_instToStringWeight___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = l_Lean_Meta_Grind_Order_getExpr(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Meta_Grind_Order_getExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_30; lean_object* x_31; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_78; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
x_35 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1;
x_36 = l_Lean_MessageData_ofExpr(x_13);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_ctor_get(x_16, 0);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
lean_dec_ref(x_16);
x_42 = l_Lean_MessageData_ofExpr(x_19);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
x_45 = l_Lean_MessageData_ofExpr(x_21);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_38);
if (x_41 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_83 = lean_int_dec_lt(x_40, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_nat_abs(x_40);
lean_dec(x_40);
x_85 = l_Nat_reprFast(x_84);
x_48 = x_85;
goto block_77;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_nat_abs(x_40);
lean_dec(x_40);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_sub(x_86, x_87);
lean_dec(x_86);
x_89 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_90 = lean_nat_add(x_88, x_87);
lean_dec(x_88);
x_91 = l_Nat_reprFast(x_90);
x_92 = lean_string_append(x_89, x_91);
lean_dec_ref(x_91);
x_48 = x_92;
goto block_77;
}
}
else
{
lean_object* x_93; uint8_t x_94; 
x_93 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_94 = lean_int_dec_lt(x_40, x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_nat_abs(x_40);
lean_dec(x_40);
x_96 = l_Nat_reprFast(x_95);
x_78 = x_96;
goto block_81;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = lean_nat_abs(x_40);
lean_dec(x_40);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_sub(x_97, x_98);
lean_dec(x_97);
x_100 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_101 = lean_nat_add(x_99, x_98);
lean_dec(x_99);
x_102 = l_Nat_reprFast(x_101);
x_103 = lean_string_append(x_100, x_102);
lean_dec_ref(x_102);
x_78 = x_103;
goto block_81;
}
}
block_29:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_MessageData_ofFormat(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
if (lean_is_scalar(x_22)) {
 x_28 = lean_alloc_ctor(0, 1, 0);
} else {
 x_28 = x_22;
}
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
block_34:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
x_33 = lean_string_append(x_31, x_32);
x_23 = x_30;
x_24 = x_33;
goto block_29;
}
block_77:
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_17, 0);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_dec_ref(x_17);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_52 = l_Lean_MessageData_ofFormat(x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_38);
if (x_50 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_56 = lean_int_dec_lt(x_49, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_nat_abs(x_49);
lean_dec(x_49);
x_58 = l_Nat_reprFast(x_57);
x_23 = x_54;
x_24 = x_58;
goto block_29;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_nat_abs(x_49);
lean_dec(x_49);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_sub(x_59, x_60);
lean_dec(x_59);
x_62 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_63 = lean_nat_add(x_61, x_60);
lean_dec(x_61);
x_64 = l_Nat_reprFast(x_63);
x_65 = lean_string_append(x_62, x_64);
lean_dec_ref(x_64);
x_23 = x_54;
x_24 = x_65;
goto block_29;
}
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_67 = lean_int_dec_lt(x_49, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_nat_abs(x_49);
lean_dec(x_49);
x_69 = l_Nat_reprFast(x_68);
x_30 = x_54;
x_31 = x_69;
goto block_34;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_nat_abs(x_49);
lean_dec(x_49);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_sub(x_70, x_71);
lean_dec(x_70);
x_73 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_74 = lean_nat_add(x_72, x_71);
lean_dec(x_72);
x_75 = l_Nat_reprFast(x_74);
x_76 = lean_string_append(x_73, x_75);
lean_dec_ref(x_75);
x_30 = x_54;
x_31 = x_76;
goto block_34;
}
}
}
block_81:
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
x_80 = lean_string_append(x_78, x_79);
x_48 = x_80;
goto block_77;
}
}
else
{
uint8_t x_104; 
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
x_104 = !lean_is_exclusive(x_20);
if (x_104 == 0)
{
return x_20;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_20, 0);
lean_inc(x_105);
lean_dec(x_20);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_13);
x_107 = !lean_is_exclusive(x_18);
if (x_107 == 0)
{
return x_18;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_18, 0);
lean_inc(x_108);
lean_dec(x_18);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
case 1:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_1, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_1, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_114);
lean_dec_ref(x_1);
x_115 = l_Lean_Meta_Grind_Order_getExpr(x_111, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_111);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
x_117 = l_Lean_Meta_Grind_Order_getExpr(x_112, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_112);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_127; lean_object* x_128; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_175; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_132 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5;
x_133 = l_Lean_MessageData_ofExpr(x_110);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_ctor_get(x_113, 0);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_113, sizeof(void*)*1);
lean_dec_ref(x_113);
x_139 = l_Lean_MessageData_ofExpr(x_116);
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_135);
x_142 = l_Lean_MessageData_ofExpr(x_118);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_135);
if (x_138 == 0)
{
lean_object* x_179; uint8_t x_180; 
x_179 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_180 = lean_int_dec_lt(x_137, x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_nat_abs(x_137);
lean_dec(x_137);
x_182 = l_Nat_reprFast(x_181);
x_145 = x_182;
goto block_174;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_183 = lean_nat_abs(x_137);
lean_dec(x_137);
x_184 = lean_unsigned_to_nat(1u);
x_185 = lean_nat_sub(x_183, x_184);
lean_dec(x_183);
x_186 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_187 = lean_nat_add(x_185, x_184);
lean_dec(x_185);
x_188 = l_Nat_reprFast(x_187);
x_189 = lean_string_append(x_186, x_188);
lean_dec_ref(x_188);
x_145 = x_189;
goto block_174;
}
}
else
{
lean_object* x_190; uint8_t x_191; 
x_190 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_191 = lean_int_dec_lt(x_137, x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_nat_abs(x_137);
lean_dec(x_137);
x_193 = l_Nat_reprFast(x_192);
x_175 = x_193;
goto block_178;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_194 = lean_nat_abs(x_137);
lean_dec(x_137);
x_195 = lean_unsigned_to_nat(1u);
x_196 = lean_nat_sub(x_194, x_195);
lean_dec(x_194);
x_197 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_198 = lean_nat_add(x_196, x_195);
lean_dec(x_196);
x_199 = l_Nat_reprFast(x_198);
x_200 = lean_string_append(x_197, x_199);
lean_dec_ref(x_199);
x_175 = x_200;
goto block_178;
}
}
block_126:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = l_Lean_MessageData_ofFormat(x_122);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
if (lean_is_scalar(x_119)) {
 x_125 = lean_alloc_ctor(0, 1, 0);
} else {
 x_125 = x_119;
}
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
block_131:
{
lean_object* x_129; lean_object* x_130; 
x_129 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
x_130 = lean_string_append(x_128, x_129);
x_120 = x_127;
x_121 = x_130;
goto block_126;
}
block_174:
{
lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_114, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_114, sizeof(void*)*1);
lean_dec_ref(x_114);
x_148 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_148, 0, x_145);
x_149 = l_Lean_MessageData_ofFormat(x_148);
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_144);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_135);
if (x_147 == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_153 = lean_int_dec_lt(x_146, x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_nat_abs(x_146);
lean_dec(x_146);
x_155 = l_Nat_reprFast(x_154);
x_120 = x_151;
x_121 = x_155;
goto block_126;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_156 = lean_nat_abs(x_146);
lean_dec(x_146);
x_157 = lean_unsigned_to_nat(1u);
x_158 = lean_nat_sub(x_156, x_157);
lean_dec(x_156);
x_159 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_160 = lean_nat_add(x_158, x_157);
lean_dec(x_158);
x_161 = l_Nat_reprFast(x_160);
x_162 = lean_string_append(x_159, x_161);
lean_dec_ref(x_161);
x_120 = x_151;
x_121 = x_162;
goto block_126;
}
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
x_164 = lean_int_dec_lt(x_146, x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_nat_abs(x_146);
lean_dec(x_146);
x_166 = l_Nat_reprFast(x_165);
x_127 = x_151;
x_128 = x_166;
goto block_131;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_167 = lean_nat_abs(x_146);
lean_dec(x_146);
x_168 = lean_unsigned_to_nat(1u);
x_169 = lean_nat_sub(x_167, x_168);
lean_dec(x_167);
x_170 = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
x_171 = lean_nat_add(x_169, x_168);
lean_dec(x_169);
x_172 = l_Nat_reprFast(x_171);
x_173 = lean_string_append(x_170, x_172);
lean_dec_ref(x_172);
x_127 = x_151;
x_128 = x_173;
goto block_131;
}
}
}
block_178:
{
lean_object* x_176; lean_object* x_177; 
x_176 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
x_177 = lean_string_append(x_175, x_176);
x_145 = x_177;
goto block_174;
}
}
else
{
uint8_t x_201; 
lean_dec(x_116);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_110);
x_201 = !lean_is_exclusive(x_117);
if (x_201 == 0)
{
return x_117;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_117, 0);
lean_inc(x_202);
lean_dec(x_117);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
return x_203;
}
}
}
else
{
uint8_t x_204; 
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_110);
x_204 = !lean_is_exclusive(x_115);
if (x_204 == 0)
{
return x_115;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_115, 0);
lean_inc(x_205);
lean_dec(x_115);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_205);
return x_206;
}
}
}
default: 
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_1);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_1, 0);
x_209 = lean_ctor_get(x_1, 1);
x_210 = l_Lean_Meta_Grind_Order_getExpr(x_208, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_208);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec_ref(x_210);
x_212 = l_Lean_Meta_Grind_Order_getExpr(x_209, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_209);
if (lean_obj_tag(x_212) == 0)
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_214 = lean_ctor_get(x_212, 0);
x_215 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7;
x_216 = l_Lean_MessageData_ofExpr(x_211);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_216);
lean_ctor_set(x_1, 0, x_215);
x_217 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_218 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_218, 0, x_1);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lean_MessageData_ofExpr(x_214);
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
lean_ctor_set(x_212, 0, x_220);
return x_212;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_221 = lean_ctor_get(x_212, 0);
lean_inc(x_221);
lean_dec(x_212);
x_222 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7;
x_223 = l_Lean_MessageData_ofExpr(x_211);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_222);
x_224 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_225 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_225, 0, x_1);
lean_ctor_set(x_225, 1, x_224);
x_226 = l_Lean_MessageData_ofExpr(x_221);
x_227 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_228, 0, x_227);
return x_228;
}
}
else
{
uint8_t x_229; 
lean_dec(x_211);
lean_free_object(x_1);
x_229 = !lean_is_exclusive(x_212);
if (x_229 == 0)
{
return x_212;
}
else
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_212, 0);
lean_inc(x_230);
lean_dec(x_212);
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_230);
return x_231;
}
}
}
else
{
uint8_t x_232; 
lean_free_object(x_1);
lean_dec(x_209);
x_232 = !lean_is_exclusive(x_210);
if (x_232 == 0)
{
return x_210;
}
else
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_210, 0);
lean_inc(x_233);
lean_dec(x_210);
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_233);
return x_234;
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_1, 0);
x_236 = lean_ctor_get(x_1, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_1);
x_237 = l_Lean_Meta_Grind_Order_getExpr(x_235, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_235);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec_ref(x_237);
x_239 = l_Lean_Meta_Grind_Order_getExpr(x_236, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_236);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_241 = x_239;
} else {
 lean_dec_ref(x_239);
 x_241 = lean_box(0);
}
x_242 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7;
x_243 = l_Lean_MessageData_ofExpr(x_238);
x_244 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
x_246 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = l_Lean_MessageData_ofExpr(x_240);
x_248 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
if (lean_is_scalar(x_241)) {
 x_249 = lean_alloc_ctor(0, 1, 0);
} else {
 x_249 = x_241;
}
lean_ctor_set(x_249, 0, x_248);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_238);
x_250 = lean_ctor_get(x_239, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_251 = x_239;
} else {
 lean_dec_ref(x_239);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 1, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_250);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_236);
x_253 = lean_ctor_get(x_237, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_254 = x_237;
} else {
 lean_dec_ref(x_237);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 1, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_253);
return x_255;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Order_ToPropagate_pp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
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
l_Lean_Meta_Grind_Order_instToStringWeight___closed__0 = _init_l_Lean_Meta_Grind_Order_instToStringWeight___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instToStringWeight___closed__0);
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
