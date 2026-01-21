// Lean compiler output
// Module: Init.Data.Ord.Basic
// Imports: import Init.ByCases import Init.Ext public import Init.PropLemmas
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
LEAN_EXPORT lean_object* l_Ordering_lt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ord_lex_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_toBEq___redArg(lean_object*);
static lean_object* l_instReprOrdering_repr___closed__3;
LEAN_EXPORT lean_object* l_instOrdFin___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_isEq___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instOrdChar;
static lean_object* l_instReprOrdering___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Ord_toLE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableRelLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_opposite___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instInhabitedOrdering;
LEAN_EXPORT uint8_t l_compareOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprOrdering_repr(uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Ord_opposite___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ltOfOrd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instOrdNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_lexOrd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Ordering_instDecidableExistsOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_eq_elim___redArg(lean_object*);
static lean_object* l_instReprOrdering_repr___closed__5;
LEAN_EXPORT lean_object* l_beqOfOrd(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_compareLex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_gt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_compareLex___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_leOfOrd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_compareOfLessAndEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_lex_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqOrdering___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_gt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_eq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_instOrdNat___closed__0;
LEAN_EXPORT lean_object* l_Ord_toLT(lean_object*, lean_object*);
static lean_object* l_lexOrd___redArg___closed__0;
LEAN_EXPORT lean_object* l_instOrdBitVec(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_lt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_beqOfOrd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_instReprOrdering_repr___closed__6;
static lean_object* l_instOrdBool___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableRelLt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Ord_lex_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_lt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_instOrdOrdering___closed__0;
LEAN_EXPORT lean_object* l_Ord_lex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprOrdering;
LEAN_EXPORT uint8_t l_instDecidableRelLt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Ordering_isLT(uint8_t);
LEAN_EXPORT lean_object* l_beqOfOrd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Ordering_isNe(uint8_t);
LEAN_EXPORT lean_object* l_instOrdBool___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_gt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Ordering_isEq(uint8_t);
LEAN_EXPORT lean_object* l_ltOfOrd(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_lexOrd___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdOption___redArg(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableRelLe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_compareOfLessAndEq(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instOrdChar___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_leOfOrd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Ordering_swap(uint8_t);
static lean_object* l_instReprOrdering_repr___closed__4;
LEAN_EXPORT lean_object* l_instOrdOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_isLT___boxed(lean_object*);
static lean_object* l_instReprOrdering_repr___closed__0;
LEAN_EXPORT uint8_t l_instOrdInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_isNe___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_swap___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ord_lex___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdBitVec___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_isGE___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_gt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_opposite___redArg(lean_object*);
LEAN_EXPORT uint8_t l_compareOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instOrdChar___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Ordering_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instOrd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_isGT___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instOrdOrdering;
LEAN_EXPORT uint8_t l_instDecidableRelLe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Ord_on___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_isLE___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ord_toBEq(lean_object*, lean_object*);
static lean_object* l_instReprOrdering_repr___closed__2;
LEAN_EXPORT uint8_t l_compareOfLessAndBEq___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Ordering_instDecidableForallOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instDecidableRelLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_opposite(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_compareOn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_compareLex___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_lt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_eq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableRelLt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_ctorIdx(uint8_t);
static lean_object* l_instReprOrdering_repr___closed__1;
LEAN_EXPORT lean_object* l_instReprOrdering_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_lex_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_compareOfLessAndEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instOrdOption___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_instOrdInt;
LEAN_EXPORT lean_object* l_Ord_on___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Ordering_isGT(uint8_t);
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_eq_elim___redArg___boxed(lean_object*);
static lean_object* l_instOrdChar___closed__0;
static lean_object* l_instOrdInt___closed__0;
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1___boxed(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Ordering_isGE(uint8_t);
LEAN_EXPORT uint8_t l_instOrdBool___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instOrdBool;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_toLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instOrd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_compareLex___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_toLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_compareOfLessAndBEq(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Ordering_instDecidableForallOfDecidablePred(lean_object*, lean_object*);
static lean_object* l_instOrdOrdering___closed__1;
LEAN_EXPORT lean_object* l_instOrdNat;
LEAN_EXPORT lean_object* l_Ord_on(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_compareLex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_toCtorIdx(uint8_t);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l_Ordering_isLE(uint8_t);
LEAN_EXPORT lean_object* l_lexOrd(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_on___redArg(lean_object*, lean_object*);
static lean_object* l_instReprOrdering_repr___closed__7;
LEAN_EXPORT lean_object* l_beqOfOrd___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdFin(lean_object*);
LEAN_EXPORT uint8_t l_Ordering_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_instDecidableRelLe___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_compareOfLessAndEq___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_instInhabitedOrdering_default;
LEAN_EXPORT lean_object* l_instOrdNat___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Ordering_instDecidableExistsOfDecidablePred(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_compareLex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Ordering_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ordering_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Ordering_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Ordering_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Ordering_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Ordering_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Ordering_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Ordering_lt_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Ordering_lt_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Ordering_eq_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Ordering_eq_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Ordering_gt_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Ordering_gt_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static uint8_t _init_l_instInhabitedOrdering_default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_instInhabitedOrdering() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Ordering_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_le(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 2;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Ordering_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOrdering(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Ordering_ctorIdx(x_1);
x_4 = l_Ordering_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOrdering___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_instDecidableEqOrdering(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ordering.lt", 11, 11);
return x_1;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprOrdering_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ordering.eq", 11, 11);
return x_1;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprOrdering_repr___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ordering.gt", 11, 11);
return x_1;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprOrdering_repr___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprOrdering_repr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; 
switch (x_1) {
case 0:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(1024u);
x_25 = lean_nat_dec_le(x_24, x_2);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_instReprOrdering_repr___closed__6;
x_3 = x_26;
goto block_9;
}
else
{
lean_object* x_27; 
x_27 = l_instReprOrdering_repr___closed__7;
x_3 = x_27;
goto block_9;
}
}
case 1:
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(1024u);
x_29 = lean_nat_dec_le(x_28, x_2);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = l_instReprOrdering_repr___closed__6;
x_10 = x_30;
goto block_16;
}
else
{
lean_object* x_31; 
x_31 = l_instReprOrdering_repr___closed__7;
x_10 = x_31;
goto block_16;
}
}
default: 
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(1024u);
x_33 = lean_nat_dec_le(x_32, x_2);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_instReprOrdering_repr___closed__6;
x_17 = x_34;
goto block_23;
}
else
{
lean_object* x_35; 
x_35 = l_instReprOrdering_repr___closed__7;
x_17 = x_35;
goto block_23;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_instReprOrdering_repr___closed__1;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_instReprOrdering_repr___closed__3;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_instReprOrdering_repr___closed__5;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_instReprOrdering_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_instReprOrdering_repr(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_instReprOrdering___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprOrdering_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instReprOrdering() {
_start:
{
lean_object* x_1; 
x_1 = l_instReprOrdering___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Ordering_swap(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
uint8_t x_2; 
x_2 = 2;
return x_2;
}
case 1:
{
return x_1;
}
default: 
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Ordering_swap___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Ordering_swap(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Ordering_isEq(uint8_t x_1) {
_start:
{
if (x_1 == 1)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isEq___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Ordering_isEq(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Ordering_isNe(uint8_t x_1) {
_start:
{
if (x_1 == 1)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isNe___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Ordering_isNe(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Ordering_isLE(uint8_t x_1) {
_start:
{
if (x_1 == 2)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isLE___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Ordering_isLE(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Ordering_isLT(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isLT___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Ordering_isLT(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Ordering_isGT(uint8_t x_1) {
_start:
{
if (x_1 == 2)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isGT___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Ordering_isGT(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Ordering_isGE(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isGE___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Ordering_isGE(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableForallOfDecidablePred___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = 0;
x_3 = lean_box(x_2);
lean_inc_ref(x_1);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec_ref(x_1);
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = 1;
x_8 = lean_box(x_7);
lean_inc_ref(x_1);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec_ref(x_1);
x_11 = lean_unbox(x_9);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = 2;
x_13 = lean_box(x_12);
x_14 = lean_apply_1(x_1, x_13);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Ordering_instDecidableForallOfDecidablePred___redArg(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableForallOfDecidablePred(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Ordering_instDecidableForallOfDecidablePred___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Ordering_instDecidableForallOfDecidablePred(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableExistsOfDecidablePred___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = 0;
x_3 = lean_box(x_2);
lean_inc_ref(x_1);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = 1;
x_7 = lean_box(x_6);
lean_inc_ref(x_1);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = 2;
x_11 = lean_box(x_10);
x_12 = lean_apply_1(x_1, x_11);
x_13 = lean_unbox(x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec_ref(x_1);
x_14 = lean_unbox(x_8);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec_ref(x_1);
x_15 = lean_unbox(x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Ordering_instDecidableExistsOfDecidablePred___redArg(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableExistsOfDecidablePred(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Ordering_instDecidableExistsOfDecidablePred___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Ordering_instDecidableExistsOfDecidablePred(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(x_1);
x_7 = lean_apply_2(x_3, x_6, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_2 == 1)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(x_2);
x_8 = lean_apply_2(x_4, x_7, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndEq___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (x_3 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_apply_2(x_4, x_1, x_2);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
x_6 = l_compareOfLessAndEq___redArg(x_1, x_2, x_5, x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
if (x_5 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_apply_2(x_6, x_2, x_3);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 2;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_5);
x_8 = l_compareOfLessAndEq(x_1, x_2, x_3, x_4, x_7, x_6);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndBEq___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (x_3 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_apply_2(x_4, x_1, x_2);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
x_6 = l_compareOfLessAndBEq___redArg(x_1, x_2, x_5, x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndBEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
if (x_5 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_apply_2(x_6, x_2, x_3);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 2;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_5);
x_8 = l_compareOfLessAndBEq(x_1, x_2, x_3, x_4, x_7, x_6);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_compareLex___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_unbox(x_5);
if (x_6 == 1)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_apply_2(x_2, x_3, x_4);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = lean_unbox(x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_compareLex___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_compareLex___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_compareLex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_apply_2(x_3, x_5, x_6);
x_8 = lean_unbox(x_7);
if (x_8 == 1)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_apply_2(x_4, x_5, x_6);
x_10 = lean_unbox(x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_11 = lean_unbox(x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_compareLex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_compareLex(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_compareOn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_2);
x_5 = lean_apply_1(x_2, x_3);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_apply_2(x_1, x_5, x_6);
x_8 = lean_unbox(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_compareOn___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_compareOn___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_compareOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_4);
x_7 = lean_apply_1(x_4, x_5);
x_8 = lean_apply_1(x_4, x_6);
x_9 = lean_apply_2(x_3, x_7, x_8);
x_10 = lean_unbox(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_compareOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_compareOn(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_instOrdNat___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_instOrdNat___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_instOrdNat___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_instOrdNat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instOrdNat___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instOrdNat() {
_start:
{
lean_object* x_1; 
x_1 = l_instOrdNat___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_instOrdInt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_int_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_instOrdInt___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_instOrdInt___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_instOrdInt___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instOrdInt___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instOrdInt() {
_start:
{
lean_object* x_1; 
x_1 = l_instOrdInt___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_instOrdBool___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 1)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
}
else
{
if (x_2 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_instOrdBool___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_instOrdBool___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_instOrdBool___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instOrdBool___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instOrdBool() {
_start:
{
lean_object* x_1; 
x_1 = l_instOrdBool___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instOrdFin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instOrdNat___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_instOrdFin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instOrdFin(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_instOrdChar___lam__0(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint32_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_uint32_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_instOrdChar___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_instOrdChar___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_instOrdChar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instOrdChar___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instOrdChar() {
_start:
{
lean_object* x_1; 
x_1 = l_instOrdChar___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instOrdNat___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instOrdBitVec(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_instOrdOption___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec_ref(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec_ref(x_3);
x_5 = 0;
return x_5;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = 2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_apply_2(x_1, x_7, x_8);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_instOrdOption___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_instOrdOption___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instOrdOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instOrdOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instOrdOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instOrdOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_instOrdOrdering___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Ordering_ctorIdx___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instOrdOrdering___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instOrdOrdering___closed__0;
x_2 = l_instOrdNat___closed__0;
x_3 = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_2);
lean_closure_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_instOrdOrdering() {
_start:
{
lean_object* x_1; 
x_1 = l_instOrdOrdering___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_List_compareLex___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec_ref(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = 2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
x_11 = lean_apply_2(x_1, x_7, x_9);
x_12 = lean_unbox(x_11);
if (x_12 == 1)
{
x_2 = x_8;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_1);
x_14 = lean_unbox(x_11);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_compareLex___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_compareLex___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_compareLex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_List_compareLex___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_compareLex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_List_compareLex(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_instOrd___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instOrd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_apply_2(x_4, x_2, lean_box(0));
return x_9;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_apply_2(x_5, x_1, lean_box(0));
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec_ref(x_2);
x_15 = lean_apply_4(x_6, x_11, x_12, x_13, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_5, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = lean_apply_2(x_6, x_4, lean_box(0));
return x_11;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; 
lean_dec(x_8);
x_12 = lean_apply_2(x_7, x_3, lean_box(0));
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec_ref(x_3);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec_ref(x_4);
x_17 = lean_apply_4(x_8, x_13, x_14, x_15, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_lexOrd___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_lexOrd___redArg___lam__1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_lexOrd___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_lexOrd___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_lexOrd___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_lexOrd___redArg___lam__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_lexOrd___redArg___closed__0;
x_4 = l_lexOrd___redArg___closed__1;
x_5 = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_1);
lean_closure_set(x_5, 3, x_3);
x_6 = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_4);
x_7 = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_lexOrd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_lexOrd___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_beqOfOrd___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_unbox(x_4);
if (x_5 == 1)
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
LEAN_EXPORT lean_object* l_beqOfOrd___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_beqOfOrd___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_beqOfOrd___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_beqOfOrd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ltOfOrd(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_unbox(x_4);
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
LEAN_EXPORT lean_object* l_instDecidableRelLt___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_instDecidableRelLt___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_apply_2(x_2, x_3, x_4);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_instDecidableRelLt(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_leOfOrd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_leOfOrd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_leOfOrd(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_unbox(x_4);
if (x_5 == 2)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLe___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_instDecidableRelLe___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_apply_2(x_2, x_3, x_4);
x_6 = lean_unbox(x_5);
if (x_6 == 2)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_instDecidableRelLe(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Ord_toBEq___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Ord_toBEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Ord_toLT(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Ord_toLE(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Ord_opposite___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_3, x_2);
x_5 = lean_unbox(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Ord_opposite___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Ord_on___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_apply_2(x_2, x_5, x_6);
x_8 = lean_unbox(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Ord_on___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Ord_on___redArg___lam__0(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Ord_on___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Ord_on___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ord_on(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Ord_on___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Ord_lex___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_lexOrd___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ord_lex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_lexOrd___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Ord_lex_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_unbox(x_5);
if (x_6 == 1)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_apply_2(x_2, x_3, x_4);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = lean_unbox(x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Ord_lex_x27___redArg___lam__0(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Ord_lex_x27___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Ord_lex_x27___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instInhabitedOrdering_default = _init_l_instInhabitedOrdering_default();
l_instInhabitedOrdering = _init_l_instInhabitedOrdering();
l_instReprOrdering_repr___closed__0 = _init_l_instReprOrdering_repr___closed__0();
lean_mark_persistent(l_instReprOrdering_repr___closed__0);
l_instReprOrdering_repr___closed__1 = _init_l_instReprOrdering_repr___closed__1();
lean_mark_persistent(l_instReprOrdering_repr___closed__1);
l_instReprOrdering_repr___closed__2 = _init_l_instReprOrdering_repr___closed__2();
lean_mark_persistent(l_instReprOrdering_repr___closed__2);
l_instReprOrdering_repr___closed__3 = _init_l_instReprOrdering_repr___closed__3();
lean_mark_persistent(l_instReprOrdering_repr___closed__3);
l_instReprOrdering_repr___closed__4 = _init_l_instReprOrdering_repr___closed__4();
lean_mark_persistent(l_instReprOrdering_repr___closed__4);
l_instReprOrdering_repr___closed__5 = _init_l_instReprOrdering_repr___closed__5();
lean_mark_persistent(l_instReprOrdering_repr___closed__5);
l_instReprOrdering_repr___closed__6 = _init_l_instReprOrdering_repr___closed__6();
lean_mark_persistent(l_instReprOrdering_repr___closed__6);
l_instReprOrdering_repr___closed__7 = _init_l_instReprOrdering_repr___closed__7();
lean_mark_persistent(l_instReprOrdering_repr___closed__7);
l_instReprOrdering___closed__0 = _init_l_instReprOrdering___closed__0();
lean_mark_persistent(l_instReprOrdering___closed__0);
l_instReprOrdering = _init_l_instReprOrdering();
lean_mark_persistent(l_instReprOrdering);
l_instOrdNat___closed__0 = _init_l_instOrdNat___closed__0();
lean_mark_persistent(l_instOrdNat___closed__0);
l_instOrdNat = _init_l_instOrdNat();
lean_mark_persistent(l_instOrdNat);
l_instOrdInt___closed__0 = _init_l_instOrdInt___closed__0();
lean_mark_persistent(l_instOrdInt___closed__0);
l_instOrdInt = _init_l_instOrdInt();
lean_mark_persistent(l_instOrdInt);
l_instOrdBool___closed__0 = _init_l_instOrdBool___closed__0();
lean_mark_persistent(l_instOrdBool___closed__0);
l_instOrdBool = _init_l_instOrdBool();
lean_mark_persistent(l_instOrdBool);
l_instOrdChar___closed__0 = _init_l_instOrdChar___closed__0();
lean_mark_persistent(l_instOrdChar___closed__0);
l_instOrdChar = _init_l_instOrdChar();
lean_mark_persistent(l_instOrdChar);
l_instOrdOrdering___closed__0 = _init_l_instOrdOrdering___closed__0();
lean_mark_persistent(l_instOrdOrdering___closed__0);
l_instOrdOrdering___closed__1 = _init_l_instOrdOrdering___closed__1();
lean_mark_persistent(l_instOrdOrdering___closed__1);
l_instOrdOrdering = _init_l_instOrdOrdering();
lean_mark_persistent(l_instOrdOrdering);
l_lexOrd___redArg___closed__0 = _init_l_lexOrd___redArg___closed__0();
lean_mark_persistent(l_lexOrd___redArg___closed__0);
l_lexOrd___redArg___closed__1 = _init_l_lexOrd___redArg___closed__1();
lean_mark_persistent(l_lexOrd___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
