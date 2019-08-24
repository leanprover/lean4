// Lean compiler output
// Module: init.data.repr
// Imports: init.data.string.basic init.data.uint init.data.nat.div
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
lean_object* l_List_HasRepr(lean_object*);
lean_object* l_Nat_digitChar___boxed(lean_object*);
lean_object* l_Char_repr___boxed(lean_object*);
lean_object* l_Sum_HasRepr___rarg___closed__1;
lean_object* l_USize_HasRepr(size_t);
lean_object* l_Fin_HasRepr___boxed(lean_object*);
lean_object* l_Substring_HasRepr___boxed(lean_object*);
lean_object* l_Decidable_HasRepr___rarg___boxed(lean_object*);
lean_object* l_UInt32_HasRepr(uint32_t);
lean_object* l_String_HasRepr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Sigma_HasRepr___rarg___closed__1;
lean_object* l_List_repr___rarg(lean_object*, lean_object*);
uint8_t l_String_isEmpty(lean_object*);
lean_object* l_List_repr___rarg___closed__3;
lean_object* l_String_Iterator_HasRepr___boxed(lean_object*);
lean_object* l_charToHex(uint32_t);
lean_object* l_Substring_HasRepr(lean_object*);
lean_object* l_Subtype_HasRepr(lean_object*, lean_object*);
lean_object* l_Char_quoteCore___closed__3;
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_List_reprAux___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_id_HasRepr___rarg___boxed(lean_object*);
lean_object* l_Sum_HasRepr___rarg___closed__2;
lean_object* l_List_reprAux___main___rarg(lean_object*, uint8_t, lean_object*);
lean_object* l_USize_HasRepr___boxed(lean_object*);
lean_object* l_String_quoteAux___main(lean_object*);
lean_object* l_List_reprAux(lean_object*);
lean_object* l_Unit_HasRepr___boxed(lean_object*);
lean_object* l_charToHex___boxed(lean_object*);
lean_object* l_String_HasRepr___closed__1;
lean_object* l_id_HasRepr(lean_object*);
lean_object* l_List_reprAux___rarg(lean_object*, uint8_t, lean_object*);
lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Char_quoteCore___closed__1;
lean_object* l_Nat_toDigitsCore___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Subtype_HasRepr___boxed(lean_object*, lean_object*);
lean_object* l_Nat_toDigitsCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_String_quote___closed__1;
lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Prod_HasRepr___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Bool_HasRepr(uint8_t);
lean_object* l_Substring_HasRepr___closed__1;
lean_object* l_Nat_HasRepr;
lean_object* l_Decidable_HasRepr(lean_object*);
lean_object* l_Bool_HasRepr___boxed(lean_object*);
lean_object* l_Char_quoteCore___closed__2;
lean_object* l_Option_HasRepr___rarg___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Decidable_HasRepr___rarg(uint8_t);
lean_object* l_Fin_HasRepr___rarg(lean_object*);
lean_object* l_Sigma_HasRepr___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quoteAux(lean_object*);
lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_List_reprAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Sum_HasRepr___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_String_quote___closed__2;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Char_HasRepr___closed__1;
lean_object* l_List_reprAux___main(lean_object*);
lean_object* l_Option_HasRepr___rarg___closed__2;
lean_object* l_Char_quoteCore(uint32_t);
lean_object* l_Char_repr(uint32_t);
lean_object* l_Char_quoteCore___closed__5;
lean_object* l_id_HasRepr___rarg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Option_HasRepr(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Unit_HasRepr(lean_object*);
lean_object* l_Nat_toDigitsCore___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subtype_HasRepr___rarg(lean_object*, lean_object*);
lean_object* l_UInt64_HasRepr___boxed(lean_object*);
lean_object* l_hexDigitRepr(lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_UInt16_HasRepr(uint16_t);
lean_object* l_Sigma_HasRepr(lean_object*, lean_object*);
lean_object* l_Sigma_HasRepr___rarg___closed__2;
lean_object* l_Char_quoteCore___boxed(lean_object*);
lean_object* l_Option_HasRepr___rarg(lean_object*, lean_object*);
lean_object* lean_string_data(lean_object*);
lean_object* l_Prod_HasRepr(lean_object*, lean_object*);
lean_object* l_Nat_toDigits___boxed(lean_object*, lean_object*);
lean_object* l_Sum_HasRepr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
lean_object* l_Nat_toDigitsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Char_HasRepr(uint32_t);
lean_object* l_UInt16_HasRepr___boxed(lean_object*);
lean_object* l_UInt32_HasRepr___boxed(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint32_t l_Nat_digitChar(lean_object*);
lean_object* l_UInt64_HasRepr(uint64_t);
lean_object* l_String_quote(lean_object*);
lean_object* l_Char_HasRepr___boxed(lean_object*);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Sigma_HasRepr___boxed(lean_object*, lean_object*);
lean_object* l_String_Iterator_HasRepr___closed__1;
lean_object* l_Bool_HasRepr___closed__1;
lean_object* l_List_repr(lean_object*);
lean_object* l_List_HasRepr___rarg(lean_object*);
lean_object* l_List_repr___rarg___closed__1;
lean_object* l_hexDigitRepr___boxed(lean_object*);
lean_object* l_Fin_HasRepr(lean_object*);
lean_object* l_Nat_HasRepr___closed__1;
lean_object* l_String_Iterator_HasRepr(lean_object*);
lean_object* l_Unit_HasRepr___closed__1;
lean_object* l_String_Iterator_remainingToString(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Char_quoteCore___closed__4;
lean_object* l_id_HasRepr___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_id_HasRepr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_id_HasRepr___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_id_HasRepr___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_id_HasRepr___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Bool_HasRepr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("false");
return x_1;
}
}
lean_object* _init_l_Bool_HasRepr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("true");
return x_1;
}
}
lean_object* l_Bool_HasRepr(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Bool_HasRepr___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Bool_HasRepr___closed__2;
return x_3;
}
}
}
lean_object* l_Bool_HasRepr___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Bool_HasRepr(x_2);
return x_3;
}
}
lean_object* l_Decidable_HasRepr___rarg(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Bool_HasRepr___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Bool_HasRepr___closed__2;
return x_3;
}
}
}
lean_object* l_Decidable_HasRepr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Decidable_HasRepr___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Decidable_HasRepr___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Decidable_HasRepr___rarg(x_2);
return x_3;
}
}
lean_object* _init_l_List_reprAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", ");
return x_1;
}
}
lean_object* l_List_reprAux___main___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (x_2 == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_String_splitAux___main___closed__1;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_5);
x_8 = l_List_reprAux___main___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_List_reprAux___main___rarg(x_1, x_2, x_6);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = l_String_splitAux___main___closed__1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_1);
x_15 = lean_apply_1(x_1, x_13);
x_16 = 0;
x_17 = l_List_reprAux___main___rarg(x_1, x_16, x_14);
x_18 = lean_string_append(x_15, x_17);
lean_dec(x_17);
return x_18;
}
}
}
}
lean_object* l_List_reprAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_reprAux___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_reprAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_reprAux___main___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_List_reprAux___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_reprAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_reprAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_reprAux___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_reprAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_reprAux___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* _init_l_List_repr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[]");
return x_1;
}
}
lean_object* _init_l_List_repr___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
lean_object* _init_l_List_repr___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
lean_object* l_List_repr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l_List_repr___rarg___closed__1;
return x_3;
}
else
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = 1;
x_5 = l_List_reprAux___main___rarg(x_1, x_4, x_2);
x_6 = l_List_repr___rarg___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_List_repr___rarg___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
}
}
lean_object* l_List_repr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_repr___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_HasRepr___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_repr___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_HasRepr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_HasRepr___rarg), 1, 0);
return x_2;
}
}
lean_object* _init_l_Unit_HasRepr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("()");
return x_1;
}
}
lean_object* l_Unit_HasRepr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Unit_HasRepr___closed__1;
return x_2;
}
}
lean_object* l_Unit_HasRepr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Unit_HasRepr(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Option_HasRepr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("none");
return x_1;
}
}
lean_object* _init_l_Option_HasRepr___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(some ");
return x_1;
}
}
lean_object* _init_l_Option_HasRepr___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
lean_object* l_Option_HasRepr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l_Option_HasRepr___rarg___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_Option_HasRepr___rarg___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Option_HasRepr___rarg___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
}
}
lean_object* l_Option_HasRepr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_HasRepr___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_Sum_HasRepr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(inl ");
return x_1;
}
}
lean_object* _init_l_Sum_HasRepr___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(inr ");
return x_1;
}
}
lean_object* l_Sum_HasRepr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_Sum_HasRepr___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Option_HasRepr___rarg___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_apply_1(x_2, x_10);
x_12 = l_Sum_HasRepr___rarg___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Option_HasRepr___rarg___closed__3;
x_15 = lean_string_append(x_13, x_14);
return x_15;
}
}
}
lean_object* l_Sum_HasRepr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sum_HasRepr___rarg), 3, 0);
return x_3;
}
}
lean_object* _init_l_Prod_HasRepr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
lean_object* l_Prod_HasRepr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_1, x_4);
x_7 = l_Prod_HasRepr___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_List_reprAux___main___rarg___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_apply_1(x_2, x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = l_Option_HasRepr___rarg___closed__3;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
lean_object* l_Prod_HasRepr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Prod_HasRepr___rarg), 3, 0);
return x_3;
}
}
lean_object* _init_l_Sigma_HasRepr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("⟨");
return x_1;
}
}
lean_object* _init_l_Sigma_HasRepr___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("⟩");
return x_1;
}
}
lean_object* l_Sigma_HasRepr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_4);
x_6 = lean_apply_1(x_1, x_4);
x_7 = l_Sigma_HasRepr___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_List_reprAux___main___rarg___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_apply_2(x_2, x_4, x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = l_Sigma_HasRepr___rarg___closed__2;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
lean_object* l_Sigma_HasRepr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sigma_HasRepr___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Sigma_HasRepr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Sigma_HasRepr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Subtype_HasRepr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Subtype_HasRepr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Subtype_HasRepr___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Subtype_HasRepr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Subtype_HasRepr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint32_t l_Nat_digitChar(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_nat_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(5u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(6u);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(7u);
x_17 = lean_nat_dec_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(8u);
x_19 = lean_nat_dec_eq(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(9u);
x_21 = lean_nat_dec_eq(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(10u);
x_23 = lean_nat_dec_eq(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(11u);
x_25 = lean_nat_dec_eq(x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_unsigned_to_nat(12u);
x_27 = lean_nat_dec_eq(x_1, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(13u);
x_29 = lean_nat_dec_eq(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(14u);
x_31 = lean_nat_dec_eq(x_1, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(15u);
x_33 = lean_nat_dec_eq(x_1, x_32);
if (x_33 == 0)
{
uint32_t x_34; 
x_34 = 42;
return x_34;
}
else
{
uint32_t x_35; 
x_35 = 102;
return x_35;
}
}
else
{
uint32_t x_36; 
x_36 = 101;
return x_36;
}
}
else
{
uint32_t x_37; 
x_37 = 100;
return x_37;
}
}
else
{
uint32_t x_38; 
x_38 = 99;
return x_38;
}
}
else
{
uint32_t x_39; 
x_39 = 98;
return x_39;
}
}
else
{
uint32_t x_40; 
x_40 = 97;
return x_40;
}
}
else
{
uint32_t x_41; 
x_41 = 57;
return x_41;
}
}
else
{
uint32_t x_42; 
x_42 = 56;
return x_42;
}
}
else
{
uint32_t x_43; 
x_43 = 55;
return x_43;
}
}
else
{
uint32_t x_44; 
x_44 = 54;
return x_44;
}
}
else
{
uint32_t x_45; 
x_45 = 53;
return x_45;
}
}
else
{
uint32_t x_46; 
x_46 = 52;
return x_46;
}
}
else
{
uint32_t x_47; 
x_47 = 51;
return x_47;
}
}
else
{
uint32_t x_48; 
x_48 = 50;
return x_48;
}
}
else
{
uint32_t x_49; 
x_49 = 49;
return x_49;
}
}
else
{
uint32_t x_50; 
x_50 = 48;
return x_50;
}
}
}
lean_object* l_Nat_digitChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Nat_digitChar(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
lean_object* l_Nat_toDigitsCore___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint32_t x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_9 = lean_nat_mod(x_3, x_1);
x_10 = l_Nat_digitChar(x_9);
lean_dec(x_9);
x_11 = lean_nat_div(x_3, x_1);
lean_dec(x_3);
x_12 = lean_nat_dec_eq(x_11, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box_uint32(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_2 = x_8;
x_3 = x_11;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_8);
x_16 = lean_box_uint32(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
}
lean_object* l_Nat_toDigitsCore___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_toDigitsCore___main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Nat_toDigitsCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_toDigitsCore___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Nat_toDigitsCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_toDigitsCore(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Nat_toDigits(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Nat_toDigitsCore___main(x_1, x_4, x_2, x_5);
return x_6;
}
}
lean_object* l_Nat_toDigits___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_toDigits(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Nat_repr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(10u);
x_3 = l_Nat_toDigits(x_2, x_1);
x_4 = lean_string_mk(x_3);
return x_4;
}
}
lean_object* _init_l_Nat_HasRepr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_repr), 1, 0);
return x_1;
}
}
lean_object* _init_l_Nat_HasRepr() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_HasRepr___closed__1;
return x_1;
}
}
lean_object* l_hexDigitRepr(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Nat_digitChar(x_1);
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_string_push(x_3, x_2);
return x_4;
}
}
lean_object* l_hexDigitRepr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_hexDigitRepr(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_charToHex(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_nat_div(x_2, x_3);
x_5 = lean_nat_mod(x_2, x_3);
lean_dec(x_2);
x_6 = l_hexDigitRepr(x_4);
lean_dec(x_4);
x_7 = l_hexDigitRepr(x_5);
lean_dec(x_5);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_charToHex___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_charToHex(x_2);
return x_3;
}
}
lean_object* _init_l_Char_quoteCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\\x");
return x_1;
}
}
lean_object* _init_l_Char_quoteCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\\\"");
return x_1;
}
}
lean_object* _init_l_Char_quoteCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\\\\");
return x_1;
}
}
lean_object* _init_l_Char_quoteCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\\t");
return x_1;
}
}
lean_object* _init_l_Char_quoteCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\\n");
return x_1;
}
}
lean_object* l_Char_quoteCore(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 10;
x_3 = x_1 == x_2;
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 9;
x_5 = x_1 == x_4;
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 92;
x_7 = x_1 == x_6;
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 34;
x_9 = x_1 == x_8;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_uint32_to_nat(x_1);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_nat_dec_le(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 127;
x_14 = x_1 == x_13;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_String_splitAux___main___closed__1;
x_16 = lean_string_push(x_15, x_1);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_charToHex(x_1);
x_18 = l_Char_quoteCore___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_charToHex(x_1);
x_21 = l_Char_quoteCore___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = l_Char_quoteCore___closed__2;
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = l_Char_quoteCore___closed__3;
return x_24;
}
}
else
{
lean_object* x_25; 
x_25 = l_Char_quoteCore___closed__4;
return x_25;
}
}
else
{
lean_object* x_26; 
x_26 = l_Char_quoteCore___closed__5;
return x_26;
}
}
}
lean_object* l_Char_quoteCore___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_quoteCore(x_2);
return x_3;
}
}
lean_object* _init_l_Char_HasRepr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
lean_object* l_Char_HasRepr(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Char_quoteCore(x_1);
x_3 = l_Char_HasRepr___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = lean_string_append(x_4, x_3);
return x_5;
}
}
lean_object* l_Char_HasRepr___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_HasRepr(x_2);
return x_3;
}
}
lean_object* l_String_quoteAux___main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_String_splitAux___main___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = l_Char_quoteCore(x_5);
x_7 = l_String_quoteAux___main(x_4);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
}
lean_object* l_String_quoteAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_quoteAux___main(x_1);
return x_2;
}
}
lean_object* _init_l_String_quote___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\"");
return x_1;
}
}
lean_object* _init_l_String_quote___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\"\"");
return x_1;
}
}
lean_object* l_String_quote(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_isEmpty(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_string_data(x_1);
x_4 = l_String_quoteAux___main(x_3);
x_5 = l_String_quote___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = lean_string_append(x_6, x_5);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_String_quote___closed__2;
return x_8;
}
}
}
lean_object* _init_l_String_HasRepr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_quote), 1, 0);
return x_1;
}
}
lean_object* _init_l_String_HasRepr() {
_start:
{
lean_object* x_1; 
x_1 = l_String_HasRepr___closed__1;
return x_1;
}
}
lean_object* _init_l_Substring_HasRepr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".toSubstring");
return x_1;
}
}
lean_object* l_Substring_HasRepr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_string_utf8_extract(x_2, x_3, x_4);
x_6 = l_String_quote(x_5);
x_7 = l_Substring_HasRepr___closed__1;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
lean_object* l_Substring_HasRepr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Substring_HasRepr(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_String_Iterator_HasRepr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".mkIterator");
return x_1;
}
}
lean_object* l_String_Iterator_HasRepr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_String_Iterator_remainingToString(x_1);
x_3 = l_String_quote(x_2);
x_4 = l_String_Iterator_HasRepr___closed__1;
x_5 = lean_string_append(x_3, x_4);
return x_5;
}
}
lean_object* l_String_Iterator_HasRepr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Iterator_HasRepr(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Fin_HasRepr___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
lean_object* l_Fin_HasRepr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_HasRepr___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Fin_HasRepr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_HasRepr(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_UInt16_HasRepr(uint16_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint16_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
lean_object* l_UInt16_HasRepr___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_UInt16_HasRepr(x_2);
return x_3;
}
}
lean_object* l_UInt32_HasRepr(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
lean_object* l_UInt32_HasRepr___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_UInt32_HasRepr(x_2);
return x_3;
}
}
lean_object* l_UInt64_HasRepr(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
lean_object* l_UInt64_HasRepr___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_UInt64_HasRepr(x_2);
return x_3;
}
}
lean_object* l_USize_HasRepr(size_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_usize_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
lean_object* l_USize_HasRepr___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_USize_HasRepr(x_2);
return x_3;
}
}
lean_object* l_Char_repr(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Char_quoteCore(x_1);
x_3 = l_Char_HasRepr___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = lean_string_append(x_4, x_3);
return x_5;
}
}
lean_object* l_Char_repr___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_repr(x_2);
return x_3;
}
}
lean_object* initialize_init_data_string_basic(lean_object*);
lean_object* initialize_init_data_uint(lean_object*);
lean_object* initialize_init_data_nat_div(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_data_repr(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_string_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_nat_div(w);
if (lean_io_result_is_error(w)) return w;
l_Bool_HasRepr___closed__1 = _init_l_Bool_HasRepr___closed__1();
lean_mark_persistent(l_Bool_HasRepr___closed__1);
l_Bool_HasRepr___closed__2 = _init_l_Bool_HasRepr___closed__2();
lean_mark_persistent(l_Bool_HasRepr___closed__2);
l_List_reprAux___main___rarg___closed__1 = _init_l_List_reprAux___main___rarg___closed__1();
lean_mark_persistent(l_List_reprAux___main___rarg___closed__1);
l_List_repr___rarg___closed__1 = _init_l_List_repr___rarg___closed__1();
lean_mark_persistent(l_List_repr___rarg___closed__1);
l_List_repr___rarg___closed__2 = _init_l_List_repr___rarg___closed__2();
lean_mark_persistent(l_List_repr___rarg___closed__2);
l_List_repr___rarg___closed__3 = _init_l_List_repr___rarg___closed__3();
lean_mark_persistent(l_List_repr___rarg___closed__3);
l_Unit_HasRepr___closed__1 = _init_l_Unit_HasRepr___closed__1();
lean_mark_persistent(l_Unit_HasRepr___closed__1);
l_Option_HasRepr___rarg___closed__1 = _init_l_Option_HasRepr___rarg___closed__1();
lean_mark_persistent(l_Option_HasRepr___rarg___closed__1);
l_Option_HasRepr___rarg___closed__2 = _init_l_Option_HasRepr___rarg___closed__2();
lean_mark_persistent(l_Option_HasRepr___rarg___closed__2);
l_Option_HasRepr___rarg___closed__3 = _init_l_Option_HasRepr___rarg___closed__3();
lean_mark_persistent(l_Option_HasRepr___rarg___closed__3);
l_Sum_HasRepr___rarg___closed__1 = _init_l_Sum_HasRepr___rarg___closed__1();
lean_mark_persistent(l_Sum_HasRepr___rarg___closed__1);
l_Sum_HasRepr___rarg___closed__2 = _init_l_Sum_HasRepr___rarg___closed__2();
lean_mark_persistent(l_Sum_HasRepr___rarg___closed__2);
l_Prod_HasRepr___rarg___closed__1 = _init_l_Prod_HasRepr___rarg___closed__1();
lean_mark_persistent(l_Prod_HasRepr___rarg___closed__1);
l_Sigma_HasRepr___rarg___closed__1 = _init_l_Sigma_HasRepr___rarg___closed__1();
lean_mark_persistent(l_Sigma_HasRepr___rarg___closed__1);
l_Sigma_HasRepr___rarg___closed__2 = _init_l_Sigma_HasRepr___rarg___closed__2();
lean_mark_persistent(l_Sigma_HasRepr___rarg___closed__2);
l_Nat_HasRepr___closed__1 = _init_l_Nat_HasRepr___closed__1();
lean_mark_persistent(l_Nat_HasRepr___closed__1);
l_Nat_HasRepr = _init_l_Nat_HasRepr();
lean_mark_persistent(l_Nat_HasRepr);
l_Char_quoteCore___closed__1 = _init_l_Char_quoteCore___closed__1();
lean_mark_persistent(l_Char_quoteCore___closed__1);
l_Char_quoteCore___closed__2 = _init_l_Char_quoteCore___closed__2();
lean_mark_persistent(l_Char_quoteCore___closed__2);
l_Char_quoteCore___closed__3 = _init_l_Char_quoteCore___closed__3();
lean_mark_persistent(l_Char_quoteCore___closed__3);
l_Char_quoteCore___closed__4 = _init_l_Char_quoteCore___closed__4();
lean_mark_persistent(l_Char_quoteCore___closed__4);
l_Char_quoteCore___closed__5 = _init_l_Char_quoteCore___closed__5();
lean_mark_persistent(l_Char_quoteCore___closed__5);
l_Char_HasRepr___closed__1 = _init_l_Char_HasRepr___closed__1();
lean_mark_persistent(l_Char_HasRepr___closed__1);
l_String_quote___closed__1 = _init_l_String_quote___closed__1();
lean_mark_persistent(l_String_quote___closed__1);
l_String_quote___closed__2 = _init_l_String_quote___closed__2();
lean_mark_persistent(l_String_quote___closed__2);
l_String_HasRepr___closed__1 = _init_l_String_HasRepr___closed__1();
lean_mark_persistent(l_String_HasRepr___closed__1);
l_String_HasRepr = _init_l_String_HasRepr();
lean_mark_persistent(l_String_HasRepr);
l_Substring_HasRepr___closed__1 = _init_l_Substring_HasRepr___closed__1();
lean_mark_persistent(l_Substring_HasRepr___closed__1);
l_String_Iterator_HasRepr___closed__1 = _init_l_String_Iterator_HasRepr___closed__1();
lean_mark_persistent(l_String_Iterator_HasRepr___closed__1);
return w;
}
#ifdef __cplusplus
}
#endif
