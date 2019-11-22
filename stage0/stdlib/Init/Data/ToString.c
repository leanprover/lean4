// Lean compiler output
// Module: Init.Data.ToString
// Imports: Init.Data.String.Basic Init.Data.UInt Init.Data.Nat.Div Init.Data.Repr
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
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_List_toStringAux___main(lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__2;
lean_object* l_String_Iterator_remainingToString(lean_object*);
lean_object* l_addParenHeuristic___closed__2;
lean_object* l_UInt64_HasToString(uint64_t);
lean_object* l_Subtype_HasToString___rarg(lean_object*, lean_object*);
extern lean_object* l_Sum_HasRepr___rarg___closed__2;
extern lean_object* l_List_repr___rarg___closed__1;
extern lean_object* l_Option_HasRepr___rarg___closed__1;
lean_object* l_Decidable_HasToString(lean_object*);
lean_object* l_UInt16_HasToString___boxed(lean_object*);
extern lean_object* l_Sum_HasRepr___rarg___closed__1;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
extern lean_object* l_Sigma_HasRepr___rarg___closed__1;
lean_object* l_USize_HasToString(size_t);
extern lean_object* l_Unit_HasRepr___closed__1;
uint8_t l_String_anyAux___main___at_addParenHeuristic___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t l_Char_isWhitespace(uint32_t);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Decidable_HasToString___rarg(uint8_t);
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_UInt8_HasToString(uint8_t);
extern lean_object* l_Sigma_HasRepr___rarg___closed__2;
lean_object* l_List_toStringAux___rarg(lean_object*, uint8_t, lean_object*);
lean_object* l_Subtype_HasToString___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_String_HasToString___boxed(lean_object*);
lean_object* l_UInt64_HasToString___boxed(lean_object*);
lean_object* l_UInt8_HasToString___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_id_HasToString(lean_object*);
lean_object* l_List_toStringAux___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Char_HasToString___boxed(lean_object*);
lean_object* l_Unit_HasToString___boxed(lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_addParenHeuristic(lean_object*);
lean_object* l_List_toString___rarg(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_List_toStringAux(lean_object*);
lean_object* l_Subtype_HasToString(lean_object*, lean_object*);
lean_object* l_Char_HasToString(uint32_t);
lean_object* l_id_HasToString___rarg(lean_object*);
lean_object* l_List_HasToString___rarg(lean_object*);
lean_object* l_Prod_HasToString___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
extern lean_object* l_Bool_HasRepr___closed__1;
lean_object* l_Sigma_HasToString(lean_object*, lean_object*);
lean_object* l_UInt32_HasToString___boxed(lean_object*);
lean_object* l_UInt16_HasToString(uint16_t);
lean_object* l_Bool_HasToString(uint8_t);
lean_object* l_List_HasToString(lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Sigma_HasToString___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_HasToString(lean_object*);
lean_object* l_List_toString(lean_object*);
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Sigma_HasToString___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_HasToString(uint32_t);
lean_object* l_String_Iterator_HasToString(lean_object*);
lean_object* l_Substring_HasToString___boxed(lean_object*);
lean_object* l_Prod_HasToString(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___rarg(lean_object*, uint8_t, lean_object*);
lean_object* l_Bool_HasToString___boxed(lean_object*);
lean_object* l_Unit_HasToString(lean_object*);
lean_object* l_Sum_HasToString___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Decidable_HasToString___rarg___boxed(lean_object*);
lean_object* l_Fin_HasToString___rarg(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Option_HasToString___rarg(lean_object*, lean_object*);
lean_object* l_USize_HasToString___boxed(lean_object*);
lean_object* l_String_anyAux___main___at_addParenHeuristic___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_HasToString(lean_object*);
lean_object* l_Substring_HasToString(lean_object*);
lean_object* l_Fin_HasToString___boxed(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Nat_HasToString(lean_object*);
lean_object* l_String_Iterator_HasToString___boxed(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_addParenHeuristic___boxed(lean_object*);
lean_object* l_Option_HasToString(lean_object*);
lean_object* l_id_HasToString___rarg___boxed(lean_object*);
lean_object* l_addParenHeuristic___closed__1;
lean_object* l_Sum_HasToString(lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_List_toStringAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_id_HasToString___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_id_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_id_HasToString___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_id_HasToString___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_id_HasToString___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_String_HasToString(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_String_HasToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_HasToString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Substring_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_string_utf8_extract(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Substring_HasToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Substring_HasToString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_String_Iterator_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Iterator_remainingToString(x_1);
return x_2;
}
}
lean_object* l_String_Iterator_HasToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Iterator_HasToString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Bool_HasToString(uint8_t x_1) {
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
lean_object* l_Bool_HasToString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Bool_HasToString(x_2);
return x_3;
}
}
lean_object* l_Decidable_HasToString___rarg(uint8_t x_1) {
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
lean_object* l_Decidable_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Decidable_HasToString___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Decidable_HasToString___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Decidable_HasToString___rarg(x_2);
return x_3;
}
}
lean_object* l_List_toStringAux___main___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
x_10 = l_List_toStringAux___main___rarg(x_1, x_2, x_6);
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
x_17 = l_List_toStringAux___main___rarg(x_1, x_16, x_14);
x_18 = lean_string_append(x_15, x_17);
lean_dec(x_17);
return x_18;
}
}
}
}
lean_object* l_List_toStringAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toStringAux___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_toStringAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_toStringAux___main___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_List_toStringAux___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_toStringAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_toStringAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toStringAux___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_toStringAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_toStringAux___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_List_toString___rarg(lean_object* x_1, lean_object* x_2) {
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
x_5 = l_List_toStringAux___main___rarg(x_1, x_4, x_2);
x_6 = l_List_repr___rarg___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_List_repr___rarg___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
}
}
lean_object* l_List_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toString___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_HasToString___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toString___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_HasToString___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Unit_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Unit_HasRepr___closed__1;
return x_2;
}
}
lean_object* l_Unit_HasToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Unit_HasToString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
lean_object* l_Char_HasToString(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
lean_object* l_Char_HasToString___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_HasToString(x_2);
return x_3;
}
}
lean_object* l_Fin_HasToString___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
lean_object* l_Fin_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_HasToString___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Fin_HasToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_HasToString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_UInt8_HasToString(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint8_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
lean_object* l_UInt8_HasToString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_UInt8_HasToString(x_2);
return x_3;
}
}
lean_object* l_UInt16_HasToString(uint16_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint16_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
lean_object* l_UInt16_HasToString___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_UInt16_HasToString(x_2);
return x_3;
}
}
lean_object* l_UInt32_HasToString(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
lean_object* l_UInt32_HasToString___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_UInt32_HasToString(x_2);
return x_3;
}
}
lean_object* l_UInt64_HasToString(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
lean_object* l_UInt64_HasToString___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_UInt64_HasToString(x_2);
return x_3;
}
}
lean_object* l_USize_HasToString(size_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_usize_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
lean_object* l_USize_HasToString___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_USize_HasToString(x_2);
return x_3;
}
}
uint8_t l_String_anyAux___main___at_addParenHeuristic___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_3, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = lean_string_utf8_get(x_1, x_3);
x_6 = l_Char_isWhitespace(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_7;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
x_9 = 1;
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = 0;
return x_10;
}
}
}
lean_object* _init_l_addParenHeuristic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("{");
return x_1;
}
}
lean_object* _init_l_addParenHeuristic___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#[");
return x_1;
}
}
lean_object* l_addParenHeuristic(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Prod_HasRepr___rarg___closed__1;
x_3 = l_String_isPrefixOf(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_List_repr___rarg___closed__2;
x_5 = l_String_isPrefixOf(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_addParenHeuristic___closed__1;
x_7 = l_String_isPrefixOf(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_addParenHeuristic___closed__2;
x_9 = l_String_isPrefixOf(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_string_utf8_byte_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_String_anyAux___main___at_addParenHeuristic___spec__1(x_1, x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_string_append(x_2, x_1);
x_14 = l_Option_HasRepr___rarg___closed__3;
x_15 = lean_string_append(x_13, x_14);
return x_15;
}
}
else
{
lean_inc(x_1);
return x_1;
}
}
else
{
lean_inc(x_1);
return x_1;
}
}
else
{
lean_inc(x_1);
return x_1;
}
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_String_anyAux___main___at_addParenHeuristic___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_anyAux___main___at_addParenHeuristic___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_addParenHeuristic___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_addParenHeuristic(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Option_HasToString___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_addParenHeuristic(x_5);
lean_dec(x_5);
x_7 = l_Option_HasRepr___rarg___closed__2;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Option_HasRepr___rarg___closed__3;
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
}
}
lean_object* l_Option_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_HasToString___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Sum_HasToString___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_addParenHeuristic(x_5);
lean_dec(x_5);
x_7 = l_Sum_HasRepr___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Option_HasRepr___rarg___closed__3;
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_apply_1(x_2, x_11);
x_13 = l_addParenHeuristic(x_12);
lean_dec(x_12);
x_14 = l_Sum_HasRepr___rarg___closed__2;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Option_HasRepr___rarg___closed__3;
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
}
}
lean_object* l_Sum_HasToString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sum_HasToString___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Prod_HasToString___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Prod_HasToString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Prod_HasToString___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Sigma_HasToString___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Sigma_HasToString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sigma_HasToString___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Sigma_HasToString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Sigma_HasToString(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Subtype_HasToString___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Subtype_HasToString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Subtype_HasToString___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Subtype_HasToString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Subtype_HasToString(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_String_Basic(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_Nat_Div(lean_object*);
lean_object* initialize_Init_Data_Repr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_ToString(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Repr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_addParenHeuristic___closed__1 = _init_l_addParenHeuristic___closed__1();
lean_mark_persistent(l_addParenHeuristic___closed__1);
l_addParenHeuristic___closed__2 = _init_l_addParenHeuristic___closed__2();
lean_mark_persistent(l_addParenHeuristic___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
