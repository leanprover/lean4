// Lean compiler output
// Module: init.data.tostring
// Imports: init.data.string.basic init.data.uint init.data.nat.div init.data.repr
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
extern "C" obj* lean_uint8_to_nat(uint8);
obj* l_List_toStringAux___rarg(obj*, uint8, obj*);
extern obj* l_Sum_HasRepr___rarg___closed__1;
extern obj* l_Sigma_HasRepr___rarg___closed__1;
obj* l_UInt16_HasToString___boxed(obj*);
extern obj* l_List_repr___rarg___closed__3;
obj* l_Decidable_HasToString___rarg(uint8);
obj* l_Sigma_HasToString(obj*, obj*);
obj* l_UInt32_HasToString___boxed(obj*);
obj* l_List_toStringAux___rarg___boxed(obj*, obj*, obj*);
obj* l_Nat_HasToString(obj*);
obj* l_UInt8_HasToString(uint8);
obj* l_List_toStringAux___main___rarg(obj*, uint8, obj*);
obj* l_Subtype_HasToString___rarg(obj*, obj*);
extern "C" obj* lean_uint16_to_nat(uint16);
obj* l_List_toString(obj*);
obj* l_Fin_HasToString___rarg(obj*);
obj* l_Bool_HasToString(uint8);
obj* l_List_toStringAux___main___rarg___boxed(obj*, obj*, obj*);
obj* l_UInt16_HasToString(uint16);
extern obj* l_Sum_HasRepr___rarg___closed__2;
obj* l_Sum_HasToString(obj*, obj*);
obj* l_UInt64_HasToString(uint64);
extern obj* l_Bool_HasRepr___closed__2;
obj* l_id_HasToString(obj*);
obj* l_Substring_HasToString___boxed(obj*);
obj* l_UInt32_HasToString(uint32);
extern "C" obj* lean_string_push(obj*, uint32);
obj* l_Sigma_HasToString___rarg(obj*, obj*, obj*);
obj* l_Nat_repr(obj*);
extern obj* l_List_repr___rarg___closed__2;
obj* l_Substring_HasToString(obj*);
obj* l_List_HasToString(obj*);
extern obj* l_Option_HasRepr___rarg___closed__1;
extern "C" obj* lean_string_append(obj*, obj*);
obj* l_id_HasToString___rarg(obj*);
extern obj* l_List_reprAux___main___rarg___closed__1;
obj* l_USize_HasToString___boxed(obj*);
obj* l_List_toString___rarg(obj*, obj*);
extern obj* l_Option_HasRepr___rarg___closed__3;
extern "C" obj* lean_uint64_to_nat(uint64);
obj* l_Subtype_HasToString___boxed(obj*, obj*);
obj* l_String_HasToString___boxed(obj*);
extern obj* l_Option_HasRepr___rarg___closed__2;
extern obj* l_Prod_HasRepr___rarg___closed__1;
obj* l_Option_HasToString___rarg(obj*, obj*);
obj* l_Subtype_HasToString(obj*, obj*);
obj* l_List_toStringAux(obj*);
obj* l_Option_HasToString(obj*);
obj* l_List_HasToString___rarg(obj*);
extern obj* l_Sigma_HasRepr___rarg___closed__2;
obj* l_String_Iterator_HasToString___boxed(obj*);
obj* l_UInt8_HasToString___boxed(obj*);
obj* l_Char_HasToString(uint32);
obj* l_Sum_HasToString___rarg(obj*, obj*, obj*);
obj* l_Prod_HasToString___rarg(obj*, obj*, obj*);
obj* l_List_toStringAux___main(obj*);
obj* l_Unit_HasToString(obj*);
obj* l_Fin_HasToString(obj*);
obj* l_Fin_HasToString___boxed(obj*);
obj* l_String_HasToString(obj*);
obj* l_Decidable_HasToString___rarg___boxed(obj*);
extern "C" obj* lean_string_utf8_extract(obj*, obj*, obj*);
obj* l_id_HasToString___rarg___boxed(obj*);
obj* l_Bool_HasToString___boxed(obj*);
obj* l_Prod_HasToString(obj*, obj*);
extern "C" obj* lean_uint32_to_nat(uint32);
obj* l_Unit_HasToString___boxed(obj*);
obj* l_Char_HasToString___boxed(obj*);
extern "C" obj* lean_usize_to_nat(usize);
obj* l_Decidable_HasToString(obj*);
extern obj* l_Bool_HasRepr___closed__1;
extern obj* l_List_repr___rarg___closed__1;
obj* l_Sigma_HasToString___boxed(obj*, obj*);
obj* l_String_Iterator_HasToString(obj*);
extern obj* l_Unit_HasRepr___closed__1;
obj* l_UInt64_HasToString___boxed(obj*);
obj* l_String_Iterator_remainingToString(obj*);
obj* l_USize_HasToString(usize);
extern obj* l_String_splitAux___main___closed__1;
obj* l_id_HasToString___rarg(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_id_HasToString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_id_HasToString___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_id_HasToString___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_id_HasToString___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_HasToString(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_String_HasToString___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_HasToString(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_HasToString(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean_string_utf8_extract(x_2, x_3, x_4);
return x_5;
}
}
obj* l_Substring_HasToString___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_HasToString(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_Iterator_HasToString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_remainingToString(x_1);
return x_2;
}
}
obj* l_String_Iterator_HasToString___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_HasToString(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Bool_HasToString(uint8 x_1) {
_start:
{
if (x_1 == 0)
{
obj* x_2; 
x_2 = l_Bool_HasRepr___closed__1;
return x_2;
}
else
{
obj* x_3; 
x_3 = l_Bool_HasRepr___closed__2;
return x_3;
}
}
}
obj* l_Bool_HasToString___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Bool_HasToString(x_2);
return x_3;
}
}
obj* l_Decidable_HasToString___rarg(uint8 x_1) {
_start:
{
if (x_1 == 0)
{
obj* x_2; 
x_2 = l_Bool_HasRepr___closed__1;
return x_2;
}
else
{
obj* x_3; 
x_3 = l_Bool_HasRepr___closed__2;
return x_3;
}
}
}
obj* l_Decidable_HasToString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Decidable_HasToString___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Decidable_HasToString___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Decidable_HasToString___rarg(x_2);
return x_3;
}
}
obj* l_List_toStringAux___main___rarg(obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
if (x_2 == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = l_String_splitAux___main___closed__1;
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
lean::inc(x_1);
x_7 = lean::apply_1(x_1, x_5);
x_8 = l_List_reprAux___main___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean::dec(x_7);
x_10 = l_List_toStringAux___main___rarg(x_1, x_2, x_6);
x_11 = lean_string_append(x_9, x_10);
lean::dec(x_10);
return x_11;
}
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_12; 
lean::dec(x_1);
x_12 = l_String_splitAux___main___closed__1;
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_3, 0);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_3, 1);
lean::inc(x_14);
lean::dec(x_3);
lean::inc(x_1);
x_15 = lean::apply_1(x_1, x_13);
x_16 = 0;
x_17 = l_List_toStringAux___main___rarg(x_1, x_16, x_14);
x_18 = lean_string_append(x_15, x_17);
lean::dec(x_17);
return x_18;
}
}
}
}
obj* l_List_toStringAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toStringAux___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_toStringAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_List_toStringAux___main___rarg(x_1, x_4, x_3);
return x_5;
}
}
obj* l_List_toStringAux___rarg(obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_toStringAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_toStringAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toStringAux___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_toStringAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_List_toStringAux___rarg(x_1, x_4, x_3);
return x_5;
}
}
obj* l_List_toString___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_List_repr___rarg___closed__1;
return x_3;
}
else
{
uint8 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = 1;
x_5 = l_List_toStringAux___main___rarg(x_1, x_4, x_2);
x_6 = l_List_repr___rarg___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean::dec(x_5);
x_8 = l_List_repr___rarg___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
}
}
obj* l_List_toString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toString___rarg), 2, 0);
return x_2;
}
}
obj* l_List_HasToString___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toString___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_List_HasToString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_HasToString___rarg), 1, 0);
return x_2;
}
}
obj* l_Unit_HasToString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Unit_HasRepr___closed__1;
return x_2;
}
}
obj* l_Unit_HasToString___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Unit_HasToString(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Nat_HasToString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
obj* l_Char_HasToString(uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
obj* l_Char_HasToString___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_HasToString(x_2);
return x_3;
}
}
obj* l_Fin_HasToString___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
obj* l_Fin_HasToString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Fin_HasToString___rarg), 1, 0);
return x_2;
}
}
obj* l_Fin_HasToString___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Fin_HasToString(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_UInt8_HasToString(uint8 x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean_uint8_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
obj* l_UInt8_HasToString___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_UInt8_HasToString(x_2);
return x_3;
}
}
obj* l_UInt16_HasToString(uint16 x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean_uint16_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
obj* l_UInt16_HasToString___boxed(obj* x_1) {
_start:
{
uint16 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_UInt16_HasToString(x_2);
return x_3;
}
}
obj* l_UInt32_HasToString(uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
obj* l_UInt32_HasToString___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_UInt32_HasToString(x_2);
return x_3;
}
}
obj* l_UInt64_HasToString(uint64 x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
obj* l_UInt64_HasToString___boxed(obj* x_1) {
_start:
{
uint64 x_2; obj* x_3; 
x_2 = lean::unbox_uint64(x_1);
lean::dec(x_1);
x_3 = l_UInt64_HasToString(x_2);
return x_3;
}
}
obj* l_USize_HasToString(usize x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean_usize_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
obj* l_USize_HasToString___boxed(obj* x_1) {
_start:
{
usize x_2; obj* x_3; 
x_2 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_3 = l_USize_HasToString(x_2);
return x_3;
}
}
obj* l_Option_HasToString___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_Option_HasRepr___rarg___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::apply_1(x_1, x_4);
x_6 = l_Option_HasRepr___rarg___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean::dec(x_5);
x_8 = l_Option_HasRepr___rarg___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
}
}
obj* l_Option_HasToString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_HasToString___rarg), 2, 0);
return x_2;
}
}
obj* l_Sum_HasToString___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = l_Sum_HasRepr___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean::dec(x_5);
x_8 = l_Option_HasRepr___rarg___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
lean::dec(x_3);
x_11 = lean::apply_1(x_2, x_10);
x_12 = l_Sum_HasRepr___rarg___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean::dec(x_11);
x_14 = l_Option_HasRepr___rarg___closed__3;
x_15 = lean_string_append(x_13, x_14);
return x_15;
}
}
}
obj* l_Sum_HasToString(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Sum_HasToString___rarg), 3, 0);
return x_3;
}
}
obj* l_Prod_HasToString___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
x_6 = lean::apply_1(x_1, x_4);
x_7 = l_Prod_HasRepr___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean::dec(x_6);
x_9 = l_List_reprAux___main___rarg___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean::apply_1(x_2, x_5);
x_12 = lean_string_append(x_10, x_11);
lean::dec(x_11);
x_13 = l_Option_HasRepr___rarg___closed__3;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
obj* l_Prod_HasToString(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Prod_HasToString___rarg), 3, 0);
return x_3;
}
}
obj* l_Sigma_HasToString___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
lean::inc(x_4);
x_6 = lean::apply_1(x_1, x_4);
x_7 = l_Sigma_HasRepr___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean::dec(x_6);
x_9 = l_List_reprAux___main___rarg___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean::apply_2(x_2, x_4, x_5);
x_12 = lean_string_append(x_10, x_11);
lean::dec(x_11);
x_13 = l_Sigma_HasRepr___rarg___closed__2;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
obj* l_Sigma_HasToString(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Sigma_HasToString___rarg), 3, 0);
return x_3;
}
}
obj* l_Sigma_HasToString___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Sigma_HasToString(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Subtype_HasToString___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_Subtype_HasToString(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Subtype_HasToString___rarg), 2, 0);
return x_3;
}
}
obj* l_Subtype_HasToString___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Subtype_HasToString(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* initialize_init_data_string_basic(obj*);
obj* initialize_init_data_uint(obj*);
obj* initialize_init_data_nat_div(obj*);
obj* initialize_init_data_repr(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_tostring(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_string_basic(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_nat_div(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_repr(w);
if (lean::io_result_is_error(w)) return w;
return w;
}
