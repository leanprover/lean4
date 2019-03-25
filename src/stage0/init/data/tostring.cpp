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
namespace lean {
obj* uint8_to_nat(uint8);
}
obj* l_List_toStringAux___rarg(obj*, uint8, obj*);
extern obj* l_Sum_HasRepr___rarg___closed__1;
obj* l_String_Iterator_remainingToString___main(obj*);
extern obj* l_Sigma_HasRepr___rarg___closed__1;
obj* l_UInt16_HasToString___boxed(obj*);
obj* l_Decidable_HasToString___rarg(uint8);
obj* l_Sigma_HasToString(obj*, obj*);
obj* l_List_toString___main(obj*);
obj* l_UInt32_HasToString___boxed(obj*);
obj* l_Sum_HasToString___boxed(obj*, obj*);
obj* l_List_toStringAux___rarg___boxed(obj*, obj*, obj*);
obj* l_Nat_HasToString(obj*);
obj* l_UInt8_HasToString(uint8);
obj* l_List_toStringAux___main___rarg(obj*, uint8, obj*);
obj* l_Subtype_HasToString___rarg(obj*, obj*);
namespace lean {
obj* uint16_to_nat(uint16);
}
obj* l_List_toString(obj*);
obj* l_Fin_HasToString___rarg(obj*);
obj* l_Bool_HasToString(uint8);
obj* l_List_toStringAux___main___rarg___boxed(obj*, obj*, obj*);
obj* l_UInt16_HasToString(uint16);
extern obj* l_Sum_HasRepr___rarg___closed__2;
obj* l_id_HasToString___boxed(obj*);
obj* l_Sum_HasToString(obj*, obj*);
obj* l_UInt64_HasToString(uint64);
obj* l_Option_HasToString___boxed(obj*);
extern obj* l_Bool_HasRepr___closed__2;
obj* l_id_HasToString(obj*);
obj* l_Substring_HasToString___boxed(obj*);
obj* l_UInt32_HasToString(uint32);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Prod_HasToString___boxed(obj*, obj*);
obj* l_Sigma_HasToString___rarg(obj*, obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Substring_HasToString(obj*);
obj* l_List_HasToString(obj*);
extern obj* l_List_repr___main___rarg___closed__3;
obj* l_Decidable_HasToString___boxed(obj*);
obj* l_List_toString___main___rarg(obj*, obj*);
extern obj* l_Option_HasRepr___rarg___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_id_HasToString___rarg(obj*);
extern obj* l_List_reprAux___main___rarg___closed__1;
obj* l_USize_HasToString___boxed(obj*);
obj* l_List_toString___rarg(obj*, obj*);
extern obj* l_Option_HasRepr___rarg___closed__3;
namespace lean {
obj* uint64_to_nat(uint64);
}
obj* l_Subtype_HasToString___boxed(obj*, obj*);
obj* l_String_HasToString___boxed(obj*);
extern obj* l_Option_HasRepr___rarg___closed__2;
extern obj* l_Prod_HasRepr___rarg___closed__1;
obj* l_Option_HasToString___rarg(obj*, obj*);
obj* l_Subtype_HasToString(obj*, obj*);
obj* l_List_toStringAux(obj*);
obj* l_List_HasToString___boxed(obj*);
obj* l_Option_HasToString(obj*);
obj* l_List_HasToString___rarg(obj*);
extern obj* l_Sigma_HasRepr___rarg___closed__2;
obj* l_String_Iterator_HasToString___boxed(obj*);
extern obj* l_List_repr___main___rarg___closed__1;
obj* l_UInt8_HasToString___boxed(obj*);
obj* l_Char_HasToString(uint32);
obj* l_List_toString___main___boxed(obj*);
obj* l_Sum_HasToString___rarg(obj*, obj*, obj*);
obj* l_Prod_HasToString___rarg(obj*, obj*, obj*);
obj* l_List_toStringAux___main(obj*);
obj* l_Unit_HasToString(obj*);
obj* l_Fin_HasToString(obj*);
obj* l_Fin_HasToString___boxed(obj*);
obj* l_String_HasToString(obj*);
obj* l_Decidable_HasToString___rarg___boxed(obj*);
namespace lean {
obj* string_utf8_extract(obj*, usize, usize);
}
obj* l_List_toStringAux___boxed(obj*);
obj* l_id_HasToString___rarg___boxed(obj*);
obj* l_Bool_HasToString___boxed(obj*);
obj* l_Prod_HasToString(obj*, obj*);
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_Unit_HasToString___boxed(obj*);
obj* l_Char_HasToString___boxed(obj*);
extern obj* l_List_repr___main___rarg___closed__2;
namespace lean {
obj* usize_to_nat(usize);
}
obj* l_Decidable_HasToString(obj*);
extern obj* l_Bool_HasRepr___closed__1;
obj* l_List_toString___boxed(obj*);
obj* l_Sigma_HasToString___boxed(obj*, obj*);
obj* l_String_Iterator_HasToString(obj*);
extern obj* l_Unit_HasRepr___closed__1;
obj* l_UInt64_HasToString___boxed(obj*);
obj* l_USize_HasToString(usize);
obj* l_List_toStringAux___main___boxed(obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_id_HasToString___rarg(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_id_HasToString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_HasToString___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_id_HasToString___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_id_HasToString___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_id_HasToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_id_HasToString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_HasToString(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_String_HasToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_HasToString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Substring_HasToString(obj* x_0) {
_start:
{
obj* x_1; usize x_2; usize x_3; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*1);
x_3 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
x_4 = lean::string_utf8_extract(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Substring_HasToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Substring_HasToString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_Iterator_HasToString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_remainingToString___main(x_0);
return x_1;
}
}
obj* l_String_Iterator_HasToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_HasToString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Bool_HasToString(uint8 x_0) {
_start:
{
if (x_0 == 0)
{
obj* x_1; 
x_1 = l_Bool_HasRepr___closed__1;
return x_1;
}
else
{
obj* x_2; 
x_2 = l_Bool_HasRepr___closed__2;
return x_2;
}
}
}
obj* l_Bool_HasToString___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_Bool_HasToString(x_1);
return x_2;
}
}
obj* l_Decidable_HasToString___rarg(uint8 x_0) {
_start:
{
if (x_0 == 0)
{
obj* x_1; 
x_1 = l_Bool_HasRepr___closed__1;
return x_1;
}
else
{
obj* x_2; 
x_2 = l_Bool_HasRepr___closed__2;
return x_2;
}
}
}
obj* l_Decidable_HasToString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Decidable_HasToString___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Decidable_HasToString___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_Decidable_HasToString___rarg(x_1);
return x_2;
}
}
obj* l_Decidable_HasToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Decidable_HasToString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_toStringAux___main___rarg(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_0);
x_4 = l_String_splitAux___main___closed__1;
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_0);
x_11 = lean::apply_1(x_0, x_5);
x_12 = l_List_reprAux___main___rarg___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = l_List_toStringAux___main___rarg(x_0, x_1, x_7);
x_16 = lean::string_append(x_13, x_15);
lean::dec(x_15);
return x_16;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_19; 
lean::dec(x_0);
x_19 = l_String_splitAux___main___closed__1;
return x_19;
}
else
{
obj* x_20; obj* x_22; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_2, 1);
lean::inc(x_22);
lean::dec(x_2);
lean::inc(x_0);
x_26 = lean::apply_1(x_0, x_20);
x_27 = 0;
x_28 = l_List_toStringAux___main___rarg(x_0, x_27, x_22);
x_29 = lean::string_append(x_26, x_28);
lean::dec(x_28);
return x_29;
}
}
}
}
obj* l_List_toStringAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toStringAux___main___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_List_toStringAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_List_toStringAux___main___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_List_toStringAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_toStringAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_toStringAux___rarg(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_toStringAux___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_List_toStringAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toStringAux___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_List_toStringAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_List_toStringAux___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_List_toStringAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_toStringAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_toString___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = l_List_repr___main___rarg___closed__1;
return x_3;
}
else
{
uint8 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_4 = 1;
x_5 = l_List_toStringAux___main___rarg(x_0, x_4, x_1);
x_6 = l_List_repr___main___rarg___closed__2;
x_7 = lean::string_append(x_6, x_5);
lean::dec(x_5);
x_9 = l_List_repr___main___rarg___closed__3;
x_10 = lean::string_append(x_7, x_9);
return x_10;
}
}
}
obj* l_List_toString___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toString___main___rarg), 2, 0);
return x_1;
}
}
obj* l_List_toString___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_toString___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_toString___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_toString___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_List_toString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toString___rarg), 2, 0);
return x_1;
}
}
obj* l_List_toString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_toString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_HasToString___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toString___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_List_HasToString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_HasToString___rarg), 1, 0);
return x_1;
}
}
obj* l_List_HasToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_HasToString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Unit_HasToString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Unit_HasRepr___closed__1;
return x_1;
}
}
obj* l_Unit_HasToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Unit_HasToString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Nat_HasToString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Nat_repr(x_0);
return x_1;
}
}
obj* l_Char_HasToString(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean::string_push(x_1, x_0);
return x_2;
}
}
obj* l_Char_HasToString___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Char_HasToString(x_1);
return x_2;
}
}
obj* l_Fin_HasToString___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Nat_repr(x_0);
return x_1;
}
}
obj* l_Fin_HasToString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Fin_HasToString___rarg), 1, 0);
return x_1;
}
}
obj* l_Fin_HasToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Fin_HasToString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_UInt8_HasToString(uint8 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::uint8_to_nat(x_0);
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
obj* l_UInt8_HasToString___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_UInt8_HasToString(x_1);
return x_2;
}
}
obj* l_UInt16_HasToString(uint16 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::uint16_to_nat(x_0);
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
obj* l_UInt16_HasToString___boxed(obj* x_0) {
_start:
{
uint16 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_UInt16_HasToString(x_1);
return x_2;
}
}
obj* l_UInt32_HasToString(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::uint32_to_nat(x_0);
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
obj* l_UInt32_HasToString___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_UInt32_HasToString(x_1);
return x_2;
}
}
obj* l_UInt64_HasToString(uint64 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::uint64_to_nat(x_0);
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
obj* l_UInt64_HasToString___boxed(obj* x_0) {
_start:
{
uint64 x_1; obj* x_2; 
x_1 = lean::unbox_uint64(x_0);
x_2 = l_UInt64_HasToString(x_1);
return x_2;
}
}
obj* l_USize_HasToString(usize x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::usize_to_nat(x_0);
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
obj* l_USize_HasToString___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = lean::unbox_size_t(x_0);
x_2 = l_USize_HasToString(x_1);
return x_2;
}
}
obj* l_Option_HasToString___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = l_Option_HasRepr___rarg___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::apply_1(x_0, x_4);
x_8 = l_Option_HasRepr___rarg___closed__2;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_11 = l_Option_HasRepr___rarg___closed__3;
x_12 = lean::string_append(x_9, x_11);
return x_12;
}
}
}
obj* l_Option_HasToString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_HasToString___rarg), 2, 0);
return x_1;
}
}
obj* l_Option_HasToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_HasToString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Sum_HasToString___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
x_8 = l_Sum_HasRepr___rarg___closed__1;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_11 = l_Option_HasRepr___rarg___closed__3;
x_12 = lean::string_append(x_9, x_11);
return x_12;
}
else
{
obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_0);
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_17 = lean::apply_1(x_1, x_14);
x_18 = l_Sum_HasRepr___rarg___closed__2;
x_19 = lean::string_append(x_18, x_17);
lean::dec(x_17);
x_21 = l_Option_HasRepr___rarg___closed__3;
x_22 = lean::string_append(x_19, x_21);
return x_22;
}
}
}
obj* l_Sum_HasToString(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Sum_HasToString___rarg), 3, 0);
return x_2;
}
}
obj* l_Sum_HasToString___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Sum_HasToString(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Prod_HasToString___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::apply_1(x_0, x_3);
x_9 = l_Prod_HasRepr___rarg___closed__1;
x_10 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_12 = l_List_reprAux___main___rarg___closed__1;
x_13 = lean::string_append(x_10, x_12);
x_14 = lean::apply_1(x_1, x_5);
x_15 = lean::string_append(x_13, x_14);
lean::dec(x_14);
x_17 = l_Option_HasRepr___rarg___closed__3;
x_18 = lean::string_append(x_15, x_17);
return x_18;
}
}
obj* l_Prod_HasToString(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Prod_HasToString___rarg), 3, 0);
return x_2;
}
}
obj* l_Prod_HasToString___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Prod_HasToString(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Sigma_HasToString___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_3);
x_9 = lean::apply_1(x_0, x_3);
x_10 = l_Sigma_HasRepr___rarg___closed__1;
x_11 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_13 = l_List_reprAux___main___rarg___closed__1;
x_14 = lean::string_append(x_11, x_13);
x_15 = lean::apply_2(x_1, x_3, x_5);
x_16 = lean::string_append(x_14, x_15);
lean::dec(x_15);
x_18 = l_Sigma_HasRepr___rarg___closed__2;
x_19 = lean::string_append(x_16, x_18);
return x_19;
}
}
obj* l_Sigma_HasToString(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Sigma_HasToString___rarg), 3, 0);
return x_2;
}
}
obj* l_Sigma_HasToString___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Sigma_HasToString(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Subtype_HasToString___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_Subtype_HasToString(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Subtype_HasToString___rarg), 2, 0);
return x_2;
}
}
obj* l_Subtype_HasToString___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Subtype_HasToString(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
if (io_result_is_error(w)) return w;
w = initialize_init_data_string_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_div(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_repr(w);
return w;
}
