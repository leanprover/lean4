// Lean compiler output
// Module: init.data.repr
// Imports: init.data.string.basic init.data.uint init.data.nat.div
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
obj* l_List_HasRepr(obj*);
obj* l_Nat_digitChar___boxed(obj*);
obj* l_Char_repr___boxed(obj*);
obj* l_Sum_HasRepr___rarg___closed__1;
obj* l_USize_HasRepr(usize);
obj* l_Fin_HasRepr___boxed(obj*);
obj* l_Substring_HasRepr___boxed(obj*);
obj* l_Decidable_HasRepr___rarg___boxed(obj*);
obj* l_UInt32_HasRepr(uint32);
obj* l_String_HasRepr;
obj* l_String_Iterator_remainingToString___main(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Sigma_HasRepr___rarg___closed__1;
obj* l_List_repr___rarg(obj*, obj*);
uint8 l_String_isEmpty(obj*);
obj* l_String_Iterator_HasRepr___boxed(obj*);
obj* l_charToHex(uint32);
obj* l_Substring_HasRepr(obj*);
obj* l_Subtype_HasRepr(obj*, obj*);
obj* l_Char_quoteCore___closed__3;
namespace lean {
obj* uint16_to_nat(uint16);
}
obj* l_List_reprAux___rarg___boxed(obj*, obj*, obj*);
obj* l_id_HasRepr___rarg___boxed(obj*);
obj* l_Sum_HasRepr___rarg___closed__2;
obj* l_List_reprAux___main___rarg(obj*, uint8, obj*);
obj* l_USize_HasRepr___boxed(obj*);
obj* l_String_quoteAux___main(obj*);
obj* l_List_repr___main(obj*);
obj* l_List_reprAux(obj*);
obj* l_Unit_HasRepr___boxed(obj*);
obj* l_charToHex___boxed(obj*);
obj* l_id_HasRepr(obj*);
obj* l_List_reprAux___rarg(obj*, uint8, obj*);
obj* l_Bool_HasRepr___closed__2;
obj* l_Char_quoteCore___closed__1;
obj* l_Nat_toDigitsCore___main___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Subtype_HasRepr___boxed(obj*, obj*);
obj* l_Nat_toDigitsCore(obj*, obj*, obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_String_quote___closed__1;
obj* l_Prod_HasRepr___rarg(obj*, obj*, obj*);
obj* l_Bool_HasRepr(uint8);
obj* l_Substring_HasRepr___closed__1;
obj* l_List_repr___main___rarg___closed__3;
obj* l_Nat_HasRepr;
obj* l_Decidable_HasRepr(obj*);
obj* l_Bool_HasRepr___boxed(obj*);
obj* l_Char_quoteCore___closed__2;
obj* l_Option_HasRepr___rarg___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Decidable_HasRepr___rarg(uint8);
obj* l_Fin_HasRepr___rarg(obj*);
obj* l_Sigma_HasRepr___rarg(obj*, obj*, obj*);
obj* l_String_quoteAux(obj*);
obj* l_List_reprAux___main___rarg___closed__1;
obj* l_List_reprAux___main___rarg___boxed(obj*, obj*, obj*);
obj* l_Sum_HasRepr___rarg(obj*, obj*, obj*);
obj* l_Option_HasRepr___rarg___closed__3;
namespace lean {
obj* uint64_to_nat(uint64);
}
obj* l_String_quote___closed__2;
namespace lean {
obj* nat_mod(obj*, obj*);
}
obj* l_Char_HasRepr___closed__1;
obj* l_List_reprAux___main(obj*);
obj* l_Option_HasRepr___rarg___closed__2;
obj* l_Char_quoteCore(uint32);
obj* l_Char_repr(uint32);
obj* l_Char_quoteCore___closed__5;
obj* l_id_HasRepr___rarg(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Option_HasRepr(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Prod_HasRepr___rarg___closed__1;
obj* l_Unit_HasRepr(obj*);
obj* l_Nat_toDigitsCore___main(obj*, obj*, obj*, obj*);
obj* l_Subtype_HasRepr___rarg(obj*, obj*);
obj* l_UInt64_HasRepr___boxed(obj*);
obj* l_hexDigitRepr(obj*);
uint8 l_UInt32_decEq(uint32, uint32);
obj* l_UInt16_HasRepr(uint16);
obj* l_Sigma_HasRepr(obj*, obj*);
obj* l_Sigma_HasRepr___rarg___closed__2;
obj* l_Char_quoteCore___boxed(obj*);
obj* l_Option_HasRepr___rarg(obj*, obj*);
obj* l_List_repr___main___rarg___closed__1;
namespace lean {
obj* string_data(obj*);
}
obj* l_Prod_HasRepr(obj*, obj*);
obj* l_Nat_toDigits___boxed(obj*, obj*);
obj* l_Sum_HasRepr(obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
obj* string_utf8_extract(obj*, obj*, obj*);
}
namespace lean {
obj* string_mk(obj*);
}
obj* l_Nat_toDigitsCore___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_Char_HasRepr(uint32);
obj* l_UInt16_HasRepr___boxed(obj*);
obj* l_UInt32_HasRepr___boxed(obj*);
namespace lean {
obj* uint32_to_nat(uint32);
}
uint32 l_Nat_digitChar(obj*);
obj* l_UInt64_HasRepr(uint64);
obj* l_String_quote(obj*);
obj* l_Char_HasRepr___boxed(obj*);
obj* l_List_repr___main___rarg___closed__2;
obj* l_Nat_toDigits(obj*, obj*);
namespace lean {
obj* usize_to_nat(usize);
}
obj* l_Sigma_HasRepr___boxed(obj*, obj*);
obj* l_String_Iterator_HasRepr___closed__1;
obj* l_Bool_HasRepr___closed__1;
obj* l_List_repr(obj*);
obj* l_List_HasRepr___rarg(obj*);
obj* l_hexDigitRepr___boxed(obj*);
obj* l_Fin_HasRepr(obj*);
obj* l_String_Iterator_HasRepr(obj*);
obj* l_List_repr___main___rarg(obj*, obj*);
obj* l_Unit_HasRepr___closed__1;
extern obj* l_String_splitAux___main___closed__1;
obj* l_Char_quoteCore___closed__4;
obj* l_id_HasRepr___rarg(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_id_HasRepr(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_id_HasRepr___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_id_HasRepr___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_id_HasRepr___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Bool_HasRepr___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("false");
return x_1;
}
}
obj* _init_l_Bool_HasRepr___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("true");
return x_1;
}
}
obj* l_Bool_HasRepr(uint8 x_1) {
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
obj* l_Bool_HasRepr___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Bool_HasRepr(x_2);
return x_3;
}
}
obj* l_Decidable_HasRepr___rarg(uint8 x_1) {
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
obj* l_Decidable_HasRepr(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Decidable_HasRepr___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Decidable_HasRepr___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Decidable_HasRepr___rarg(x_2);
return x_3;
}
}
obj* _init_l_List_reprAux___main___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(", ");
return x_1;
}
}
obj* l_List_reprAux___main___rarg(obj* x_1, uint8 x_2, obj* x_3) {
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
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_10 = l_List_reprAux___main___rarg(x_1, x_2, x_6);
x_11 = lean::string_append(x_9, x_10);
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
x_17 = l_List_reprAux___main___rarg(x_1, x_16, x_14);
x_18 = lean::string_append(x_15, x_17);
lean::dec(x_17);
return x_18;
}
}
}
}
obj* l_List_reprAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_reprAux___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_reprAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_List_reprAux___main___rarg(x_1, x_4, x_3);
return x_5;
}
}
obj* l_List_reprAux___rarg(obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_reprAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_reprAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_reprAux___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_reprAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_List_reprAux___rarg(x_1, x_4, x_3);
return x_5;
}
}
obj* _init_l_List_repr___main___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("[]");
return x_1;
}
}
obj* _init_l_List_repr___main___rarg___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("[");
return x_1;
}
}
obj* _init_l_List_repr___main___rarg___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("]");
return x_1;
}
}
obj* l_List_repr___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_List_repr___main___rarg___closed__1;
return x_3;
}
else
{
uint8 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = 1;
x_5 = l_List_reprAux___main___rarg(x_1, x_4, x_2);
x_6 = l_List_repr___main___rarg___closed__2;
x_7 = lean::string_append(x_6, x_5);
lean::dec(x_5);
x_8 = l_List_repr___main___rarg___closed__3;
x_9 = lean::string_append(x_7, x_8);
return x_9;
}
}
}
obj* l_List_repr___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_repr___main___rarg), 2, 0);
return x_2;
}
}
obj* l_List_repr___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_repr___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_repr(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_repr___rarg), 2, 0);
return x_2;
}
}
obj* l_List_HasRepr___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_repr___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_List_HasRepr(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_HasRepr___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_Unit_HasRepr___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("()");
return x_1;
}
}
obj* l_Unit_HasRepr(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Unit_HasRepr___closed__1;
return x_2;
}
}
obj* l_Unit_HasRepr___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Unit_HasRepr(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Option_HasRepr___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("none");
return x_1;
}
}
obj* _init_l_Option_HasRepr___rarg___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("(some ");
return x_1;
}
}
obj* _init_l_Option_HasRepr___rarg___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(")");
return x_1;
}
}
obj* l_Option_HasRepr___rarg(obj* x_1, obj* x_2) {
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
x_7 = lean::string_append(x_6, x_5);
lean::dec(x_5);
x_8 = l_Option_HasRepr___rarg___closed__3;
x_9 = lean::string_append(x_7, x_8);
return x_9;
}
}
}
obj* l_Option_HasRepr(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_HasRepr___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Sum_HasRepr___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("(inl ");
return x_1;
}
}
obj* _init_l_Sum_HasRepr___rarg___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("(inr ");
return x_1;
}
}
obj* l_Sum_HasRepr___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
x_7 = lean::string_append(x_6, x_5);
lean::dec(x_5);
x_8 = l_Option_HasRepr___rarg___closed__3;
x_9 = lean::string_append(x_7, x_8);
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
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_14 = l_Option_HasRepr___rarg___closed__3;
x_15 = lean::string_append(x_13, x_14);
return x_15;
}
}
}
obj* l_Sum_HasRepr(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Sum_HasRepr___rarg), 3, 0);
return x_3;
}
}
obj* _init_l_Prod_HasRepr___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("(");
return x_1;
}
}
obj* l_Prod_HasRepr___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_9 = l_List_reprAux___main___rarg___closed__1;
x_10 = lean::string_append(x_8, x_9);
x_11 = lean::apply_1(x_2, x_5);
x_12 = lean::string_append(x_10, x_11);
lean::dec(x_11);
x_13 = l_Option_HasRepr___rarg___closed__3;
x_14 = lean::string_append(x_12, x_13);
return x_14;
}
}
obj* l_Prod_HasRepr(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Prod_HasRepr___rarg), 3, 0);
return x_3;
}
}
obj* _init_l_Sigma_HasRepr___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("⟨");
return x_1;
}
}
obj* _init_l_Sigma_HasRepr___rarg___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("⟩");
return x_1;
}
}
obj* l_Sigma_HasRepr___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_9 = l_List_reprAux___main___rarg___closed__1;
x_10 = lean::string_append(x_8, x_9);
x_11 = lean::apply_2(x_2, x_4, x_5);
x_12 = lean::string_append(x_10, x_11);
lean::dec(x_11);
x_13 = l_Sigma_HasRepr___rarg___closed__2;
x_14 = lean::string_append(x_12, x_13);
return x_14;
}
}
obj* l_Sigma_HasRepr(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Sigma_HasRepr___rarg), 3, 0);
return x_3;
}
}
obj* l_Sigma_HasRepr___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Sigma_HasRepr(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Subtype_HasRepr___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_Subtype_HasRepr(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Subtype_HasRepr___rarg), 2, 0);
return x_3;
}
}
obj* l_Subtype_HasRepr___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Subtype_HasRepr(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
uint32 l_Nat_digitChar(obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(2u);
x_7 = lean::nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(3u);
x_9 = lean::nat_dec_eq(x_1, x_8);
if (x_9 == 0)
{
obj* x_10; uint8 x_11; 
x_10 = lean::mk_nat_obj(4u);
x_11 = lean::nat_dec_eq(x_1, x_10);
if (x_11 == 0)
{
obj* x_12; uint8 x_13; 
x_12 = lean::mk_nat_obj(5u);
x_13 = lean::nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
obj* x_14; uint8 x_15; 
x_14 = lean::mk_nat_obj(6u);
x_15 = lean::nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
obj* x_16; uint8 x_17; 
x_16 = lean::mk_nat_obj(7u);
x_17 = lean::nat_dec_eq(x_1, x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
x_18 = lean::mk_nat_obj(8u);
x_19 = lean::nat_dec_eq(x_1, x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = lean::mk_nat_obj(9u);
x_21 = lean::nat_dec_eq(x_1, x_20);
if (x_21 == 0)
{
obj* x_22; uint8 x_23; 
x_22 = lean::mk_nat_obj(10u);
x_23 = lean::nat_dec_eq(x_1, x_22);
if (x_23 == 0)
{
obj* x_24; uint8 x_25; 
x_24 = lean::mk_nat_obj(11u);
x_25 = lean::nat_dec_eq(x_1, x_24);
if (x_25 == 0)
{
obj* x_26; uint8 x_27; 
x_26 = lean::mk_nat_obj(12u);
x_27 = lean::nat_dec_eq(x_1, x_26);
if (x_27 == 0)
{
obj* x_28; uint8 x_29; 
x_28 = lean::mk_nat_obj(13u);
x_29 = lean::nat_dec_eq(x_1, x_28);
if (x_29 == 0)
{
obj* x_30; uint8 x_31; 
x_30 = lean::mk_nat_obj(14u);
x_31 = lean::nat_dec_eq(x_1, x_30);
if (x_31 == 0)
{
obj* x_32; uint8 x_33; 
x_32 = lean::mk_nat_obj(15u);
x_33 = lean::nat_dec_eq(x_1, x_32);
if (x_33 == 0)
{
uint32 x_34; 
x_34 = 42;
return x_34;
}
else
{
uint32 x_35; 
x_35 = 102;
return x_35;
}
}
else
{
uint32 x_36; 
x_36 = 101;
return x_36;
}
}
else
{
uint32 x_37; 
x_37 = 100;
return x_37;
}
}
else
{
uint32 x_38; 
x_38 = 99;
return x_38;
}
}
else
{
uint32 x_39; 
x_39 = 98;
return x_39;
}
}
else
{
uint32 x_40; 
x_40 = 97;
return x_40;
}
}
else
{
uint32 x_41; 
x_41 = 57;
return x_41;
}
}
else
{
uint32 x_42; 
x_42 = 56;
return x_42;
}
}
else
{
uint32 x_43; 
x_43 = 55;
return x_43;
}
}
else
{
uint32 x_44; 
x_44 = 54;
return x_44;
}
}
else
{
uint32 x_45; 
x_45 = 53;
return x_45;
}
}
else
{
uint32 x_46; 
x_46 = 52;
return x_46;
}
}
else
{
uint32 x_47; 
x_47 = 51;
return x_47;
}
}
else
{
uint32 x_48; 
x_48 = 50;
return x_48;
}
}
else
{
uint32 x_49; 
x_49 = 49;
return x_49;
}
}
else
{
uint32 x_50; 
x_50 = 48;
return x_50;
}
}
}
obj* l_Nat_digitChar___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = l_Nat_digitChar(x_1);
lean::dec(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
obj* l_Nat_toDigitsCore___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; uint32 x_10; obj* x_11; uint8 x_12; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_9 = lean::nat_mod(x_3, x_1);
x_10 = l_Nat_digitChar(x_9);
lean::dec(x_9);
x_11 = lean::nat_div(x_3, x_1);
lean::dec(x_3);
x_12 = lean::nat_dec_eq(x_11, x_5);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::box_uint32(x_10);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_4);
x_2 = x_8;
x_3 = x_11;
x_4 = x_14;
goto _start;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_11);
lean::dec(x_8);
x_16 = lean::box_uint32(x_10);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_4);
return x_17;
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
}
obj* l_Nat_toDigitsCore___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Nat_toDigitsCore___main(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Nat_toDigitsCore(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Nat_toDigitsCore___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Nat_toDigitsCore___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Nat_toDigitsCore(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Nat_toDigits(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_add(x_2, x_3);
x_5 = lean::box(0);
x_6 = l_Nat_toDigitsCore___main(x_1, x_4, x_2, x_5);
return x_6;
}
}
obj* l_Nat_toDigits___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_toDigits(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Nat_repr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(10u);
x_3 = l_Nat_toDigits(x_2, x_1);
x_4 = lean::string_mk(x_3);
return x_4;
}
}
obj* _init_l_Nat_HasRepr() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_repr), 1, 0);
return x_1;
}
}
obj* l_hexDigitRepr(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; obj* x_4; 
x_2 = l_Nat_digitChar(x_1);
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean::string_push(x_3, x_2);
return x_4;
}
}
obj* l_hexDigitRepr___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hexDigitRepr(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_charToHex(uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::uint32_to_nat(x_1);
x_3 = lean::mk_nat_obj(16u);
x_4 = lean::nat_div(x_2, x_3);
x_5 = lean::nat_mod(x_2, x_3);
lean::dec(x_2);
x_6 = l_hexDigitRepr(x_4);
lean::dec(x_4);
x_7 = l_hexDigitRepr(x_5);
lean::dec(x_5);
x_8 = lean::string_append(x_6, x_7);
lean::dec(x_7);
return x_8;
}
}
obj* l_charToHex___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_charToHex(x_2);
return x_3;
}
}
obj* _init_l_Char_quoteCore___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("\\x");
return x_1;
}
}
obj* _init_l_Char_quoteCore___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("\\\"");
return x_1;
}
}
obj* _init_l_Char_quoteCore___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("\\\\");
return x_1;
}
}
obj* _init_l_Char_quoteCore___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("\\t");
return x_1;
}
}
obj* _init_l_Char_quoteCore___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("\\n");
return x_1;
}
}
obj* l_Char_quoteCore(uint32 x_1) {
_start:
{
uint32 x_2; uint8 x_3; 
x_2 = 10;
x_3 = x_1 == x_2;
if (x_3 == 0)
{
uint32 x_4; uint8 x_5; 
x_4 = 9;
x_5 = x_1 == x_4;
if (x_5 == 0)
{
uint32 x_6; uint8 x_7; 
x_6 = 92;
x_7 = x_1 == x_6;
if (x_7 == 0)
{
uint32 x_8; uint8 x_9; 
x_8 = 34;
x_9 = x_1 == x_8;
if (x_9 == 0)
{
obj* x_10; obj* x_11; uint8 x_12; 
x_10 = lean::uint32_to_nat(x_1);
x_11 = lean::mk_nat_obj(31u);
x_12 = lean::nat_dec_le(x_10, x_11);
lean::dec(x_10);
if (x_12 == 0)
{
uint32 x_13; uint8 x_14; 
x_13 = 127;
x_14 = x_1 == x_13;
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = l_String_splitAux___main___closed__1;
x_16 = lean::string_push(x_15, x_1);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = l_charToHex(x_1);
x_18 = l_Char_quoteCore___closed__1;
x_19 = lean::string_append(x_18, x_17);
lean::dec(x_17);
return x_19;
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
x_20 = l_charToHex(x_1);
x_21 = l_Char_quoteCore___closed__1;
x_22 = lean::string_append(x_21, x_20);
lean::dec(x_20);
return x_22;
}
}
else
{
obj* x_23; 
x_23 = l_Char_quoteCore___closed__2;
return x_23;
}
}
else
{
obj* x_24; 
x_24 = l_Char_quoteCore___closed__3;
return x_24;
}
}
else
{
obj* x_25; 
x_25 = l_Char_quoteCore___closed__4;
return x_25;
}
}
else
{
obj* x_26; 
x_26 = l_Char_quoteCore___closed__5;
return x_26;
}
}
}
obj* l_Char_quoteCore___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_quoteCore(x_2);
return x_3;
}
}
obj* _init_l_Char_HasRepr___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("'");
return x_1;
}
}
obj* l_Char_HasRepr(uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Char_quoteCore(x_1);
x_3 = l_Char_HasRepr___closed__1;
x_4 = lean::string_append(x_3, x_2);
lean::dec(x_2);
x_5 = lean::string_append(x_4, x_3);
return x_5;
}
}
obj* l_Char_HasRepr___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_HasRepr(x_2);
return x_3;
}
}
obj* l_String_quoteAux___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_String_splitAux___main___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_4; uint32 x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_6 = l_Char_quoteCore(x_5);
x_7 = l_String_quoteAux___main(x_4);
x_8 = lean::string_append(x_6, x_7);
lean::dec(x_7);
return x_8;
}
}
}
obj* l_String_quoteAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_quoteAux___main(x_1);
return x_2;
}
}
obj* _init_l_String_quote___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("\"");
return x_1;
}
}
obj* _init_l_String_quote___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("\"\"");
return x_1;
}
}
obj* l_String_quote(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_String_isEmpty(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::string_data(x_1);
x_4 = l_String_quoteAux___main(x_3);
x_5 = l_String_quote___closed__1;
x_6 = lean::string_append(x_5, x_4);
lean::dec(x_4);
x_7 = lean::string_append(x_6, x_5);
return x_7;
}
else
{
obj* x_8; 
lean::dec(x_1);
x_8 = l_String_quote___closed__2;
return x_8;
}
}
}
obj* _init_l_String_HasRepr() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_String_quote), 1, 0);
return x_1;
}
}
obj* _init_l_Substring_HasRepr___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(".toSubstring");
return x_1;
}
}
obj* l_Substring_HasRepr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::string_utf8_extract(x_2, x_3, x_4);
x_6 = l_String_quote(x_5);
x_7 = l_Substring_HasRepr___closed__1;
x_8 = lean::string_append(x_6, x_7);
return x_8;
}
}
obj* l_Substring_HasRepr___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_HasRepr(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_String_Iterator_HasRepr___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(".mkIterator");
return x_1;
}
}
obj* l_String_Iterator_HasRepr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_Iterator_remainingToString___main(x_1);
x_3 = l_String_quote(x_2);
x_4 = l_String_Iterator_HasRepr___closed__1;
x_5 = lean::string_append(x_3, x_4);
return x_5;
}
}
obj* l_String_Iterator_HasRepr___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_HasRepr(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Fin_HasRepr___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
obj* l_Fin_HasRepr(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Fin_HasRepr___rarg), 1, 0);
return x_2;
}
}
obj* l_Fin_HasRepr___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Fin_HasRepr(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_UInt16_HasRepr(uint16 x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::uint16_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
obj* l_UInt16_HasRepr___boxed(obj* x_1) {
_start:
{
uint16 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_UInt16_HasRepr(x_2);
return x_3;
}
}
obj* l_UInt32_HasRepr(uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::uint32_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
obj* l_UInt32_HasRepr___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_UInt32_HasRepr(x_2);
return x_3;
}
}
obj* l_UInt64_HasRepr(uint64 x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::uint64_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
obj* l_UInt64_HasRepr___boxed(obj* x_1) {
_start:
{
uint64 x_2; obj* x_3; 
x_2 = lean::unbox_uint64(x_1);
lean::dec(x_1);
x_3 = l_UInt64_HasRepr(x_2);
return x_3;
}
}
obj* l_USize_HasRepr(usize x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::usize_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
obj* l_USize_HasRepr___boxed(obj* x_1) {
_start:
{
usize x_2; obj* x_3; 
x_2 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_3 = l_USize_HasRepr(x_2);
return x_3;
}
}
obj* l_Char_repr(uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Char_quoteCore(x_1);
x_3 = l_Char_HasRepr___closed__1;
x_4 = lean::string_append(x_3, x_2);
lean::dec(x_2);
x_5 = lean::string_append(x_4, x_3);
return x_5;
}
}
obj* l_Char_repr___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_repr(x_2);
return x_3;
}
}
obj* initialize_init_data_string_basic(obj*);
obj* initialize_init_data_uint(obj*);
obj* initialize_init_data_nat_div(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_repr(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_string_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_div(w);
if (io_result_is_error(w)) return w;
l_Bool_HasRepr___closed__1 = _init_l_Bool_HasRepr___closed__1();
lean::mark_persistent(l_Bool_HasRepr___closed__1);
l_Bool_HasRepr___closed__2 = _init_l_Bool_HasRepr___closed__2();
lean::mark_persistent(l_Bool_HasRepr___closed__2);
l_List_reprAux___main___rarg___closed__1 = _init_l_List_reprAux___main___rarg___closed__1();
lean::mark_persistent(l_List_reprAux___main___rarg___closed__1);
l_List_repr___main___rarg___closed__1 = _init_l_List_repr___main___rarg___closed__1();
lean::mark_persistent(l_List_repr___main___rarg___closed__1);
l_List_repr___main___rarg___closed__2 = _init_l_List_repr___main___rarg___closed__2();
lean::mark_persistent(l_List_repr___main___rarg___closed__2);
l_List_repr___main___rarg___closed__3 = _init_l_List_repr___main___rarg___closed__3();
lean::mark_persistent(l_List_repr___main___rarg___closed__3);
l_Unit_HasRepr___closed__1 = _init_l_Unit_HasRepr___closed__1();
lean::mark_persistent(l_Unit_HasRepr___closed__1);
l_Option_HasRepr___rarg___closed__1 = _init_l_Option_HasRepr___rarg___closed__1();
lean::mark_persistent(l_Option_HasRepr___rarg___closed__1);
l_Option_HasRepr___rarg___closed__2 = _init_l_Option_HasRepr___rarg___closed__2();
lean::mark_persistent(l_Option_HasRepr___rarg___closed__2);
l_Option_HasRepr___rarg___closed__3 = _init_l_Option_HasRepr___rarg___closed__3();
lean::mark_persistent(l_Option_HasRepr___rarg___closed__3);
l_Sum_HasRepr___rarg___closed__1 = _init_l_Sum_HasRepr___rarg___closed__1();
lean::mark_persistent(l_Sum_HasRepr___rarg___closed__1);
l_Sum_HasRepr___rarg___closed__2 = _init_l_Sum_HasRepr___rarg___closed__2();
lean::mark_persistent(l_Sum_HasRepr___rarg___closed__2);
l_Prod_HasRepr___rarg___closed__1 = _init_l_Prod_HasRepr___rarg___closed__1();
lean::mark_persistent(l_Prod_HasRepr___rarg___closed__1);
l_Sigma_HasRepr___rarg___closed__1 = _init_l_Sigma_HasRepr___rarg___closed__1();
lean::mark_persistent(l_Sigma_HasRepr___rarg___closed__1);
l_Sigma_HasRepr___rarg___closed__2 = _init_l_Sigma_HasRepr___rarg___closed__2();
lean::mark_persistent(l_Sigma_HasRepr___rarg___closed__2);
l_Nat_HasRepr = _init_l_Nat_HasRepr();
lean::mark_persistent(l_Nat_HasRepr);
l_Char_quoteCore___closed__1 = _init_l_Char_quoteCore___closed__1();
lean::mark_persistent(l_Char_quoteCore___closed__1);
l_Char_quoteCore___closed__2 = _init_l_Char_quoteCore___closed__2();
lean::mark_persistent(l_Char_quoteCore___closed__2);
l_Char_quoteCore___closed__3 = _init_l_Char_quoteCore___closed__3();
lean::mark_persistent(l_Char_quoteCore___closed__3);
l_Char_quoteCore___closed__4 = _init_l_Char_quoteCore___closed__4();
lean::mark_persistent(l_Char_quoteCore___closed__4);
l_Char_quoteCore___closed__5 = _init_l_Char_quoteCore___closed__5();
lean::mark_persistent(l_Char_quoteCore___closed__5);
l_Char_HasRepr___closed__1 = _init_l_Char_HasRepr___closed__1();
lean::mark_persistent(l_Char_HasRepr___closed__1);
l_String_quote___closed__1 = _init_l_String_quote___closed__1();
lean::mark_persistent(l_String_quote___closed__1);
l_String_quote___closed__2 = _init_l_String_quote___closed__2();
lean::mark_persistent(l_String_quote___closed__2);
l_String_HasRepr = _init_l_String_HasRepr();
lean::mark_persistent(l_String_HasRepr);
l_Substring_HasRepr___closed__1 = _init_l_Substring_HasRepr___closed__1();
lean::mark_persistent(l_Substring_HasRepr___closed__1);
l_String_Iterator_HasRepr___closed__1 = _init_l_String_Iterator_HasRepr___closed__1();
lean::mark_persistent(l_String_Iterator_HasRepr___closed__1);
return w;
}
