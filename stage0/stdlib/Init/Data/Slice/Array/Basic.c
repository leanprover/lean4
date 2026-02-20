// Lean compiler output
// Module: Init.Data.Slice.Array.Basic
// Imports: public import Init.Data.Array.Subarray public import Init.Data.Slice.Notation public import Init.Data.Range.Polymorphic.Nat
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__1___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__1___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__1___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__2___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__2___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__2___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__3___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__3___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__4___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__4___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__4___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__5___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__5___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__5___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__6___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__6___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__6___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__7___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__7___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__7___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__8___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__8___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__8___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__1___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__1___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__1___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__2___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__2___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__3___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__3___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__4___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__4___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__4___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__5___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__5___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__5___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__6___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__6___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__6___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__7___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__7___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__7___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__8___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__8___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
x_7 = l_Array_toSubarray___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableArrayNatSubarray___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Array_toSubarray___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableArrayNatSubarray__1___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_le(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Array_toSubarray___redArg(x_1, x_2, x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Array_toSubarray___redArg(x_1, x_3, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableArrayNatSubarray__2___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_3, x_5);
x_7 = lean_nat_add(x_4, x_5);
x_8 = l_Array_toSubarray___redArg(x_1, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instSliceableArrayNatSubarray__3___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableArrayNatSubarray__3___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_7 = l_Array_toSubarray___redArg(x_1, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableArrayNatSubarray__4___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
x_7 = lean_nat_dec_le(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Array_toSubarray___redArg(x_1, x_6, x_4);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = l_Array_toSubarray___redArg(x_1, x_3, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instSliceableArrayNatSubarray__5___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableArrayNatSubarray__5___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
x_6 = l_Array_toSubarray___redArg(x_1, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instSliceableArrayNatSubarray__6___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableArrayNatSubarray__6___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_toSubarray___redArg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableArrayNatSubarray__7___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = l_Array_toSubarray___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableArrayNatSubarray__8___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_21; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_sub(x_5, x_4);
lean_dec(x_5);
x_21 = lean_nat_dec_le(x_12, x_14);
if (x_21 == 0)
{
x_16 = x_12;
goto block_20;
}
else
{
x_16 = x_14;
goto block_20;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_nat_add(x_6, x_4);
x_9 = lean_nat_add(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
x_10 = l_Array_toSubarray___redArg(x_3, x_8, x_9);
return x_10;
}
block_20:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
x_19 = lean_nat_dec_le(x_18, x_15);
if (x_19 == 0)
{
lean_dec(x_18);
x_6 = x_16;
x_7 = x_15;
goto block_11;
}
else
{
lean_dec(x_15);
x_6 = x_16;
x_7 = x_18;
goto block_11;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instSliceableSubarrayNat___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableSubarrayNat___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_19; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_sub(x_5, x_4);
lean_dec(x_5);
x_19 = lean_nat_dec_le(x_12, x_14);
if (x_19 == 0)
{
x_16 = x_12;
goto block_18;
}
else
{
lean_dec(x_12);
x_16 = x_14;
goto block_18;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_9 = lean_nat_add(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
x_10 = l_Array_toSubarray___redArg(x_3, x_8, x_9);
return x_10;
}
block_18:
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_13, x_15);
if (x_17 == 0)
{
lean_dec(x_13);
x_6 = x_16;
x_7 = x_15;
goto block_11;
}
else
{
lean_dec(x_15);
x_6 = x_16;
x_7 = x_13;
goto block_11;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableSubarrayNat__1___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_sub(x_5, x_4);
lean_dec(x_5);
x_14 = lean_nat_dec_le(x_2, x_12);
if (x_14 == 0)
{
x_6 = x_2;
x_7 = x_13;
goto block_11;
}
else
{
x_6 = x_12;
x_7 = x_13;
goto block_11;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_nat_add(x_6, x_4);
x_9 = lean_nat_add(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
x_10 = l_Array_toSubarray___redArg(x_3, x_8, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instSliceableSubarrayNat__2___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableSubarrayNat__2___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_21; uint8_t x_22; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_sub(x_5, x_4);
lean_dec(x_5);
x_16 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_12, x_16);
x_22 = lean_nat_dec_le(x_21, x_14);
if (x_22 == 0)
{
x_17 = x_21;
goto block_20;
}
else
{
lean_dec(x_21);
x_17 = x_14;
goto block_20;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_9 = lean_nat_add(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
x_10 = l_Array_toSubarray___redArg(x_3, x_8, x_9);
return x_10;
}
block_20:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_nat_add(x_13, x_16);
x_19 = lean_nat_dec_le(x_18, x_15);
if (x_19 == 0)
{
lean_dec(x_18);
x_6 = x_17;
x_7 = x_15;
goto block_11;
}
else
{
lean_dec(x_15);
x_6 = x_17;
x_7 = x_18;
goto block_11;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instSliceableSubarrayNat__3___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableSubarrayNat__3___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_sub(x_5, x_4);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_12, x_19);
lean_dec(x_12);
x_21 = lean_nat_dec_le(x_20, x_14);
if (x_21 == 0)
{
x_16 = x_20;
goto block_18;
}
else
{
lean_dec(x_20);
x_16 = x_14;
goto block_18;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_9 = lean_nat_add(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
x_10 = l_Array_toSubarray___redArg(x_3, x_8, x_9);
return x_10;
}
block_18:
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_13, x_15);
if (x_17 == 0)
{
lean_dec(x_13);
x_6 = x_16;
x_7 = x_15;
goto block_11;
}
else
{
lean_dec(x_15);
x_6 = x_16;
x_7 = x_13;
goto block_11;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableSubarrayNat__4___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_sub(x_5, x_4);
lean_dec(x_5);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
x_16 = lean_nat_dec_le(x_15, x_12);
if (x_16 == 0)
{
x_6 = x_15;
x_7 = x_13;
goto block_11;
}
else
{
lean_dec(x_15);
x_6 = x_12;
x_7 = x_13;
goto block_11;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_9 = lean_nat_add(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
x_10 = l_Array_toSubarray___redArg(x_3, x_8, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instSliceableSubarrayNat__5___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableSubarrayNat__5___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_sub(x_5, x_4);
lean_dec(x_5);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
x_16 = lean_nat_dec_le(x_15, x_13);
if (x_16 == 0)
{
lean_dec(x_15);
x_6 = x_12;
x_7 = x_13;
goto block_11;
}
else
{
lean_dec(x_13);
x_6 = x_12;
x_7 = x_15;
goto block_11;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_nat_add(x_6, x_4);
x_9 = lean_nat_add(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
x_10 = l_Array_toSubarray___redArg(x_3, x_8, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instSliceableSubarrayNat__6___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableSubarrayNat__6___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_sub(x_5, x_4);
lean_dec(x_5);
x_14 = lean_nat_dec_le(x_2, x_13);
if (x_14 == 0)
{
lean_dec(x_2);
x_6 = x_12;
x_7 = x_13;
goto block_11;
}
else
{
lean_dec(x_13);
x_6 = x_12;
x_7 = x_2;
goto block_11;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_nat_add(x_6, x_4);
x_9 = lean_nat_add(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
x_10 = l_Array_toSubarray___redArg(x_3, x_8, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableSubarrayNat__7___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instSliceableSubarrayNat__8___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceableSubarrayNat__8___closed__0));
return x_2;
}
}
lean_object* initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Notation(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_Array_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
