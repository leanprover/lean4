// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Nat
// Imports: import Init.Data.Nat.Lemmas public import Init.Data.Range.Polymorphic.Instances import Init.Data.Nat.MinMax import Init.Omega import Init.RCases
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
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_PRange_instUpwardEnumerableNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instUpwardEnumerableNat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instUpwardEnumerableNat___closed__0 = (const lean_object*)&l_Std_PRange_instUpwardEnumerableNat___closed__0_value;
static const lean_closure_object l_Std_PRange_instUpwardEnumerableNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instUpwardEnumerableNat___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instUpwardEnumerableNat___closed__1 = (const lean_object*)&l_Std_PRange_instUpwardEnumerableNat___closed__1_value;
static const lean_ctor_object l_Std_PRange_instUpwardEnumerableNat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_PRange_instUpwardEnumerableNat___closed__0_value),((lean_object*)&l_Std_PRange_instUpwardEnumerableNat___closed__1_value)}};
static const lean_object* l_Std_PRange_instUpwardEnumerableNat___closed__2 = (const lean_object*)&l_Std_PRange_instUpwardEnumerableNat___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_PRange_instUpwardEnumerableNat = (const lean_object*)&l_Std_PRange_instUpwardEnumerableNat___closed__2_value;
static const lean_ctor_object l_Std_PRange_instLeast_x3fNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_PRange_instLeast_x3fNat___closed__0 = (const lean_object*)&l_Std_PRange_instLeast_x3fNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_PRange_instLeast_x3fNat = (const lean_object*)&l_Std_PRange_instLeast_x3fNat___closed__0_value;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_PRange_instHasSizeNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instHasSizeNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instHasSizeNat___closed__0 = (const lean_object*)&l_Std_PRange_instHasSizeNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_PRange_instHasSizeNat = (const lean_object*)&l_Std_PRange_instHasSizeNat___closed__0_value;
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_PRange_instHasSizeNat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instHasSizeNat__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instHasSizeNat__1___closed__0 = (const lean_object*)&l_Std_PRange_instHasSizeNat__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_PRange_instHasSizeNat__1 = (const lean_object*)&l_Std_PRange_instHasSizeNat__1___closed__0_value;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat = (const lean_object*)&l_Std_instHasRcoIntersectionNat___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat__1___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat__1 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat__2___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat__2 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__3___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat__3___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat__3___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat__3 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__3___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__4___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat__4___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat__4___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat__4 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__4___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__5___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat__5___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat__5___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat__5 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__5___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__6___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat__6___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat__6___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat__6 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__6___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__7___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__7___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat__7___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat__7___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__7___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat__7 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__7___closed__0_value;
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_PRange_instUpwardEnumerableNat___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_nat_add(x_2, x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PRange_instUpwardEnumerableNat___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_nat_sub(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PRange_instHasSizeNat___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_nat_sub(x_4, x_1);
lean_dec(x_4);
x_6 = lean_nat_sub(x_5, x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PRange_instHasSizeNat__1___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
x_15 = lean_nat_dec_le(x_14, x_5);
if (x_15 == 0)
{
lean_dec(x_5);
x_8 = x_14;
goto block_12;
}
else
{
lean_dec(x_14);
x_8 = x_5;
goto block_12;
}
block_12:
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_6);
if (x_9 == 0)
{
lean_object* x_10; 
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(0, 2, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_6);
lean_inc(x_4);
if (lean_is_scalar(x_7)) {
 x_11 = lean_alloc_ctor(0, 2, 0);
} else {
 x_11 = x_7;
}
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_instHasRcoIntersectionNat___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_15; uint8_t x_16; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_8 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_8);
x_16 = lean_nat_dec_le(x_15, x_5);
if (x_16 == 0)
{
lean_dec(x_5);
x_9 = x_15;
goto block_14;
}
else
{
lean_dec(x_15);
x_9 = x_5;
goto block_14;
}
block_14:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_nat_add(x_4, x_8);
x_11 = lean_nat_dec_le(x_10, x_6);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
if (lean_is_scalar(x_7)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_7;
}
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_6);
if (lean_is_scalar(x_7)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_7;
}
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_instHasRcoIntersectionNat__1___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_1, x_5);
x_7 = lean_nat_dec_le(x_6, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_dec(x_6);
return x_2;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = lean_nat_dec_le(x_11, x_8);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__2___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_instHasRcoIntersectionNat__2___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_13 = lean_nat_dec_le(x_3, x_5);
if (x_13 == 0)
{
lean_dec(x_5);
x_8 = x_3;
goto block_12;
}
else
{
lean_dec(x_3);
x_8 = x_5;
goto block_12;
}
block_12:
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(0, 2, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_6);
if (lean_is_scalar(x_7)) {
 x_11 = lean_alloc_ctor(0, 2, 0);
} else {
 x_11 = x_7;
}
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__4___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_15; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_15 = lean_nat_dec_le(x_3, x_5);
if (x_15 == 0)
{
lean_dec(x_5);
x_8 = x_3;
goto block_14;
}
else
{
lean_dec(x_3);
x_8 = x_5;
goto block_14;
}
block_14:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_dec_le(x_10, x_6);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
if (lean_is_scalar(x_7)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_7;
}
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_6);
if (lean_is_scalar(x_7)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_7;
}
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__5___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_le(x_1, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_dec(x_1);
return x_2;
}
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_nat_dec_le(x_1, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__6___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_le(x_1, x_4);
if (x_5 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_nat_dec_le(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_1);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__7___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_1, x_5);
x_7 = lean_nat_dec_le(x_6, x_4);
if (x_7 == 0)
{
lean_dec(x_6);
return x_2;
}
else
{
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_6);
return x_2;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = lean_nat_dec_le(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__7___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_instHasRcoIntersectionNat__7___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
