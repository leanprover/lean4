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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_22; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
x_7 = x_2;
x_8 = x_22;
goto block_21;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_9; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
x_20 = lean_nat_dec_le(x_19, x_5);
if (x_20 == 0)
{
lean_dec(x_5);
x_9 = x_19;
goto block_17;
}
else
{
lean_dec(x_19);
x_9 = x_5;
goto block_17;
}
block_17:
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_4, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_9);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_6);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_6);
lean_inc(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 0, x_9);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_4);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_23; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
x_7 = x_2;
x_8 = x_23;
goto block_22;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_9; lean_object* x_10; lean_object* x_20; uint8_t x_21; 
x_9 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_3, x_9);
x_21 = lean_nat_dec_le(x_20, x_5);
if (x_21 == 0)
{
lean_dec(x_5);
x_10 = x_20;
goto block_19;
}
else
{
lean_dec(x_20);
x_10 = x_5;
goto block_19;
}
block_19:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_nat_add(x_4, x_9);
x_12 = lean_nat_dec_le(x_11, x_6);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_10);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_6);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; 
lean_dec(x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_11);
lean_ctor_set(x_7, 0, x_10);
x_16 = x_7;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_11);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_17; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
x_5 = x_2;
x_6 = x_17;
goto block_16;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = lean_nat_dec_le(x_8, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_10 = x_5;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_4);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
else
{
lean_object* x_13; 
lean_dec(x_8);
if (x_6 == 0)
{
x_13 = x_5;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_4);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_20; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
x_7 = x_2;
x_8 = x_20;
goto block_19;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_9; uint8_t x_18; 
x_18 = lean_nat_dec_le(x_3, x_5);
if (x_18 == 0)
{
lean_dec(x_5);
x_9 = x_3;
goto block_17;
}
else
{
lean_dec(x_3);
x_9 = x_5;
goto block_17;
}
block_17:
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_4, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_9);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_6);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 0, x_9);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_4);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__4___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_22; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
x_7 = x_2;
x_8 = x_22;
goto block_21;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_9; uint8_t x_20; 
x_20 = lean_nat_dec_le(x_3, x_5);
if (x_20 == 0)
{
lean_dec(x_5);
x_9 = x_3;
goto block_19;
}
else
{
lean_dec(x_3);
x_9 = x_5;
goto block_19;
}
block_19:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_dec_le(x_11, x_6);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_9);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_6);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; 
lean_dec(x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_11);
lean_ctor_set(x_7, 0, x_9);
x_16 = x_7;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_11);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__5___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_15; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
x_5 = x_2;
x_6 = x_15;
goto block_14;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_15;
goto block_14;
}
block_14:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_1, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_1);
x_8 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_4);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
else
{
lean_object* x_11; 
lean_dec(x_1);
if (x_6 == 0)
{
x_11 = x_5;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__6___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_15; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
x_5 = x_2;
x_6 = x_15;
goto block_14;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_15;
goto block_14;
}
block_14:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_1, x_4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
if (x_6 == 0)
{
x_8 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
else
{
lean_object* x_11; 
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_1);
x_11 = x_5;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_1);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__7___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_17; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
x_5 = x_2;
x_6 = x_17;
goto block_16;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = lean_nat_dec_le(x_8, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
if (x_6 == 0)
{
x_10 = x_5;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_4);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
else
{
lean_object* x_13; 
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_8);
x_13 = x_5;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_8);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
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
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Instances(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = initialize_Init_Data_Nat_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Instances(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_Nat(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_Nat(builtin);
}
#ifdef __cplusplus
}
#endif
