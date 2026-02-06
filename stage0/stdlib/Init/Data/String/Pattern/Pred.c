// Lean compiler output
// Module: Init.Data.String.Pattern.Pred
// Imports: public import Init.Data.String.Pattern.Basic import Init.Data.String.Termination public import Init.Data.String.Basic import Init.Omega public import Init.Data.String.Lemmas.IsEmpty import Init.Data.String.Lemmas.Order import Init.Data.Option.Lemmas
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharBoolDefaultForwardSearcher(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred(lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharPropDefaultForwardSearcherOfDecidablePred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharPropDefaultForwardSearcherOfDecidablePred___closed__0 = (const lean_object*)&l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharPropDefaultForwardSearcherOfDecidablePred___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharPropDefaultForwardSearcherOfDecidablePred(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharPropDefaultForwardSearcherOfDecidablePred___boxed(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharBoolDefaultBackwardSearcher(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred(lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharPropDefaultBackwardSearcherOfDecidablePred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharPropDefaultBackwardSearcherOfDecidablePred___closed__0 = (const lean_object*)&l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharPropDefaultBackwardSearcherOfDecidablePred___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharPropDefaultBackwardSearcherOfDecidablePred(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharPropDefaultBackwardSearcherOfDecidablePred___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_sub(x_5, x_4);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_3, x_4);
x_10 = lean_box_uint32(x_9);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_string_utf8_next_fast(x_3, x_4);
x_15 = lean_nat_sub(x_14, x_4);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec_ref(x_1);
x_17 = lean_box(0);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_string_utf8_get_fast(x_4, x_5);
x_7 = lean_box_uint32(x_6);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_string_utf8_next_fast(x_4, x_5);
x_12 = lean_nat_sub(x_11, x_5);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_sub(x_5, x_4);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_3, x_4);
x_10 = lean_box_uint32(x_9);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec_ref(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharBoolDefaultForwardSearcher(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_sub(x_5, x_4);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_3, x_4);
x_10 = lean_box_uint32(x_9);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_string_utf8_next_fast(x_3, x_4);
x_15 = lean_nat_sub(x_14, x_4);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec_ref(x_1);
x_17 = lean_box(0);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_string_utf8_get_fast(x_4, x_5);
x_7 = lean_box_uint32(x_6);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_string_utf8_next_fast(x_4, x_5);
x_12 = lean_nat_sub(x_11, x_5);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_sub(x_5, x_4);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_3, x_4);
x_10 = lean_box_uint32(x_9);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec_ref(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharPropOfDecidablePred___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharPropDefaultForwardSearcherOfDecidablePred(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharPropDefaultForwardSearcherOfDecidablePred___closed__0));
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharPropDefaultForwardSearcherOfDecidablePred___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharPropDefaultForwardSearcherOfDecidablePred(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_6, x_9);
lean_dec(x_6);
x_11 = l_String_Slice_Pos_prevAux_go___redArg(x_2, x_10);
x_12 = lean_nat_add(x_4, x_11);
x_13 = lean_string_utf8_get_fast(x_3, x_12);
lean_dec(x_12);
x_14 = lean_box_uint32(x_13);
x_15 = lean_apply_1(x_1, x_14);
x_16 = lean_unbox(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = l_String_Slice_Pos_prevAux_go___redArg(x_2, x_9);
x_11 = lean_nat_add(x_5, x_10);
x_12 = lean_string_utf8_get_fast(x_4, x_11);
lean_dec(x_11);
x_13 = lean_box_uint32(x_12);
x_14 = lean_apply_1(x_1, x_13);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_10);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_6, x_9);
lean_dec(x_6);
x_11 = l_String_Slice_Pos_prevAux_go___redArg(x_2, x_10);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_11);
x_13 = lean_string_utf8_get_fast(x_3, x_12);
lean_dec(x_12);
x_14 = lean_box_uint32(x_13);
x_15 = lean_apply_1(x_1, x_14);
x_16 = lean_unbox(x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharBoolDefaultBackwardSearcher(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_6, x_9);
lean_dec(x_6);
x_11 = l_String_Slice_Pos_prevAux_go___redArg(x_2, x_10);
x_12 = lean_nat_add(x_4, x_11);
x_13 = lean_string_utf8_get_fast(x_3, x_12);
lean_dec(x_12);
x_14 = lean_box_uint32(x_13);
x_15 = lean_apply_1(x_1, x_14);
x_16 = lean_unbox(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = l_String_Slice_Pos_prevAux_go___redArg(x_2, x_9);
x_11 = lean_nat_add(x_5, x_10);
x_12 = lean_string_utf8_get_fast(x_4, x_11);
lean_dec(x_11);
x_13 = lean_box_uint32(x_12);
x_14 = lean_apply_1(x_1, x_13);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_10);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_6, x_9);
lean_dec(x_6);
x_11 = l_String_Slice_Pos_prevAux_go___redArg(x_2, x_10);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_11);
x_13 = lean_string_utf8_get_fast(x_3, x_12);
lean_dec(x_12);
x_14 = lean_box_uint32(x_13);
x_15 = lean_apply_1(x_1, x_14);
x_16 = lean_unbox(x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharPropOfDecidablePred___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharPropDefaultBackwardSearcherOfDecidablePred(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharPropDefaultBackwardSearcherOfDecidablePred___closed__0));
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharPropDefaultBackwardSearcherOfDecidablePred___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharPropDefaultBackwardSearcherOfDecidablePred(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_String_Pattern_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Pattern_Pred(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
