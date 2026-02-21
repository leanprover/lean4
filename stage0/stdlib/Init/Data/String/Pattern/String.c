// Lean compiler output
// Module: Init.Data.String.Pattern.String
// Imports: public import Init.Data.String.Pattern.Basic public import Init.Data.Vector.Basic public import Init.Data.String.FindPos import Init.Data.String.Termination import Init.Data.String.Lemmas.FindPos import Init.ByCases import Init.Data.Array.Lemmas import Init.Data.Option.Lemmas import Init.Omega
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
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0 = (const lean_object*)&l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep(lean_object*);
lean_object* l_String_Slice_Pos_remainingBytes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_dropPrefix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_dropPrefix_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1(lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_dropSuffix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_dropSuffix_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_nat_add(x_6, x_4);
x_8 = lean_string_get_byte_fast(x_5, x_7);
x_9 = lean_uint8_dec_eq(x_8, x_2);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_4, x_12);
lean_dec(x_4);
x_14 = lean_array_fget_borrowed(x_3, x_13);
lean_dec(x_13);
lean_inc(x_14);
x_4 = x_14;
goto _start;
}
else
{
lean_dec(x_4);
return x_10;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(x_1, x_5, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(x_1, x_2, x_3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_sub(x_5, x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
return x_2;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_nat_add(x_4, x_6);
x_10 = lean_string_get_byte_fast(x_3, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_6, x_11);
x_13 = lean_array_fget_borrowed(x_2, x_12);
lean_dec(x_12);
lean_inc(x_13);
x_14 = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(x_1, x_10, x_2, x_13);
x_15 = lean_array_push(x_2, x_14);
x_2 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_sub(x_3, x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_empty_array_with_capacity(x_4);
lean_dec(x_4);
x_8 = lean_array_push(x_7, x_5);
x_9 = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(x_1, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_obj_once(&l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0, &l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0_once, _init_l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
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
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_2(x_2, x_5, lean_box(0));
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_apply_6(x_2, x_7, x_8, lean_box(0), x_9, x_10, lean_box(0));
return x_11;
}
default: 
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_sub(x_3, x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
x_8 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_5);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0));
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_nat_sub(x_4, x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
x_9 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec_ref(x_1);
x_10 = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_ForwardSliceSearcher_iter(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_n(x_4, 2);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_nat_sub(x_7, x_6);
x_9 = lean_nat_dec_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_ctor_set_tag(x_2, 1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_2);
lean_dec(x_4);
x_11 = lean_box(3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
lean_inc_n(x_13, 2);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_nat_sub(x_16, x_15);
x_18 = lean_nat_dec_eq(x_13, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
x_21 = lean_box(3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
}
}
case 1:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_nat_add(x_26, x_24);
x_28 = lean_string_utf8_next_fast(x_25, x_27);
lean_dec(x_27);
x_29 = lean_nat_sub(x_28, x_26);
lean_inc(x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_nat_add(x_34, x_32);
x_36 = lean_string_utf8_next_fast(x_33, x_35);
lean_dec(x_35);
x_37 = lean_nat_sub(x_36, x_34);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
case 2:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_ctor_get(x_2, 2);
x_45 = lean_ctor_get(x_2, 3);
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_42, 1);
x_48 = lean_ctor_get(x_42, 2);
x_49 = lean_ctor_get(x_1, 0);
x_50 = lean_ctor_get(x_1, 1);
x_51 = lean_ctor_get(x_1, 2);
x_52 = lean_nat_sub(x_44, x_45);
x_53 = lean_nat_sub(x_48, x_47);
x_54 = lean_nat_add(x_52, x_53);
x_55 = lean_nat_sub(x_51, x_50);
x_56 = lean_nat_dec_le(x_54, x_55);
lean_dec(x_54);
if (x_56 == 0)
{
uint8_t x_57; 
lean_dec(x_53);
lean_free_object(x_2);
lean_dec(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec_ref(x_42);
x_57 = lean_nat_dec_lt(x_52, x_55);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_52);
x_58 = lean_box(2);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = l_String_Slice_pos_x21(x_1, x_52);
lean_dec(x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
x_61 = lean_box(3);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; 
lean_dec(x_55);
x_63 = lean_nat_add(x_50, x_44);
x_64 = lean_string_get_byte_fast(x_49, x_63);
x_65 = lean_nat_add(x_47, x_45);
x_66 = lean_string_get_byte_fast(x_46, x_65);
x_67 = lean_uint8_dec_eq(x_64, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
lean_dec(x_53);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_nat_dec_eq(x_45, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_45, x_70);
lean_dec(x_45);
x_72 = lean_array_fget_borrowed(x_43, x_71);
lean_dec(x_71);
x_73 = lean_nat_dec_eq(x_72, x_68);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_inc(x_72);
x_74 = l_String_Slice_pos_x21(x_1, x_52);
lean_dec(x_52);
x_75 = lean_nat_sub(x_44, x_72);
x_76 = l_String_Slice_pos_x21(x_1, x_75);
lean_dec(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_2, 3, x_72);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_2);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = l_String_Slice_pos_x21(x_1, x_52);
lean_dec(x_52);
x_80 = l_String_Slice_posGE___redArg(x_1, x_44);
lean_inc(x_80);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_2, 3, x_68);
lean_ctor_set(x_2, 2, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_2);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_52);
lean_dec(x_45);
x_83 = l_String_Slice_pos_x21(x_1, x_44);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_add(x_44, x_84);
lean_dec(x_44);
x_86 = l_String_Slice_posGE___redArg(x_1, x_85);
lean_inc(x_86);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_2, 3, x_68);
lean_ctor_set(x_2, 2, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_2);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_52);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_add(x_44, x_89);
lean_dec(x_44);
x_91 = lean_nat_add(x_45, x_89);
lean_dec(x_45);
x_92 = lean_nat_dec_eq(x_91, x_53);
lean_dec(x_53);
if (x_92 == 0)
{
lean_object* x_93; 
lean_ctor_set(x_2, 3, x_91);
lean_ctor_set(x_2, 2, x_90);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_2);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_nat_sub(x_90, x_91);
lean_dec(x_91);
x_95 = l_String_Slice_pos_x21(x_1, x_94);
lean_dec(x_94);
x_96 = l_String_Slice_pos_x21(x_1, x_90);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_2, 3, x_98);
lean_ctor_set(x_2, 2, x_90);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_2);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_100 = lean_ctor_get(x_2, 0);
x_101 = lean_ctor_get(x_2, 1);
x_102 = lean_ctor_get(x_2, 2);
x_103 = lean_ctor_get(x_2, 3);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_2);
x_104 = lean_ctor_get(x_100, 0);
x_105 = lean_ctor_get(x_100, 1);
x_106 = lean_ctor_get(x_100, 2);
x_107 = lean_ctor_get(x_1, 0);
x_108 = lean_ctor_get(x_1, 1);
x_109 = lean_ctor_get(x_1, 2);
x_110 = lean_nat_sub(x_102, x_103);
x_111 = lean_nat_sub(x_106, x_105);
x_112 = lean_nat_add(x_110, x_111);
x_113 = lean_nat_sub(x_109, x_108);
x_114 = lean_nat_dec_le(x_112, x_113);
lean_dec(x_112);
if (x_114 == 0)
{
uint8_t x_115; 
lean_dec(x_111);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
x_115 = lean_nat_dec_lt(x_110, x_113);
if (x_115 == 0)
{
lean_object* x_116; 
lean_dec(x_113);
lean_dec(x_110);
x_116 = lean_box(2);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = l_String_Slice_pos_x21(x_1, x_110);
lean_dec(x_110);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_113);
x_119 = lean_box(3);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; uint8_t x_122; lean_object* x_123; uint8_t x_124; uint8_t x_125; 
lean_dec(x_113);
x_121 = lean_nat_add(x_108, x_102);
x_122 = lean_string_get_byte_fast(x_107, x_121);
x_123 = lean_nat_add(x_105, x_103);
x_124 = lean_string_get_byte_fast(x_104, x_123);
x_125 = lean_uint8_dec_eq(x_122, x_124);
if (x_125 == 0)
{
lean_object* x_126; uint8_t x_127; 
lean_dec(x_111);
x_126 = lean_unsigned_to_nat(0u);
x_127 = lean_nat_dec_eq(x_103, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_nat_sub(x_103, x_128);
lean_dec(x_103);
x_130 = lean_array_fget_borrowed(x_101, x_129);
lean_dec(x_129);
x_131 = lean_nat_dec_eq(x_130, x_126);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_inc(x_130);
x_132 = l_String_Slice_pos_x21(x_1, x_110);
lean_dec(x_110);
x_133 = lean_nat_sub(x_102, x_130);
x_134 = l_String_Slice_pos_x21(x_1, x_133);
lean_dec(x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_136, 0, x_100);
lean_ctor_set(x_136, 1, x_101);
lean_ctor_set(x_136, 2, x_102);
lean_ctor_set(x_136, 3, x_130);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = l_String_Slice_pos_x21(x_1, x_110);
lean_dec(x_110);
x_139 = l_String_Slice_posGE___redArg(x_1, x_102);
lean_inc(x_139);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_141, 0, x_100);
lean_ctor_set(x_141, 1, x_101);
lean_ctor_set(x_141, 2, x_139);
lean_ctor_set(x_141, 3, x_126);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_110);
lean_dec(x_103);
x_143 = l_String_Slice_pos_x21(x_1, x_102);
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_add(x_102, x_144);
lean_dec(x_102);
x_146 = l_String_Slice_posGE___redArg(x_1, x_145);
lean_inc(x_146);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_143);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_148, 0, x_100);
lean_ctor_set(x_148, 1, x_101);
lean_ctor_set(x_148, 2, x_146);
lean_ctor_set(x_148, 3, x_126);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_dec(x_110);
x_150 = lean_unsigned_to_nat(1u);
x_151 = lean_nat_add(x_102, x_150);
lean_dec(x_102);
x_152 = lean_nat_add(x_103, x_150);
lean_dec(x_103);
x_153 = lean_nat_dec_eq(x_152, x_111);
lean_dec(x_111);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_154, 0, x_100);
lean_ctor_set(x_154, 1, x_101);
lean_ctor_set(x_154, 2, x_151);
lean_ctor_set(x_154, 3, x_152);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_156 = lean_nat_sub(x_151, x_152);
lean_dec(x_152);
x_157 = l_String_Slice_pos_x21(x_1, x_156);
lean_dec(x_156);
x_158 = l_String_Slice_pos_x21(x_1, x_151);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_161, 0, x_100);
lean_ctor_set(x_161, 1, x_101);
lean_ctor_set(x_161, 2, x_151);
lean_ctor_set(x_161, 3, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_159);
return x_162;
}
}
}
}
}
default: 
{
lean_object* x_163; 
x_163 = lean_box(2);
return x_163;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_String_Slice_Pos_remainingBytes(x_1, x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_String_Slice_Pos_remainingBytes(x_1, x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
case 1:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = l_String_Slice_Pos_remainingBytes(x_1, x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_2, 0, x_17);
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_String_Slice_Pos_remainingBytes(x_1, x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_dec_ref(x_2);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
x_27 = lean_nat_sub(x_26, x_25);
x_28 = lean_nat_sub(x_27, x_23);
lean_dec(x_23);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
default: 
{
lean_object* x_31; 
x_31 = lean_box(0);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_2(x_3, x_8, lean_box(0));
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = lean_apply_6(x_4, x_10, x_11, lean_box(0), x_12, x_13, lean_box(0));
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_5, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_apply_3(x_1, x_6, lean_box(0), x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_apply_4(x_3, x_5, x_9, lean_box(0), lean_box(0));
return x_10;
}
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_apply_4(x_3, x_11, x_2, lean_box(0), lean_box(0));
return x_12;
}
default: 
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0), 4, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_7);
switch (lean_obj_tag(x_4)) {
case 0:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc_n(x_10, 2);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_nat_sub(x_13, x_12);
x_15 = lean_nat_dec_eq(x_10, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_ctor_set_tag(x_4, 1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_11);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_4);
lean_dec(x_10);
x_18 = lean_box(3);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
x_20 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
lean_inc_n(x_21, 2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_nat_sub(x_24, x_23);
x_26 = lean_nat_dec_eq(x_21, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
x_29 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_21);
x_30 = lean_box(3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_22);
x_32 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_31);
return x_32;
}
}
}
case 1:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_nat_add(x_36, x_34);
x_38 = lean_string_utf8_next_fast(x_35, x_37);
lean_dec(x_37);
x_39 = lean_nat_sub(x_38, x_36);
lean_inc(x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_4, 0);
lean_inc(x_43);
lean_dec(x_4);
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_nat_add(x_45, x_43);
x_47 = lean_string_utf8_next_fast(x_44, x_46);
lean_dec(x_46);
x_48 = lean_nat_sub(x_47, x_45);
lean_inc(x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_51);
return x_52;
}
}
case 2:
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_4);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_54 = lean_ctor_get(x_4, 0);
x_55 = lean_ctor_get(x_4, 1);
x_56 = lean_ctor_get(x_4, 2);
x_57 = lean_ctor_get(x_4, 3);
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
x_60 = lean_ctor_get(x_54, 2);
x_61 = lean_ctor_get(x_2, 0);
x_62 = lean_ctor_get(x_2, 1);
x_63 = lean_ctor_get(x_2, 2);
x_64 = lean_nat_sub(x_56, x_57);
x_65 = lean_nat_sub(x_60, x_59);
x_66 = lean_nat_add(x_64, x_65);
x_67 = lean_nat_sub(x_63, x_62);
x_68 = lean_nat_dec_le(x_66, x_67);
lean_dec(x_66);
if (x_68 == 0)
{
uint8_t x_69; 
lean_dec(x_65);
lean_free_object(x_4);
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
x_69 = lean_nat_dec_lt(x_64, x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_64);
x_70 = lean_box(2);
x_71 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = l_String_Slice_pos_x21(x_2, x_64);
lean_dec(x_64);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
x_74 = lean_box(3);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_75);
return x_76;
}
}
else
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; uint8_t x_80; uint8_t x_81; 
lean_dec(x_67);
x_77 = lean_nat_add(x_62, x_56);
x_78 = lean_string_get_byte_fast(x_61, x_77);
x_79 = lean_nat_add(x_59, x_57);
x_80 = lean_string_get_byte_fast(x_58, x_79);
x_81 = lean_uint8_dec_eq(x_78, x_80);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
lean_dec(x_65);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_nat_dec_eq(x_57, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_sub(x_57, x_84);
lean_dec(x_57);
x_86 = lean_array_fget_borrowed(x_55, x_85);
lean_dec(x_85);
x_87 = lean_nat_dec_eq(x_86, x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_inc(x_86);
x_88 = l_String_Slice_pos_x21(x_2, x_64);
lean_dec(x_64);
x_89 = lean_nat_sub(x_56, x_86);
x_90 = l_String_Slice_pos_x21(x_2, x_89);
lean_dec(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_4, 3, x_86);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_4);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = l_String_Slice_pos_x21(x_2, x_64);
lean_dec(x_64);
x_95 = l_String_Slice_posGE___redArg(x_2, x_56);
lean_inc(x_95);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_4, 3, x_82);
lean_ctor_set(x_4, 2, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_4);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_64);
lean_dec(x_57);
x_99 = l_String_Slice_pos_x21(x_2, x_56);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_add(x_56, x_100);
lean_dec(x_56);
x_102 = l_String_Slice_posGE___redArg(x_2, x_101);
lean_inc(x_102);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_4, 3, x_82);
lean_ctor_set(x_4, 2, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_4);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_104);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_64);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_56, x_106);
lean_dec(x_56);
x_108 = lean_nat_add(x_57, x_106);
lean_dec(x_57);
x_109 = lean_nat_dec_eq(x_108, x_65);
lean_dec(x_65);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_ctor_set(x_4, 3, x_108);
lean_ctor_set(x_4, 2, x_107);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_4);
x_111 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_112 = lean_nat_sub(x_107, x_108);
lean_dec(x_108);
x_113 = l_String_Slice_pos_x21(x_2, x_112);
lean_dec(x_112);
x_114 = l_String_Slice_pos_x21(x_2, x_107);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_4, 3, x_116);
lean_ctor_set(x_4, 2, x_107);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_4);
lean_ctor_set(x_117, 1, x_115);
x_118 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_117);
return x_118;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
x_121 = lean_ctor_get(x_4, 2);
x_122 = lean_ctor_get(x_4, 3);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_123 = lean_ctor_get(x_119, 0);
x_124 = lean_ctor_get(x_119, 1);
x_125 = lean_ctor_get(x_119, 2);
x_126 = lean_ctor_get(x_2, 0);
x_127 = lean_ctor_get(x_2, 1);
x_128 = lean_ctor_get(x_2, 2);
x_129 = lean_nat_sub(x_121, x_122);
x_130 = lean_nat_sub(x_125, x_124);
x_131 = lean_nat_add(x_129, x_130);
x_132 = lean_nat_sub(x_128, x_127);
x_133 = lean_nat_dec_le(x_131, x_132);
lean_dec(x_131);
if (x_133 == 0)
{
uint8_t x_134; 
lean_dec(x_130);
lean_dec(x_122);
lean_dec(x_121);
lean_dec_ref(x_120);
lean_dec_ref(x_119);
x_134 = lean_nat_dec_lt(x_129, x_132);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_132);
lean_dec(x_129);
x_135 = lean_box(2);
x_136 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_135);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = l_String_Slice_pos_x21(x_2, x_129);
lean_dec(x_129);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_132);
x_139 = lean_box(3);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_140);
return x_141;
}
}
else
{
lean_object* x_142; uint8_t x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; 
lean_dec(x_132);
x_142 = lean_nat_add(x_127, x_121);
x_143 = lean_string_get_byte_fast(x_126, x_142);
x_144 = lean_nat_add(x_124, x_122);
x_145 = lean_string_get_byte_fast(x_123, x_144);
x_146 = lean_uint8_dec_eq(x_143, x_145);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
lean_dec(x_130);
x_147 = lean_unsigned_to_nat(0u);
x_148 = lean_nat_dec_eq(x_122, x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_149 = lean_unsigned_to_nat(1u);
x_150 = lean_nat_sub(x_122, x_149);
lean_dec(x_122);
x_151 = lean_array_fget_borrowed(x_120, x_150);
lean_dec(x_150);
x_152 = lean_nat_dec_eq(x_151, x_147);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_inc(x_151);
x_153 = l_String_Slice_pos_x21(x_2, x_129);
lean_dec(x_129);
x_154 = lean_nat_sub(x_121, x_151);
x_155 = l_String_Slice_pos_x21(x_2, x_154);
lean_dec(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_157, 0, x_119);
lean_ctor_set(x_157, 1, x_120);
lean_ctor_set(x_157, 2, x_121);
lean_ctor_set(x_157, 3, x_151);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_158);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_160 = l_String_Slice_pos_x21(x_2, x_129);
lean_dec(x_129);
x_161 = l_String_Slice_posGE___redArg(x_2, x_121);
lean_inc(x_161);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_163, 0, x_119);
lean_ctor_set(x_163, 1, x_120);
lean_ctor_set(x_163, 2, x_161);
lean_ctor_set(x_163, 3, x_147);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_164);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_129);
lean_dec(x_122);
x_166 = l_String_Slice_pos_x21(x_2, x_121);
x_167 = lean_unsigned_to_nat(1u);
x_168 = lean_nat_add(x_121, x_167);
lean_dec(x_121);
x_169 = l_String_Slice_posGE___redArg(x_2, x_168);
lean_inc(x_169);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_166);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_171, 0, x_119);
lean_ctor_set(x_171, 1, x_120);
lean_ctor_set(x_171, 2, x_169);
lean_ctor_set(x_171, 3, x_147);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
x_173 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_172);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
lean_dec(x_129);
x_174 = lean_unsigned_to_nat(1u);
x_175 = lean_nat_add(x_121, x_174);
lean_dec(x_121);
x_176 = lean_nat_add(x_122, x_174);
lean_dec(x_122);
x_177 = lean_nat_dec_eq(x_176, x_130);
lean_dec(x_130);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_178, 0, x_119);
lean_ctor_set(x_178, 1, x_120);
lean_ctor_set(x_178, 2, x_175);
lean_ctor_set(x_178, 3, x_176);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_179);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_181 = lean_nat_sub(x_175, x_176);
lean_dec(x_176);
x_182 = l_String_Slice_pos_x21(x_2, x_181);
lean_dec(x_181);
x_183 = l_String_Slice_pos_x21(x_2, x_175);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_unsigned_to_nat(0u);
x_186 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_186, 0, x_119);
lean_ctor_set(x_186, 1, x_120);
lean_ctor_set(x_186, 2, x_175);
lean_ctor_set(x_186, 3, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_184);
x_188 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_187);
return x_188;
}
}
}
}
}
default: 
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_box(2);
x_190 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_189);
return x_190;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed), 7, 3);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
x_9 = l_WellFounded_opaqueFix_u2083___redArg(x_8, x_5, x_6, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_nat_sub(x_5, x_4);
x_10 = lean_nat_sub(x_8, x_7);
x_11 = lean_nat_dec_le(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_dec(x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_string_memcmp(x_6, x_3, x_7, x_4, x_9);
lean_dec(x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_dropPrefix_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_nat_sub(x_5, x_4);
x_10 = lean_nat_sub(x_8, x_7);
x_11 = lean_nat_dec_le(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_string_memcmp(x_6, x_3, x_7, x_4, x_9);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_String_Slice_pos_x21(x_2, x_9);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_dropPrefix_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_ForwardSliceSearcher_dropPrefix_x3f(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_nat_sub(x_6, x_5);
x_11 = lean_nat_sub(x_9, x_8);
x_12 = lean_nat_dec_le(x_10, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_box(0);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_string_memcmp(x_7, x_4, x_8, x_5, x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_String_Slice_pos_x21(x_2, x_10);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_dropPrefix_x3f___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
x_9 = lean_nat_sub(x_8, x_7);
x_10 = lean_nat_dec_le(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_string_memcmp(x_6, x_2, x_7, x_3, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_String_Slice_pos_x21(x_4, x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed), 5, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_inc_ref(x_5);
x_6 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_dropPrefix_x3f___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed), 2, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_nat_sub(x_5, x_4);
x_10 = lean_nat_sub(x_8, x_7);
x_11 = lean_nat_dec_le(x_9, x_10);
if (x_11 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_nat_sub(x_10, x_9);
lean_dec(x_10);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_12);
x_14 = lean_string_memcmp(x_6, x_3, x_13, x_4, x_9);
lean_dec(x_9);
lean_dec(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_dropSuffix_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_nat_sub(x_5, x_4);
x_10 = lean_nat_sub(x_8, x_7);
x_11 = lean_nat_dec_le(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_nat_sub(x_10, x_9);
lean_dec(x_10);
x_14 = lean_nat_add(x_7, x_13);
x_15 = lean_string_memcmp(x_6, x_3, x_14, x_4, x_9);
lean_dec(x_9);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_String_Slice_pos_x21(x_2, x_13);
lean_dec(x_13);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_dropSuffix_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_BackwardSliceSearcher_dropSuffix_x3f(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_nat_sub(x_6, x_5);
x_11 = lean_nat_sub(x_9, x_8);
x_12 = lean_nat_dec_le(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_nat_sub(x_11, x_10);
lean_dec(x_11);
x_15 = lean_nat_add(x_8, x_14);
x_16 = lean_string_memcmp(x_7, x_4, x_15, x_5, x_10);
lean_dec(x_10);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_String_Slice_pos_x21(x_2, x_14);
lean_dec(x_14);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_dropSuffix_x3f___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
x_9 = lean_nat_sub(x_8, x_7);
x_10 = lean_nat_dec_le(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_nat_sub(x_9, x_1);
lean_dec(x_9);
x_13 = lean_nat_add(x_7, x_12);
x_14 = lean_string_memcmp(x_6, x_2, x_13, x_3, x_1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_String_Slice_pos_x21(x_4, x_12);
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed), 5, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_inc_ref(x_5);
x_6 = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_dropSuffix_x3f___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed), 2, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
lean_object* initialize_Init_Data_String_Pattern_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Pattern_String(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
