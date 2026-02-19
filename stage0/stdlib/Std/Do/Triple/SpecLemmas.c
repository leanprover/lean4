// Lean compiler output
// Module: Std.Do.Triple.SpecLemmas
// Imports: public import Std.Do.Triple.Basic public import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic public import Init.Data.Slice.Array public import Init.Data.Iterators.Lemmas.Combinators.FilterMap public import Init.Data.Range import Init.Data.Iterators.Lemmas import Init.Data.List.Nat.Range import Init.Data.List.Nat.TakeDrop import Init.Data.List.Range import Init.Data.List.TakeDrop import Init.Data.Nat.Mod import Init.Data.Slice.Lemmas import Init.Omega public import Init.Data.String.Defs public import Init.Data.String.Iterate import Init.Data.String.Lemmas.Splits import Init.Data.String.Termination import Init.Data.String.Lemmas.Iterate
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_range_x27TR_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_toList(lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_toList___boxed(lean_object*);
lean_object* l_List_take___redArg(lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_at___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_at(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_begin___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_begin(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_end___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_end(lean_object*, lean_object*);
static const lean_string_object l_List_Cursor_current___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_List_Cursor_current___auto__1___closed__0 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__0_value;
static const lean_string_object l_List_Cursor_current___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_List_Cursor_current___auto__1___closed__1 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__1_value;
static const lean_string_object l_List_Cursor_current___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_List_Cursor_current___auto__1___closed__2 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__2_value;
static const lean_string_object l_List_Cursor_current___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_List_Cursor_current___auto__1___closed__3 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_Cursor_current___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_Cursor_current___auto__1___closed__4_value_aux_0),((lean_object*)&l_List_Cursor_current___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_Cursor_current___auto__1___closed__4_value_aux_1),((lean_object*)&l_List_Cursor_current___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_Cursor_current___auto__1___closed__4_value_aux_2),((lean_object*)&l_List_Cursor_current___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_List_Cursor_current___auto__1___closed__4 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_List_Cursor_current___auto__1___closed__5;
static const lean_string_object l_List_Cursor_current___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_List_Cursor_current___auto__1___closed__6 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__6_value;
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_Cursor_current___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_Cursor_current___auto__1___closed__7_value_aux_0),((lean_object*)&l_List_Cursor_current___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_Cursor_current___auto__1___closed__7_value_aux_1),((lean_object*)&l_List_Cursor_current___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_Cursor_current___auto__1___closed__7_value_aux_2),((lean_object*)&l_List_Cursor_current___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_List_Cursor_current___auto__1___closed__7 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__7_value;
static const lean_string_object l_List_Cursor_current___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_List_Cursor_current___auto__1___closed__8 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_Cursor_current___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_List_Cursor_current___auto__1___closed__9 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__9_value;
static const lean_string_object l_List_Cursor_current___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticGet_elem_tactic"};
static const lean_object* l_List_Cursor_current___auto__1___closed__10 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__10_value;
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_Cursor_current___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(141, 31, 109, 153, 11, 229, 201, 51)}};
static const lean_object* l_List_Cursor_current___auto__1___closed__11 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__11_value;
static const lean_string_object l_List_Cursor_current___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_tactic"};
static const lean_object* l_List_Cursor_current___auto__1___closed__12 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__12_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* l_List_Cursor_current___auto__1___closed__13;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_List_Cursor_current___auto__1___closed__14;
static lean_object* l_List_Cursor_current___auto__1___closed__15;
static lean_object* l_List_Cursor_current___auto__1___closed__16;
static lean_object* l_List_Cursor_current___auto__1___closed__17;
static lean_object* l_List_Cursor_current___auto__1___closed__18;
static lean_object* l_List_Cursor_current___auto__1___closed__19;
static lean_object* l_List_Cursor_current___auto__1___closed__20;
static lean_object* l_List_Cursor_current___auto__1___closed__21;
LEAN_EXPORT lean_object* l_List_Cursor_current___auto__1;
lean_object* l_List_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_current___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_current___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_current(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_current___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_tail___auto__1;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_tail___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_tail(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_tail___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_pos___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_pos___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_pos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_pos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_SPred_and(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_PostShape_args(lean_object*);
lean_object* l_Std_Do_SPred_pure___redArg(lean_object*);
lean_object* l_Std_Do_SPred_exists___redArg(lean_object*, lean_object*);
lean_object* l_Std_Do_SPred_or(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_nat_sub(x_3, x_2);
x_6 = lean_nat_add(x_5, x_4);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = lean_nat_div(x_8, x_4);
lean_dec(x_8);
x_10 = lean_nat_mul(x_4, x_9);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = l_List_range_x27TR_go(x_4, x_9, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_toList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Legacy_Range_toList(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_at___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_3 = l_List_take___redArg(x_2, x_1);
x_4 = l_List_drop___redArg(x_2, x_1);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_at(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_Cursor_at___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_begin___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_List_Cursor_at___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_begin(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_Cursor_at___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_end___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_List_lengthTR___redArg(x_1);
x_3 = l_List_Cursor_at___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_end(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_lengthTR___redArg(x_2);
x_4 = l_List_Cursor_at___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_Cursor_current___auto__1___closed__12));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_Cursor_current___auto__1___closed__13;
x_2 = l_List_Cursor_current___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_Cursor_current___auto__1___closed__14;
x_2 = ((lean_object*)(l_List_Cursor_current___auto__1___closed__11));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_Cursor_current___auto__1___closed__15;
x_2 = l_List_Cursor_current___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_Cursor_current___auto__1___closed__16;
x_2 = ((lean_object*)(l_List_Cursor_current___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_Cursor_current___auto__1___closed__17;
x_2 = l_List_Cursor_current___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_Cursor_current___auto__1___closed__18;
x_2 = ((lean_object*)(l_List_Cursor_current___auto__1___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_Cursor_current___auto__1___closed__19;
x_2 = l_List_Cursor_current___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_Cursor_current___auto__1___closed__20;
x_2 = ((lean_object*)(l_List_Cursor_current___auto__1___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1() {
_start:
{
lean_object* x_1; 
x_1 = l_List_Cursor_current___auto__1___closed__21;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_get___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_Cursor_current___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_Cursor_current___redArg(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_Cursor_current(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_List_Cursor_tail___auto__1() {
_start:
{
lean_object* x_1; 
x_1 = l_List_Cursor_current___auto__1___closed__21;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_tail___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = l_List_Cursor_current___redArg(x_1);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_List_appendTR___redArg(x_2, x_9);
if (lean_obj_tag(x_3) == 0)
{
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec_ref(x_3);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_List_appendTR___redArg(x_2, x_13);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec_ref(x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_List_Cursor_tail(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_Cursor_tail___redArg(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_tail___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_Cursor_tail(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_List_lengthTR___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_Cursor_pos___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_List_lengthTR___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_Cursor_pos(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_2(x_1, x_5, x_2);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Std_Do_SPred_and(x_3, x_4, x_6);
x_8 = l_Std_Do_SPred_and(x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Std_Do_PostShape_args(x_1);
lean_inc(x_8);
x_9 = l_Std_Do_SPred_pure___redArg(x_8);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_apply_2(x_3, x_6, x_7);
lean_inc(x_8);
x_12 = l_Std_Do_SPred_and(x_8, x_9, x_11);
lean_inc(x_8);
x_13 = l_Std_Do_SPred_exists___redArg(x_8, x_10);
x_14 = l_Std_Do_SPred_or(x_8, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Do_Invariant_withEarlyReturn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Std_Do_PostShape_args(x_1);
lean_inc(x_8);
x_9 = l_Std_Do_SPred_pure___redArg(x_8);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_apply_2(x_3, x_6, x_7);
lean_inc(x_8);
x_12 = l_Std_Do_SPred_and(x_8, x_9, x_11);
lean_inc(x_8);
x_13 = l_Std_Do_SPred_exists___redArg(x_8, x_10);
x_14 = l_Std_Do_SPred_or(x_8, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Do_StringInvariant_withEarlyReturn(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Do_StringSliceInvariant_withEarlyReturn(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
return x_8;
}
}
lean_object* initialize_Std_Do_Triple_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_Range(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Iterate(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_Triple_SpecLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_Cursor_current___auto__1___closed__5 = _init_l_List_Cursor_current___auto__1___closed__5();
lean_mark_persistent(l_List_Cursor_current___auto__1___closed__5);
l_List_Cursor_current___auto__1___closed__13 = _init_l_List_Cursor_current___auto__1___closed__13();
lean_mark_persistent(l_List_Cursor_current___auto__1___closed__13);
l_List_Cursor_current___auto__1___closed__14 = _init_l_List_Cursor_current___auto__1___closed__14();
lean_mark_persistent(l_List_Cursor_current___auto__1___closed__14);
l_List_Cursor_current___auto__1___closed__15 = _init_l_List_Cursor_current___auto__1___closed__15();
lean_mark_persistent(l_List_Cursor_current___auto__1___closed__15);
l_List_Cursor_current___auto__1___closed__16 = _init_l_List_Cursor_current___auto__1___closed__16();
lean_mark_persistent(l_List_Cursor_current___auto__1___closed__16);
l_List_Cursor_current___auto__1___closed__17 = _init_l_List_Cursor_current___auto__1___closed__17();
lean_mark_persistent(l_List_Cursor_current___auto__1___closed__17);
l_List_Cursor_current___auto__1___closed__18 = _init_l_List_Cursor_current___auto__1___closed__18();
lean_mark_persistent(l_List_Cursor_current___auto__1___closed__18);
l_List_Cursor_current___auto__1___closed__19 = _init_l_List_Cursor_current___auto__1___closed__19();
lean_mark_persistent(l_List_Cursor_current___auto__1___closed__19);
l_List_Cursor_current___auto__1___closed__20 = _init_l_List_Cursor_current___auto__1___closed__20();
lean_mark_persistent(l_List_Cursor_current___auto__1___closed__20);
l_List_Cursor_current___auto__1___closed__21 = _init_l_List_Cursor_current___auto__1___closed__21();
lean_mark_persistent(l_List_Cursor_current___auto__1___closed__21);
l_List_Cursor_current___auto__1 = _init_l_List_Cursor_current___auto__1();
lean_mark_persistent(l_List_Cursor_current___auto__1);
l_List_Cursor_tail___auto__1 = _init_l_List_Cursor_tail___auto__1();
lean_mark_persistent(l_List_Cursor_tail___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
