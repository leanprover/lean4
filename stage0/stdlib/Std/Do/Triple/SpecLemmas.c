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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Std_Do_PostShape_args(lean_object*);
lean_object* l_Std_Do_SPred_pure___redArg(lean_object*);
lean_object* l_Std_Do_SPred_and(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_SPred_exists___redArg(lean_object*, lean_object*);
lean_object* l_Std_Do_SPred_or(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_take___redArg(lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_range_x27TR_go(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_toList(lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_toList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_at___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_at(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_begin___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_begin(lean_object*, lean_object*);
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
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_Cursor_current___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_Cursor_current___auto__1___closed__4_value_aux_0),((lean_object*)&l_List_Cursor_current___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_Cursor_current___auto__1___closed__4_value_aux_1),((lean_object*)&l_List_Cursor_current___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_Cursor_current___auto__1___closed__4_value_aux_2),((lean_object*)&l_List_Cursor_current___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_List_Cursor_current___auto__1___closed__4 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__4_value;
static const lean_array_object l_List_Cursor_current___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_Cursor_current___auto__1___closed__5 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__5_value;
static const lean_string_object l_List_Cursor_current___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_List_Cursor_current___auto__1___closed__6 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__6_value;
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_Cursor_current___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_Cursor_current___auto__1___closed__7_value_aux_0),((lean_object*)&l_List_Cursor_current___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_Cursor_current___auto__1___closed__7_value_aux_1),((lean_object*)&l_List_Cursor_current___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_Cursor_current___auto__1___closed__7_value_aux_2),((lean_object*)&l_List_Cursor_current___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_List_Cursor_current___auto__1___closed__7 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__7_value;
static const lean_string_object l_List_Cursor_current___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_List_Cursor_current___auto__1___closed__8 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__8_value;
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_Cursor_current___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_List_Cursor_current___auto__1___closed__9 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__9_value;
static const lean_string_object l_List_Cursor_current___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticGet_elem_tactic"};
static const lean_object* l_List_Cursor_current___auto__1___closed__10 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__10_value;
static const lean_ctor_object l_List_Cursor_current___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_Cursor_current___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(141, 31, 109, 153, 11, 229, 201, 51)}};
static const lean_object* l_List_Cursor_current___auto__1___closed__11 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__11_value;
static const lean_string_object l_List_Cursor_current___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_tactic"};
static const lean_object* l_List_Cursor_current___auto__1___closed__12 = (const lean_object*)&l_List_Cursor_current___auto__1___closed__12_value;
static lean_once_cell_t l_List_Cursor_current___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_Cursor_current___auto__1___closed__13;
static lean_once_cell_t l_List_Cursor_current___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_Cursor_current___auto__1___closed__14;
static lean_once_cell_t l_List_Cursor_current___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_Cursor_current___auto__1___closed__15;
static lean_once_cell_t l_List_Cursor_current___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_Cursor_current___auto__1___closed__16;
static lean_once_cell_t l_List_Cursor_current___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_Cursor_current___auto__1___closed__17;
static lean_once_cell_t l_List_Cursor_current___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_Cursor_current___auto__1___closed__18;
static lean_once_cell_t l_List_Cursor_current___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_Cursor_current___auto__1___closed__19;
static lean_once_cell_t l_List_Cursor_current___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_Cursor_current___auto__1___closed__20;
static lean_once_cell_t l_List_Cursor_current___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_Cursor_current___auto__1___closed__21;
LEAN_EXPORT lean_object* l_List_Cursor_current___auto__1;
LEAN_EXPORT lean_object* l_List_Cursor_current___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_current___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_current(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_current___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_tail___auto__1;
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
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_toList(lean_object* v_r_1_){
_start:
{
lean_object* v_start_2_; lean_object* v_stop_3_; lean_object* v_step_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v_start_2_ = lean_ctor_get(v_r_1_, 0);
v_stop_3_ = lean_ctor_get(v_r_1_, 1);
v_step_4_ = lean_ctor_get(v_r_1_, 2);
v___x_5_ = lean_nat_sub(v_stop_3_, v_start_2_);
v___x_6_ = lean_nat_add(v___x_5_, v_step_4_);
lean_dec(v___x_5_);
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_sub(v___x_6_, v___x_7_);
lean_dec(v___x_6_);
v___x_9_ = lean_nat_div(v___x_8_, v_step_4_);
lean_dec(v___x_8_);
v___x_10_ = lean_nat_mul(v_step_4_, v___x_9_);
v___x_11_ = lean_nat_add(v_start_2_, v___x_10_);
lean_dec(v___x_10_);
v___x_12_ = lean_box(0);
v___x_13_ = l_List_range_x27TR_go(v_step_4_, v___x_9_, v___x_11_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_toList___boxed(lean_object* v_r_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Std_Legacy_Range_toList(v_r_14_);
lean_dec_ref(v_r_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_at___redArg(lean_object* v_l_16_, lean_object* v_n_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
lean_inc(v_l_16_);
v___x_18_ = l_List_take___redArg(v_n_17_, v_l_16_);
v___x_19_ = l_List_drop___redArg(v_n_17_, v_l_16_);
lean_dec(v_l_16_);
v___x_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_20_, 0, v___x_18_);
lean_ctor_set(v___x_20_, 1, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_at(lean_object* v_00_u03b1_21_, lean_object* v_l_22_, lean_object* v_n_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_List_Cursor_at___redArg(v_l_22_, v_n_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_begin___redArg(lean_object* v_l_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = l_List_Cursor_at___redArg(v_l_25_, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_begin(lean_object* v_00_u03b1_28_, lean_object* v_l_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = l_List_Cursor_at___redArg(v_l_29_, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_end___redArg(lean_object* v_l_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = l_List_lengthTR___redArg(v_l_32_);
v___x_34_ = l_List_Cursor_at___redArg(v_l_32_, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_end(lean_object* v_00_u03b1_35_, lean_object* v_l_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = l_List_lengthTR___redArg(v_l_36_);
v___x_38_ = l_List_Cursor_at___redArg(v_l_36_, v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__13(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__12));
v___x_64_ = l_Lean_mkAtom(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__14(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__13, &l_List_Cursor_current___auto__1___closed__13_once, _init_l_List_Cursor_current___auto__1___closed__13);
v___x_66_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__5));
v___x_67_ = lean_array_push(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__15(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__14, &l_List_Cursor_current___auto__1___closed__14_once, _init_l_List_Cursor_current___auto__1___closed__14);
v___x_69_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__11));
v___x_70_ = lean_box(2);
v___x_71_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__16(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__15, &l_List_Cursor_current___auto__1___closed__15_once, _init_l_List_Cursor_current___auto__1___closed__15);
v___x_73_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__5));
v___x_74_ = lean_array_push(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__17(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_75_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__16, &l_List_Cursor_current___auto__1___closed__16_once, _init_l_List_Cursor_current___auto__1___closed__16);
v___x_76_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__9));
v___x_77_ = lean_box(2);
v___x_78_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_76_);
lean_ctor_set(v___x_78_, 2, v___x_75_);
return v___x_78_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__18(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__17, &l_List_Cursor_current___auto__1___closed__17_once, _init_l_List_Cursor_current___auto__1___closed__17);
v___x_80_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__5));
v___x_81_ = lean_array_push(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__19(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__18, &l_List_Cursor_current___auto__1___closed__18_once, _init_l_List_Cursor_current___auto__1___closed__18);
v___x_83_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__7));
v___x_84_ = lean_box(2);
v___x_85_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_83_);
lean_ctor_set(v___x_85_, 2, v___x_82_);
return v___x_85_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__20(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__19, &l_List_Cursor_current___auto__1___closed__19_once, _init_l_List_Cursor_current___auto__1___closed__19);
v___x_87_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__5));
v___x_88_ = lean_array_push(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__21(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__20, &l_List_Cursor_current___auto__1___closed__20_once, _init_l_List_Cursor_current___auto__1___closed__20);
v___x_90_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__4));
v___x_91_ = lean_box(2);
v___x_92_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v___x_90_);
lean_ctor_set(v___x_92_, 2, v___x_89_);
return v___x_92_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1(void){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__21, &l_List_Cursor_current___auto__1___closed__21_once, _init_l_List_Cursor_current___auto__1___closed__21);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current___redArg(lean_object* v_c_94_){
_start:
{
lean_object* v_suffix_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_suffix_95_ = lean_ctor_get(v_c_94_, 1);
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = l_List_get___redArg(v_suffix_95_, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current___redArg___boxed(lean_object* v_c_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_List_Cursor_current___redArg(v_c_98_);
lean_dec_ref(v_c_98_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current(lean_object* v_00_u03b1_100_, lean_object* v_l_101_, lean_object* v_c_102_, lean_object* v_h_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_List_Cursor_current___redArg(v_c_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current___boxed(lean_object* v_00_u03b1_105_, lean_object* v_l_106_, lean_object* v_c_107_, lean_object* v_h_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_List_Cursor_current(v_00_u03b1_105_, v_l_106_, v_c_107_, v_h_108_);
lean_dec_ref(v_c_107_);
lean_dec(v_l_106_);
return v_res_109_;
}
}
static lean_object* _init_l_List_Cursor_tail___auto__1(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__21, &l_List_Cursor_current___auto__1___closed__21_once, _init_l_List_Cursor_current___auto__1___closed__21);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_tail___redArg(lean_object* v_s_111_){
_start:
{
lean_object* v_prefix_112_; lean_object* v_suffix_113_; lean_object* v___x_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_128_; 
v_prefix_112_ = lean_ctor_get(v_s_111_, 0);
lean_inc(v_prefix_112_);
v_suffix_113_ = lean_ctor_get(v_s_111_, 1);
lean_inc(v_suffix_113_);
v___x_114_ = l_List_Cursor_current___redArg(v_s_111_);
v_isSharedCheck_128_ = !lean_is_exclusive(v_s_111_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; lean_object* v_unused_130_; 
v_unused_129_ = lean_ctor_get(v_s_111_, 1);
lean_dec(v_unused_129_);
v_unused_130_ = lean_ctor_get(v_s_111_, 0);
lean_dec(v_unused_130_);
v___x_116_ = v_s_111_;
v_isShared_117_ = v_isSharedCheck_128_;
goto v_resetjp_115_;
}
else
{
lean_dec(v_s_111_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_128_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_box(0);
v___x_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_114_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = l_List_appendTR___redArg(v_prefix_112_, v___x_119_);
if (lean_obj_tag(v_suffix_113_) == 0)
{
lean_object* v___x_122_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_120_);
v___x_122_ = v___x_116_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_suffix_113_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
else
{
lean_object* v_tail_124_; lean_object* v___x_126_; 
v_tail_124_ = lean_ctor_get(v_suffix_113_, 1);
lean_inc(v_tail_124_);
lean_dec_ref(v_suffix_113_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v_tail_124_);
lean_ctor_set(v___x_116_, 0, v___x_120_);
v___x_126_ = v___x_116_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_tail_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_Cursor_tail(lean_object* v_00_u03b1_131_, lean_object* v_l_132_, lean_object* v_s_133_, lean_object* v_h_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_List_Cursor_tail___redArg(v_s_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_tail___boxed(lean_object* v_00_u03b1_136_, lean_object* v_l_137_, lean_object* v_s_138_, lean_object* v_h_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_List_Cursor_tail(v_00_u03b1_136_, v_l_137_, v_s_138_, v_h_139_);
lean_dec(v_l_137_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos___redArg(lean_object* v_c_141_){
_start:
{
lean_object* v_prefix_142_; lean_object* v___x_143_; 
v_prefix_142_ = lean_ctor_get(v_c_141_, 0);
v___x_143_ = l_List_lengthTR___redArg(v_prefix_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos___redArg___boxed(lean_object* v_c_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_List_Cursor_pos___redArg(v_c_144_);
lean_dec_ref(v_c_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos(lean_object* v_00_u03b1_146_, lean_object* v_l_147_, lean_object* v_c_148_){
_start:
{
lean_object* v_prefix_149_; lean_object* v___x_150_; 
v_prefix_149_ = lean_ctor_get(v_c_148_, 0);
v___x_150_ = l_List_lengthTR___redArg(v_prefix_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos___boxed(lean_object* v_00_u03b1_151_, lean_object* v_l_152_, lean_object* v_c_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_List_Cursor_pos(v_00_u03b1_151_, v_l_152_, v_c_153_);
lean_dec_ref(v_c_153_);
lean_dec(v_l_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(lean_object* v_x_155_, lean_object* v_h__1_156_, lean_object* v_h__2_157_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_159_; 
lean_dec(v_h__1_156_);
v_a_158_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_a_158_);
lean_dec_ref(v_x_155_);
v___x_159_ = lean_apply_1(v_h__2_157_, v_a_158_);
return v___x_159_;
}
else
{
lean_object* v_a_160_; lean_object* v___x_161_; 
lean_dec(v_h__2_157_);
v_a_160_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_a_160_);
lean_dec_ref(v_x_155_);
v___x_161_ = lean_apply_1(v_h__1_156_, v_a_160_);
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter(lean_object* v_00_u03b1_162_, lean_object* v_00_u03b5_163_, lean_object* v_motive_164_, lean_object* v_x_165_, lean_object* v_h__1_166_, lean_object* v_h__2_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(v_x_165_, v_h__1_166_, v_h__2_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object* v_x_169_, lean_object* v_h__1_170_, lean_object* v_h__2_171_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec(v_h__1_170_);
v___x_172_ = lean_box(0);
v___x_173_ = lean_apply_1(v_h__2_171_, v___x_172_);
return v___x_173_;
}
else
{
lean_object* v_val_174_; lean_object* v___x_175_; 
lean_dec(v_h__2_171_);
v_val_174_ = lean_ctor_get(v_x_169_, 0);
lean_inc(v_val_174_);
lean_dec_ref(v_x_169_);
v___x_175_ = lean_apply_1(v_h__1_170_, v_val_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object* v_00_u03b1_176_, lean_object* v_motive_177_, lean_object* v_x_178_, lean_object* v_h__1_179_, lean_object* v_h__2_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(v_x_178_, v_h__1_179_, v_h__2_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0(lean_object* v_onReturn_182_, lean_object* v_snd_183_, lean_object* v___x_184_, lean_object* v___x_185_, lean_object* v_r_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_apply_2(v_onReturn_182_, v_r_186_, v_snd_183_);
lean_inc(v___x_185_);
lean_inc(v___x_184_);
v___x_188_ = l_Std_Do_SPred_and(v___x_184_, v___x_185_, v___x_187_);
v___x_189_ = l_Std_Do_SPred_and(v___x_184_, v___x_185_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1(lean_object* v_ps_190_, lean_object* v_onReturn_191_, lean_object* v_onContinue_192_, lean_object* v_x_193_){
_start:
{
lean_object* v_snd_194_; lean_object* v_fst_195_; lean_object* v_snd_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_snd_194_ = lean_ctor_get(v_x_193_, 1);
lean_inc(v_snd_194_);
v_fst_195_ = lean_ctor_get(v_x_193_, 0);
lean_inc(v_fst_195_);
lean_dec_ref(v_x_193_);
v_snd_196_ = lean_ctor_get(v_snd_194_, 1);
lean_inc(v_snd_196_);
lean_dec(v_snd_194_);
v___x_197_ = l_Std_Do_PostShape_args(v_ps_190_);
lean_inc(v___x_197_);
v___x_198_ = l_Std_Do_SPred_pure___redArg(v___x_197_);
lean_inc(v___x_198_);
lean_inc(v___x_197_);
lean_inc(v_snd_196_);
v___f_199_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_199_, 0, v_onReturn_191_);
lean_closure_set(v___f_199_, 1, v_snd_196_);
lean_closure_set(v___f_199_, 2, v___x_197_);
lean_closure_set(v___f_199_, 3, v___x_198_);
v___x_200_ = lean_apply_2(v_onContinue_192_, v_fst_195_, v_snd_196_);
lean_inc(v___x_197_);
v___x_201_ = l_Std_Do_SPred_and(v___x_197_, v___x_198_, v___x_200_);
lean_inc(v___x_197_);
v___x_202_ = l_Std_Do_SPred_exists___redArg(v___x_197_, v___f_199_);
v___x_203_ = l_Std_Do_SPred_or(v___x_197_, v___x_201_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed(lean_object* v_ps_204_, lean_object* v_onReturn_205_, lean_object* v_onContinue_206_, lean_object* v_x_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1(v_ps_204_, v_onReturn_205_, v_onContinue_206_, v_x_207_);
lean_dec(v_ps_204_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg(lean_object* v_ps_209_, lean_object* v_onContinue_210_, lean_object* v_onReturn_211_, lean_object* v_onExcept_212_){
_start:
{
lean_object* v___f_213_; lean_object* v___x_214_; 
v___f_213_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_213_, 0, v_ps_209_);
lean_closure_set(v___f_213_, 1, v_onReturn_211_);
lean_closure_set(v___f_213_, 2, v_onContinue_210_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___f_213_);
lean_ctor_set(v___x_214_, 1, v_onExcept_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn(lean_object* v_00_u03b2_215_, lean_object* v_ps_216_, lean_object* v_00_u03b1_217_, lean_object* v_xs_218_, lean_object* v_00_u03b3_219_, lean_object* v_onContinue_220_, lean_object* v_onReturn_221_, lean_object* v_onExcept_222_){
_start:
{
lean_object* v___f_223_; lean_object* v___x_224_; 
v___f_223_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_223_, 0, v_ps_216_);
lean_closure_set(v___f_223_, 1, v_onReturn_221_);
lean_closure_set(v___f_223_, 2, v_onContinue_220_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___f_223_);
lean_ctor_set(v___x_224_, 1, v_onExcept_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___boxed(lean_object* v_00_u03b2_225_, lean_object* v_ps_226_, lean_object* v_00_u03b1_227_, lean_object* v_xs_228_, lean_object* v_00_u03b3_229_, lean_object* v_onContinue_230_, lean_object* v_onReturn_231_, lean_object* v_onExcept_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Std_Do_Invariant_withEarlyReturn(v_00_u03b2_225_, v_ps_226_, v_00_u03b1_227_, v_xs_228_, v_00_u03b3_229_, v_onContinue_230_, v_onReturn_231_, v_onExcept_232_);
lean_dec(v_xs_228_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1(lean_object* v_ps_234_, lean_object* v_onReturn_235_, lean_object* v_onContinue_236_, lean_object* v_x_237_){
_start:
{
lean_object* v_snd_238_; lean_object* v_fst_239_; lean_object* v_snd_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___f_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_snd_238_ = lean_ctor_get(v_x_237_, 1);
lean_inc(v_snd_238_);
v_fst_239_ = lean_ctor_get(v_x_237_, 0);
lean_inc(v_fst_239_);
lean_dec_ref(v_x_237_);
v_snd_240_ = lean_ctor_get(v_snd_238_, 1);
lean_inc(v_snd_240_);
lean_dec(v_snd_238_);
v___x_241_ = l_Std_Do_PostShape_args(v_ps_234_);
lean_inc(v___x_241_);
v___x_242_ = l_Std_Do_SPred_pure___redArg(v___x_241_);
lean_inc(v___x_242_);
lean_inc(v___x_241_);
lean_inc(v_snd_240_);
v___f_243_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_243_, 0, v_onReturn_235_);
lean_closure_set(v___f_243_, 1, v_snd_240_);
lean_closure_set(v___f_243_, 2, v___x_241_);
lean_closure_set(v___f_243_, 3, v___x_242_);
v___x_244_ = lean_apply_2(v_onContinue_236_, v_fst_239_, v_snd_240_);
lean_inc(v___x_241_);
v___x_245_ = l_Std_Do_SPred_and(v___x_241_, v___x_242_, v___x_244_);
lean_inc(v___x_241_);
v___x_246_ = l_Std_Do_SPred_exists___redArg(v___x_241_, v___f_243_);
v___x_247_ = l_Std_Do_SPred_or(v___x_241_, v___x_245_, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed(lean_object* v_ps_248_, lean_object* v_onReturn_249_, lean_object* v_onContinue_250_, lean_object* v_x_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1(v_ps_248_, v_onReturn_249_, v_onContinue_250_, v_x_251_);
lean_dec(v_ps_248_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg(lean_object* v_ps_253_, lean_object* v_onContinue_254_, lean_object* v_onReturn_255_, lean_object* v_onExcept_256_){
_start:
{
lean_object* v___f_257_; lean_object* v___x_258_; 
v___f_257_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_257_, 0, v_ps_253_);
lean_closure_set(v___f_257_, 1, v_onReturn_255_);
lean_closure_set(v___f_257_, 2, v_onContinue_254_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___f_257_);
lean_ctor_set(v___x_258_, 1, v_onExcept_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo(lean_object* v_00_u03b2_259_, lean_object* v_ps_260_, lean_object* v_00_u03b1_261_, lean_object* v_xs_262_, lean_object* v_00_u03b3_263_, lean_object* v_onContinue_264_, lean_object* v_onReturn_265_, lean_object* v_onExcept_266_){
_start:
{
lean_object* v___f_267_; lean_object* v___x_268_; 
v___f_267_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_267_, 0, v_ps_260_);
lean_closure_set(v___f_267_, 1, v_onReturn_265_);
lean_closure_set(v___f_267_, 2, v_onContinue_264_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___f_267_);
lean_ctor_set(v___x_268_, 1, v_onExcept_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___boxed(lean_object* v_00_u03b2_269_, lean_object* v_ps_270_, lean_object* v_00_u03b1_271_, lean_object* v_xs_272_, lean_object* v_00_u03b3_273_, lean_object* v_onContinue_274_, lean_object* v_onReturn_275_, lean_object* v_onExcept_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_Do_Invariant_withEarlyReturnNewDo(v_00_u03b2_269_, v_ps_270_, v_00_u03b1_271_, v_xs_272_, v_00_u03b3_273_, v_onContinue_274_, v_onReturn_275_, v_onExcept_276_);
lean_dec(v_xs_272_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_278_, lean_object* v_h__1_279_, lean_object* v_h__2_280_){
_start:
{
if (lean_obj_tag(v_x_278_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; 
lean_dec(v_h__2_280_);
v_a_281_ = lean_ctor_get(v_x_278_, 0);
lean_inc(v_a_281_);
lean_dec_ref(v_x_278_);
v___x_282_ = lean_apply_1(v_h__1_279_, v_a_281_);
return v___x_282_;
}
else
{
lean_object* v_a_283_; lean_object* v___x_284_; 
lean_dec(v_h__1_279_);
v_a_283_ = lean_ctor_get(v_x_278_, 0);
lean_inc(v_a_283_);
lean_dec_ref(v_x_278_);
v___x_284_ = lean_apply_1(v_h__2_280_, v_a_283_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_285_, lean_object* v_motive_286_, lean_object* v_x_287_, lean_object* v_h__1_288_, lean_object* v_h__2_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(v_x_287_, v_h__1_288_, v_h__2_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1(lean_object* v_ps_291_, lean_object* v_onReturn_292_, lean_object* v_onContinue_293_, lean_object* v_x_294_){
_start:
{
lean_object* v_snd_295_; lean_object* v_fst_296_; lean_object* v_snd_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___f_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_snd_295_ = lean_ctor_get(v_x_294_, 1);
lean_inc(v_snd_295_);
v_fst_296_ = lean_ctor_get(v_x_294_, 0);
lean_inc(v_fst_296_);
lean_dec_ref(v_x_294_);
v_snd_297_ = lean_ctor_get(v_snd_295_, 1);
lean_inc(v_snd_297_);
lean_dec(v_snd_295_);
v___x_298_ = l_Std_Do_PostShape_args(v_ps_291_);
lean_inc(v___x_298_);
v___x_299_ = l_Std_Do_SPred_pure___redArg(v___x_298_);
lean_inc(v___x_299_);
lean_inc(v___x_298_);
lean_inc(v_snd_297_);
v___f_300_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_300_, 0, v_onReturn_292_);
lean_closure_set(v___f_300_, 1, v_snd_297_);
lean_closure_set(v___f_300_, 2, v___x_298_);
lean_closure_set(v___f_300_, 3, v___x_299_);
v___x_301_ = lean_apply_2(v_onContinue_293_, v_fst_296_, v_snd_297_);
lean_inc(v___x_298_);
v___x_302_ = l_Std_Do_SPred_and(v___x_298_, v___x_299_, v___x_301_);
lean_inc(v___x_298_);
v___x_303_ = l_Std_Do_SPred_exists___redArg(v___x_298_, v___f_300_);
v___x_304_ = l_Std_Do_SPred_or(v___x_298_, v___x_302_, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed(lean_object* v_ps_305_, lean_object* v_onReturn_306_, lean_object* v_onContinue_307_, lean_object* v_x_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1(v_ps_305_, v_onReturn_306_, v_onContinue_307_, v_x_308_);
lean_dec(v_ps_305_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg(lean_object* v_ps_310_, lean_object* v_onContinue_311_, lean_object* v_onReturn_312_, lean_object* v_onExcept_313_){
_start:
{
lean_object* v___f_314_; lean_object* v___x_315_; 
v___f_314_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_314_, 0, v_ps_310_);
lean_closure_set(v___f_314_, 1, v_onReturn_312_);
lean_closure_set(v___f_314_, 2, v_onContinue_311_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___f_314_);
lean_ctor_set(v___x_315_, 1, v_onExcept_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn(lean_object* v_00_u03b2_316_, lean_object* v_ps_317_, lean_object* v_00_u03b3_318_, lean_object* v_s_319_, lean_object* v_onContinue_320_, lean_object* v_onReturn_321_, lean_object* v_onExcept_322_){
_start:
{
lean_object* v___f_323_; lean_object* v___x_324_; 
v___f_323_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_323_, 0, v_ps_317_);
lean_closure_set(v___f_323_, 1, v_onReturn_321_);
lean_closure_set(v___f_323_, 2, v_onContinue_320_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___f_323_);
lean_ctor_set(v___x_324_, 1, v_onExcept_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___boxed(lean_object* v_00_u03b2_325_, lean_object* v_ps_326_, lean_object* v_00_u03b3_327_, lean_object* v_s_328_, lean_object* v_onContinue_329_, lean_object* v_onReturn_330_, lean_object* v_onExcept_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_Do_StringInvariant_withEarlyReturn(v_00_u03b2_325_, v_ps_326_, v_00_u03b3_327_, v_s_328_, v_onContinue_329_, v_onReturn_330_, v_onExcept_331_);
lean_dec_ref(v_s_328_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1(lean_object* v_ps_333_, lean_object* v_onReturn_334_, lean_object* v_onContinue_335_, lean_object* v_x_336_){
_start:
{
lean_object* v_snd_337_; lean_object* v_fst_338_; lean_object* v_snd_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___f_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_snd_337_ = lean_ctor_get(v_x_336_, 1);
lean_inc(v_snd_337_);
v_fst_338_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_fst_338_);
lean_dec_ref(v_x_336_);
v_snd_339_ = lean_ctor_get(v_snd_337_, 1);
lean_inc(v_snd_339_);
lean_dec(v_snd_337_);
v___x_340_ = l_Std_Do_PostShape_args(v_ps_333_);
lean_inc(v___x_340_);
v___x_341_ = l_Std_Do_SPred_pure___redArg(v___x_340_);
lean_inc(v___x_341_);
lean_inc(v___x_340_);
lean_inc(v_snd_339_);
v___f_342_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_342_, 0, v_onReturn_334_);
lean_closure_set(v___f_342_, 1, v_snd_339_);
lean_closure_set(v___f_342_, 2, v___x_340_);
lean_closure_set(v___f_342_, 3, v___x_341_);
v___x_343_ = lean_apply_2(v_onContinue_335_, v_fst_338_, v_snd_339_);
lean_inc(v___x_340_);
v___x_344_ = l_Std_Do_SPred_and(v___x_340_, v___x_341_, v___x_343_);
lean_inc(v___x_340_);
v___x_345_ = l_Std_Do_SPred_exists___redArg(v___x_340_, v___f_342_);
v___x_346_ = l_Std_Do_SPred_or(v___x_340_, v___x_344_, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed(lean_object* v_ps_347_, lean_object* v_onReturn_348_, lean_object* v_onContinue_349_, lean_object* v_x_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1(v_ps_347_, v_onReturn_348_, v_onContinue_349_, v_x_350_);
lean_dec(v_ps_347_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg(lean_object* v_ps_352_, lean_object* v_onContinue_353_, lean_object* v_onReturn_354_, lean_object* v_onExcept_355_){
_start:
{
lean_object* v___f_356_; lean_object* v___x_357_; 
v___f_356_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_356_, 0, v_ps_352_);
lean_closure_set(v___f_356_, 1, v_onReturn_354_);
lean_closure_set(v___f_356_, 2, v_onContinue_353_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___f_356_);
lean_ctor_set(v___x_357_, 1, v_onExcept_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo(lean_object* v_00_u03b2_358_, lean_object* v_ps_359_, lean_object* v_00_u03b3_360_, lean_object* v_s_361_, lean_object* v_onContinue_362_, lean_object* v_onReturn_363_, lean_object* v_onExcept_364_){
_start:
{
lean_object* v___f_365_; lean_object* v___x_366_; 
v___f_365_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_365_, 0, v_ps_359_);
lean_closure_set(v___f_365_, 1, v_onReturn_363_);
lean_closure_set(v___f_365_, 2, v_onContinue_362_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___f_365_);
lean_ctor_set(v___x_366_, 1, v_onExcept_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___boxed(lean_object* v_00_u03b2_367_, lean_object* v_ps_368_, lean_object* v_00_u03b3_369_, lean_object* v_s_370_, lean_object* v_onContinue_371_, lean_object* v_onReturn_372_, lean_object* v_onExcept_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Std_Do_StringInvariant_withEarlyReturnNewDo(v_00_u03b2_367_, v_ps_368_, v_00_u03b3_369_, v_s_370_, v_onContinue_371_, v_onReturn_372_, v_onExcept_373_);
lean_dec_ref(v_s_370_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn___redArg(lean_object* v_ps_375_, lean_object* v_onContinue_376_, lean_object* v_onReturn_377_, lean_object* v_onExcept_378_){
_start:
{
lean_object* v___f_379_; lean_object* v___x_380_; 
v___f_379_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_379_, 0, v_ps_375_);
lean_closure_set(v___f_379_, 1, v_onReturn_377_);
lean_closure_set(v___f_379_, 2, v_onContinue_376_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___f_379_);
lean_ctor_set(v___x_380_, 1, v_onExcept_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn(lean_object* v_00_u03b2_381_, lean_object* v_ps_382_, lean_object* v_00_u03b3_383_, lean_object* v_s_384_, lean_object* v_onContinue_385_, lean_object* v_onReturn_386_, lean_object* v_onExcept_387_){
_start:
{
lean_object* v___f_388_; lean_object* v___x_389_; 
v___f_388_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_388_, 0, v_ps_382_);
lean_closure_set(v___f_388_, 1, v_onReturn_386_);
lean_closure_set(v___f_388_, 2, v_onContinue_385_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___f_388_);
lean_ctor_set(v___x_389_, 1, v_onExcept_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn___boxed(lean_object* v_00_u03b2_390_, lean_object* v_ps_391_, lean_object* v_00_u03b3_392_, lean_object* v_s_393_, lean_object* v_onContinue_394_, lean_object* v_onReturn_395_, lean_object* v_onExcept_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_Do_StringSliceInvariant_withEarlyReturn(v_00_u03b2_390_, v_ps_391_, v_00_u03b3_392_, v_s_393_, v_onContinue_394_, v_onReturn_395_, v_onExcept_396_);
lean_dec_ref(v_s_393_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo___redArg(lean_object* v_ps_398_, lean_object* v_onContinue_399_, lean_object* v_onReturn_400_, lean_object* v_onExcept_401_){
_start:
{
lean_object* v___f_402_; lean_object* v___x_403_; 
v___f_402_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_402_, 0, v_ps_398_);
lean_closure_set(v___f_402_, 1, v_onReturn_400_);
lean_closure_set(v___f_402_, 2, v_onContinue_399_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___f_402_);
lean_ctor_set(v___x_403_, 1, v_onExcept_401_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo(lean_object* v_00_u03b2_404_, lean_object* v_ps_405_, lean_object* v_00_u03b3_406_, lean_object* v_s_407_, lean_object* v_onContinue_408_, lean_object* v_onReturn_409_, lean_object* v_onExcept_410_){
_start:
{
lean_object* v___f_411_; lean_object* v___x_412_; 
v___f_411_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_411_, 0, v_ps_405_);
lean_closure_set(v___f_411_, 1, v_onReturn_409_);
lean_closure_set(v___f_411_, 2, v_onContinue_408_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___f_411_);
lean_ctor_set(v___x_412_, 1, v_onExcept_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo___boxed(lean_object* v_00_u03b2_413_, lean_object* v_ps_414_, lean_object* v_00_u03b3_415_, lean_object* v_s_416_, lean_object* v_onContinue_417_, lean_object* v_onReturn_418_, lean_object* v_onExcept_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo(v_00_u03b2_413_, v_ps_414_, v_00_u03b3_415_, v_s_416_, v_onContinue_417_, v_onReturn_418_, v_onExcept_419_);
lean_dec_ref(v_s_416_);
return v_res_420_;
}
}
lean_object* runtime_initialize_Std_Do_Triple_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Iterate(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_Triple_SpecLemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Do_Triple_SpecLemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_List_Cursor_current___auto__1 = _init_l_List_Cursor_current___auto__1();
lean_mark_persistent(l_List_Cursor_current___auto__1);
l_List_Cursor_tail___auto__1 = _init_l_List_Cursor_tail___auto__1();
lean_mark_persistent(l_List_Cursor_tail___auto__1);
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Std_Do_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Do_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Do_Triple_SpecLemmas(builtin);
}
#ifdef __cplusplus
}
#endif
