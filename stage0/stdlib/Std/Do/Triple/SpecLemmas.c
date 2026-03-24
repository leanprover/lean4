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
if (lean_obj_tag(v_x_165_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_169_; 
lean_dec(v_h__1_166_);
v_a_168_ = lean_ctor_get(v_x_165_, 0);
lean_inc(v_a_168_);
lean_dec_ref(v_x_165_);
v___x_169_ = lean_apply_1(v_h__2_167_, v_a_168_);
return v___x_169_;
}
else
{
lean_object* v_a_170_; lean_object* v___x_171_; 
lean_dec(v_h__2_167_);
v_a_170_ = lean_ctor_get(v_x_165_, 0);
lean_inc(v_a_170_);
lean_dec_ref(v_x_165_);
v___x_171_ = lean_apply_1(v_h__1_166_, v_a_170_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object* v_x_172_, lean_object* v_h__1_173_, lean_object* v_h__2_174_){
_start:
{
if (lean_obj_tag(v_x_172_) == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_h__1_173_);
v___x_175_ = lean_box(0);
v___x_176_ = lean_apply_1(v_h__2_174_, v___x_175_);
return v___x_176_;
}
else
{
lean_object* v_val_177_; lean_object* v___x_178_; 
lean_dec(v_h__2_174_);
v_val_177_ = lean_ctor_get(v_x_172_, 0);
lean_inc(v_val_177_);
lean_dec_ref(v_x_172_);
v___x_178_ = lean_apply_1(v_h__1_173_, v_val_177_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object* v_00_u03b1_179_, lean_object* v_motive_180_, lean_object* v_x_181_, lean_object* v_h__1_182_, lean_object* v_h__2_183_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec(v_h__1_182_);
v___x_184_ = lean_box(0);
v___x_185_ = lean_apply_1(v_h__2_183_, v___x_184_);
return v___x_185_;
}
else
{
lean_object* v_val_186_; lean_object* v___x_187_; 
lean_dec(v_h__2_183_);
v_val_186_ = lean_ctor_get(v_x_181_, 0);
lean_inc(v_val_186_);
lean_dec_ref(v_x_181_);
v___x_187_ = lean_apply_1(v_h__1_182_, v_val_186_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0(lean_object* v_onReturn_188_, lean_object* v_snd_189_, lean_object* v___x_190_, lean_object* v___x_191_, lean_object* v_r_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_apply_2(v_onReturn_188_, v_r_192_, v_snd_189_);
lean_inc(v___x_191_);
lean_inc(v___x_190_);
v___x_194_ = l_Std_Do_SPred_and(v___x_190_, v___x_191_, v___x_193_);
v___x_195_ = l_Std_Do_SPred_and(v___x_190_, v___x_191_, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1(lean_object* v_ps_196_, lean_object* v_onReturn_197_, lean_object* v_onContinue_198_, lean_object* v_x_199_){
_start:
{
lean_object* v_snd_200_; lean_object* v_fst_201_; lean_object* v_snd_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_snd_200_ = lean_ctor_get(v_x_199_, 1);
lean_inc(v_snd_200_);
v_fst_201_ = lean_ctor_get(v_x_199_, 0);
lean_inc(v_fst_201_);
lean_dec_ref(v_x_199_);
v_snd_202_ = lean_ctor_get(v_snd_200_, 1);
lean_inc(v_snd_202_);
lean_dec(v_snd_200_);
v___x_203_ = l_Std_Do_PostShape_args(v_ps_196_);
lean_inc(v___x_203_);
v___x_204_ = l_Std_Do_SPred_pure___redArg(v___x_203_);
lean_inc(v___x_204_);
lean_inc(v___x_203_);
lean_inc(v_snd_202_);
v___f_205_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_205_, 0, v_onReturn_197_);
lean_closure_set(v___f_205_, 1, v_snd_202_);
lean_closure_set(v___f_205_, 2, v___x_203_);
lean_closure_set(v___f_205_, 3, v___x_204_);
v___x_206_ = lean_apply_2(v_onContinue_198_, v_fst_201_, v_snd_202_);
lean_inc(v___x_203_);
v___x_207_ = l_Std_Do_SPred_and(v___x_203_, v___x_204_, v___x_206_);
lean_inc(v___x_203_);
v___x_208_ = l_Std_Do_SPred_exists___redArg(v___x_203_, v___f_205_);
v___x_209_ = l_Std_Do_SPred_or(v___x_203_, v___x_207_, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed(lean_object* v_ps_210_, lean_object* v_onReturn_211_, lean_object* v_onContinue_212_, lean_object* v_x_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1(v_ps_210_, v_onReturn_211_, v_onContinue_212_, v_x_213_);
lean_dec(v_ps_210_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg(lean_object* v_ps_215_, lean_object* v_onContinue_216_, lean_object* v_onReturn_217_, lean_object* v_onExcept_218_){
_start:
{
lean_object* v___f_219_; lean_object* v___x_220_; 
v___f_219_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_219_, 0, v_ps_215_);
lean_closure_set(v___f_219_, 1, v_onReturn_217_);
lean_closure_set(v___f_219_, 2, v_onContinue_216_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___f_219_);
lean_ctor_set(v___x_220_, 1, v_onExcept_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn(lean_object* v_00_u03b2_221_, lean_object* v_ps_222_, lean_object* v_00_u03b1_223_, lean_object* v_xs_224_, lean_object* v_00_u03b3_225_, lean_object* v_onContinue_226_, lean_object* v_onReturn_227_, lean_object* v_onExcept_228_){
_start:
{
lean_object* v___f_229_; lean_object* v___x_230_; 
v___f_229_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_229_, 0, v_ps_222_);
lean_closure_set(v___f_229_, 1, v_onReturn_227_);
lean_closure_set(v___f_229_, 2, v_onContinue_226_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v___f_229_);
lean_ctor_set(v___x_230_, 1, v_onExcept_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___boxed(lean_object* v_00_u03b2_231_, lean_object* v_ps_232_, lean_object* v_00_u03b1_233_, lean_object* v_xs_234_, lean_object* v_00_u03b3_235_, lean_object* v_onContinue_236_, lean_object* v_onReturn_237_, lean_object* v_onExcept_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_Do_Invariant_withEarlyReturn(v_00_u03b2_231_, v_ps_232_, v_00_u03b1_233_, v_xs_234_, v_00_u03b3_235_, v_onContinue_236_, v_onReturn_237_, v_onExcept_238_);
lean_dec(v_xs_234_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1(lean_object* v_ps_240_, lean_object* v_onReturn_241_, lean_object* v_onContinue_242_, lean_object* v_x_243_){
_start:
{
lean_object* v_snd_244_; lean_object* v_fst_245_; lean_object* v_snd_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___f_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_snd_244_ = lean_ctor_get(v_x_243_, 1);
lean_inc(v_snd_244_);
v_fst_245_ = lean_ctor_get(v_x_243_, 0);
lean_inc(v_fst_245_);
lean_dec_ref(v_x_243_);
v_snd_246_ = lean_ctor_get(v_snd_244_, 1);
lean_inc(v_snd_246_);
lean_dec(v_snd_244_);
v___x_247_ = l_Std_Do_PostShape_args(v_ps_240_);
lean_inc(v___x_247_);
v___x_248_ = l_Std_Do_SPred_pure___redArg(v___x_247_);
lean_inc(v___x_248_);
lean_inc(v___x_247_);
lean_inc(v_snd_246_);
v___f_249_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_249_, 0, v_onReturn_241_);
lean_closure_set(v___f_249_, 1, v_snd_246_);
lean_closure_set(v___f_249_, 2, v___x_247_);
lean_closure_set(v___f_249_, 3, v___x_248_);
v___x_250_ = lean_apply_2(v_onContinue_242_, v_fst_245_, v_snd_246_);
lean_inc(v___x_247_);
v___x_251_ = l_Std_Do_SPred_and(v___x_247_, v___x_248_, v___x_250_);
lean_inc(v___x_247_);
v___x_252_ = l_Std_Do_SPred_exists___redArg(v___x_247_, v___f_249_);
v___x_253_ = l_Std_Do_SPred_or(v___x_247_, v___x_251_, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed(lean_object* v_ps_254_, lean_object* v_onReturn_255_, lean_object* v_onContinue_256_, lean_object* v_x_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1(v_ps_254_, v_onReturn_255_, v_onContinue_256_, v_x_257_);
lean_dec(v_ps_254_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg(lean_object* v_ps_259_, lean_object* v_onContinue_260_, lean_object* v_onReturn_261_, lean_object* v_onExcept_262_){
_start:
{
lean_object* v___f_263_; lean_object* v___x_264_; 
v___f_263_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_263_, 0, v_ps_259_);
lean_closure_set(v___f_263_, 1, v_onReturn_261_);
lean_closure_set(v___f_263_, 2, v_onContinue_260_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___f_263_);
lean_ctor_set(v___x_264_, 1, v_onExcept_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo(lean_object* v_00_u03b2_265_, lean_object* v_ps_266_, lean_object* v_00_u03b1_267_, lean_object* v_xs_268_, lean_object* v_00_u03b3_269_, lean_object* v_onContinue_270_, lean_object* v_onReturn_271_, lean_object* v_onExcept_272_){
_start:
{
lean_object* v___f_273_; lean_object* v___x_274_; 
v___f_273_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_273_, 0, v_ps_266_);
lean_closure_set(v___f_273_, 1, v_onReturn_271_);
lean_closure_set(v___f_273_, 2, v_onContinue_270_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___f_273_);
lean_ctor_set(v___x_274_, 1, v_onExcept_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___boxed(lean_object* v_00_u03b2_275_, lean_object* v_ps_276_, lean_object* v_00_u03b1_277_, lean_object* v_xs_278_, lean_object* v_00_u03b3_279_, lean_object* v_onContinue_280_, lean_object* v_onReturn_281_, lean_object* v_onExcept_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Std_Do_Invariant_withEarlyReturnNewDo(v_00_u03b2_275_, v_ps_276_, v_00_u03b1_277_, v_xs_278_, v_00_u03b3_279_, v_onContinue_280_, v_onReturn_281_, v_onExcept_282_);
lean_dec(v_xs_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_284_, lean_object* v_h__1_285_, lean_object* v_h__2_286_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_288_; 
lean_dec(v_h__2_286_);
v_a_287_ = lean_ctor_get(v_x_284_, 0);
lean_inc(v_a_287_);
lean_dec_ref(v_x_284_);
v___x_288_ = lean_apply_1(v_h__1_285_, v_a_287_);
return v___x_288_;
}
else
{
lean_object* v_a_289_; lean_object* v___x_290_; 
lean_dec(v_h__1_285_);
v_a_289_ = lean_ctor_get(v_x_284_, 0);
lean_inc(v_a_289_);
lean_dec_ref(v_x_284_);
v___x_290_ = lean_apply_1(v_h__2_286_, v_a_289_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_291_, lean_object* v_motive_292_, lean_object* v_x_293_, lean_object* v_h__1_294_, lean_object* v_h__2_295_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_297_; 
lean_dec(v_h__2_295_);
v_a_296_ = lean_ctor_get(v_x_293_, 0);
lean_inc(v_a_296_);
lean_dec_ref(v_x_293_);
v___x_297_ = lean_apply_1(v_h__1_294_, v_a_296_);
return v___x_297_;
}
else
{
lean_object* v_a_298_; lean_object* v___x_299_; 
lean_dec(v_h__1_294_);
v_a_298_ = lean_ctor_get(v_x_293_, 0);
lean_inc(v_a_298_);
lean_dec_ref(v_x_293_);
v___x_299_ = lean_apply_1(v_h__2_295_, v_a_298_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1(lean_object* v_ps_300_, lean_object* v_onReturn_301_, lean_object* v_onContinue_302_, lean_object* v_x_303_){
_start:
{
lean_object* v_snd_304_; lean_object* v_fst_305_; lean_object* v_snd_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_snd_304_ = lean_ctor_get(v_x_303_, 1);
lean_inc(v_snd_304_);
v_fst_305_ = lean_ctor_get(v_x_303_, 0);
lean_inc(v_fst_305_);
lean_dec_ref(v_x_303_);
v_snd_306_ = lean_ctor_get(v_snd_304_, 1);
lean_inc(v_snd_306_);
lean_dec(v_snd_304_);
v___x_307_ = l_Std_Do_PostShape_args(v_ps_300_);
lean_inc(v___x_307_);
v___x_308_ = l_Std_Do_SPred_pure___redArg(v___x_307_);
lean_inc(v___x_308_);
lean_inc(v___x_307_);
lean_inc(v_snd_306_);
v___f_309_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_309_, 0, v_onReturn_301_);
lean_closure_set(v___f_309_, 1, v_snd_306_);
lean_closure_set(v___f_309_, 2, v___x_307_);
lean_closure_set(v___f_309_, 3, v___x_308_);
v___x_310_ = lean_apply_2(v_onContinue_302_, v_fst_305_, v_snd_306_);
lean_inc(v___x_307_);
v___x_311_ = l_Std_Do_SPred_and(v___x_307_, v___x_308_, v___x_310_);
lean_inc(v___x_307_);
v___x_312_ = l_Std_Do_SPred_exists___redArg(v___x_307_, v___f_309_);
v___x_313_ = l_Std_Do_SPred_or(v___x_307_, v___x_311_, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed(lean_object* v_ps_314_, lean_object* v_onReturn_315_, lean_object* v_onContinue_316_, lean_object* v_x_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1(v_ps_314_, v_onReturn_315_, v_onContinue_316_, v_x_317_);
lean_dec(v_ps_314_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg(lean_object* v_ps_319_, lean_object* v_onContinue_320_, lean_object* v_onReturn_321_, lean_object* v_onExcept_322_){
_start:
{
lean_object* v___f_323_; lean_object* v___x_324_; 
v___f_323_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_323_, 0, v_ps_319_);
lean_closure_set(v___f_323_, 1, v_onReturn_321_);
lean_closure_set(v___f_323_, 2, v_onContinue_320_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___f_323_);
lean_ctor_set(v___x_324_, 1, v_onExcept_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn(lean_object* v_00_u03b2_325_, lean_object* v_ps_326_, lean_object* v_00_u03b3_327_, lean_object* v_s_328_, lean_object* v_onContinue_329_, lean_object* v_onReturn_330_, lean_object* v_onExcept_331_){
_start:
{
lean_object* v___f_332_; lean_object* v___x_333_; 
v___f_332_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_332_, 0, v_ps_326_);
lean_closure_set(v___f_332_, 1, v_onReturn_330_);
lean_closure_set(v___f_332_, 2, v_onContinue_329_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___f_332_);
lean_ctor_set(v___x_333_, 1, v_onExcept_331_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___boxed(lean_object* v_00_u03b2_334_, lean_object* v_ps_335_, lean_object* v_00_u03b3_336_, lean_object* v_s_337_, lean_object* v_onContinue_338_, lean_object* v_onReturn_339_, lean_object* v_onExcept_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_Do_StringInvariant_withEarlyReturn(v_00_u03b2_334_, v_ps_335_, v_00_u03b3_336_, v_s_337_, v_onContinue_338_, v_onReturn_339_, v_onExcept_340_);
lean_dec_ref(v_s_337_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1(lean_object* v_ps_342_, lean_object* v_onReturn_343_, lean_object* v_onContinue_344_, lean_object* v_x_345_){
_start:
{
lean_object* v_snd_346_; lean_object* v_fst_347_; lean_object* v_snd_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___f_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_snd_346_ = lean_ctor_get(v_x_345_, 1);
lean_inc(v_snd_346_);
v_fst_347_ = lean_ctor_get(v_x_345_, 0);
lean_inc(v_fst_347_);
lean_dec_ref(v_x_345_);
v_snd_348_ = lean_ctor_get(v_snd_346_, 1);
lean_inc(v_snd_348_);
lean_dec(v_snd_346_);
v___x_349_ = l_Std_Do_PostShape_args(v_ps_342_);
lean_inc(v___x_349_);
v___x_350_ = l_Std_Do_SPred_pure___redArg(v___x_349_);
lean_inc(v___x_350_);
lean_inc(v___x_349_);
lean_inc(v_snd_348_);
v___f_351_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_351_, 0, v_onReturn_343_);
lean_closure_set(v___f_351_, 1, v_snd_348_);
lean_closure_set(v___f_351_, 2, v___x_349_);
lean_closure_set(v___f_351_, 3, v___x_350_);
v___x_352_ = lean_apply_2(v_onContinue_344_, v_fst_347_, v_snd_348_);
lean_inc(v___x_349_);
v___x_353_ = l_Std_Do_SPred_and(v___x_349_, v___x_350_, v___x_352_);
lean_inc(v___x_349_);
v___x_354_ = l_Std_Do_SPred_exists___redArg(v___x_349_, v___f_351_);
v___x_355_ = l_Std_Do_SPred_or(v___x_349_, v___x_353_, v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed(lean_object* v_ps_356_, lean_object* v_onReturn_357_, lean_object* v_onContinue_358_, lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1(v_ps_356_, v_onReturn_357_, v_onContinue_358_, v_x_359_);
lean_dec(v_ps_356_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg(lean_object* v_ps_361_, lean_object* v_onContinue_362_, lean_object* v_onReturn_363_, lean_object* v_onExcept_364_){
_start:
{
lean_object* v___f_365_; lean_object* v___x_366_; 
v___f_365_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_365_, 0, v_ps_361_);
lean_closure_set(v___f_365_, 1, v_onReturn_363_);
lean_closure_set(v___f_365_, 2, v_onContinue_362_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___f_365_);
lean_ctor_set(v___x_366_, 1, v_onExcept_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo(lean_object* v_00_u03b2_367_, lean_object* v_ps_368_, lean_object* v_00_u03b3_369_, lean_object* v_s_370_, lean_object* v_onContinue_371_, lean_object* v_onReturn_372_, lean_object* v_onExcept_373_){
_start:
{
lean_object* v___f_374_; lean_object* v___x_375_; 
v___f_374_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_374_, 0, v_ps_368_);
lean_closure_set(v___f_374_, 1, v_onReturn_372_);
lean_closure_set(v___f_374_, 2, v_onContinue_371_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___f_374_);
lean_ctor_set(v___x_375_, 1, v_onExcept_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___boxed(lean_object* v_00_u03b2_376_, lean_object* v_ps_377_, lean_object* v_00_u03b3_378_, lean_object* v_s_379_, lean_object* v_onContinue_380_, lean_object* v_onReturn_381_, lean_object* v_onExcept_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_Do_StringInvariant_withEarlyReturnNewDo(v_00_u03b2_376_, v_ps_377_, v_00_u03b3_378_, v_s_379_, v_onContinue_380_, v_onReturn_381_, v_onExcept_382_);
lean_dec_ref(v_s_379_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn___redArg(lean_object* v_ps_384_, lean_object* v_onContinue_385_, lean_object* v_onReturn_386_, lean_object* v_onExcept_387_){
_start:
{
lean_object* v___f_388_; lean_object* v___x_389_; 
v___f_388_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_388_, 0, v_ps_384_);
lean_closure_set(v___f_388_, 1, v_onReturn_386_);
lean_closure_set(v___f_388_, 2, v_onContinue_385_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___f_388_);
lean_ctor_set(v___x_389_, 1, v_onExcept_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn(lean_object* v_00_u03b2_390_, lean_object* v_ps_391_, lean_object* v_00_u03b3_392_, lean_object* v_s_393_, lean_object* v_onContinue_394_, lean_object* v_onReturn_395_, lean_object* v_onExcept_396_){
_start:
{
lean_object* v___f_397_; lean_object* v___x_398_; 
v___f_397_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_397_, 0, v_ps_391_);
lean_closure_set(v___f_397_, 1, v_onReturn_395_);
lean_closure_set(v___f_397_, 2, v_onContinue_394_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v___f_397_);
lean_ctor_set(v___x_398_, 1, v_onExcept_396_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn___boxed(lean_object* v_00_u03b2_399_, lean_object* v_ps_400_, lean_object* v_00_u03b3_401_, lean_object* v_s_402_, lean_object* v_onContinue_403_, lean_object* v_onReturn_404_, lean_object* v_onExcept_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Std_Do_StringSliceInvariant_withEarlyReturn(v_00_u03b2_399_, v_ps_400_, v_00_u03b3_401_, v_s_402_, v_onContinue_403_, v_onReturn_404_, v_onExcept_405_);
lean_dec_ref(v_s_402_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo___redArg(lean_object* v_ps_407_, lean_object* v_onContinue_408_, lean_object* v_onReturn_409_, lean_object* v_onExcept_410_){
_start:
{
lean_object* v___f_411_; lean_object* v___x_412_; 
v___f_411_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_411_, 0, v_ps_407_);
lean_closure_set(v___f_411_, 1, v_onReturn_409_);
lean_closure_set(v___f_411_, 2, v_onContinue_408_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___f_411_);
lean_ctor_set(v___x_412_, 1, v_onExcept_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo(lean_object* v_00_u03b2_413_, lean_object* v_ps_414_, lean_object* v_00_u03b3_415_, lean_object* v_s_416_, lean_object* v_onContinue_417_, lean_object* v_onReturn_418_, lean_object* v_onExcept_419_){
_start:
{
lean_object* v___f_420_; lean_object* v___x_421_; 
v___f_420_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_420_, 0, v_ps_414_);
lean_closure_set(v___f_420_, 1, v_onReturn_418_);
lean_closure_set(v___f_420_, 2, v_onContinue_417_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___f_420_);
lean_ctor_set(v___x_421_, 1, v_onExcept_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo___boxed(lean_object* v_00_u03b2_422_, lean_object* v_ps_423_, lean_object* v_00_u03b3_424_, lean_object* v_s_425_, lean_object* v_onContinue_426_, lean_object* v_onReturn_427_, lean_object* v_onExcept_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo(v_00_u03b2_422_, v_ps_423_, v_00_u03b3_424_, v_s_425_, v_onContinue_426_, v_onReturn_427_, v_onExcept_428_);
lean_dec_ref(v_s_425_);
return v_res_429_;
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
