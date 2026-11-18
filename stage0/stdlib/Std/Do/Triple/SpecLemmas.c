// Lean compiler output
// Module: Std.Do.Triple.SpecLemmas
// Imports: public import Std.Do.Triple.Basic public import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic public import Init.Data.Slice.Array public import Init.While public import Init.Internal.Order.While public import Init.Data.Iterators.Lemmas.Combinators.FilterMap public import Init.Data.Range import Init.Data.Iterators.Lemmas import Init.Data.List.Nat.Range import Init.Data.List.Nat.TakeDrop import Init.Data.List.Range import Init.Data.List.TakeDrop import Init.Data.List.Impl import Init.Data.Nat.Mod import Init.Data.Slice.Lemmas import Init.Omega public import Init.Data.String.Defs public import Init.Data.String.Iterate import Init.Data.String.Lemmas.Splits import Init.Data.String.Termination import Init.Data.String.Lemmas.Iterate
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_range_x27TR_go(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_SVal_evalsTo___redArg(lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_toList(lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_toList___boxed(lean_object*);
static const lean_array_object l_List_Cursor_at___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_Cursor_at___redArg___closed__0 = (const lean_object*)&l_List_Cursor_at___redArg___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_Do_WhileVariant_eval___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_WhileVariant_eval___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_WhileVariant_eval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_WhileVariant_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_Cursor_at___redArg(lean_object* v_l_18_, lean_object* v_n_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_20_ = ((lean_object*)(l_List_Cursor_at___redArg___closed__0));
lean_inc(v_n_19_);
lean_inc(v_l_18_);
v___x_21_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_l_18_, v_l_18_, v_n_19_, v___x_20_);
v___x_22_ = l_List_drop___redArg(v_n_19_, v_l_18_);
lean_dec(v_l_18_);
v___x_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_21_);
lean_ctor_set(v___x_23_, 1, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_at(lean_object* v_00_u03b1_24_, lean_object* v_l_25_, lean_object* v_n_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_List_Cursor_at___redArg(v_l_25_, v_n_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_begin___redArg(lean_object* v_l_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = l_List_Cursor_at___redArg(v_l_28_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_begin(lean_object* v_00_u03b1_31_, lean_object* v_l_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = l_List_Cursor_at___redArg(v_l_32_, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_end___redArg(lean_object* v_l_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = l_List_lengthTR___redArg(v_l_35_);
v___x_37_ = l_List_Cursor_at___redArg(v_l_35_, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_end(lean_object* v_00_u03b1_38_, lean_object* v_l_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = l_List_lengthTR___redArg(v_l_39_);
v___x_41_ = l_List_Cursor_at___redArg(v_l_39_, v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__13(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__12));
v___x_67_ = l_Lean_mkAtom(v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__14(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__13, &l_List_Cursor_current___auto__1___closed__13_once, _init_l_List_Cursor_current___auto__1___closed__13);
v___x_69_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__5));
v___x_70_ = lean_array_push(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__15(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__14, &l_List_Cursor_current___auto__1___closed__14_once, _init_l_List_Cursor_current___auto__1___closed__14);
v___x_72_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__11));
v___x_73_ = lean_box(2);
v___x_74_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_72_);
lean_ctor_set(v___x_74_, 2, v___x_71_);
return v___x_74_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__16(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__15, &l_List_Cursor_current___auto__1___closed__15_once, _init_l_List_Cursor_current___auto__1___closed__15);
v___x_76_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__5));
v___x_77_ = lean_array_push(v___x_76_, v___x_75_);
return v___x_77_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__17(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__16, &l_List_Cursor_current___auto__1___closed__16_once, _init_l_List_Cursor_current___auto__1___closed__16);
v___x_79_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__9));
v___x_80_ = lean_box(2);
v___x_81_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
lean_ctor_set(v___x_81_, 2, v___x_78_);
return v___x_81_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__18(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__17, &l_List_Cursor_current___auto__1___closed__17_once, _init_l_List_Cursor_current___auto__1___closed__17);
v___x_83_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__5));
v___x_84_ = lean_array_push(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__19(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__18, &l_List_Cursor_current___auto__1___closed__18_once, _init_l_List_Cursor_current___auto__1___closed__18);
v___x_86_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__7));
v___x_87_ = lean_box(2);
v___x_88_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_85_);
return v___x_88_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__20(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__19, &l_List_Cursor_current___auto__1___closed__19_once, _init_l_List_Cursor_current___auto__1___closed__19);
v___x_90_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__5));
v___x_91_ = lean_array_push(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__21(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__20, &l_List_Cursor_current___auto__1___closed__20_once, _init_l_List_Cursor_current___auto__1___closed__20);
v___x_93_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__4));
v___x_94_ = lean_box(2);
v___x_95_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___x_93_);
lean_ctor_set(v___x_95_, 2, v___x_92_);
return v___x_95_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1(void){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__21, &l_List_Cursor_current___auto__1___closed__21_once, _init_l_List_Cursor_current___auto__1___closed__21);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current___redArg(lean_object* v_c_97_){
_start:
{
lean_object* v_suffix_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_suffix_98_ = lean_ctor_get(v_c_97_, 1);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = l_List_get___redArg(v_suffix_98_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current___redArg___boxed(lean_object* v_c_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_List_Cursor_current___redArg(v_c_101_);
lean_dec_ref(v_c_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current(lean_object* v_00_u03b1_103_, lean_object* v_l_104_, lean_object* v_c_105_, lean_object* v_h_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_List_Cursor_current___redArg(v_c_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current___boxed(lean_object* v_00_u03b1_108_, lean_object* v_l_109_, lean_object* v_c_110_, lean_object* v_h_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_List_Cursor_current(v_00_u03b1_108_, v_l_109_, v_c_110_, v_h_111_);
lean_dec_ref(v_c_110_);
lean_dec(v_l_109_);
return v_res_112_;
}
}
static lean_object* _init_l_List_Cursor_tail___auto__1(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__21, &l_List_Cursor_current___auto__1___closed__21_once, _init_l_List_Cursor_current___auto__1___closed__21);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_tail___redArg(lean_object* v_s_114_){
_start:
{
lean_object* v_prefix_115_; lean_object* v_suffix_116_; lean_object* v___x_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_131_; 
v_prefix_115_ = lean_ctor_get(v_s_114_, 0);
lean_inc(v_prefix_115_);
v_suffix_116_ = lean_ctor_get(v_s_114_, 1);
lean_inc(v_suffix_116_);
v___x_117_ = l_List_Cursor_current___redArg(v_s_114_);
v_isSharedCheck_131_ = !lean_is_exclusive(v_s_114_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; lean_object* v_unused_133_; 
v_unused_132_ = lean_ctor_get(v_s_114_, 1);
lean_dec(v_unused_132_);
v_unused_133_ = lean_ctor_get(v_s_114_, 0);
lean_dec(v_unused_133_);
v___x_119_ = v_s_114_;
v_isShared_120_ = v_isSharedCheck_131_;
goto v_resetjp_118_;
}
else
{
lean_dec(v_s_114_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_131_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_box(0);
v___x_122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_117_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = l_List_appendTR___redArg(v_prefix_115_, v___x_122_);
if (lean_obj_tag(v_suffix_116_) == 0)
{
lean_object* v___x_125_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_123_);
v___x_125_ = v___x_119_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_suffix_116_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
else
{
lean_object* v_tail_127_; lean_object* v___x_129_; 
v_tail_127_ = lean_ctor_get(v_suffix_116_, 1);
lean_inc(v_tail_127_);
lean_dec_ref_known(v_suffix_116_, 2);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 1, v_tail_127_);
lean_ctor_set(v___x_119_, 0, v___x_123_);
v___x_129_ = v___x_119_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_tail_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_Cursor_tail(lean_object* v_00_u03b1_134_, lean_object* v_l_135_, lean_object* v_s_136_, lean_object* v_h_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_List_Cursor_tail___redArg(v_s_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_tail___boxed(lean_object* v_00_u03b1_139_, lean_object* v_l_140_, lean_object* v_s_141_, lean_object* v_h_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_List_Cursor_tail(v_00_u03b1_139_, v_l_140_, v_s_141_, v_h_142_);
lean_dec(v_l_140_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos___redArg(lean_object* v_c_144_){
_start:
{
lean_object* v_prefix_145_; lean_object* v___x_146_; 
v_prefix_145_ = lean_ctor_get(v_c_144_, 0);
v___x_146_ = l_List_lengthTR___redArg(v_prefix_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos___redArg___boxed(lean_object* v_c_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_List_Cursor_pos___redArg(v_c_147_);
lean_dec_ref(v_c_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos(lean_object* v_00_u03b1_149_, lean_object* v_l_150_, lean_object* v_c_151_){
_start:
{
lean_object* v_prefix_152_; lean_object* v___x_153_; 
v_prefix_152_ = lean_ctor_get(v_c_151_, 0);
v___x_153_ = l_List_lengthTR___redArg(v_prefix_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos___boxed(lean_object* v_00_u03b1_154_, lean_object* v_l_155_, lean_object* v_c_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_List_Cursor_pos(v_00_u03b1_154_, v_l_155_, v_c_156_);
lean_dec_ref(v_c_156_);
lean_dec(v_l_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(lean_object* v_x_158_, lean_object* v_h__1_159_, lean_object* v_h__2_160_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_162_; 
lean_dec(v_h__1_159_);
v_a_161_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v_x_158_, 1);
v___x_162_ = lean_apply_1(v_h__2_160_, v_a_161_);
return v___x_162_;
}
else
{
lean_object* v_a_163_; lean_object* v___x_164_; 
lean_dec(v_h__2_160_);
v_a_163_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_a_163_);
lean_dec_ref_known(v_x_158_, 1);
v___x_164_ = lean_apply_1(v_h__1_159_, v_a_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter(lean_object* v_00_u03b1_165_, lean_object* v_00_u03b5_166_, lean_object* v_motive_167_, lean_object* v_x_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_172_; 
lean_dec(v_h__1_169_);
v_a_171_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_a_171_);
lean_dec_ref_known(v_x_168_, 1);
v___x_172_ = lean_apply_1(v_h__2_170_, v_a_171_);
return v___x_172_;
}
else
{
lean_object* v_a_173_; lean_object* v___x_174_; 
lean_dec(v_h__2_170_);
v_a_173_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_a_173_);
lean_dec_ref_known(v_x_168_, 1);
v___x_174_ = lean_apply_1(v_h__1_169_, v_a_173_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object* v_x_175_, lean_object* v_h__1_176_, lean_object* v_h__2_177_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_h__1_176_);
v___x_178_ = lean_box(0);
v___x_179_ = lean_apply_1(v_h__2_177_, v___x_178_);
return v___x_179_;
}
else
{
lean_object* v_val_180_; lean_object* v___x_181_; 
lean_dec(v_h__2_177_);
v_val_180_ = lean_ctor_get(v_x_175_, 0);
lean_inc(v_val_180_);
lean_dec_ref_known(v_x_175_, 1);
v___x_181_ = lean_apply_1(v_h__1_176_, v_val_180_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object* v_00_u03b1_182_, lean_object* v_motive_183_, lean_object* v_x_184_, lean_object* v_h__1_185_, lean_object* v_h__2_186_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec(v_h__1_185_);
v___x_187_ = lean_box(0);
v___x_188_ = lean_apply_1(v_h__2_186_, v___x_187_);
return v___x_188_;
}
else
{
lean_object* v_val_189_; lean_object* v___x_190_; 
lean_dec(v_h__2_186_);
v_val_189_ = lean_ctor_get(v_x_184_, 0);
lean_inc(v_val_189_);
lean_dec_ref_known(v_x_184_, 1);
v___x_190_ = lean_apply_1(v_h__1_185_, v_val_189_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0(lean_object* v_onReturn_191_, lean_object* v_snd_192_, lean_object* v___x_193_, lean_object* v___x_194_, lean_object* v_r_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_apply_2(v_onReturn_191_, v_r_195_, v_snd_192_);
lean_inc(v___x_194_);
lean_inc(v___x_193_);
v___x_197_ = l_Std_Do_SPred_and(v___x_193_, v___x_194_, v___x_196_);
v___x_198_ = l_Std_Do_SPred_and(v___x_193_, v___x_194_, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1(lean_object* v_ps_199_, lean_object* v_onReturn_200_, lean_object* v_onContinue_201_, lean_object* v_x_202_){
_start:
{
lean_object* v_snd_203_; lean_object* v_fst_204_; lean_object* v_snd_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___f_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_snd_203_ = lean_ctor_get(v_x_202_, 1);
lean_inc(v_snd_203_);
v_fst_204_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_fst_204_);
lean_dec_ref(v_x_202_);
v_snd_205_ = lean_ctor_get(v_snd_203_, 1);
lean_inc_n(v_snd_205_, 2);
lean_dec(v_snd_203_);
v___x_206_ = l_Std_Do_PostShape_args(v_ps_199_);
lean_inc_n(v___x_206_, 4);
v___x_207_ = l_Std_Do_SPred_pure___redArg(v___x_206_);
lean_inc(v___x_207_);
v___f_208_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_208_, 0, v_onReturn_200_);
lean_closure_set(v___f_208_, 1, v_snd_205_);
lean_closure_set(v___f_208_, 2, v___x_206_);
lean_closure_set(v___f_208_, 3, v___x_207_);
v___x_209_ = lean_apply_2(v_onContinue_201_, v_fst_204_, v_snd_205_);
v___x_210_ = l_Std_Do_SPred_and(v___x_206_, v___x_207_, v___x_209_);
v___x_211_ = l_Std_Do_SPred_exists___redArg(v___x_206_, v___f_208_);
v___x_212_ = l_Std_Do_SPred_or(v___x_206_, v___x_210_, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed(lean_object* v_ps_213_, lean_object* v_onReturn_214_, lean_object* v_onContinue_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1(v_ps_213_, v_onReturn_214_, v_onContinue_215_, v_x_216_);
lean_dec(v_ps_213_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg(lean_object* v_ps_218_, lean_object* v_onContinue_219_, lean_object* v_onReturn_220_, lean_object* v_onExcept_221_){
_start:
{
lean_object* v___f_222_; lean_object* v___x_223_; 
v___f_222_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_222_, 0, v_ps_218_);
lean_closure_set(v___f_222_, 1, v_onReturn_220_);
lean_closure_set(v___f_222_, 2, v_onContinue_219_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v___f_222_);
lean_ctor_set(v___x_223_, 1, v_onExcept_221_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn(lean_object* v_00_u03b2_224_, lean_object* v_ps_225_, lean_object* v_00_u03b1_226_, lean_object* v_xs_227_, lean_object* v_00_u03b3_228_, lean_object* v_onContinue_229_, lean_object* v_onReturn_230_, lean_object* v_onExcept_231_){
_start:
{
lean_object* v___f_232_; lean_object* v___x_233_; 
v___f_232_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_232_, 0, v_ps_225_);
lean_closure_set(v___f_232_, 1, v_onReturn_230_);
lean_closure_set(v___f_232_, 2, v_onContinue_229_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v___f_232_);
lean_ctor_set(v___x_233_, 1, v_onExcept_231_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___boxed(lean_object* v_00_u03b2_234_, lean_object* v_ps_235_, lean_object* v_00_u03b1_236_, lean_object* v_xs_237_, lean_object* v_00_u03b3_238_, lean_object* v_onContinue_239_, lean_object* v_onReturn_240_, lean_object* v_onExcept_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Do_Invariant_withEarlyReturn(v_00_u03b2_234_, v_ps_235_, v_00_u03b1_236_, v_xs_237_, v_00_u03b3_238_, v_onContinue_239_, v_onReturn_240_, v_onExcept_241_);
lean_dec(v_xs_237_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1(lean_object* v_ps_243_, lean_object* v_onReturn_244_, lean_object* v_onContinue_245_, lean_object* v_x_246_){
_start:
{
lean_object* v_snd_247_; lean_object* v_fst_248_; lean_object* v_snd_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___f_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_snd_247_ = lean_ctor_get(v_x_246_, 1);
lean_inc(v_snd_247_);
v_fst_248_ = lean_ctor_get(v_x_246_, 0);
lean_inc(v_fst_248_);
lean_dec_ref(v_x_246_);
v_snd_249_ = lean_ctor_get(v_snd_247_, 1);
lean_inc_n(v_snd_249_, 2);
lean_dec(v_snd_247_);
v___x_250_ = l_Std_Do_PostShape_args(v_ps_243_);
lean_inc_n(v___x_250_, 4);
v___x_251_ = l_Std_Do_SPred_pure___redArg(v___x_250_);
lean_inc(v___x_251_);
v___f_252_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_252_, 0, v_onReturn_244_);
lean_closure_set(v___f_252_, 1, v_snd_249_);
lean_closure_set(v___f_252_, 2, v___x_250_);
lean_closure_set(v___f_252_, 3, v___x_251_);
v___x_253_ = lean_apply_2(v_onContinue_245_, v_fst_248_, v_snd_249_);
v___x_254_ = l_Std_Do_SPred_and(v___x_250_, v___x_251_, v___x_253_);
v___x_255_ = l_Std_Do_SPred_exists___redArg(v___x_250_, v___f_252_);
v___x_256_ = l_Std_Do_SPred_or(v___x_250_, v___x_254_, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed(lean_object* v_ps_257_, lean_object* v_onReturn_258_, lean_object* v_onContinue_259_, lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1(v_ps_257_, v_onReturn_258_, v_onContinue_259_, v_x_260_);
lean_dec(v_ps_257_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg(lean_object* v_ps_262_, lean_object* v_onContinue_263_, lean_object* v_onReturn_264_, lean_object* v_onExcept_265_){
_start:
{
lean_object* v___f_266_; lean_object* v___x_267_; 
v___f_266_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_266_, 0, v_ps_262_);
lean_closure_set(v___f_266_, 1, v_onReturn_264_);
lean_closure_set(v___f_266_, 2, v_onContinue_263_);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___f_266_);
lean_ctor_set(v___x_267_, 1, v_onExcept_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo(lean_object* v_00_u03b2_268_, lean_object* v_ps_269_, lean_object* v_00_u03b1_270_, lean_object* v_xs_271_, lean_object* v_00_u03b3_272_, lean_object* v_onContinue_273_, lean_object* v_onReturn_274_, lean_object* v_onExcept_275_){
_start:
{
lean_object* v___f_276_; lean_object* v___x_277_; 
v___f_276_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_276_, 0, v_ps_269_);
lean_closure_set(v___f_276_, 1, v_onReturn_274_);
lean_closure_set(v___f_276_, 2, v_onContinue_273_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___f_276_);
lean_ctor_set(v___x_277_, 1, v_onExcept_275_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___boxed(lean_object* v_00_u03b2_278_, lean_object* v_ps_279_, lean_object* v_00_u03b1_280_, lean_object* v_xs_281_, lean_object* v_00_u03b3_282_, lean_object* v_onContinue_283_, lean_object* v_onReturn_284_, lean_object* v_onExcept_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Std_Do_Invariant_withEarlyReturnNewDo(v_00_u03b2_278_, v_ps_279_, v_00_u03b1_280_, v_xs_281_, v_00_u03b3_282_, v_onContinue_283_, v_onReturn_284_, v_onExcept_285_);
lean_dec(v_xs_281_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_287_, lean_object* v_h__1_288_, lean_object* v_h__2_289_){
_start:
{
if (lean_obj_tag(v_x_287_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_291_; 
lean_dec(v_h__2_289_);
v_a_290_ = lean_ctor_get(v_x_287_, 0);
lean_inc(v_a_290_);
lean_dec_ref_known(v_x_287_, 1);
v___x_291_ = lean_apply_1(v_h__1_288_, v_a_290_);
return v___x_291_;
}
else
{
lean_object* v_a_292_; lean_object* v___x_293_; 
lean_dec(v_h__1_288_);
v_a_292_ = lean_ctor_get(v_x_287_, 0);
lean_inc(v_a_292_);
lean_dec_ref_known(v_x_287_, 1);
v___x_293_ = lean_apply_1(v_h__2_289_, v_a_292_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_294_, lean_object* v_motive_295_, lean_object* v_x_296_, lean_object* v_h__1_297_, lean_object* v_h__2_298_){
_start:
{
if (lean_obj_tag(v_x_296_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_300_; 
lean_dec(v_h__2_298_);
v_a_299_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_a_299_);
lean_dec_ref_known(v_x_296_, 1);
v___x_300_ = lean_apply_1(v_h__1_297_, v_a_299_);
return v___x_300_;
}
else
{
lean_object* v_a_301_; lean_object* v___x_302_; 
lean_dec(v_h__1_297_);
v_a_301_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v_x_296_, 1);
v___x_302_ = lean_apply_1(v_h__2_298_, v_a_301_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1(lean_object* v_ps_303_, lean_object* v_onReturn_304_, lean_object* v_onContinue_305_, lean_object* v_x_306_){
_start:
{
lean_object* v_snd_307_; lean_object* v_fst_308_; lean_object* v_snd_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___f_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_snd_307_ = lean_ctor_get(v_x_306_, 1);
lean_inc(v_snd_307_);
v_fst_308_ = lean_ctor_get(v_x_306_, 0);
lean_inc(v_fst_308_);
lean_dec_ref(v_x_306_);
v_snd_309_ = lean_ctor_get(v_snd_307_, 1);
lean_inc_n(v_snd_309_, 2);
lean_dec(v_snd_307_);
v___x_310_ = l_Std_Do_PostShape_args(v_ps_303_);
lean_inc_n(v___x_310_, 4);
v___x_311_ = l_Std_Do_SPred_pure___redArg(v___x_310_);
lean_inc(v___x_311_);
v___f_312_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_312_, 0, v_onReturn_304_);
lean_closure_set(v___f_312_, 1, v_snd_309_);
lean_closure_set(v___f_312_, 2, v___x_310_);
lean_closure_set(v___f_312_, 3, v___x_311_);
v___x_313_ = lean_apply_2(v_onContinue_305_, v_fst_308_, v_snd_309_);
v___x_314_ = l_Std_Do_SPred_and(v___x_310_, v___x_311_, v___x_313_);
v___x_315_ = l_Std_Do_SPred_exists___redArg(v___x_310_, v___f_312_);
v___x_316_ = l_Std_Do_SPred_or(v___x_310_, v___x_314_, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed(lean_object* v_ps_317_, lean_object* v_onReturn_318_, lean_object* v_onContinue_319_, lean_object* v_x_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1(v_ps_317_, v_onReturn_318_, v_onContinue_319_, v_x_320_);
lean_dec(v_ps_317_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg(lean_object* v_ps_322_, lean_object* v_onContinue_323_, lean_object* v_onReturn_324_, lean_object* v_onExcept_325_){
_start:
{
lean_object* v___f_326_; lean_object* v___x_327_; 
v___f_326_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_326_, 0, v_ps_322_);
lean_closure_set(v___f_326_, 1, v_onReturn_324_);
lean_closure_set(v___f_326_, 2, v_onContinue_323_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___f_326_);
lean_ctor_set(v___x_327_, 1, v_onExcept_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn(lean_object* v_00_u03b2_328_, lean_object* v_ps_329_, lean_object* v_00_u03b3_330_, lean_object* v_s_331_, lean_object* v_onContinue_332_, lean_object* v_onReturn_333_, lean_object* v_onExcept_334_){
_start:
{
lean_object* v___f_335_; lean_object* v___x_336_; 
v___f_335_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_335_, 0, v_ps_329_);
lean_closure_set(v___f_335_, 1, v_onReturn_333_);
lean_closure_set(v___f_335_, 2, v_onContinue_332_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___f_335_);
lean_ctor_set(v___x_336_, 1, v_onExcept_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___boxed(lean_object* v_00_u03b2_337_, lean_object* v_ps_338_, lean_object* v_00_u03b3_339_, lean_object* v_s_340_, lean_object* v_onContinue_341_, lean_object* v_onReturn_342_, lean_object* v_onExcept_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Std_Do_StringInvariant_withEarlyReturn(v_00_u03b2_337_, v_ps_338_, v_00_u03b3_339_, v_s_340_, v_onContinue_341_, v_onReturn_342_, v_onExcept_343_);
lean_dec_ref(v_s_340_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1(lean_object* v_ps_345_, lean_object* v_onReturn_346_, lean_object* v_onContinue_347_, lean_object* v_x_348_){
_start:
{
lean_object* v_snd_349_; lean_object* v_fst_350_; lean_object* v_snd_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___f_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_snd_349_ = lean_ctor_get(v_x_348_, 1);
lean_inc(v_snd_349_);
v_fst_350_ = lean_ctor_get(v_x_348_, 0);
lean_inc(v_fst_350_);
lean_dec_ref(v_x_348_);
v_snd_351_ = lean_ctor_get(v_snd_349_, 1);
lean_inc_n(v_snd_351_, 2);
lean_dec(v_snd_349_);
v___x_352_ = l_Std_Do_PostShape_args(v_ps_345_);
lean_inc_n(v___x_352_, 4);
v___x_353_ = l_Std_Do_SPred_pure___redArg(v___x_352_);
lean_inc(v___x_353_);
v___f_354_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_354_, 0, v_onReturn_346_);
lean_closure_set(v___f_354_, 1, v_snd_351_);
lean_closure_set(v___f_354_, 2, v___x_352_);
lean_closure_set(v___f_354_, 3, v___x_353_);
v___x_355_ = lean_apply_2(v_onContinue_347_, v_fst_350_, v_snd_351_);
v___x_356_ = l_Std_Do_SPred_and(v___x_352_, v___x_353_, v___x_355_);
v___x_357_ = l_Std_Do_SPred_exists___redArg(v___x_352_, v___f_354_);
v___x_358_ = l_Std_Do_SPred_or(v___x_352_, v___x_356_, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed(lean_object* v_ps_359_, lean_object* v_onReturn_360_, lean_object* v_onContinue_361_, lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1(v_ps_359_, v_onReturn_360_, v_onContinue_361_, v_x_362_);
lean_dec(v_ps_359_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg(lean_object* v_ps_364_, lean_object* v_onContinue_365_, lean_object* v_onReturn_366_, lean_object* v_onExcept_367_){
_start:
{
lean_object* v___f_368_; lean_object* v___x_369_; 
v___f_368_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_368_, 0, v_ps_364_);
lean_closure_set(v___f_368_, 1, v_onReturn_366_);
lean_closure_set(v___f_368_, 2, v_onContinue_365_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___f_368_);
lean_ctor_set(v___x_369_, 1, v_onExcept_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo(lean_object* v_00_u03b2_370_, lean_object* v_ps_371_, lean_object* v_00_u03b3_372_, lean_object* v_s_373_, lean_object* v_onContinue_374_, lean_object* v_onReturn_375_, lean_object* v_onExcept_376_){
_start:
{
lean_object* v___f_377_; lean_object* v___x_378_; 
v___f_377_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_377_, 0, v_ps_371_);
lean_closure_set(v___f_377_, 1, v_onReturn_375_);
lean_closure_set(v___f_377_, 2, v_onContinue_374_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___f_377_);
lean_ctor_set(v___x_378_, 1, v_onExcept_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___boxed(lean_object* v_00_u03b2_379_, lean_object* v_ps_380_, lean_object* v_00_u03b3_381_, lean_object* v_s_382_, lean_object* v_onContinue_383_, lean_object* v_onReturn_384_, lean_object* v_onExcept_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Std_Do_StringInvariant_withEarlyReturnNewDo(v_00_u03b2_379_, v_ps_380_, v_00_u03b3_381_, v_s_382_, v_onContinue_383_, v_onReturn_384_, v_onExcept_385_);
lean_dec_ref(v_s_382_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn___redArg(lean_object* v_ps_387_, lean_object* v_onContinue_388_, lean_object* v_onReturn_389_, lean_object* v_onExcept_390_){
_start:
{
lean_object* v___f_391_; lean_object* v___x_392_; 
v___f_391_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_391_, 0, v_ps_387_);
lean_closure_set(v___f_391_, 1, v_onReturn_389_);
lean_closure_set(v___f_391_, 2, v_onContinue_388_);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v___f_391_);
lean_ctor_set(v___x_392_, 1, v_onExcept_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn(lean_object* v_00_u03b2_393_, lean_object* v_ps_394_, lean_object* v_00_u03b3_395_, lean_object* v_s_396_, lean_object* v_onContinue_397_, lean_object* v_onReturn_398_, lean_object* v_onExcept_399_){
_start:
{
lean_object* v___f_400_; lean_object* v___x_401_; 
v___f_400_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_400_, 0, v_ps_394_);
lean_closure_set(v___f_400_, 1, v_onReturn_398_);
lean_closure_set(v___f_400_, 2, v_onContinue_397_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v___f_400_);
lean_ctor_set(v___x_401_, 1, v_onExcept_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn___boxed(lean_object* v_00_u03b2_402_, lean_object* v_ps_403_, lean_object* v_00_u03b3_404_, lean_object* v_s_405_, lean_object* v_onContinue_406_, lean_object* v_onReturn_407_, lean_object* v_onExcept_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_Do_StringSliceInvariant_withEarlyReturn(v_00_u03b2_402_, v_ps_403_, v_00_u03b3_404_, v_s_405_, v_onContinue_406_, v_onReturn_407_, v_onExcept_408_);
lean_dec_ref(v_s_405_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo___redArg(lean_object* v_ps_410_, lean_object* v_onContinue_411_, lean_object* v_onReturn_412_, lean_object* v_onExcept_413_){
_start:
{
lean_object* v___f_414_; lean_object* v___x_415_; 
v___f_414_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_414_, 0, v_ps_410_);
lean_closure_set(v___f_414_, 1, v_onReturn_412_);
lean_closure_set(v___f_414_, 2, v_onContinue_411_);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v___f_414_);
lean_ctor_set(v___x_415_, 1, v_onExcept_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo(lean_object* v_00_u03b2_416_, lean_object* v_ps_417_, lean_object* v_00_u03b3_418_, lean_object* v_s_419_, lean_object* v_onContinue_420_, lean_object* v_onReturn_421_, lean_object* v_onExcept_422_){
_start:
{
lean_object* v___f_423_; lean_object* v___x_424_; 
v___f_423_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_423_, 0, v_ps_417_);
lean_closure_set(v___f_423_, 1, v_onReturn_421_);
lean_closure_set(v___f_423_, 2, v_onContinue_420_);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v___f_423_);
lean_ctor_set(v___x_424_, 1, v_onExcept_422_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo___boxed(lean_object* v_00_u03b2_425_, lean_object* v_ps_426_, lean_object* v_00_u03b3_427_, lean_object* v_s_428_, lean_object* v_onContinue_429_, lean_object* v_onReturn_430_, lean_object* v_onExcept_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo(v_00_u03b2_425_, v_ps_426_, v_00_u03b3_427_, v_s_428_, v_onContinue_429_, v_onReturn_430_, v_onExcept_431_);
lean_dec_ref(v_s_428_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_WhileVariant_eval___redArg(lean_object* v_ps_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = l_Std_Do_PostShape_args(v_ps_433_);
v___x_435_ = l_Std_Do_SVal_evalsTo___redArg(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_WhileVariant_eval___redArg___boxed(lean_object* v_ps_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_Do_WhileVariant_eval___redArg(v_ps_436_);
lean_dec(v_ps_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_WhileVariant_eval(lean_object* v_00_u03b1_438_, lean_object* v_ps_439_, lean_object* v_variant_440_, lean_object* v_a_441_, lean_object* v_n_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = l_Std_Do_PostShape_args(v_ps_439_);
v___x_444_ = l_Std_Do_SVal_evalsTo___redArg(v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_WhileVariant_eval___boxed(lean_object* v_00_u03b1_445_, lean_object* v_ps_446_, lean_object* v_variant_447_, lean_object* v_a_448_, lean_object* v_n_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_Do_WhileVariant_eval(v_00_u03b1_445_, v_ps_446_, v_variant_447_, v_a_448_, v_n_449_);
lean_dec(v_n_449_);
lean_dec(v_a_448_);
lean_dec(v_variant_447_);
lean_dec(v_ps_446_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter___redArg(lean_object* v_____do__lift_451_, lean_object* v_h__1_452_, lean_object* v_h__2_453_){
_start:
{
if (lean_obj_tag(v_____do__lift_451_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_455_; 
lean_dec(v_h__2_453_);
v_a_454_ = lean_ctor_get(v_____do__lift_451_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v_____do__lift_451_, 1);
v___x_455_ = lean_apply_1(v_h__1_452_, v_a_454_);
return v___x_455_;
}
else
{
lean_object* v_a_456_; lean_object* v___x_457_; 
lean_dec(v_h__1_452_);
v_a_456_ = lean_ctor_get(v_____do__lift_451_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v_____do__lift_451_, 1);
v___x_457_ = lean_apply_1(v_h__2_453_, v_a_456_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter(lean_object* v_00_u03b2_458_, lean_object* v_motive_459_, lean_object* v_____do__lift_460_, lean_object* v_h__1_461_, lean_object* v_h__2_462_){
_start:
{
if (lean_obj_tag(v_____do__lift_460_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; 
lean_dec(v_h__2_462_);
v_a_463_ = lean_ctor_get(v_____do__lift_460_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v_____do__lift_460_, 1);
v___x_464_ = lean_apply_1(v_h__1_461_, v_a_463_);
return v___x_464_;
}
else
{
lean_object* v_a_465_; lean_object* v___x_466_; 
lean_dec(v_h__1_461_);
v_a_465_ = lean_ctor_get(v_____do__lift_460_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v_____do__lift_460_, 1);
v___x_466_ = lean_apply_1(v_h__2_462_, v_a_465_);
return v___x_466_;
}
}
}
lean_object* runtime_initialize_Std_Do_Triple_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Internal_Order_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Iterate(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_Triple_SpecLemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Internal_Order_While(builtin);
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
res = runtime_initialize_Init_Data_List_Impl(builtin);
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
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Internal_Order_While(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_Range(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
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
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Internal_Order_While(builtin);
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
res = initialize_Init_Data_List_Impl(builtin);
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
