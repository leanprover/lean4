// Lean compiler output
// Module: Std.Do.Triple.SpecLemmas
// Imports: public import Std.Do.Triple.Basic public import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic public import Init.Data.Slice.Array public import Init.While public import Init.Internal.Order.While public import Init.Data.Iterators.Lemmas.Combinators.FilterMap public import Init.Data.Range import Init.Data.Iterators.Lemmas import Init.Data.List.Nat.Range import Init.Data.List.Nat.TakeDrop import Init.Data.List.Range import Init.Data.List.TakeDrop import Init.Data.Nat.Mod import Init.Data.Slice.Lemmas import Init.Omega public import Init.Data.String.Defs public import Init.Data.String.Iterate import Init.Data.String.Lemmas.Splits import Init.Data.String.Termination import Init.Data.String.Lemmas.Iterate
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
lean_object* l_Std_Do_SVal_evalsTo___redArg(lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_toList(lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_toList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_Cursor_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_Cursor_cast___redArg(lean_object* v_c_16_){
_start:
{
lean_object* v_prefix_17_; lean_object* v_suffix_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_25_; 
v_prefix_17_ = lean_ctor_get(v_c_16_, 0);
v_suffix_18_ = lean_ctor_get(v_c_16_, 1);
v_isSharedCheck_25_ = !lean_is_exclusive(v_c_16_);
if (v_isSharedCheck_25_ == 0)
{
v___x_20_ = v_c_16_;
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_suffix_18_);
lean_inc(v_prefix_17_);
lean_dec(v_c_16_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
if (v_isShared_21_ == 0)
{
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_prefix_17_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v_suffix_18_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_Cursor_cast(lean_object* v_00_u03b1_26_, lean_object* v_l_27_, lean_object* v_l_x27_28_, lean_object* v_c_29_, lean_object* v_h_30_){
_start:
{
lean_object* v_prefix_31_; lean_object* v_suffix_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
v_prefix_31_ = lean_ctor_get(v_c_29_, 0);
v_suffix_32_ = lean_ctor_get(v_c_29_, 1);
v_isSharedCheck_39_ = !lean_is_exclusive(v_c_29_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v_c_29_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_suffix_32_);
lean_inc(v_prefix_31_);
lean_dec(v_c_29_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_prefix_31_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_suffix_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_Cursor_cast___boxed(lean_object* v_00_u03b1_40_, lean_object* v_l_41_, lean_object* v_l_x27_42_, lean_object* v_c_43_, lean_object* v_h_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_List_Cursor_cast(v_00_u03b1_40_, v_l_41_, v_l_x27_42_, v_c_43_, v_h_44_);
lean_dec(v_l_x27_42_);
lean_dec(v_l_41_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_at___redArg(lean_object* v_l_46_, lean_object* v_n_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
lean_inc(v_l_46_);
v___x_48_ = l_List_take___redArg(v_n_47_, v_l_46_);
v___x_49_ = l_List_drop___redArg(v_n_47_, v_l_46_);
lean_dec(v_l_46_);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_48_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_at(lean_object* v_00_u03b1_51_, lean_object* v_l_52_, lean_object* v_n_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_List_Cursor_at___redArg(v_l_52_, v_n_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_begin___redArg(lean_object* v_l_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = l_List_Cursor_at___redArg(v_l_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_begin(lean_object* v_00_u03b1_58_, lean_object* v_l_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = l_List_Cursor_at___redArg(v_l_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_end___redArg(lean_object* v_l_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = l_List_lengthTR___redArg(v_l_62_);
v___x_64_ = l_List_Cursor_at___redArg(v_l_62_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_end(lean_object* v_00_u03b1_65_, lean_object* v_l_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = l_List_lengthTR___redArg(v_l_66_);
v___x_68_ = l_List_Cursor_at___redArg(v_l_66_, v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__13(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__12));
v___x_94_ = l_Lean_mkAtom(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__14(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__13, &l_List_Cursor_current___auto__1___closed__13_once, _init_l_List_Cursor_current___auto__1___closed__13);
v___x_96_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__5));
v___x_97_ = lean_array_push(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__15(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__14, &l_List_Cursor_current___auto__1___closed__14_once, _init_l_List_Cursor_current___auto__1___closed__14);
v___x_99_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__11));
v___x_100_ = lean_box(2);
v___x_101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_98_);
return v___x_101_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__16(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__15, &l_List_Cursor_current___auto__1___closed__15_once, _init_l_List_Cursor_current___auto__1___closed__15);
v___x_103_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__5));
v___x_104_ = lean_array_push(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__17(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__16, &l_List_Cursor_current___auto__1___closed__16_once, _init_l_List_Cursor_current___auto__1___closed__16);
v___x_106_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__9));
v___x_107_ = lean_box(2);
v___x_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
lean_ctor_set(v___x_108_, 2, v___x_105_);
return v___x_108_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__18(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__17, &l_List_Cursor_current___auto__1___closed__17_once, _init_l_List_Cursor_current___auto__1___closed__17);
v___x_110_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__5));
v___x_111_ = lean_array_push(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__19(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__18, &l_List_Cursor_current___auto__1___closed__18_once, _init_l_List_Cursor_current___auto__1___closed__18);
v___x_113_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__7));
v___x_114_ = lean_box(2);
v___x_115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
lean_ctor_set(v___x_115_, 2, v___x_112_);
return v___x_115_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__20(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__19, &l_List_Cursor_current___auto__1___closed__19_once, _init_l_List_Cursor_current___auto__1___closed__19);
v___x_117_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__5));
v___x_118_ = lean_array_push(v___x_117_, v___x_116_);
return v___x_118_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1___closed__21(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_119_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__20, &l_List_Cursor_current___auto__1___closed__20_once, _init_l_List_Cursor_current___auto__1___closed__20);
v___x_120_ = ((lean_object*)(l_List_Cursor_current___auto__1___closed__4));
v___x_121_ = lean_box(2);
v___x_122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v___x_120_);
lean_ctor_set(v___x_122_, 2, v___x_119_);
return v___x_122_;
}
}
static lean_object* _init_l_List_Cursor_current___auto__1(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__21, &l_List_Cursor_current___auto__1___closed__21_once, _init_l_List_Cursor_current___auto__1___closed__21);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current___redArg(lean_object* v_c_124_){
_start:
{
lean_object* v_suffix_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v_suffix_125_ = lean_ctor_get(v_c_124_, 1);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = l_List_get___redArg(v_suffix_125_, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current___redArg___boxed(lean_object* v_c_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_List_Cursor_current___redArg(v_c_128_);
lean_dec_ref(v_c_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current(lean_object* v_00_u03b1_130_, lean_object* v_l_131_, lean_object* v_c_132_, lean_object* v_h_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_List_Cursor_current___redArg(v_c_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_current___boxed(lean_object* v_00_u03b1_135_, lean_object* v_l_136_, lean_object* v_c_137_, lean_object* v_h_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_List_Cursor_current(v_00_u03b1_135_, v_l_136_, v_c_137_, v_h_138_);
lean_dec_ref(v_c_137_);
lean_dec(v_l_136_);
return v_res_139_;
}
}
static lean_object* _init_l_List_Cursor_tail___auto__1(void){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_List_Cursor_current___auto__1___closed__21, &l_List_Cursor_current___auto__1___closed__21_once, _init_l_List_Cursor_current___auto__1___closed__21);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_tail___redArg(lean_object* v_s_141_){
_start:
{
lean_object* v_prefix_142_; lean_object* v_suffix_143_; lean_object* v___x_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_158_; 
v_prefix_142_ = lean_ctor_get(v_s_141_, 0);
lean_inc(v_prefix_142_);
v_suffix_143_ = lean_ctor_get(v_s_141_, 1);
lean_inc(v_suffix_143_);
v___x_144_ = l_List_Cursor_current___redArg(v_s_141_);
v_isSharedCheck_158_ = !lean_is_exclusive(v_s_141_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; lean_object* v_unused_160_; 
v_unused_159_ = lean_ctor_get(v_s_141_, 1);
lean_dec(v_unused_159_);
v_unused_160_ = lean_ctor_get(v_s_141_, 0);
lean_dec(v_unused_160_);
v___x_146_ = v_s_141_;
v_isShared_147_ = v_isSharedCheck_158_;
goto v_resetjp_145_;
}
else
{
lean_dec(v_s_141_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_158_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_box(0);
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_144_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = l_List_appendTR___redArg(v_prefix_142_, v___x_149_);
if (lean_obj_tag(v_suffix_143_) == 0)
{
lean_object* v___x_152_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_150_);
v___x_152_ = v___x_146_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_suffix_143_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
else
{
lean_object* v_tail_154_; lean_object* v___x_156_; 
v_tail_154_ = lean_ctor_get(v_suffix_143_, 1);
lean_inc(v_tail_154_);
lean_dec_ref_known(v_suffix_143_, 2);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v_tail_154_);
lean_ctor_set(v___x_146_, 0, v___x_150_);
v___x_156_ = v___x_146_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_tail_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_Cursor_tail(lean_object* v_00_u03b1_161_, lean_object* v_l_162_, lean_object* v_s_163_, lean_object* v_h_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_List_Cursor_tail___redArg(v_s_163_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_tail___boxed(lean_object* v_00_u03b1_166_, lean_object* v_l_167_, lean_object* v_s_168_, lean_object* v_h_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_List_Cursor_tail(v_00_u03b1_166_, v_l_167_, v_s_168_, v_h_169_);
lean_dec(v_l_167_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos___redArg(lean_object* v_c_171_){
_start:
{
lean_object* v_prefix_172_; lean_object* v___x_173_; 
v_prefix_172_ = lean_ctor_get(v_c_171_, 0);
v___x_173_ = l_List_lengthTR___redArg(v_prefix_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos___redArg___boxed(lean_object* v_c_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_List_Cursor_pos___redArg(v_c_174_);
lean_dec_ref(v_c_174_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos(lean_object* v_00_u03b1_176_, lean_object* v_l_177_, lean_object* v_c_178_){
_start:
{
lean_object* v_prefix_179_; lean_object* v___x_180_; 
v_prefix_179_ = lean_ctor_get(v_c_178_, 0);
v___x_180_ = l_List_lengthTR___redArg(v_prefix_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_List_Cursor_pos___boxed(lean_object* v_00_u03b1_181_, lean_object* v_l_182_, lean_object* v_c_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_List_Cursor_pos(v_00_u03b1_181_, v_l_182_, v_c_183_);
lean_dec_ref(v_c_183_);
lean_dec(v_l_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(lean_object* v_x_185_, lean_object* v_h__1_186_, lean_object* v_h__2_187_){
_start:
{
if (lean_obj_tag(v_x_185_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_189_; 
lean_dec(v_h__1_186_);
v_a_188_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_a_188_);
lean_dec_ref_known(v_x_185_, 1);
v___x_189_ = lean_apply_1(v_h__2_187_, v_a_188_);
return v___x_189_;
}
else
{
lean_object* v_a_190_; lean_object* v___x_191_; 
lean_dec(v_h__2_187_);
v_a_190_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_a_190_);
lean_dec_ref_known(v_x_185_, 1);
v___x_191_ = lean_apply_1(v_h__1_186_, v_a_190_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter(lean_object* v_00_u03b1_192_, lean_object* v_00_u03b5_193_, lean_object* v_motive_194_, lean_object* v_x_195_, lean_object* v_h__1_196_, lean_object* v_h__2_197_){
_start:
{
if (lean_obj_tag(v_x_195_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_199_; 
lean_dec(v_h__1_196_);
v_a_198_ = lean_ctor_get(v_x_195_, 0);
lean_inc(v_a_198_);
lean_dec_ref_known(v_x_195_, 1);
v___x_199_ = lean_apply_1(v_h__2_197_, v_a_198_);
return v___x_199_;
}
else
{
lean_object* v_a_200_; lean_object* v___x_201_; 
lean_dec(v_h__2_197_);
v_a_200_ = lean_ctor_get(v_x_195_, 0);
lean_inc(v_a_200_);
lean_dec_ref_known(v_x_195_, 1);
v___x_201_ = lean_apply_1(v_h__1_196_, v_a_200_);
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object* v_x_202_, lean_object* v_h__1_203_, lean_object* v_h__2_204_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec(v_h__1_203_);
v___x_205_ = lean_box(0);
v___x_206_ = lean_apply_1(v_h__2_204_, v___x_205_);
return v___x_206_;
}
else
{
lean_object* v_val_207_; lean_object* v___x_208_; 
lean_dec(v_h__2_204_);
v_val_207_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v_x_202_, 1);
v___x_208_ = lean_apply_1(v_h__1_203_, v_val_207_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object* v_00_u03b1_209_, lean_object* v_motive_210_, lean_object* v_x_211_, lean_object* v_h__1_212_, lean_object* v_h__2_213_){
_start:
{
if (lean_obj_tag(v_x_211_) == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v_h__1_212_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_apply_1(v_h__2_213_, v___x_214_);
return v___x_215_;
}
else
{
lean_object* v_val_216_; lean_object* v___x_217_; 
lean_dec(v_h__2_213_);
v_val_216_ = lean_ctor_get(v_x_211_, 0);
lean_inc(v_val_216_);
lean_dec_ref_known(v_x_211_, 1);
v___x_217_ = lean_apply_1(v_h__1_212_, v_val_216_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0(lean_object* v_onReturn_218_, lean_object* v_snd_219_, lean_object* v___x_220_, lean_object* v___x_221_, lean_object* v_r_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_223_ = lean_apply_2(v_onReturn_218_, v_r_222_, v_snd_219_);
lean_inc(v___x_221_);
lean_inc(v___x_220_);
v___x_224_ = l_Std_Do_SPred_and(v___x_220_, v___x_221_, v___x_223_);
v___x_225_ = l_Std_Do_SPred_and(v___x_220_, v___x_221_, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1(lean_object* v_ps_226_, lean_object* v_onReturn_227_, lean_object* v_onContinue_228_, lean_object* v_x_229_){
_start:
{
lean_object* v_snd_230_; lean_object* v_fst_231_; lean_object* v_snd_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___f_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_snd_230_ = lean_ctor_get(v_x_229_, 1);
lean_inc(v_snd_230_);
v_fst_231_ = lean_ctor_get(v_x_229_, 0);
lean_inc(v_fst_231_);
lean_dec_ref(v_x_229_);
v_snd_232_ = lean_ctor_get(v_snd_230_, 1);
lean_inc_n(v_snd_232_, 2);
lean_dec(v_snd_230_);
v___x_233_ = l_Std_Do_PostShape_args(v_ps_226_);
lean_inc_n(v___x_233_, 4);
v___x_234_ = l_Std_Do_SPred_pure___redArg(v___x_233_);
lean_inc(v___x_234_);
v___f_235_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_235_, 0, v_onReturn_227_);
lean_closure_set(v___f_235_, 1, v_snd_232_);
lean_closure_set(v___f_235_, 2, v___x_233_);
lean_closure_set(v___f_235_, 3, v___x_234_);
v___x_236_ = lean_apply_2(v_onContinue_228_, v_fst_231_, v_snd_232_);
v___x_237_ = l_Std_Do_SPred_and(v___x_233_, v___x_234_, v___x_236_);
v___x_238_ = l_Std_Do_SPred_exists___redArg(v___x_233_, v___f_235_);
v___x_239_ = l_Std_Do_SPred_or(v___x_233_, v___x_237_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed(lean_object* v_ps_240_, lean_object* v_onReturn_241_, lean_object* v_onContinue_242_, lean_object* v_x_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1(v_ps_240_, v_onReturn_241_, v_onContinue_242_, v_x_243_);
lean_dec(v_ps_240_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___redArg(lean_object* v_ps_245_, lean_object* v_onContinue_246_, lean_object* v_onReturn_247_, lean_object* v_onExcept_248_){
_start:
{
lean_object* v___f_249_; lean_object* v___x_250_; 
v___f_249_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_249_, 0, v_ps_245_);
lean_closure_set(v___f_249_, 1, v_onReturn_247_);
lean_closure_set(v___f_249_, 2, v_onContinue_246_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___f_249_);
lean_ctor_set(v___x_250_, 1, v_onExcept_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn(lean_object* v_00_u03b2_251_, lean_object* v_ps_252_, lean_object* v_00_u03b1_253_, lean_object* v_xs_254_, lean_object* v_00_u03b3_255_, lean_object* v_onContinue_256_, lean_object* v_onReturn_257_, lean_object* v_onExcept_258_){
_start:
{
lean_object* v___f_259_; lean_object* v___x_260_; 
v___f_259_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_259_, 0, v_ps_252_);
lean_closure_set(v___f_259_, 1, v_onReturn_257_);
lean_closure_set(v___f_259_, 2, v_onContinue_256_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___f_259_);
lean_ctor_set(v___x_260_, 1, v_onExcept_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturn___boxed(lean_object* v_00_u03b2_261_, lean_object* v_ps_262_, lean_object* v_00_u03b1_263_, lean_object* v_xs_264_, lean_object* v_00_u03b3_265_, lean_object* v_onContinue_266_, lean_object* v_onReturn_267_, lean_object* v_onExcept_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Std_Do_Invariant_withEarlyReturn(v_00_u03b2_261_, v_ps_262_, v_00_u03b1_263_, v_xs_264_, v_00_u03b3_265_, v_onContinue_266_, v_onReturn_267_, v_onExcept_268_);
lean_dec(v_xs_264_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1(lean_object* v_ps_270_, lean_object* v_onReturn_271_, lean_object* v_onContinue_272_, lean_object* v_x_273_){
_start:
{
lean_object* v_snd_274_; lean_object* v_fst_275_; lean_object* v_snd_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___f_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_snd_274_ = lean_ctor_get(v_x_273_, 1);
lean_inc(v_snd_274_);
v_fst_275_ = lean_ctor_get(v_x_273_, 0);
lean_inc(v_fst_275_);
lean_dec_ref(v_x_273_);
v_snd_276_ = lean_ctor_get(v_snd_274_, 1);
lean_inc_n(v_snd_276_, 2);
lean_dec(v_snd_274_);
v___x_277_ = l_Std_Do_PostShape_args(v_ps_270_);
lean_inc_n(v___x_277_, 4);
v___x_278_ = l_Std_Do_SPred_pure___redArg(v___x_277_);
lean_inc(v___x_278_);
v___f_279_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_279_, 0, v_onReturn_271_);
lean_closure_set(v___f_279_, 1, v_snd_276_);
lean_closure_set(v___f_279_, 2, v___x_277_);
lean_closure_set(v___f_279_, 3, v___x_278_);
v___x_280_ = lean_apply_2(v_onContinue_272_, v_fst_275_, v_snd_276_);
v___x_281_ = l_Std_Do_SPred_and(v___x_277_, v___x_278_, v___x_280_);
v___x_282_ = l_Std_Do_SPred_exists___redArg(v___x_277_, v___f_279_);
v___x_283_ = l_Std_Do_SPred_or(v___x_277_, v___x_281_, v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed(lean_object* v_ps_284_, lean_object* v_onReturn_285_, lean_object* v_onContinue_286_, lean_object* v_x_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1(v_ps_284_, v_onReturn_285_, v_onContinue_286_, v_x_287_);
lean_dec(v_ps_284_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___redArg(lean_object* v_ps_289_, lean_object* v_onContinue_290_, lean_object* v_onReturn_291_, lean_object* v_onExcept_292_){
_start:
{
lean_object* v___f_293_; lean_object* v___x_294_; 
v___f_293_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_293_, 0, v_ps_289_);
lean_closure_set(v___f_293_, 1, v_onReturn_291_);
lean_closure_set(v___f_293_, 2, v_onContinue_290_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v___f_293_);
lean_ctor_set(v___x_294_, 1, v_onExcept_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo(lean_object* v_00_u03b2_295_, lean_object* v_ps_296_, lean_object* v_00_u03b1_297_, lean_object* v_xs_298_, lean_object* v_00_u03b3_299_, lean_object* v_onContinue_300_, lean_object* v_onReturn_301_, lean_object* v_onExcept_302_){
_start:
{
lean_object* v___f_303_; lean_object* v___x_304_; 
v___f_303_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_303_, 0, v_ps_296_);
lean_closure_set(v___f_303_, 1, v_onReturn_301_);
lean_closure_set(v___f_303_, 2, v_onContinue_300_);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v___f_303_);
lean_ctor_set(v___x_304_, 1, v_onExcept_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Invariant_withEarlyReturnNewDo___boxed(lean_object* v_00_u03b2_305_, lean_object* v_ps_306_, lean_object* v_00_u03b1_307_, lean_object* v_xs_308_, lean_object* v_00_u03b3_309_, lean_object* v_onContinue_310_, lean_object* v_onReturn_311_, lean_object* v_onExcept_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_Do_Invariant_withEarlyReturnNewDo(v_00_u03b2_305_, v_ps_306_, v_00_u03b1_307_, v_xs_308_, v_00_u03b3_309_, v_onContinue_310_, v_onReturn_311_, v_onExcept_312_);
lean_dec(v_xs_308_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_314_, lean_object* v_h__1_315_, lean_object* v_h__2_316_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_318_; 
lean_dec(v_h__2_316_);
v_a_317_ = lean_ctor_get(v_x_314_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v_x_314_, 1);
v___x_318_ = lean_apply_1(v_h__1_315_, v_a_317_);
return v___x_318_;
}
else
{
lean_object* v_a_319_; lean_object* v___x_320_; 
lean_dec(v_h__1_315_);
v_a_319_ = lean_ctor_get(v_x_314_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v_x_314_, 1);
v___x_320_ = lean_apply_1(v_h__2_316_, v_a_319_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_321_, lean_object* v_motive_322_, lean_object* v_x_323_, lean_object* v_h__1_324_, lean_object* v_h__2_325_){
_start:
{
if (lean_obj_tag(v_x_323_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_327_; 
lean_dec(v_h__2_325_);
v_a_326_ = lean_ctor_get(v_x_323_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v_x_323_, 1);
v___x_327_ = lean_apply_1(v_h__1_324_, v_a_326_);
return v___x_327_;
}
else
{
lean_object* v_a_328_; lean_object* v___x_329_; 
lean_dec(v_h__1_324_);
v_a_328_ = lean_ctor_get(v_x_323_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v_x_323_, 1);
v___x_329_ = lean_apply_1(v_h__2_325_, v_a_328_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1(lean_object* v_ps_330_, lean_object* v_onReturn_331_, lean_object* v_onContinue_332_, lean_object* v_x_333_){
_start:
{
lean_object* v_snd_334_; lean_object* v_fst_335_; lean_object* v_snd_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___f_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_snd_334_ = lean_ctor_get(v_x_333_, 1);
lean_inc(v_snd_334_);
v_fst_335_ = lean_ctor_get(v_x_333_, 0);
lean_inc(v_fst_335_);
lean_dec_ref(v_x_333_);
v_snd_336_ = lean_ctor_get(v_snd_334_, 1);
lean_inc_n(v_snd_336_, 2);
lean_dec(v_snd_334_);
v___x_337_ = l_Std_Do_PostShape_args(v_ps_330_);
lean_inc_n(v___x_337_, 4);
v___x_338_ = l_Std_Do_SPred_pure___redArg(v___x_337_);
lean_inc(v___x_338_);
v___f_339_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_339_, 0, v_onReturn_331_);
lean_closure_set(v___f_339_, 1, v_snd_336_);
lean_closure_set(v___f_339_, 2, v___x_337_);
lean_closure_set(v___f_339_, 3, v___x_338_);
v___x_340_ = lean_apply_2(v_onContinue_332_, v_fst_335_, v_snd_336_);
v___x_341_ = l_Std_Do_SPred_and(v___x_337_, v___x_338_, v___x_340_);
v___x_342_ = l_Std_Do_SPred_exists___redArg(v___x_337_, v___f_339_);
v___x_343_ = l_Std_Do_SPred_or(v___x_337_, v___x_341_, v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed(lean_object* v_ps_344_, lean_object* v_onReturn_345_, lean_object* v_onContinue_346_, lean_object* v_x_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1(v_ps_344_, v_onReturn_345_, v_onContinue_346_, v_x_347_);
lean_dec(v_ps_344_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___redArg(lean_object* v_ps_349_, lean_object* v_onContinue_350_, lean_object* v_onReturn_351_, lean_object* v_onExcept_352_){
_start:
{
lean_object* v___f_353_; lean_object* v___x_354_; 
v___f_353_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_353_, 0, v_ps_349_);
lean_closure_set(v___f_353_, 1, v_onReturn_351_);
lean_closure_set(v___f_353_, 2, v_onContinue_350_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___f_353_);
lean_ctor_set(v___x_354_, 1, v_onExcept_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn(lean_object* v_00_u03b2_355_, lean_object* v_ps_356_, lean_object* v_00_u03b3_357_, lean_object* v_s_358_, lean_object* v_onContinue_359_, lean_object* v_onReturn_360_, lean_object* v_onExcept_361_){
_start:
{
lean_object* v___f_362_; lean_object* v___x_363_; 
v___f_362_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_362_, 0, v_ps_356_);
lean_closure_set(v___f_362_, 1, v_onReturn_360_);
lean_closure_set(v___f_362_, 2, v_onContinue_359_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___f_362_);
lean_ctor_set(v___x_363_, 1, v_onExcept_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturn___boxed(lean_object* v_00_u03b2_364_, lean_object* v_ps_365_, lean_object* v_00_u03b3_366_, lean_object* v_s_367_, lean_object* v_onContinue_368_, lean_object* v_onReturn_369_, lean_object* v_onExcept_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Std_Do_StringInvariant_withEarlyReturn(v_00_u03b2_364_, v_ps_365_, v_00_u03b3_366_, v_s_367_, v_onContinue_368_, v_onReturn_369_, v_onExcept_370_);
lean_dec_ref(v_s_367_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1(lean_object* v_ps_372_, lean_object* v_onReturn_373_, lean_object* v_onContinue_374_, lean_object* v_x_375_){
_start:
{
lean_object* v_snd_376_; lean_object* v_fst_377_; lean_object* v_snd_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___f_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_snd_376_ = lean_ctor_get(v_x_375_, 1);
lean_inc(v_snd_376_);
v_fst_377_ = lean_ctor_get(v_x_375_, 0);
lean_inc(v_fst_377_);
lean_dec_ref(v_x_375_);
v_snd_378_ = lean_ctor_get(v_snd_376_, 1);
lean_inc_n(v_snd_378_, 2);
lean_dec(v_snd_376_);
v___x_379_ = l_Std_Do_PostShape_args(v_ps_372_);
lean_inc_n(v___x_379_, 4);
v___x_380_ = l_Std_Do_SPred_pure___redArg(v___x_379_);
lean_inc(v___x_380_);
v___f_381_ = lean_alloc_closure((void*)(l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_381_, 0, v_onReturn_373_);
lean_closure_set(v___f_381_, 1, v_snd_378_);
lean_closure_set(v___f_381_, 2, v___x_379_);
lean_closure_set(v___f_381_, 3, v___x_380_);
v___x_382_ = lean_apply_2(v_onContinue_374_, v_fst_377_, v_snd_378_);
v___x_383_ = l_Std_Do_SPred_and(v___x_379_, v___x_380_, v___x_382_);
v___x_384_ = l_Std_Do_SPred_exists___redArg(v___x_379_, v___f_381_);
v___x_385_ = l_Std_Do_SPred_or(v___x_379_, v___x_383_, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed(lean_object* v_ps_386_, lean_object* v_onReturn_387_, lean_object* v_onContinue_388_, lean_object* v_x_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1(v_ps_386_, v_onReturn_387_, v_onContinue_388_, v_x_389_);
lean_dec(v_ps_386_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg(lean_object* v_ps_391_, lean_object* v_onContinue_392_, lean_object* v_onReturn_393_, lean_object* v_onExcept_394_){
_start:
{
lean_object* v___f_395_; lean_object* v___x_396_; 
v___f_395_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_395_, 0, v_ps_391_);
lean_closure_set(v___f_395_, 1, v_onReturn_393_);
lean_closure_set(v___f_395_, 2, v_onContinue_392_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___f_395_);
lean_ctor_set(v___x_396_, 1, v_onExcept_394_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo(lean_object* v_00_u03b2_397_, lean_object* v_ps_398_, lean_object* v_00_u03b3_399_, lean_object* v_s_400_, lean_object* v_onContinue_401_, lean_object* v_onReturn_402_, lean_object* v_onExcept_403_){
_start:
{
lean_object* v___f_404_; lean_object* v___x_405_; 
v___f_404_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_404_, 0, v_ps_398_);
lean_closure_set(v___f_404_, 1, v_onReturn_402_);
lean_closure_set(v___f_404_, 2, v_onContinue_401_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___f_404_);
lean_ctor_set(v___x_405_, 1, v_onExcept_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringInvariant_withEarlyReturnNewDo___boxed(lean_object* v_00_u03b2_406_, lean_object* v_ps_407_, lean_object* v_00_u03b3_408_, lean_object* v_s_409_, lean_object* v_onContinue_410_, lean_object* v_onReturn_411_, lean_object* v_onExcept_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Std_Do_StringInvariant_withEarlyReturnNewDo(v_00_u03b2_406_, v_ps_407_, v_00_u03b3_408_, v_s_409_, v_onContinue_410_, v_onReturn_411_, v_onExcept_412_);
lean_dec_ref(v_s_409_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn___redArg(lean_object* v_ps_414_, lean_object* v_onContinue_415_, lean_object* v_onReturn_416_, lean_object* v_onExcept_417_){
_start:
{
lean_object* v___f_418_; lean_object* v___x_419_; 
v___f_418_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_418_, 0, v_ps_414_);
lean_closure_set(v___f_418_, 1, v_onReturn_416_);
lean_closure_set(v___f_418_, 2, v_onContinue_415_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___f_418_);
lean_ctor_set(v___x_419_, 1, v_onExcept_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn(lean_object* v_00_u03b2_420_, lean_object* v_ps_421_, lean_object* v_00_u03b3_422_, lean_object* v_s_423_, lean_object* v_onContinue_424_, lean_object* v_onReturn_425_, lean_object* v_onExcept_426_){
_start:
{
lean_object* v___f_427_; lean_object* v___x_428_; 
v___f_427_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_427_, 0, v_ps_421_);
lean_closure_set(v___f_427_, 1, v_onReturn_425_);
lean_closure_set(v___f_427_, 2, v_onContinue_424_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v___f_427_);
lean_ctor_set(v___x_428_, 1, v_onExcept_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturn___boxed(lean_object* v_00_u03b2_429_, lean_object* v_ps_430_, lean_object* v_00_u03b3_431_, lean_object* v_s_432_, lean_object* v_onContinue_433_, lean_object* v_onReturn_434_, lean_object* v_onExcept_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_Do_StringSliceInvariant_withEarlyReturn(v_00_u03b2_429_, v_ps_430_, v_00_u03b3_431_, v_s_432_, v_onContinue_433_, v_onReturn_434_, v_onExcept_435_);
lean_dec_ref(v_s_432_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo___redArg(lean_object* v_ps_437_, lean_object* v_onContinue_438_, lean_object* v_onReturn_439_, lean_object* v_onExcept_440_){
_start:
{
lean_object* v___f_441_; lean_object* v___x_442_; 
v___f_441_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_441_, 0, v_ps_437_);
lean_closure_set(v___f_441_, 1, v_onReturn_439_);
lean_closure_set(v___f_441_, 2, v_onContinue_438_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___f_441_);
lean_ctor_set(v___x_442_, 1, v_onExcept_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo(lean_object* v_00_u03b2_443_, lean_object* v_ps_444_, lean_object* v_00_u03b3_445_, lean_object* v_s_446_, lean_object* v_onContinue_447_, lean_object* v_onReturn_448_, lean_object* v_onExcept_449_){
_start:
{
lean_object* v___f_450_; lean_object* v___x_451_; 
v___f_450_ = lean_alloc_closure((void*)(l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_450_, 0, v_ps_444_);
lean_closure_set(v___f_450_, 1, v_onReturn_448_);
lean_closure_set(v___f_450_, 2, v_onContinue_447_);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v___f_450_);
lean_ctor_set(v___x_451_, 1, v_onExcept_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo___boxed(lean_object* v_00_u03b2_452_, lean_object* v_ps_453_, lean_object* v_00_u03b3_454_, lean_object* v_s_455_, lean_object* v_onContinue_456_, lean_object* v_onReturn_457_, lean_object* v_onExcept_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo(v_00_u03b2_452_, v_ps_453_, v_00_u03b3_454_, v_s_455_, v_onContinue_456_, v_onReturn_457_, v_onExcept_458_);
lean_dec_ref(v_s_455_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_WhileVariant_eval___redArg(lean_object* v_ps_460_){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = l_Std_Do_PostShape_args(v_ps_460_);
v___x_462_ = l_Std_Do_SVal_evalsTo___redArg(v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_WhileVariant_eval___redArg___boxed(lean_object* v_ps_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_Do_WhileVariant_eval___redArg(v_ps_463_);
lean_dec(v_ps_463_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_WhileVariant_eval(lean_object* v_00_u03b1_465_, lean_object* v_ps_466_, lean_object* v_variant_467_, lean_object* v_a_468_, lean_object* v_n_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = l_Std_Do_PostShape_args(v_ps_466_);
v___x_471_ = l_Std_Do_SVal_evalsTo___redArg(v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_WhileVariant_eval___boxed(lean_object* v_00_u03b1_472_, lean_object* v_ps_473_, lean_object* v_variant_474_, lean_object* v_a_475_, lean_object* v_n_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_Do_WhileVariant_eval(v_00_u03b1_472_, v_ps_473_, v_variant_474_, v_a_475_, v_n_476_);
lean_dec(v_n_476_);
lean_dec(v_a_475_);
lean_dec(v_variant_474_);
lean_dec(v_ps_473_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter___redArg(lean_object* v_____do__lift_478_, lean_object* v_h__1_479_, lean_object* v_h__2_480_){
_start:
{
if (lean_obj_tag(v_____do__lift_478_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; 
lean_dec(v_h__2_480_);
v_a_481_ = lean_ctor_get(v_____do__lift_478_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v_____do__lift_478_, 1);
v___x_482_ = lean_apply_1(v_h__1_479_, v_a_481_);
return v___x_482_;
}
else
{
lean_object* v_a_483_; lean_object* v___x_484_; 
lean_dec(v_h__1_479_);
v_a_483_ = lean_ctor_get(v_____do__lift_478_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v_____do__lift_478_, 1);
v___x_484_ = lean_apply_1(v_h__2_480_, v_a_483_);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter(lean_object* v_00_u03b2_485_, lean_object* v_motive_486_, lean_object* v_____do__lift_487_, lean_object* v_h__1_488_, lean_object* v_h__2_489_){
_start:
{
if (lean_obj_tag(v_____do__lift_487_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_491_; 
lean_dec(v_h__2_489_);
v_a_490_ = lean_ctor_get(v_____do__lift_487_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v_____do__lift_487_, 1);
v___x_491_ = lean_apply_1(v_h__1_488_, v_a_490_);
return v___x_491_;
}
else
{
lean_object* v_a_492_; lean_object* v___x_493_; 
lean_dec(v_h__1_488_);
v_a_492_ = lean_ctor_get(v_____do__lift_487_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v_____do__lift_487_, 1);
v___x_493_ = lean_apply_1(v_h__2_489_, v_a_492_);
return v___x_493_;
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
