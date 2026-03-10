// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Operations
// Imports: public import Std.Data.DTreeMap.Internal.Balancing public import Std.Data.DTreeMap.Internal.Queries public import Init.Data.List.Control import Init.Data.Nat.Lemmas import Init.Data.Nat.Linear import Init.Omega import Init.WFTactics
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minView_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__1_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxView_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_glue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_glue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_glue_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_glue_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMin___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMin_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMin_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMax___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMax_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMax_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link2_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsertIfNew_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsertIfNew_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseMany_x21___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseMany_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseMany_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseManyEntries___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseManyEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseManyEntries_x21___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseManyEntries_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseManyEntries_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertManyIfNew___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertManyIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertManyIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_union___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_union___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_union___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_union___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_union___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_union___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__6_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_union___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__0_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__1_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg___closed__7 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__7_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_union___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__7_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__2_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__3_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__4_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__5_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg___closed__8 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__8_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__8_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__6_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9_value;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMany_x21___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMany_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMany_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertManyIfNew_x21___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertManyIfNew_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertManyIfNew_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertMany_x21___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertMany_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertMany_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit_x21___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_SizedBalancedTree_toBalancedTree___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_SizedBalancedTree_toBalancedTree___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_SizedBalancedTree_toBalancedTree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_SizedBalancedTree_toBalancedTree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ofArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ofArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_ofArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_ofArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_unitOfArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_unitOfArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_unitOfArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_unitOfList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_unitOfList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mapM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mapM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mapM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mapM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mapM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmallerFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmallerFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_inter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_beq___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_beq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_beq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_beq___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_beq___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_alter_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mergeWith___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mergeWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mergeWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mergeWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mergeWith_x21___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mergeWith_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mergeWith_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_instCoeTypeForall(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_mergeWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_mergeWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_mergeWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_mergeWith_x21___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_mergeWith_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_mergeWith_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_202; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_202 = !lean_is_exclusive(x_3);
if (x_202 == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_3, 0);
lean_dec(x_203);
x_9 = x_3;
x_10 = x_202;
goto block_201;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = x_202;
goto block_201;
}
block_201:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_200; 
x_11 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 2);
x_200 = !lean_is_exclusive(x_11);
if (x_200 == 0)
{
x_15 = x_11;
x_16 = x_200;
goto block_199;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = x_200;
goto block_199;
}
block_199:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
if (lean_obj_tag(x_14) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_54 = lean_ctor_get(x_14, 0);
x_55 = lean_ctor_get(x_4, 0);
x_56 = lean_ctor_get(x_4, 1);
x_57 = lean_ctor_get(x_4, 2);
x_58 = lean_ctor_get(x_4, 3);
x_59 = lean_ctor_get(x_4, 4);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_mul(x_60, x_54);
x_62 = lean_nat_dec_lt(x_61, x_55);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_del_object(x_15);
lean_del_object(x_9);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_63, x_54);
x_65 = lean_nat_add(x_64, x_55);
lean_dec(x_64);
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_1);
lean_ctor_set(x_66, 2, x_2);
lean_ctor_set(x_66, 3, x_14);
lean_ctor_set(x_66, 4, x_4);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_12);
lean_ctor_set(x_67, 1, x_13);
lean_ctor_set(x_67, 2, x_66);
return x_67;
}
else
{
lean_object* x_68; uint8_t x_69; uint8_t x_105; 
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_105 = !lean_is_exclusive(x_4);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_4, 4);
lean_dec(x_106);
x_107 = lean_ctor_get(x_4, 3);
lean_dec(x_107);
x_108 = lean_ctor_get(x_4, 2);
lean_dec(x_108);
x_109 = lean_ctor_get(x_4, 1);
lean_dec(x_109);
x_110 = lean_ctor_get(x_4, 0);
lean_dec(x_110);
x_68 = x_4;
x_69 = x_105;
goto block_104;
}
else
{
lean_dec(x_4);
x_68 = lean_box(0);
x_69 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_70 = lean_ctor_get(x_58, 0);
x_71 = lean_ctor_get(x_58, 1);
x_72 = lean_ctor_get(x_58, 2);
x_73 = lean_ctor_get(x_58, 3);
x_74 = lean_ctor_get(x_58, 4);
x_75 = lean_ctor_get(x_59, 0);
x_76 = lean_unsigned_to_nat(2u);
x_77 = lean_nat_mul(x_76, x_75);
x_78 = lean_nat_dec_lt(x_70, x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_del_object(x_68);
lean_dec(x_58);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_79, x_54);
x_81 = lean_nat_add(x_80, x_55);
lean_dec(x_55);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_73, 0);
lean_inc(x_82);
x_36 = x_73;
x_37 = x_80;
x_38 = x_57;
x_39 = x_72;
x_40 = x_75;
x_41 = x_59;
x_42 = x_71;
x_43 = x_56;
x_44 = x_74;
x_45 = x_81;
x_46 = x_79;
x_47 = x_82;
goto block_53;
}
else
{
lean_object* x_83; 
x_83 = lean_unsigned_to_nat(0u);
x_36 = x_73;
x_37 = x_80;
x_38 = x_57;
x_39 = x_72;
x_40 = x_75;
x_41 = x_59;
x_42 = x_71;
x_43 = x_56;
x_44 = x_74;
x_45 = x_81;
x_46 = x_79;
x_47 = x_83;
goto block_53;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_del_object(x_15);
lean_del_object(x_9);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_add(x_84, x_54);
x_86 = lean_nat_add(x_85, x_55);
lean_dec(x_55);
x_87 = lean_nat_add(x_85, x_70);
lean_dec(x_85);
lean_inc_ref(x_14);
if (x_69 == 0)
{
lean_ctor_set(x_68, 4, x_58);
lean_ctor_set(x_68, 3, x_14);
lean_ctor_set(x_68, 2, x_2);
lean_ctor_set(x_68, 1, x_1);
lean_ctor_set(x_68, 0, x_87);
x_88 = x_68;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_103, 0, x_87);
lean_ctor_set(x_103, 1, x_1);
lean_ctor_set(x_103, 2, x_2);
lean_ctor_set(x_103, 3, x_14);
lean_ctor_set(x_103, 4, x_58);
x_88 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_89; uint8_t x_90; uint8_t x_96; 
x_96 = !lean_is_exclusive(x_14);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_14, 4);
lean_dec(x_97);
x_98 = lean_ctor_get(x_14, 3);
lean_dec(x_98);
x_99 = lean_ctor_get(x_14, 2);
lean_dec(x_99);
x_100 = lean_ctor_get(x_14, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_14, 0);
lean_dec(x_101);
x_89 = x_14;
x_90 = x_96;
goto block_95;
}
else
{
lean_dec(x_14);
x_89 = lean_box(0);
x_90 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_91; 
if (x_90 == 0)
{
lean_ctor_set(x_89, 4, x_59);
lean_ctor_set(x_89, 3, x_88);
lean_ctor_set(x_89, 2, x_57);
lean_ctor_set(x_89, 1, x_56);
lean_ctor_set(x_89, 0, x_86);
x_91 = x_89;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_94, 0, x_86);
lean_ctor_set(x_94, 1, x_56);
lean_ctor_set(x_94, 2, x_57);
lean_ctor_set(x_94, 3, x_88);
lean_ctor_set(x_94, 4, x_59);
x_91 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_12);
lean_ctor_set(x_92, 1, x_13);
lean_ctor_set(x_92, 2, x_91);
return x_92;
}
}
}
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_del_object(x_15);
lean_del_object(x_9);
x_111 = lean_ctor_get(x_14, 0);
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_nat_add(x_112, x_111);
x_114 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_1);
lean_ctor_set(x_114, 2, x_2);
lean_ctor_set(x_114, 3, x_14);
lean_ctor_set(x_114, 4, x_4);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_12);
lean_ctor_set(x_115, 1, x_13);
lean_ctor_set(x_115, 2, x_114);
return x_115;
}
}
else
{
lean_del_object(x_15);
lean_del_object(x_9);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_4, 3);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_4, 4);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_133; 
x_118 = lean_ctor_get(x_4, 0);
x_119 = lean_ctor_get(x_4, 1);
x_120 = lean_ctor_get(x_4, 2);
x_133 = !lean_is_exclusive(x_4);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_4, 4);
lean_dec(x_134);
x_135 = lean_ctor_get(x_4, 3);
lean_dec(x_135);
x_121 = x_4;
x_122 = x_133;
goto block_132;
}
else
{
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_4);
x_121 = lean_box(0);
x_122 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_116, 0);
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_nat_add(x_124, x_118);
lean_dec(x_118);
x_126 = lean_nat_add(x_124, x_123);
if (x_122 == 0)
{
lean_ctor_set(x_121, 4, x_116);
lean_ctor_set(x_121, 3, x_14);
lean_ctor_set(x_121, 2, x_2);
lean_ctor_set(x_121, 1, x_1);
lean_ctor_set(x_121, 0, x_126);
x_127 = x_121;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_131, 1, x_1);
lean_ctor_set(x_131, 2, x_2);
lean_ctor_set(x_131, 3, x_14);
lean_ctor_set(x_131, 4, x_116);
x_127 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_119);
lean_ctor_set(x_128, 2, x_120);
lean_ctor_set(x_128, 3, x_127);
lean_ctor_set(x_128, 4, x_117);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_12);
lean_ctor_set(x_129, 1, x_13);
lean_ctor_set(x_129, 2, x_128);
return x_129;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_160; 
x_136 = lean_ctor_get(x_4, 1);
x_137 = lean_ctor_get(x_4, 2);
x_160 = !lean_is_exclusive(x_4);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_4, 4);
lean_dec(x_161);
x_162 = lean_ctor_get(x_4, 3);
lean_dec(x_162);
x_163 = lean_ctor_get(x_4, 0);
lean_dec(x_163);
x_138 = x_4;
x_139 = x_160;
goto block_159;
}
else
{
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_4);
x_138 = lean_box(0);
x_139 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_155; 
x_140 = lean_ctor_get(x_116, 1);
x_141 = lean_ctor_get(x_116, 2);
x_155 = !lean_is_exclusive(x_116);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_116, 4);
lean_dec(x_156);
x_157 = lean_ctor_get(x_116, 3);
lean_dec(x_157);
x_158 = lean_ctor_get(x_116, 0);
lean_dec(x_158);
x_142 = x_116;
x_143 = x_155;
goto block_154;
}
else
{
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_116);
x_142 = lean_box(0);
x_143 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_unsigned_to_nat(3u);
x_145 = lean_unsigned_to_nat(1u);
if (x_143 == 0)
{
lean_ctor_set(x_142, 4, x_117);
lean_ctor_set(x_142, 3, x_117);
lean_ctor_set(x_142, 2, x_2);
lean_ctor_set(x_142, 1, x_1);
lean_ctor_set(x_142, 0, x_145);
x_146 = x_142;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_145);
lean_ctor_set(x_153, 1, x_1);
lean_ctor_set(x_153, 2, x_2);
lean_ctor_set(x_153, 3, x_117);
lean_ctor_set(x_153, 4, x_117);
x_146 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_147; 
if (x_139 == 0)
{
lean_ctor_set(x_138, 3, x_117);
lean_ctor_set(x_138, 0, x_145);
x_147 = x_138;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_136);
lean_ctor_set(x_151, 2, x_137);
lean_ctor_set(x_151, 3, x_117);
lean_ctor_set(x_151, 4, x_117);
x_147 = x_151;
goto block_150;
}
block_150:
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_148, 0, x_144);
lean_ctor_set(x_148, 1, x_140);
lean_ctor_set(x_148, 2, x_141);
lean_ctor_set(x_148, 3, x_146);
lean_ctor_set(x_148, 4, x_147);
x_149 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_149, 0, x_12);
lean_ctor_set(x_149, 1, x_13);
lean_ctor_set(x_149, 2, x_148);
return x_149;
}
}
}
}
}
}
else
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_4, 4);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_177; 
x_165 = lean_ctor_get(x_4, 1);
x_166 = lean_ctor_get(x_4, 2);
x_177 = !lean_is_exclusive(x_4);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_4, 4);
lean_dec(x_178);
x_179 = lean_ctor_get(x_4, 3);
lean_dec(x_179);
x_180 = lean_ctor_get(x_4, 0);
lean_dec(x_180);
x_167 = x_4;
x_168 = x_177;
goto block_176;
}
else
{
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_4);
x_167 = lean_box(0);
x_168 = x_177;
goto block_176;
}
block_176:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_unsigned_to_nat(3u);
x_170 = lean_unsigned_to_nat(1u);
if (x_168 == 0)
{
lean_ctor_set(x_167, 4, x_116);
lean_ctor_set(x_167, 2, x_2);
lean_ctor_set(x_167, 1, x_1);
lean_ctor_set(x_167, 0, x_170);
x_171 = x_167;
goto block_174;
}
else
{
lean_object* x_175; 
x_175 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_175, 0, x_170);
lean_ctor_set(x_175, 1, x_1);
lean_ctor_set(x_175, 2, x_2);
lean_ctor_set(x_175, 3, x_116);
lean_ctor_set(x_175, 4, x_116);
x_171 = x_175;
goto block_174;
}
block_174:
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_165);
lean_ctor_set(x_172, 2, x_166);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set(x_172, 4, x_164);
x_173 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_173, 0, x_12);
lean_ctor_set(x_173, 1, x_13);
lean_ctor_set(x_173, 2, x_172);
return x_173;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_193; 
x_181 = lean_ctor_get(x_4, 0);
x_182 = lean_ctor_get(x_4, 1);
x_183 = lean_ctor_get(x_4, 2);
x_193 = !lean_is_exclusive(x_4);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_4, 4);
lean_dec(x_194);
x_195 = lean_ctor_get(x_4, 3);
lean_dec(x_195);
x_184 = x_4;
x_185 = x_193;
goto block_192;
}
else
{
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_4);
x_184 = lean_box(0);
x_185 = x_193;
goto block_192;
}
block_192:
{
lean_object* x_186; 
if (x_185 == 0)
{
lean_ctor_set(x_184, 3, x_164);
x_186 = x_184;
goto block_190;
}
else
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_191, 0, x_181);
lean_ctor_set(x_191, 1, x_182);
lean_ctor_set(x_191, 2, x_183);
lean_ctor_set(x_191, 3, x_164);
lean_ctor_set(x_191, 4, x_164);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_unsigned_to_nat(2u);
x_188 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_1);
lean_ctor_set(x_188, 2, x_2);
lean_ctor_set(x_188, 3, x_164);
lean_ctor_set(x_188, 4, x_186);
x_189 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_189, 0, x_12);
lean_ctor_set(x_189, 1, x_13);
lean_ctor_set(x_189, 2, x_188);
return x_189;
}
}
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_unsigned_to_nat(1u);
x_197 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_1);
lean_ctor_set(x_197, 2, x_2);
lean_ctor_set(x_197, 3, x_4);
lean_ctor_set(x_197, 4, x_4);
x_198 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_198, 0, x_12);
lean_ctor_set(x_198, 1, x_13);
lean_ctor_set(x_198, 2, x_197);
return x_198;
}
}
block_35:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_nat_add(x_20, x_26);
lean_dec(x_26);
lean_dec(x_20);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_22);
lean_ctor_set(x_9, 3, x_24);
lean_ctor_set(x_9, 2, x_18);
lean_ctor_set(x_9, 1, x_25);
lean_ctor_set(x_9, 0, x_27);
x_28 = x_9;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_18);
lean_ctor_set(x_34, 3, x_24);
lean_ctor_set(x_34, 4, x_22);
x_28 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_19);
lean_ctor_set(x_29, 3, x_17);
lean_ctor_set(x_29, 4, x_28);
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_29);
x_30 = x_15;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_13);
lean_ctor_set(x_32, 2, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
block_53:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_nat_add(x_37, x_47);
lean_dec(x_47);
lean_dec(x_37);
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_1);
lean_ctor_set(x_49, 2, x_2);
lean_ctor_set(x_49, 3, x_14);
lean_ctor_set(x_49, 4, x_36);
x_50 = lean_nat_add(x_46, x_40);
lean_dec(x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
x_17 = x_49;
x_18 = x_38;
x_19 = x_39;
x_20 = x_50;
x_21 = x_42;
x_22 = x_41;
x_23 = x_45;
x_24 = x_44;
x_25 = x_43;
x_26 = x_51;
goto block_35;
}
else
{
lean_object* x_52; 
x_52 = lean_unsigned_to_nat(0u);
x_17 = x_49;
x_18 = x_38;
x_19 = x_39;
x_20 = x_50;
x_21 = x_42;
x_22 = x_41;
x_23 = x_45;
x_24 = x_44;
x_25 = x_43;
x_26 = x_52;
goto block_35;
}
}
}
}
}
else
{
lean_object* x_204; 
x_204 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_204, 0, x_1);
lean_ctor_set(x_204, 1, x_2);
lean_ctor_set(x_204, 2, x_4);
return x_204;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(1);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__2));
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_unsigned_to_nat(276u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__1));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__2));
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(277u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__1));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_268; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_268 = !lean_is_exclusive(x_3);
if (x_268 == 0)
{
lean_object* x_269; 
x_269 = lean_ctor_get(x_3, 0);
lean_dec(x_269);
x_9 = x_3;
x_10 = x_268;
goto block_267;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = x_268;
goto block_267;
}
block_267:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_123; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_123 = !lean_is_exclusive(x_11);
if (x_123 == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_11, 2);
lean_dec(x_124);
x_15 = x_11;
x_16 = x_123;
goto block_122;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
x_20 = lean_ctor_get(x_4, 2);
x_21 = lean_ctor_get(x_4, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 4);
x_23 = lean_unsigned_to_nat(3u);
x_24 = lean_nat_mul(x_23, x_17);
x_25 = lean_nat_dec_lt(x_24, x_18);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_21);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_26, x_17);
x_28 = lean_nat_add(x_27, x_18);
lean_dec(x_27);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_4);
lean_ctor_set(x_9, 3, x_12);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_28);
x_29 = x_9;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_1);
lean_ctor_set(x_34, 2, x_2);
lean_ctor_set(x_34, 3, x_12);
lean_ctor_set(x_34, 4, x_4);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_29);
x_30 = x_15;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_14);
lean_ctor_set(x_32, 2, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
lean_object* x_35; uint8_t x_36; uint8_t x_116; 
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_116 = !lean_is_exclusive(x_4);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_4, 4);
lean_dec(x_117);
x_118 = lean_ctor_get(x_4, 3);
lean_dec(x_118);
x_119 = lean_ctor_get(x_4, 2);
lean_dec(x_119);
x_120 = lean_ctor_get(x_4, 1);
lean_dec(x_120);
x_121 = lean_ctor_get(x_4, 0);
lean_dec(x_121);
x_35 = x_4;
x_36 = x_116;
goto block_115;
}
else
{
lean_dec(x_4);
x_35 = lean_box(0);
x_36 = x_116;
goto block_115;
}
block_115:
{
if (lean_obj_tag(x_21) == 0)
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
x_39 = lean_ctor_get(x_21, 2);
x_40 = lean_ctor_get(x_21, 3);
x_41 = lean_ctor_get(x_21, 4);
x_42 = lean_ctor_get(x_22, 0);
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_mul(x_43, x_42);
x_45 = lean_nat_dec_lt(x_37, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; uint8_t x_77; 
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
x_77 = !lean_is_exclusive(x_21);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_21, 4);
lean_dec(x_78);
x_79 = lean_ctor_get(x_21, 3);
lean_dec(x_79);
x_80 = lean_ctor_get(x_21, 2);
lean_dec(x_80);
x_81 = lean_ctor_get(x_21, 1);
lean_dec(x_81);
x_82 = lean_ctor_get(x_21, 0);
lean_dec(x_82);
x_46 = x_21;
x_47 = x_77;
goto block_76;
}
else
{
lean_dec(x_21);
x_46 = lean_box(0);
x_47 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_65; 
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_48, x_17);
x_50 = lean_nat_add(x_49, x_18);
lean_dec(x_18);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_40, 0);
lean_inc(x_74);
x_65 = x_74;
goto block_73;
}
else
{
lean_object* x_75; 
x_75 = lean_unsigned_to_nat(0u);
x_65 = x_75;
goto block_73;
}
block_64:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_nat_add(x_51, x_53);
lean_dec(x_53);
lean_dec(x_51);
if (x_47 == 0)
{
lean_ctor_set(x_46, 4, x_22);
lean_ctor_set(x_46, 3, x_41);
lean_ctor_set(x_46, 2, x_20);
lean_ctor_set(x_46, 1, x_19);
lean_ctor_set(x_46, 0, x_54);
x_55 = x_46;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_54);
lean_ctor_set(x_63, 1, x_19);
lean_ctor_set(x_63, 2, x_20);
lean_ctor_set(x_63, 3, x_41);
lean_ctor_set(x_63, 4, x_22);
x_55 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_56; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 4, x_55);
lean_ctor_set(x_35, 3, x_52);
lean_ctor_set(x_35, 2, x_39);
lean_ctor_set(x_35, 1, x_38);
lean_ctor_set(x_35, 0, x_50);
x_56 = x_35;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_38);
lean_ctor_set(x_61, 2, x_39);
lean_ctor_set(x_61, 3, x_52);
lean_ctor_set(x_61, 4, x_55);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_56);
x_57 = x_15;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_13);
lean_ctor_set(x_59, 1, x_14);
lean_ctor_set(x_59, 2, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
block_73:
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_nat_add(x_49, x_65);
lean_dec(x_65);
lean_dec(x_49);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_40);
lean_ctor_set(x_9, 3, x_12);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_66);
x_67 = x_9;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_1);
lean_ctor_set(x_72, 2, x_2);
lean_ctor_set(x_72, 3, x_12);
lean_ctor_set(x_72, 4, x_40);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
x_68 = lean_nat_add(x_48, x_42);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_41, 0);
lean_inc(x_69);
x_51 = x_68;
x_52 = x_67;
x_53 = x_69;
goto block_64;
}
else
{
lean_object* x_70; 
x_70 = lean_unsigned_to_nat(0u);
x_51 = x_68;
x_52 = x_67;
x_53 = x_70;
goto block_64;
}
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_del_object(x_9);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_add(x_83, x_17);
x_85 = lean_nat_add(x_84, x_18);
lean_dec(x_18);
x_86 = lean_nat_add(x_84, x_37);
lean_dec(x_84);
lean_inc_ref(x_12);
if (x_36 == 0)
{
lean_ctor_set(x_35, 4, x_21);
lean_ctor_set(x_35, 3, x_12);
lean_ctor_set(x_35, 2, x_2);
lean_ctor_set(x_35, 1, x_1);
lean_ctor_set(x_35, 0, x_86);
x_87 = x_35;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_104, 0, x_86);
lean_ctor_set(x_104, 1, x_1);
lean_ctor_set(x_104, 2, x_2);
lean_ctor_set(x_104, 3, x_12);
lean_ctor_set(x_104, 4, x_21);
x_87 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_88; uint8_t x_89; uint8_t x_97; 
x_97 = !lean_is_exclusive(x_12);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_12, 4);
lean_dec(x_98);
x_99 = lean_ctor_get(x_12, 3);
lean_dec(x_99);
x_100 = lean_ctor_get(x_12, 2);
lean_dec(x_100);
x_101 = lean_ctor_get(x_12, 1);
lean_dec(x_101);
x_102 = lean_ctor_get(x_12, 0);
lean_dec(x_102);
x_88 = x_12;
x_89 = x_97;
goto block_96;
}
else
{
lean_dec(x_12);
x_88 = lean_box(0);
x_89 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_90; 
if (x_89 == 0)
{
lean_ctor_set(x_88, 4, x_22);
lean_ctor_set(x_88, 3, x_87);
lean_ctor_set(x_88, 2, x_20);
lean_ctor_set(x_88, 1, x_19);
lean_ctor_set(x_88, 0, x_85);
x_90 = x_88;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_19);
lean_ctor_set(x_95, 2, x_20);
lean_ctor_set(x_95, 3, x_87);
lean_ctor_set(x_95, 4, x_22);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_90);
x_91 = x_15;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_13);
lean_ctor_set(x_93, 1, x_14);
lean_ctor_set(x_93, 2, x_90);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_21);
lean_del_object(x_35);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_12);
lean_del_object(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_105 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3);
x_106 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_105);
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_106);
x_107 = x_15;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_109, 0, x_13);
lean_ctor_set(x_109, 1, x_14);
lean_ctor_set(x_109, 2, x_106);
x_107 = x_109;
goto block_108;
}
block_108:
{
return x_107;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_del_object(x_35);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_12);
lean_del_object(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_110 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4);
x_111 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_110);
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_111);
x_112 = x_15;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_13);
lean_ctor_set(x_114, 1, x_14);
lean_ctor_set(x_114, 2, x_111);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_139; 
x_125 = lean_ctor_get(x_11, 0);
x_126 = lean_ctor_get(x_11, 1);
x_139 = !lean_is_exclusive(x_11);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_11, 2);
lean_dec(x_140);
x_127 = x_11;
x_128 = x_139;
goto block_138;
}
else
{
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_11);
x_127 = lean_box(0);
x_128 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_12, 0);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_add(x_130, x_129);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_4);
lean_ctor_set(x_9, 3, x_12);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_131);
x_132 = x_9;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_137, 0, x_131);
lean_ctor_set(x_137, 1, x_1);
lean_ctor_set(x_137, 2, x_2);
lean_ctor_set(x_137, 3, x_12);
lean_ctor_set(x_137, 4, x_4);
x_132 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_133; 
if (x_128 == 0)
{
lean_ctor_set(x_127, 2, x_132);
x_133 = x_127;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_135, 0, x_125);
lean_ctor_set(x_135, 1, x_126);
lean_ctor_set(x_135, 2, x_132);
x_133 = x_135;
goto block_134;
}
block_134:
{
return x_133;
}
}
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_4, 3);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_4, 4);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_170; 
x_143 = lean_ctor_get(x_11, 0);
x_144 = lean_ctor_get(x_11, 1);
x_170 = !lean_is_exclusive(x_11);
if (x_170 == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_11, 2);
lean_dec(x_171);
x_145 = x_11;
x_146 = x_170;
goto block_169;
}
else
{
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_11);
x_145 = lean_box(0);
x_146 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_166; 
x_147 = lean_ctor_get(x_4, 0);
x_148 = lean_ctor_get(x_4, 1);
x_149 = lean_ctor_get(x_4, 2);
x_166 = !lean_is_exclusive(x_4);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_4, 4);
lean_dec(x_167);
x_168 = lean_ctor_get(x_4, 3);
lean_dec(x_168);
x_150 = x_4;
x_151 = x_166;
goto block_165;
}
else
{
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_4);
x_150 = lean_box(0);
x_151 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_152 = lean_ctor_get(x_141, 0);
x_153 = lean_unsigned_to_nat(1u);
x_154 = lean_nat_add(x_153, x_147);
lean_dec(x_147);
x_155 = lean_nat_add(x_153, x_152);
if (x_151 == 0)
{
lean_ctor_set(x_150, 4, x_141);
lean_ctor_set(x_150, 3, x_12);
lean_ctor_set(x_150, 2, x_2);
lean_ctor_set(x_150, 1, x_1);
lean_ctor_set(x_150, 0, x_155);
x_156 = x_150;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_164, 0, x_155);
lean_ctor_set(x_164, 1, x_1);
lean_ctor_set(x_164, 2, x_2);
lean_ctor_set(x_164, 3, x_12);
lean_ctor_set(x_164, 4, x_141);
x_156 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_157; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_142);
lean_ctor_set(x_9, 3, x_156);
lean_ctor_set(x_9, 2, x_149);
lean_ctor_set(x_9, 1, x_148);
lean_ctor_set(x_9, 0, x_154);
x_157 = x_9;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_162, 0, x_154);
lean_ctor_set(x_162, 1, x_148);
lean_ctor_set(x_162, 2, x_149);
lean_ctor_set(x_162, 3, x_156);
lean_ctor_set(x_162, 4, x_142);
x_157 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_158; 
if (x_146 == 0)
{
lean_ctor_set(x_145, 2, x_157);
x_158 = x_145;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_160, 0, x_143);
lean_ctor_set(x_160, 1, x_144);
lean_ctor_set(x_160, 2, x_157);
x_158 = x_160;
goto block_159;
}
block_159:
{
return x_158;
}
}
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_209; 
x_172 = lean_ctor_get(x_11, 0);
x_173 = lean_ctor_get(x_11, 1);
x_209 = !lean_is_exclusive(x_11);
if (x_209 == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_11, 2);
lean_dec(x_210);
x_174 = x_11;
x_175 = x_209;
goto block_208;
}
else
{
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_11);
x_174 = lean_box(0);
x_175 = x_209;
goto block_208;
}
block_208:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_204; 
x_176 = lean_ctor_get(x_4, 1);
x_177 = lean_ctor_get(x_4, 2);
x_204 = !lean_is_exclusive(x_4);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_4, 4);
lean_dec(x_205);
x_206 = lean_ctor_get(x_4, 3);
lean_dec(x_206);
x_207 = lean_ctor_get(x_4, 0);
lean_dec(x_207);
x_178 = x_4;
x_179 = x_204;
goto block_203;
}
else
{
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_4);
x_178 = lean_box(0);
x_179 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; uint8_t x_199; 
x_180 = lean_ctor_get(x_141, 1);
x_181 = lean_ctor_get(x_141, 2);
x_199 = !lean_is_exclusive(x_141);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_141, 4);
lean_dec(x_200);
x_201 = lean_ctor_get(x_141, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_141, 0);
lean_dec(x_202);
x_182 = x_141;
x_183 = x_199;
goto block_198;
}
else
{
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_141);
x_182 = lean_box(0);
x_183 = x_199;
goto block_198;
}
block_198:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_unsigned_to_nat(3u);
x_185 = lean_unsigned_to_nat(1u);
if (x_183 == 0)
{
lean_ctor_set(x_182, 4, x_142);
lean_ctor_set(x_182, 3, x_142);
lean_ctor_set(x_182, 2, x_2);
lean_ctor_set(x_182, 1, x_1);
lean_ctor_set(x_182, 0, x_185);
x_186 = x_182;
goto block_196;
}
else
{
lean_object* x_197; 
x_197 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_197, 0, x_185);
lean_ctor_set(x_197, 1, x_1);
lean_ctor_set(x_197, 2, x_2);
lean_ctor_set(x_197, 3, x_142);
lean_ctor_set(x_197, 4, x_142);
x_186 = x_197;
goto block_196;
}
block_196:
{
lean_object* x_187; 
if (x_179 == 0)
{
lean_ctor_set(x_178, 3, x_142);
lean_ctor_set(x_178, 0, x_185);
x_187 = x_178;
goto block_194;
}
else
{
lean_object* x_195; 
x_195 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_195, 0, x_185);
lean_ctor_set(x_195, 1, x_176);
lean_ctor_set(x_195, 2, x_177);
lean_ctor_set(x_195, 3, x_142);
lean_ctor_set(x_195, 4, x_142);
x_187 = x_195;
goto block_194;
}
block_194:
{
lean_object* x_188; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_187);
lean_ctor_set(x_9, 3, x_186);
lean_ctor_set(x_9, 2, x_181);
lean_ctor_set(x_9, 1, x_180);
lean_ctor_set(x_9, 0, x_184);
x_188 = x_9;
goto block_192;
}
else
{
lean_object* x_193; 
x_193 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_193, 0, x_184);
lean_ctor_set(x_193, 1, x_180);
lean_ctor_set(x_193, 2, x_181);
lean_ctor_set(x_193, 3, x_186);
lean_ctor_set(x_193, 4, x_187);
x_188 = x_193;
goto block_192;
}
block_192:
{
lean_object* x_189; 
if (x_175 == 0)
{
lean_ctor_set(x_174, 2, x_188);
x_189 = x_174;
goto block_190;
}
else
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_191, 0, x_172);
lean_ctor_set(x_191, 1, x_173);
lean_ctor_set(x_191, 2, x_188);
x_189 = x_191;
goto block_190;
}
block_190:
{
return x_189;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_4, 4);
lean_inc(x_211);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_237; 
x_212 = lean_ctor_get(x_11, 0);
x_213 = lean_ctor_get(x_11, 1);
x_237 = !lean_is_exclusive(x_11);
if (x_237 == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_11, 2);
lean_dec(x_238);
x_214 = x_11;
x_215 = x_237;
goto block_236;
}
else
{
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_11);
x_214 = lean_box(0);
x_215 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; uint8_t x_232; 
x_216 = lean_ctor_get(x_4, 1);
x_217 = lean_ctor_get(x_4, 2);
x_232 = !lean_is_exclusive(x_4);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_4, 4);
lean_dec(x_233);
x_234 = lean_ctor_get(x_4, 3);
lean_dec(x_234);
x_235 = lean_ctor_get(x_4, 0);
lean_dec(x_235);
x_218 = x_4;
x_219 = x_232;
goto block_231;
}
else
{
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_4);
x_218 = lean_box(0);
x_219 = x_232;
goto block_231;
}
block_231:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_unsigned_to_nat(3u);
x_221 = lean_unsigned_to_nat(1u);
if (x_219 == 0)
{
lean_ctor_set(x_218, 4, x_141);
lean_ctor_set(x_218, 2, x_2);
lean_ctor_set(x_218, 1, x_1);
lean_ctor_set(x_218, 0, x_221);
x_222 = x_218;
goto block_229;
}
else
{
lean_object* x_230; 
x_230 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_230, 0, x_221);
lean_ctor_set(x_230, 1, x_1);
lean_ctor_set(x_230, 2, x_2);
lean_ctor_set(x_230, 3, x_141);
lean_ctor_set(x_230, 4, x_141);
x_222 = x_230;
goto block_229;
}
block_229:
{
lean_object* x_223; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_211);
lean_ctor_set(x_9, 3, x_222);
lean_ctor_set(x_9, 2, x_217);
lean_ctor_set(x_9, 1, x_216);
lean_ctor_set(x_9, 0, x_220);
x_223 = x_9;
goto block_227;
}
else
{
lean_object* x_228; 
x_228 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_228, 0, x_220);
lean_ctor_set(x_228, 1, x_216);
lean_ctor_set(x_228, 2, x_217);
lean_ctor_set(x_228, 3, x_222);
lean_ctor_set(x_228, 4, x_211);
x_223 = x_228;
goto block_227;
}
block_227:
{
lean_object* x_224; 
if (x_215 == 0)
{
lean_ctor_set(x_214, 2, x_223);
x_224 = x_214;
goto block_225;
}
else
{
lean_object* x_226; 
x_226 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_226, 0, x_212);
lean_ctor_set(x_226, 1, x_213);
lean_ctor_set(x_226, 2, x_223);
x_224 = x_226;
goto block_225;
}
block_225:
{
return x_224;
}
}
}
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_251; 
x_239 = lean_ctor_get(x_11, 0);
x_240 = lean_ctor_get(x_11, 1);
x_251 = !lean_is_exclusive(x_11);
if (x_251 == 0)
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_11, 2);
lean_dec(x_252);
x_241 = x_11;
x_242 = x_251;
goto block_250;
}
else
{
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_11);
x_241 = lean_box(0);
x_242 = x_251;
goto block_250;
}
block_250:
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_unsigned_to_nat(2u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_4);
lean_ctor_set(x_9, 3, x_211);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_243);
x_244 = x_9;
goto block_248;
}
else
{
lean_object* x_249; 
x_249 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_249, 0, x_243);
lean_ctor_set(x_249, 1, x_1);
lean_ctor_set(x_249, 2, x_2);
lean_ctor_set(x_249, 3, x_211);
lean_ctor_set(x_249, 4, x_4);
x_244 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_245; 
if (x_242 == 0)
{
lean_ctor_set(x_241, 2, x_244);
x_245 = x_241;
goto block_246;
}
else
{
lean_object* x_247; 
x_247 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_247, 0, x_239);
lean_ctor_set(x_247, 1, x_240);
lean_ctor_set(x_247, 2, x_244);
x_245 = x_247;
goto block_246;
}
block_246:
{
return x_245;
}
}
}
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; uint8_t x_265; 
x_253 = lean_ctor_get(x_11, 0);
x_254 = lean_ctor_get(x_11, 1);
x_265 = !lean_is_exclusive(x_11);
if (x_265 == 0)
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_11, 2);
lean_dec(x_266);
x_255 = x_11;
x_256 = x_265;
goto block_264;
}
else
{
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_11);
x_255 = lean_box(0);
x_256 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_unsigned_to_nat(1u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_4);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_257);
x_258 = x_9;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_257);
lean_ctor_set(x_263, 1, x_1);
lean_ctor_set(x_263, 2, x_2);
lean_ctor_set(x_263, 3, x_4);
lean_ctor_set(x_263, 4, x_4);
x_258 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_259; 
if (x_256 == 0)
{
lean_ctor_set(x_255, 2, x_258);
x_259 = x_255;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_261, 0, x_253);
lean_ctor_set(x_261, 1, x_254);
lean_ctor_set(x_261, 2, x_258);
x_259 = x_261;
goto block_260;
}
block_260:
{
return x_259;
}
}
}
}
}
}
}
else
{
lean_object* x_270; 
x_270 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_270, 0, x_1);
lean_ctor_set(x_270, 1, x_2);
lean_ctor_set(x_270, 2, x_4);
return x_270;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minView_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_200; 
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_4, 3);
x_8 = lean_ctor_get(x_4, 4);
x_200 = !lean_is_exclusive(x_4);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_4, 0);
lean_dec(x_201);
x_9 = x_4;
x_10 = x_200;
goto block_199;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = x_200;
goto block_199;
}
block_199:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_198; 
x_11 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 2);
x_198 = !lean_is_exclusive(x_11);
if (x_198 == 0)
{
x_15 = x_11;
x_16 = x_198;
goto block_197;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
if (lean_obj_tag(x_14) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_51 = lean_ctor_get(x_14, 0);
x_52 = lean_ctor_get(x_3, 0);
x_53 = lean_ctor_get(x_3, 1);
x_54 = lean_ctor_get(x_3, 2);
x_55 = lean_ctor_get(x_3, 3);
x_56 = lean_ctor_get(x_3, 4);
x_57 = lean_unsigned_to_nat(3u);
x_58 = lean_nat_mul(x_57, x_51);
x_59 = lean_nat_dec_lt(x_58, x_52);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_del_object(x_15);
lean_del_object(x_9);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_60, x_52);
x_62 = lean_nat_add(x_61, x_51);
lean_dec(x_61);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_1);
lean_ctor_set(x_63, 2, x_2);
lean_ctor_set(x_63, 3, x_3);
lean_ctor_set(x_63, 4, x_14);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_12);
lean_ctor_set(x_64, 1, x_13);
lean_ctor_set(x_64, 2, x_63);
return x_64;
}
else
{
lean_object* x_65; uint8_t x_66; uint8_t x_104; 
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_104 = !lean_is_exclusive(x_3);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_3, 4);
lean_dec(x_105);
x_106 = lean_ctor_get(x_3, 3);
lean_dec(x_106);
x_107 = lean_ctor_get(x_3, 2);
lean_dec(x_107);
x_108 = lean_ctor_get(x_3, 1);
lean_dec(x_108);
x_109 = lean_ctor_get(x_3, 0);
lean_dec(x_109);
x_65 = x_3;
x_66 = x_104;
goto block_103;
}
else
{
lean_dec(x_3);
x_65 = lean_box(0);
x_66 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_67 = lean_ctor_get(x_55, 0);
x_68 = lean_ctor_get(x_56, 0);
x_69 = lean_ctor_get(x_56, 1);
x_70 = lean_ctor_get(x_56, 2);
x_71 = lean_ctor_get(x_56, 3);
x_72 = lean_ctor_get(x_56, 4);
x_73 = lean_unsigned_to_nat(2u);
x_74 = lean_nat_mul(x_73, x_67);
x_75 = lean_nat_dec_lt(x_68, x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_del_object(x_65);
lean_dec(x_56);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_add(x_76, x_52);
lean_dec(x_52);
x_78 = lean_nat_add(x_77, x_51);
lean_dec(x_77);
x_79 = lean_nat_add(x_76, x_67);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_71, 0);
lean_inc(x_80);
lean_inc(x_51);
x_33 = x_72;
x_34 = x_53;
x_35 = x_76;
x_36 = x_78;
x_37 = x_70;
x_38 = x_55;
x_39 = x_54;
x_40 = x_79;
x_41 = x_69;
x_42 = x_71;
x_43 = x_51;
x_44 = x_80;
goto block_50;
}
else
{
lean_object* x_81; 
x_81 = lean_unsigned_to_nat(0u);
lean_inc(x_51);
x_33 = x_72;
x_34 = x_53;
x_35 = x_76;
x_36 = x_78;
x_37 = x_70;
x_38 = x_55;
x_39 = x_54;
x_40 = x_79;
x_41 = x_69;
x_42 = x_71;
x_43 = x_51;
x_44 = x_81;
goto block_50;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_del_object(x_15);
lean_del_object(x_9);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_82, x_52);
lean_dec(x_52);
x_84 = lean_nat_add(x_83, x_51);
lean_dec(x_83);
x_85 = lean_nat_add(x_82, x_51);
x_86 = lean_nat_add(x_85, x_68);
lean_dec(x_85);
lean_inc_ref(x_14);
if (x_66 == 0)
{
lean_ctor_set(x_65, 4, x_14);
lean_ctor_set(x_65, 3, x_56);
lean_ctor_set(x_65, 2, x_2);
lean_ctor_set(x_65, 1, x_1);
lean_ctor_set(x_65, 0, x_86);
x_87 = x_65;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_102, 0, x_86);
lean_ctor_set(x_102, 1, x_1);
lean_ctor_set(x_102, 2, x_2);
lean_ctor_set(x_102, 3, x_56);
lean_ctor_set(x_102, 4, x_14);
x_87 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_88; uint8_t x_89; uint8_t x_95; 
x_95 = !lean_is_exclusive(x_14);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_14, 4);
lean_dec(x_96);
x_97 = lean_ctor_get(x_14, 3);
lean_dec(x_97);
x_98 = lean_ctor_get(x_14, 2);
lean_dec(x_98);
x_99 = lean_ctor_get(x_14, 1);
lean_dec(x_99);
x_100 = lean_ctor_get(x_14, 0);
lean_dec(x_100);
x_88 = x_14;
x_89 = x_95;
goto block_94;
}
else
{
lean_dec(x_14);
x_88 = lean_box(0);
x_89 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_90; 
if (x_89 == 0)
{
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 3, x_55);
lean_ctor_set(x_88, 2, x_54);
lean_ctor_set(x_88, 1, x_53);
lean_ctor_set(x_88, 0, x_84);
x_90 = x_88;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_93, 0, x_84);
lean_ctor_set(x_93, 1, x_53);
lean_ctor_set(x_93, 2, x_54);
lean_ctor_set(x_93, 3, x_55);
lean_ctor_set(x_93, 4, x_87);
x_90 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_12);
lean_ctor_set(x_91, 1, x_13);
lean_ctor_set(x_91, 2, x_90);
return x_91;
}
}
}
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_del_object(x_15);
lean_del_object(x_9);
x_110 = lean_ctor_get(x_14, 0);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_add(x_111, x_110);
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_1);
lean_ctor_set(x_113, 2, x_2);
lean_ctor_set(x_113, 3, x_3);
lean_ctor_set(x_113, 4, x_14);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_12);
lean_ctor_set(x_114, 1, x_13);
lean_ctor_set(x_114, 2, x_113);
return x_114;
}
}
else
{
lean_del_object(x_15);
lean_del_object(x_9);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_3, 4);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_143; 
x_117 = lean_ctor_get(x_3, 0);
x_118 = lean_ctor_get(x_3, 1);
x_119 = lean_ctor_get(x_3, 2);
x_143 = !lean_is_exclusive(x_3);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_3, 4);
lean_dec(x_144);
x_145 = lean_ctor_get(x_3, 3);
lean_dec(x_145);
x_120 = x_3;
x_121 = x_143;
goto block_142;
}
else
{
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_3);
x_120 = lean_box(0);
x_121 = x_143;
goto block_142;
}
block_142:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_116, 0);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_nat_add(x_123, x_117);
lean_dec(x_117);
x_125 = lean_nat_add(x_123, x_122);
lean_inc_ref(x_116);
if (x_121 == 0)
{
lean_ctor_set(x_120, 4, x_14);
lean_ctor_set(x_120, 3, x_116);
lean_ctor_set(x_120, 2, x_2);
lean_ctor_set(x_120, 1, x_1);
lean_ctor_set(x_120, 0, x_125);
x_126 = x_120;
goto block_140;
}
else
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_141, 0, x_125);
lean_ctor_set(x_141, 1, x_1);
lean_ctor_set(x_141, 2, x_2);
lean_ctor_set(x_141, 3, x_116);
lean_ctor_set(x_141, 4, x_14);
x_126 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_127; uint8_t x_128; uint8_t x_134; 
x_134 = !lean_is_exclusive(x_116);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_116, 4);
lean_dec(x_135);
x_136 = lean_ctor_get(x_116, 3);
lean_dec(x_136);
x_137 = lean_ctor_get(x_116, 2);
lean_dec(x_137);
x_138 = lean_ctor_get(x_116, 1);
lean_dec(x_138);
x_139 = lean_ctor_get(x_116, 0);
lean_dec(x_139);
x_127 = x_116;
x_128 = x_134;
goto block_133;
}
else
{
lean_dec(x_116);
x_127 = lean_box(0);
x_128 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_129; 
if (x_128 == 0)
{
lean_ctor_set(x_127, 4, x_126);
lean_ctor_set(x_127, 3, x_115);
lean_ctor_set(x_127, 2, x_119);
lean_ctor_set(x_127, 1, x_118);
lean_ctor_set(x_127, 0, x_124);
x_129 = x_127;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_124);
lean_ctor_set(x_132, 1, x_118);
lean_ctor_set(x_132, 2, x_119);
lean_ctor_set(x_132, 3, x_115);
lean_ctor_set(x_132, 4, x_126);
x_129 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_130, 0, x_12);
lean_ctor_set(x_130, 1, x_13);
lean_ctor_set(x_130, 2, x_129);
return x_130;
}
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_158; 
x_146 = lean_ctor_get(x_3, 1);
x_147 = lean_ctor_get(x_3, 2);
x_158 = !lean_is_exclusive(x_3);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_3, 4);
lean_dec(x_159);
x_160 = lean_ctor_get(x_3, 3);
lean_dec(x_160);
x_161 = lean_ctor_get(x_3, 0);
lean_dec(x_161);
x_148 = x_3;
x_149 = x_158;
goto block_157;
}
else
{
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_3);
x_148 = lean_box(0);
x_149 = x_158;
goto block_157;
}
block_157:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_unsigned_to_nat(3u);
x_151 = lean_unsigned_to_nat(1u);
if (x_149 == 0)
{
lean_ctor_set(x_148, 3, x_116);
lean_ctor_set(x_148, 2, x_2);
lean_ctor_set(x_148, 1, x_1);
lean_ctor_set(x_148, 0, x_151);
x_152 = x_148;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_156, 0, x_151);
lean_ctor_set(x_156, 1, x_1);
lean_ctor_set(x_156, 2, x_2);
lean_ctor_set(x_156, 3, x_116);
lean_ctor_set(x_156, 4, x_116);
x_152 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_146);
lean_ctor_set(x_153, 2, x_147);
lean_ctor_set(x_153, 3, x_115);
lean_ctor_set(x_153, 4, x_152);
x_154 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_154, 0, x_12);
lean_ctor_set(x_154, 1, x_13);
lean_ctor_set(x_154, 2, x_153);
return x_154;
}
}
}
}
else
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_3, 4);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; uint8_t x_187; 
lean_inc(x_115);
x_163 = lean_ctor_get(x_3, 1);
x_164 = lean_ctor_get(x_3, 2);
x_187 = !lean_is_exclusive(x_3);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_3, 4);
lean_dec(x_188);
x_189 = lean_ctor_get(x_3, 3);
lean_dec(x_189);
x_190 = lean_ctor_get(x_3, 0);
lean_dec(x_190);
x_165 = x_3;
x_166 = x_187;
goto block_186;
}
else
{
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_3);
x_165 = lean_box(0);
x_166 = x_187;
goto block_186;
}
block_186:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_182; 
x_167 = lean_ctor_get(x_162, 1);
x_168 = lean_ctor_get(x_162, 2);
x_182 = !lean_is_exclusive(x_162);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_162, 4);
lean_dec(x_183);
x_184 = lean_ctor_get(x_162, 3);
lean_dec(x_184);
x_185 = lean_ctor_get(x_162, 0);
lean_dec(x_185);
x_169 = x_162;
x_170 = x_182;
goto block_181;
}
else
{
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_162);
x_169 = lean_box(0);
x_170 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_unsigned_to_nat(3u);
x_172 = lean_unsigned_to_nat(1u);
if (x_170 == 0)
{
lean_ctor_set(x_169, 4, x_115);
lean_ctor_set(x_169, 3, x_115);
lean_ctor_set(x_169, 2, x_164);
lean_ctor_set(x_169, 1, x_163);
lean_ctor_set(x_169, 0, x_172);
x_173 = x_169;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_180, 0, x_172);
lean_ctor_set(x_180, 1, x_163);
lean_ctor_set(x_180, 2, x_164);
lean_ctor_set(x_180, 3, x_115);
lean_ctor_set(x_180, 4, x_115);
x_173 = x_180;
goto block_179;
}
block_179:
{
lean_object* x_174; 
if (x_166 == 0)
{
lean_ctor_set(x_165, 4, x_115);
lean_ctor_set(x_165, 2, x_2);
lean_ctor_set(x_165, 1, x_1);
lean_ctor_set(x_165, 0, x_172);
x_174 = x_165;
goto block_177;
}
else
{
lean_object* x_178; 
x_178 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set(x_178, 1, x_1);
lean_ctor_set(x_178, 2, x_2);
lean_ctor_set(x_178, 3, x_115);
lean_ctor_set(x_178, 4, x_115);
x_174 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_167);
lean_ctor_set(x_175, 2, x_168);
lean_ctor_set(x_175, 3, x_173);
lean_ctor_set(x_175, 4, x_174);
x_176 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_176, 0, x_12);
lean_ctor_set(x_176, 1, x_13);
lean_ctor_set(x_176, 2, x_175);
return x_176;
}
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_unsigned_to_nat(2u);
x_192 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_1);
lean_ctor_set(x_192, 2, x_2);
lean_ctor_set(x_192, 3, x_3);
lean_ctor_set(x_192, 4, x_162);
x_193 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_193, 0, x_12);
lean_ctor_set(x_193, 1, x_13);
lean_ctor_set(x_193, 2, x_192);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_unsigned_to_nat(1u);
x_195 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_1);
lean_ctor_set(x_195, 2, x_2);
lean_ctor_set(x_195, 3, x_3);
lean_ctor_set(x_195, 4, x_3);
x_196 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_196, 0, x_12);
lean_ctor_set(x_196, 1, x_13);
lean_ctor_set(x_196, 2, x_195);
return x_196;
}
}
block_32:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_nat_add(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_14);
lean_ctor_set(x_9, 3, x_17);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_24);
x_25 = x_9;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_1);
lean_ctor_set(x_31, 2, x_2);
lean_ctor_set(x_31, 3, x_17);
lean_ctor_set(x_31, 4, x_14);
x_25 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_25);
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_26);
x_27 = x_15;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_13);
lean_ctor_set(x_29, 2, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
block_50:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_nat_add(x_40, x_44);
lean_dec(x_44);
lean_dec(x_40);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_34);
lean_ctor_set(x_46, 2, x_39);
lean_ctor_set(x_46, 3, x_38);
lean_ctor_set(x_46, 4, x_42);
x_47 = lean_nat_add(x_35, x_43);
lean_dec(x_43);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_33, 0);
lean_inc(x_48);
x_17 = x_33;
x_18 = x_36;
x_19 = x_37;
x_20 = x_46;
x_21 = x_41;
x_22 = x_47;
x_23 = x_48;
goto block_32;
}
else
{
lean_object* x_49; 
x_49 = lean_unsigned_to_nat(0u);
x_17 = x_33;
x_18 = x_36;
x_19 = x_37;
x_20 = x_46;
x_21 = x_41;
x_22 = x_47;
x_23 = x_49;
goto block_32;
}
}
}
}
}
else
{
lean_object* x_202; 
x_202 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_202, 0, x_1);
lean_ctor_set(x_202, 1, x_2);
lean_ctor_set(x_202, 2, x_3);
return x_202;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_3, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__1));
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_unsigned_to_nat(182u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__0));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__1));
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(183u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__0));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_270; 
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_4, 3);
x_8 = lean_ctor_get(x_4, 4);
x_270 = !lean_is_exclusive(x_4);
if (x_270 == 0)
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_4, 0);
lean_dec(x_271);
x_9 = x_4;
x_10 = x_270;
goto block_269;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = x_270;
goto block_269;
}
block_269:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_125; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_125 = !lean_is_exclusive(x_11);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_11, 2);
lean_dec(x_126);
x_15 = x_11;
x_16 = x_125;
goto block_124;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
lean_inc(x_22);
x_23 = lean_unsigned_to_nat(3u);
x_24 = lean_nat_mul(x_23, x_17);
x_25 = lean_nat_dec_lt(x_24, x_18);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_26, x_18);
x_28 = lean_nat_add(x_27, x_17);
lean_dec(x_27);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_12);
lean_ctor_set(x_9, 3, x_3);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_28);
x_29 = x_9;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_1);
lean_ctor_set(x_34, 2, x_2);
lean_ctor_set(x_34, 3, x_3);
lean_ctor_set(x_34, 4, x_12);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_29);
x_30 = x_15;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_14);
lean_ctor_set(x_32, 2, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
lean_object* x_35; uint8_t x_36; uint8_t x_118; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_118 = !lean_is_exclusive(x_3);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_3, 4);
lean_dec(x_119);
x_120 = lean_ctor_get(x_3, 3);
lean_dec(x_120);
x_121 = lean_ctor_get(x_3, 2);
lean_dec(x_121);
x_122 = lean_ctor_get(x_3, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_3, 0);
lean_dec(x_123);
x_35 = x_3;
x_36 = x_118;
goto block_117;
}
else
{
lean_dec(x_3);
x_35 = lean_box(0);
x_36 = x_118;
goto block_117;
}
block_117:
{
if (lean_obj_tag(x_21) == 0)
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_ctor_get(x_22, 1);
x_40 = lean_ctor_get(x_22, 2);
x_41 = lean_ctor_get(x_22, 3);
x_42 = lean_ctor_get(x_22, 4);
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_mul(x_43, x_37);
x_45 = lean_nat_dec_lt(x_38, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; uint8_t x_78; 
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
x_78 = !lean_is_exclusive(x_22);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_22, 4);
lean_dec(x_79);
x_80 = lean_ctor_get(x_22, 3);
lean_dec(x_80);
x_81 = lean_ctor_get(x_22, 2);
lean_dec(x_81);
x_82 = lean_ctor_get(x_22, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_22, 0);
lean_dec(x_83);
x_46 = x_22;
x_47 = x_78;
goto block_77;
}
else
{
lean_dec(x_22);
x_46 = lean_box(0);
x_47 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_65; lean_object* x_66; 
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_48, x_18);
lean_dec(x_18);
x_50 = lean_nat_add(x_49, x_17);
lean_dec(x_49);
x_65 = lean_nat_add(x_48, x_37);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_41, 0);
lean_inc(x_75);
x_66 = x_75;
goto block_74;
}
else
{
lean_object* x_76; 
x_76 = lean_unsigned_to_nat(0u);
x_66 = x_76;
goto block_74;
}
block_64:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_nat_add(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
if (x_47 == 0)
{
lean_ctor_set(x_46, 4, x_12);
lean_ctor_set(x_46, 3, x_42);
lean_ctor_set(x_46, 2, x_2);
lean_ctor_set(x_46, 1, x_1);
lean_ctor_set(x_46, 0, x_54);
x_55 = x_46;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_54);
lean_ctor_set(x_63, 1, x_1);
lean_ctor_set(x_63, 2, x_2);
lean_ctor_set(x_63, 3, x_42);
lean_ctor_set(x_63, 4, x_12);
x_55 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_56; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 4, x_55);
lean_ctor_set(x_35, 3, x_51);
lean_ctor_set(x_35, 2, x_40);
lean_ctor_set(x_35, 1, x_39);
lean_ctor_set(x_35, 0, x_50);
x_56 = x_35;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_39);
lean_ctor_set(x_61, 2, x_40);
lean_ctor_set(x_61, 3, x_51);
lean_ctor_set(x_61, 4, x_55);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_56);
x_57 = x_15;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_13);
lean_ctor_set(x_59, 1, x_14);
lean_ctor_set(x_59, 2, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
block_74:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_nat_add(x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_41);
lean_ctor_set(x_9, 3, x_21);
lean_ctor_set(x_9, 2, x_20);
lean_ctor_set(x_9, 1, x_19);
lean_ctor_set(x_9, 0, x_67);
x_68 = x_9;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_19);
lean_ctor_set(x_73, 2, x_20);
lean_ctor_set(x_73, 3, x_21);
lean_ctor_set(x_73, 4, x_41);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
x_69 = lean_nat_add(x_48, x_17);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_42, 0);
lean_inc(x_70);
x_51 = x_68;
x_52 = x_69;
x_53 = x_70;
goto block_64;
}
else
{
lean_object* x_71; 
x_71 = lean_unsigned_to_nat(0u);
x_51 = x_68;
x_52 = x_69;
x_53 = x_71;
goto block_64;
}
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_del_object(x_9);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_add(x_84, x_18);
lean_dec(x_18);
x_86 = lean_nat_add(x_85, x_17);
lean_dec(x_85);
x_87 = lean_nat_add(x_84, x_17);
x_88 = lean_nat_add(x_87, x_38);
lean_dec(x_87);
lean_inc_ref(x_12);
if (x_36 == 0)
{
lean_ctor_set(x_35, 4, x_12);
lean_ctor_set(x_35, 3, x_22);
lean_ctor_set(x_35, 2, x_2);
lean_ctor_set(x_35, 1, x_1);
lean_ctor_set(x_35, 0, x_88);
x_89 = x_35;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_106, 0, x_88);
lean_ctor_set(x_106, 1, x_1);
lean_ctor_set(x_106, 2, x_2);
lean_ctor_set(x_106, 3, x_22);
lean_ctor_set(x_106, 4, x_12);
x_89 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_90; uint8_t x_91; uint8_t x_99; 
x_99 = !lean_is_exclusive(x_12);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_12, 4);
lean_dec(x_100);
x_101 = lean_ctor_get(x_12, 3);
lean_dec(x_101);
x_102 = lean_ctor_get(x_12, 2);
lean_dec(x_102);
x_103 = lean_ctor_get(x_12, 1);
lean_dec(x_103);
x_104 = lean_ctor_get(x_12, 0);
lean_dec(x_104);
x_90 = x_12;
x_91 = x_99;
goto block_98;
}
else
{
lean_dec(x_12);
x_90 = lean_box(0);
x_91 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_92; 
if (x_91 == 0)
{
lean_ctor_set(x_90, 4, x_89);
lean_ctor_set(x_90, 3, x_21);
lean_ctor_set(x_90, 2, x_20);
lean_ctor_set(x_90, 1, x_19);
lean_ctor_set(x_90, 0, x_86);
x_92 = x_90;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_86);
lean_ctor_set(x_97, 1, x_19);
lean_ctor_set(x_97, 2, x_20);
lean_ctor_set(x_97, 3, x_21);
lean_ctor_set(x_97, 4, x_89);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_92);
x_93 = x_15;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_13);
lean_ctor_set(x_95, 1, x_14);
lean_ctor_set(x_95, 2, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_21);
lean_del_object(x_35);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_12);
lean_del_object(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_107 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2);
x_108 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_107);
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_108);
x_109 = x_15;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_111, 0, x_13);
lean_ctor_set(x_111, 1, x_14);
lean_ctor_set(x_111, 2, x_108);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_del_object(x_35);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_12);
lean_del_object(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_112 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3);
x_113 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_112);
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_113);
x_114 = x_15;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_116, 0, x_13);
lean_ctor_set(x_116, 1, x_14);
lean_ctor_set(x_116, 2, x_113);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_141; 
x_127 = lean_ctor_get(x_11, 0);
x_128 = lean_ctor_get(x_11, 1);
x_141 = !lean_is_exclusive(x_11);
if (x_141 == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_11, 2);
lean_dec(x_142);
x_129 = x_11;
x_130 = x_141;
goto block_140;
}
else
{
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_11);
x_129 = lean_box(0);
x_130 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_12, 0);
x_132 = lean_unsigned_to_nat(1u);
x_133 = lean_nat_add(x_132, x_131);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_12);
lean_ctor_set(x_9, 3, x_3);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_133);
x_134 = x_9;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_1);
lean_ctor_set(x_139, 2, x_2);
lean_ctor_set(x_139, 3, x_3);
lean_ctor_set(x_139, 4, x_12);
x_134 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_135; 
if (x_130 == 0)
{
lean_ctor_set(x_129, 2, x_134);
x_135 = x_129;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_137, 0, x_127);
lean_ctor_set(x_137, 1, x_128);
lean_ctor_set(x_137, 2, x_134);
x_135 = x_137;
goto block_136;
}
block_136:
{
return x_135;
}
}
}
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
lean_inc_ref(x_143);
x_144 = lean_ctor_get(x_3, 4);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_172; 
x_145 = lean_ctor_get(x_11, 0);
x_146 = lean_ctor_get(x_11, 1);
x_172 = !lean_is_exclusive(x_11);
if (x_172 == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_11, 2);
lean_dec(x_173);
x_147 = x_11;
x_148 = x_172;
goto block_171;
}
else
{
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_11);
x_147 = lean_box(0);
x_148 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_168; 
x_149 = lean_ctor_get(x_3, 0);
x_150 = lean_ctor_get(x_3, 1);
x_151 = lean_ctor_get(x_3, 2);
x_168 = !lean_is_exclusive(x_3);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_3, 4);
lean_dec(x_169);
x_170 = lean_ctor_get(x_3, 3);
lean_dec(x_170);
x_152 = x_3;
x_153 = x_168;
goto block_167;
}
else
{
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_3);
x_152 = lean_box(0);
x_153 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_144, 0);
x_155 = lean_unsigned_to_nat(1u);
x_156 = lean_nat_add(x_155, x_149);
lean_dec(x_149);
x_157 = lean_nat_add(x_155, x_154);
if (x_153 == 0)
{
lean_ctor_set(x_152, 4, x_12);
lean_ctor_set(x_152, 3, x_144);
lean_ctor_set(x_152, 2, x_2);
lean_ctor_set(x_152, 1, x_1);
lean_ctor_set(x_152, 0, x_157);
x_158 = x_152;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_166, 0, x_157);
lean_ctor_set(x_166, 1, x_1);
lean_ctor_set(x_166, 2, x_2);
lean_ctor_set(x_166, 3, x_144);
lean_ctor_set(x_166, 4, x_12);
x_158 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_159; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_158);
lean_ctor_set(x_9, 3, x_143);
lean_ctor_set(x_9, 2, x_151);
lean_ctor_set(x_9, 1, x_150);
lean_ctor_set(x_9, 0, x_156);
x_159 = x_9;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_164, 0, x_156);
lean_ctor_set(x_164, 1, x_150);
lean_ctor_set(x_164, 2, x_151);
lean_ctor_set(x_164, 3, x_143);
lean_ctor_set(x_164, 4, x_158);
x_159 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_160; 
if (x_148 == 0)
{
lean_ctor_set(x_147, 2, x_159);
x_160 = x_147;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_162, 0, x_145);
lean_ctor_set(x_162, 1, x_146);
lean_ctor_set(x_162, 2, x_159);
x_160 = x_162;
goto block_161;
}
block_161:
{
return x_160;
}
}
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_199; 
x_174 = lean_ctor_get(x_11, 0);
x_175 = lean_ctor_get(x_11, 1);
x_199 = !lean_is_exclusive(x_11);
if (x_199 == 0)
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_11, 2);
lean_dec(x_200);
x_176 = x_11;
x_177 = x_199;
goto block_198;
}
else
{
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_11);
x_176 = lean_box(0);
x_177 = x_199;
goto block_198;
}
block_198:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_194; 
x_178 = lean_ctor_get(x_3, 1);
x_179 = lean_ctor_get(x_3, 2);
x_194 = !lean_is_exclusive(x_3);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_3, 4);
lean_dec(x_195);
x_196 = lean_ctor_get(x_3, 3);
lean_dec(x_196);
x_197 = lean_ctor_get(x_3, 0);
lean_dec(x_197);
x_180 = x_3;
x_181 = x_194;
goto block_193;
}
else
{
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_3);
x_180 = lean_box(0);
x_181 = x_194;
goto block_193;
}
block_193:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_unsigned_to_nat(3u);
x_183 = lean_unsigned_to_nat(1u);
if (x_181 == 0)
{
lean_ctor_set(x_180, 3, x_144);
lean_ctor_set(x_180, 2, x_2);
lean_ctor_set(x_180, 1, x_1);
lean_ctor_set(x_180, 0, x_183);
x_184 = x_180;
goto block_191;
}
else
{
lean_object* x_192; 
x_192 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_192, 0, x_183);
lean_ctor_set(x_192, 1, x_1);
lean_ctor_set(x_192, 2, x_2);
lean_ctor_set(x_192, 3, x_144);
lean_ctor_set(x_192, 4, x_144);
x_184 = x_192;
goto block_191;
}
block_191:
{
lean_object* x_185; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_184);
lean_ctor_set(x_9, 3, x_143);
lean_ctor_set(x_9, 2, x_179);
lean_ctor_set(x_9, 1, x_178);
lean_ctor_set(x_9, 0, x_182);
x_185 = x_9;
goto block_189;
}
else
{
lean_object* x_190; 
x_190 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_190, 0, x_182);
lean_ctor_set(x_190, 1, x_178);
lean_ctor_set(x_190, 2, x_179);
lean_ctor_set(x_190, 3, x_143);
lean_ctor_set(x_190, 4, x_184);
x_185 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_186; 
if (x_177 == 0)
{
lean_ctor_set(x_176, 2, x_185);
x_186 = x_176;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_188, 0, x_174);
lean_ctor_set(x_188, 1, x_175);
lean_ctor_set(x_188, 2, x_185);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
}
}
}
}
}
else
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_3, 4);
lean_inc(x_201);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_239; 
lean_inc(x_143);
x_202 = lean_ctor_get(x_11, 0);
x_203 = lean_ctor_get(x_11, 1);
x_239 = !lean_is_exclusive(x_11);
if (x_239 == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_11, 2);
lean_dec(x_240);
x_204 = x_11;
x_205 = x_239;
goto block_238;
}
else
{
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_11);
x_204 = lean_box(0);
x_205 = x_239;
goto block_238;
}
block_238:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; uint8_t x_234; 
x_206 = lean_ctor_get(x_3, 1);
x_207 = lean_ctor_get(x_3, 2);
x_234 = !lean_is_exclusive(x_3);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_3, 4);
lean_dec(x_235);
x_236 = lean_ctor_get(x_3, 3);
lean_dec(x_236);
x_237 = lean_ctor_get(x_3, 0);
lean_dec(x_237);
x_208 = x_3;
x_209 = x_234;
goto block_233;
}
else
{
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_3);
x_208 = lean_box(0);
x_209 = x_234;
goto block_233;
}
block_233:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; uint8_t x_229; 
x_210 = lean_ctor_get(x_201, 1);
x_211 = lean_ctor_get(x_201, 2);
x_229 = !lean_is_exclusive(x_201);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_201, 4);
lean_dec(x_230);
x_231 = lean_ctor_get(x_201, 3);
lean_dec(x_231);
x_232 = lean_ctor_get(x_201, 0);
lean_dec(x_232);
x_212 = x_201;
x_213 = x_229;
goto block_228;
}
else
{
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_201);
x_212 = lean_box(0);
x_213 = x_229;
goto block_228;
}
block_228:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_unsigned_to_nat(3u);
x_215 = lean_unsigned_to_nat(1u);
if (x_213 == 0)
{
lean_ctor_set(x_212, 4, x_143);
lean_ctor_set(x_212, 3, x_143);
lean_ctor_set(x_212, 2, x_207);
lean_ctor_set(x_212, 1, x_206);
lean_ctor_set(x_212, 0, x_215);
x_216 = x_212;
goto block_226;
}
else
{
lean_object* x_227; 
x_227 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_227, 0, x_215);
lean_ctor_set(x_227, 1, x_206);
lean_ctor_set(x_227, 2, x_207);
lean_ctor_set(x_227, 3, x_143);
lean_ctor_set(x_227, 4, x_143);
x_216 = x_227;
goto block_226;
}
block_226:
{
lean_object* x_217; 
if (x_209 == 0)
{
lean_ctor_set(x_208, 4, x_143);
lean_ctor_set(x_208, 2, x_2);
lean_ctor_set(x_208, 1, x_1);
lean_ctor_set(x_208, 0, x_215);
x_217 = x_208;
goto block_224;
}
else
{
lean_object* x_225; 
x_225 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_225, 0, x_215);
lean_ctor_set(x_225, 1, x_1);
lean_ctor_set(x_225, 2, x_2);
lean_ctor_set(x_225, 3, x_143);
lean_ctor_set(x_225, 4, x_143);
x_217 = x_225;
goto block_224;
}
block_224:
{
lean_object* x_218; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_217);
lean_ctor_set(x_9, 3, x_216);
lean_ctor_set(x_9, 2, x_211);
lean_ctor_set(x_9, 1, x_210);
lean_ctor_set(x_9, 0, x_214);
x_218 = x_9;
goto block_222;
}
else
{
lean_object* x_223; 
x_223 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_223, 0, x_214);
lean_ctor_set(x_223, 1, x_210);
lean_ctor_set(x_223, 2, x_211);
lean_ctor_set(x_223, 3, x_216);
lean_ctor_set(x_223, 4, x_217);
x_218 = x_223;
goto block_222;
}
block_222:
{
lean_object* x_219; 
if (x_205 == 0)
{
lean_ctor_set(x_204, 2, x_218);
x_219 = x_204;
goto block_220;
}
else
{
lean_object* x_221; 
x_221 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_221, 0, x_202);
lean_ctor_set(x_221, 1, x_203);
lean_ctor_set(x_221, 2, x_218);
x_219 = x_221;
goto block_220;
}
block_220:
{
return x_219;
}
}
}
}
}
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_253; 
x_241 = lean_ctor_get(x_11, 0);
x_242 = lean_ctor_get(x_11, 1);
x_253 = !lean_is_exclusive(x_11);
if (x_253 == 0)
{
lean_object* x_254; 
x_254 = lean_ctor_get(x_11, 2);
lean_dec(x_254);
x_243 = x_11;
x_244 = x_253;
goto block_252;
}
else
{
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_11);
x_243 = lean_box(0);
x_244 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_unsigned_to_nat(2u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_201);
lean_ctor_set(x_9, 3, x_3);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_245);
x_246 = x_9;
goto block_250;
}
else
{
lean_object* x_251; 
x_251 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_251, 0, x_245);
lean_ctor_set(x_251, 1, x_1);
lean_ctor_set(x_251, 2, x_2);
lean_ctor_set(x_251, 3, x_3);
lean_ctor_set(x_251, 4, x_201);
x_246 = x_251;
goto block_250;
}
block_250:
{
lean_object* x_247; 
if (x_244 == 0)
{
lean_ctor_set(x_243, 2, x_246);
x_247 = x_243;
goto block_248;
}
else
{
lean_object* x_249; 
x_249 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_249, 0, x_241);
lean_ctor_set(x_249, 1, x_242);
lean_ctor_set(x_249, 2, x_246);
x_247 = x_249;
goto block_248;
}
block_248:
{
return x_247;
}
}
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; uint8_t x_267; 
x_255 = lean_ctor_get(x_11, 0);
x_256 = lean_ctor_get(x_11, 1);
x_267 = !lean_is_exclusive(x_11);
if (x_267 == 0)
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_11, 2);
lean_dec(x_268);
x_257 = x_11;
x_258 = x_267;
goto block_266;
}
else
{
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_11);
x_257 = lean_box(0);
x_258 = x_267;
goto block_266;
}
block_266:
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_unsigned_to_nat(1u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_3);
lean_ctor_set(x_9, 3, x_3);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_259);
x_260 = x_9;
goto block_264;
}
else
{
lean_object* x_265; 
x_265 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_265, 0, x_259);
lean_ctor_set(x_265, 1, x_1);
lean_ctor_set(x_265, 2, x_2);
lean_ctor_set(x_265, 3, x_3);
lean_ctor_set(x_265, 4, x_3);
x_260 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_261; 
if (x_258 == 0)
{
lean_ctor_set(x_257, 2, x_260);
x_261 = x_257;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_263, 0, x_255);
lean_ctor_set(x_263, 1, x_256);
lean_ctor_set(x_263, 2, x_260);
x_261 = x_263;
goto block_262;
}
block_262:
{
return x_261;
}
}
}
}
}
}
}
else
{
lean_object* x_272; 
x_272 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_272, 0, x_1);
lean_ctor_set(x_272, 1, x_2);
lean_ctor_set(x_272, 2, x_3);
return x_272;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxView_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_glue___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_nat_dec_lt(x_3, x_8);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_155; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_155 = !lean_is_exclusive(x_1);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_1, 4);
lean_dec(x_156);
x_157 = lean_ctor_get(x_1, 3);
lean_dec(x_157);
x_158 = lean_ctor_get(x_1, 2);
lean_dec(x_158);
x_159 = lean_ctor_get(x_1, 1);
lean_dec(x_159);
x_160 = lean_ctor_get(x_1, 0);
lean_dec(x_160);
x_14 = x_1;
x_15 = x_155;
goto block_154;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_4, x_5, x_6, x_7);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_mul(x_21, x_20);
x_23 = lean_nat_dec_lt(x_22, x_8);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_24, x_20);
x_26 = lean_nat_add(x_25, x_8);
lean_dec(x_25);
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_2);
lean_ctor_set(x_14, 3, x_17);
lean_ctor_set(x_14, 2, x_19);
lean_ctor_set(x_14, 1, x_18);
lean_ctor_set(x_14, 0, x_26);
x_27 = x_14;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_29, 2, x_19);
lean_ctor_set(x_29, 3, x_17);
lean_ctor_set(x_29, 4, x_2);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
else
{
lean_object* x_30; uint8_t x_31; uint8_t x_86; 
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_86 = !lean_is_exclusive(x_2);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_2, 4);
lean_dec(x_87);
x_88 = lean_ctor_get(x_2, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_2, 2);
lean_dec(x_89);
x_90 = lean_ctor_get(x_2, 1);
lean_dec(x_90);
x_91 = lean_ctor_get(x_2, 0);
lean_dec(x_91);
x_30 = x_2;
x_31 = x_86;
goto block_85;
}
else
{
lean_dec(x_2);
x_30 = lean_box(0);
x_31 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
x_34 = lean_ctor_get(x_11, 2);
x_35 = lean_ctor_get(x_11, 3);
x_36 = lean_ctor_get(x_11, 4);
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_mul(x_38, x_37);
x_40 = lean_nat_dec_lt(x_32, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; uint8_t x_69; 
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_69 = !lean_is_exclusive(x_11);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_11, 4);
lean_dec(x_70);
x_71 = lean_ctor_get(x_11, 3);
lean_dec(x_71);
x_72 = lean_ctor_get(x_11, 2);
lean_dec(x_72);
x_73 = lean_ctor_get(x_11, 1);
lean_dec(x_73);
x_74 = lean_ctor_get(x_11, 0);
lean_dec(x_74);
x_41 = x_11;
x_42 = x_69;
goto block_68;
}
else
{
lean_dec(x_11);
x_41 = lean_box(0);
x_42 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_57; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_43, x_20);
x_45 = lean_nat_add(x_44, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_35, 0);
lean_inc(x_66);
x_57 = x_66;
goto block_65;
}
else
{
lean_object* x_67; 
x_67 = lean_unsigned_to_nat(0u);
x_57 = x_67;
goto block_65;
}
block_56:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_nat_add(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_42 == 0)
{
lean_ctor_set(x_41, 4, x_12);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_10);
lean_ctor_set(x_41, 1, x_9);
lean_ctor_set(x_41, 0, x_49);
x_50 = x_41;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_9);
lean_ctor_set(x_55, 2, x_10);
lean_ctor_set(x_55, 3, x_36);
lean_ctor_set(x_55, 4, x_12);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_50);
lean_ctor_set(x_30, 3, x_46);
lean_ctor_set(x_30, 2, x_34);
lean_ctor_set(x_30, 1, x_33);
lean_ctor_set(x_30, 0, x_45);
x_51 = x_30;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_33);
lean_ctor_set(x_53, 2, x_34);
lean_ctor_set(x_53, 3, x_46);
lean_ctor_set(x_53, 4, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
block_65:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_nat_add(x_44, x_57);
lean_dec(x_57);
lean_dec(x_44);
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_35);
lean_ctor_set(x_14, 3, x_17);
lean_ctor_set(x_14, 2, x_19);
lean_ctor_set(x_14, 1, x_18);
lean_ctor_set(x_14, 0, x_58);
x_59 = x_14;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_18);
lean_ctor_set(x_64, 2, x_19);
lean_ctor_set(x_64, 3, x_17);
lean_ctor_set(x_64, 4, x_35);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
x_60 = lean_nat_add(x_43, x_37);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_36, 0);
lean_inc(x_61);
x_46 = x_59;
x_47 = x_60;
x_48 = x_61;
goto block_56;
}
else
{
lean_object* x_62; 
x_62 = lean_unsigned_to_nat(0u);
x_46 = x_59;
x_47 = x_60;
x_48 = x_62;
goto block_56;
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_75, x_20);
x_77 = lean_nat_add(x_76, x_8);
lean_dec(x_8);
x_78 = lean_nat_add(x_76, x_32);
lean_dec(x_76);
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_11);
lean_ctor_set(x_30, 3, x_17);
lean_ctor_set(x_30, 2, x_19);
lean_ctor_set(x_30, 1, x_18);
lean_ctor_set(x_30, 0, x_78);
x_79 = x_30;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_18);
lean_ctor_set(x_84, 2, x_19);
lean_ctor_set(x_84, 3, x_17);
lean_ctor_set(x_84, 4, x_11);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 3, x_79);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 0, x_77);
x_80 = x_14;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_9);
lean_ctor_set(x_82, 2, x_10);
lean_ctor_set(x_82, 3, x_79);
lean_ctor_set(x_82, 4, x_12);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
}
}
else
{
lean_object* x_92; uint8_t x_93; uint8_t x_148; 
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_148 = !lean_is_exclusive(x_2);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_149 = lean_ctor_get(x_2, 4);
lean_dec(x_149);
x_150 = lean_ctor_get(x_2, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_2, 2);
lean_dec(x_151);
x_152 = lean_ctor_get(x_2, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_2, 0);
lean_dec(x_153);
x_92 = x_2;
x_93 = x_148;
goto block_147;
}
else
{
lean_dec(x_2);
x_92 = lean_box(0);
x_93 = x_148;
goto block_147;
}
block_147:
{
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_16, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_16, 1);
lean_inc(x_95);
lean_dec_ref(x_16);
x_96 = lean_ctor_get(x_11, 0);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_add(x_97, x_8);
lean_dec(x_8);
x_99 = lean_nat_add(x_97, x_96);
if (x_93 == 0)
{
lean_ctor_set(x_92, 4, x_11);
lean_ctor_set(x_92, 3, x_17);
lean_ctor_set(x_92, 2, x_95);
lean_ctor_set(x_92, 1, x_94);
lean_ctor_set(x_92, 0, x_99);
x_100 = x_92;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_94);
lean_ctor_set(x_105, 2, x_95);
lean_ctor_set(x_105, 3, x_17);
lean_ctor_set(x_105, 4, x_11);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 3, x_100);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 0, x_98);
x_101 = x_14;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_9);
lean_ctor_set(x_103, 2, x_10);
lean_ctor_set(x_103, 3, x_100);
lean_ctor_set(x_103, 4, x_12);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_124; 
lean_dec(x_8);
x_106 = lean_ctor_get(x_16, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_16, 1);
lean_inc(x_107);
lean_dec_ref(x_16);
x_108 = lean_ctor_get(x_11, 1);
x_109 = lean_ctor_get(x_11, 2);
x_124 = !lean_is_exclusive(x_11);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_11, 4);
lean_dec(x_125);
x_126 = lean_ctor_get(x_11, 3);
lean_dec(x_126);
x_127 = lean_ctor_get(x_11, 0);
lean_dec(x_127);
x_110 = x_11;
x_111 = x_124;
goto block_123;
}
else
{
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_11);
x_110 = lean_box(0);
x_111 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_unsigned_to_nat(3u);
x_113 = lean_unsigned_to_nat(1u);
if (x_111 == 0)
{
lean_ctor_set(x_110, 4, x_12);
lean_ctor_set(x_110, 3, x_12);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set(x_110, 0, x_113);
x_114 = x_110;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_122, 0, x_113);
lean_ctor_set(x_122, 1, x_106);
lean_ctor_set(x_122, 2, x_107);
lean_ctor_set(x_122, 3, x_12);
lean_ctor_set(x_122, 4, x_12);
x_114 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_115; 
if (x_93 == 0)
{
lean_ctor_set(x_92, 3, x_12);
lean_ctor_set(x_92, 0, x_113);
x_115 = x_92;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_9);
lean_ctor_set(x_120, 2, x_10);
lean_ctor_set(x_120, 3, x_12);
lean_ctor_set(x_120, 4, x_12);
x_115 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_116; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_115);
lean_ctor_set(x_14, 3, x_114);
lean_ctor_set(x_14, 2, x_109);
lean_ctor_set(x_14, 1, x_108);
lean_ctor_set(x_14, 0, x_112);
x_116 = x_14;
goto block_117;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_118, 0, x_112);
lean_ctor_set(x_118, 1, x_108);
lean_ctor_set(x_118, 2, x_109);
lean_ctor_set(x_118, 3, x_114);
lean_ctor_set(x_118, 4, x_115);
x_116 = x_118;
goto block_117;
}
block_117:
{
return x_116;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_8);
x_128 = lean_ctor_get(x_16, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_16, 1);
lean_inc(x_129);
lean_dec_ref(x_16);
x_130 = lean_unsigned_to_nat(3u);
x_131 = lean_unsigned_to_nat(1u);
if (x_93 == 0)
{
lean_ctor_set(x_92, 4, x_11);
lean_ctor_set(x_92, 2, x_129);
lean_ctor_set(x_92, 1, x_128);
lean_ctor_set(x_92, 0, x_131);
x_132 = x_92;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_137, 0, x_131);
lean_ctor_set(x_137, 1, x_128);
lean_ctor_set(x_137, 2, x_129);
lean_ctor_set(x_137, 3, x_11);
lean_ctor_set(x_137, 4, x_11);
x_132 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_133; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 3, x_132);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 0, x_130);
x_133 = x_14;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_9);
lean_ctor_set(x_135, 2, x_10);
lean_ctor_set(x_135, 3, x_132);
lean_ctor_set(x_135, 4, x_12);
x_133 = x_135;
goto block_134;
}
block_134:
{
return x_133;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_16, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_16, 1);
lean_inc(x_139);
lean_dec_ref(x_16);
if (x_93 == 0)
{
lean_ctor_set(x_92, 3, x_12);
x_140 = x_92;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_146, 0, x_8);
lean_ctor_set(x_146, 1, x_9);
lean_ctor_set(x_146, 2, x_10);
lean_ctor_set(x_146, 3, x_12);
lean_ctor_set(x_146, 4, x_12);
x_140 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_unsigned_to_nat(2u);
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_140);
lean_ctor_set(x_14, 3, x_12);
lean_ctor_set(x_14, 2, x_139);
lean_ctor_set(x_14, 1, x_138);
lean_ctor_set(x_14, 0, x_141);
x_142 = x_14;
goto block_143;
}
else
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_138);
lean_ctor_set(x_144, 2, x_139);
lean_ctor_set(x_144, 3, x_12);
lean_ctor_set(x_144, 4, x_140);
x_142 = x_144;
goto block_143;
}
block_143:
{
return x_142;
}
}
}
}
}
}
}
}
else
{
lean_object* x_161; uint8_t x_162; uint8_t x_319; 
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
x_319 = !lean_is_exclusive(x_2);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_320 = lean_ctor_get(x_2, 4);
lean_dec(x_320);
x_321 = lean_ctor_get(x_2, 3);
lean_dec(x_321);
x_322 = lean_ctor_get(x_2, 2);
lean_dec(x_322);
x_323 = lean_ctor_get(x_2, 1);
lean_dec(x_323);
x_324 = lean_ctor_get(x_2, 0);
lean_dec(x_324);
x_161 = x_2;
x_162 = x_319;
goto block_318;
}
else
{
lean_dec(x_2);
x_161 = lean_box(0);
x_162 = x_319;
goto block_318;
}
block_318:
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_9, x_10, x_11, x_12);
x_164 = lean_ctor_get(x_163, 2);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec_ref(x_163);
x_167 = lean_ctor_get(x_164, 0);
x_168 = lean_unsigned_to_nat(3u);
x_169 = lean_nat_mul(x_168, x_167);
x_170 = lean_nat_dec_lt(x_169, x_3);
lean_dec(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_7);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_add(x_171, x_3);
x_173 = lean_nat_add(x_172, x_167);
lean_dec(x_172);
if (x_162 == 0)
{
lean_ctor_set(x_161, 4, x_164);
lean_ctor_set(x_161, 3, x_1);
lean_ctor_set(x_161, 2, x_166);
lean_ctor_set(x_161, 1, x_165);
lean_ctor_set(x_161, 0, x_173);
x_174 = x_161;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_165);
lean_ctor_set(x_176, 2, x_166);
lean_ctor_set(x_176, 3, x_1);
lean_ctor_set(x_176, 4, x_164);
x_174 = x_176;
goto block_175;
}
block_175:
{
return x_174;
}
}
else
{
lean_object* x_177; uint8_t x_178; uint8_t x_244; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_244 = !lean_is_exclusive(x_1);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_245 = lean_ctor_get(x_1, 4);
lean_dec(x_245);
x_246 = lean_ctor_get(x_1, 3);
lean_dec(x_246);
x_247 = lean_ctor_get(x_1, 2);
lean_dec(x_247);
x_248 = lean_ctor_get(x_1, 1);
lean_dec(x_248);
x_249 = lean_ctor_get(x_1, 0);
lean_dec(x_249);
x_177 = x_1;
x_178 = x_244;
goto block_243;
}
else
{
lean_dec(x_1);
x_177 = lean_box(0);
x_178 = x_244;
goto block_243;
}
block_243:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_179 = lean_ctor_get(x_6, 0);
x_180 = lean_ctor_get(x_7, 0);
x_181 = lean_ctor_get(x_7, 1);
x_182 = lean_ctor_get(x_7, 2);
x_183 = lean_ctor_get(x_7, 3);
x_184 = lean_ctor_get(x_7, 4);
x_185 = lean_unsigned_to_nat(2u);
x_186 = lean_nat_mul(x_185, x_179);
x_187 = lean_nat_dec_lt(x_180, x_186);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; uint8_t x_189; uint8_t x_226; 
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_del_object(x_177);
x_226 = !lean_is_exclusive(x_7);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_227 = lean_ctor_get(x_7, 4);
lean_dec(x_227);
x_228 = lean_ctor_get(x_7, 3);
lean_dec(x_228);
x_229 = lean_ctor_get(x_7, 2);
lean_dec(x_229);
x_230 = lean_ctor_get(x_7, 1);
lean_dec(x_230);
x_231 = lean_ctor_get(x_7, 0);
lean_dec(x_231);
x_188 = x_7;
x_189 = x_226;
goto block_225;
}
else
{
lean_dec(x_7);
x_188 = lean_box(0);
x_189 = x_226;
goto block_225;
}
block_225:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_213; lean_object* x_214; 
x_190 = lean_unsigned_to_nat(1u);
x_191 = lean_nat_add(x_190, x_3);
lean_dec(x_3);
x_192 = lean_nat_add(x_191, x_167);
lean_dec(x_191);
x_213 = lean_nat_add(x_190, x_179);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_183, 0);
lean_inc(x_223);
x_214 = x_223;
goto block_222;
}
else
{
lean_object* x_224; 
x_224 = lean_unsigned_to_nat(0u);
x_214 = x_224;
goto block_222;
}
block_212:
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_nat_add(x_194, x_195);
lean_dec(x_195);
lean_dec(x_194);
lean_inc_ref(x_164);
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_164);
lean_ctor_set(x_188, 3, x_184);
lean_ctor_set(x_188, 2, x_166);
lean_ctor_set(x_188, 1, x_165);
lean_ctor_set(x_188, 0, x_196);
x_197 = x_188;
goto block_210;
}
else
{
lean_object* x_211; 
x_211 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_211, 0, x_196);
lean_ctor_set(x_211, 1, x_165);
lean_ctor_set(x_211, 2, x_166);
lean_ctor_set(x_211, 3, x_184);
lean_ctor_set(x_211, 4, x_164);
x_197 = x_211;
goto block_210;
}
block_210:
{
lean_object* x_198; uint8_t x_199; uint8_t x_204; 
x_204 = !lean_is_exclusive(x_164);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_164, 4);
lean_dec(x_205);
x_206 = lean_ctor_get(x_164, 3);
lean_dec(x_206);
x_207 = lean_ctor_get(x_164, 2);
lean_dec(x_207);
x_208 = lean_ctor_get(x_164, 1);
lean_dec(x_208);
x_209 = lean_ctor_get(x_164, 0);
lean_dec(x_209);
x_198 = x_164;
x_199 = x_204;
goto block_203;
}
else
{
lean_dec(x_164);
x_198 = lean_box(0);
x_199 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_200; 
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_197);
lean_ctor_set(x_198, 3, x_193);
lean_ctor_set(x_198, 2, x_182);
lean_ctor_set(x_198, 1, x_181);
lean_ctor_set(x_198, 0, x_192);
x_200 = x_198;
goto block_201;
}
else
{
lean_object* x_202; 
x_202 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_202, 0, x_192);
lean_ctor_set(x_202, 1, x_181);
lean_ctor_set(x_202, 2, x_182);
lean_ctor_set(x_202, 3, x_193);
lean_ctor_set(x_202, 4, x_197);
x_200 = x_202;
goto block_201;
}
block_201:
{
return x_200;
}
}
}
}
block_222:
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_nat_add(x_213, x_214);
lean_dec(x_214);
lean_dec(x_213);
if (x_162 == 0)
{
lean_ctor_set(x_161, 4, x_183);
lean_ctor_set(x_161, 3, x_6);
lean_ctor_set(x_161, 2, x_5);
lean_ctor_set(x_161, 1, x_4);
lean_ctor_set(x_161, 0, x_215);
x_216 = x_161;
goto block_220;
}
else
{
lean_object* x_221; 
x_221 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_221, 0, x_215);
lean_ctor_set(x_221, 1, x_4);
lean_ctor_set(x_221, 2, x_5);
lean_ctor_set(x_221, 3, x_6);
lean_ctor_set(x_221, 4, x_183);
x_216 = x_221;
goto block_220;
}
block_220:
{
lean_object* x_217; 
x_217 = lean_nat_add(x_190, x_167);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_184, 0);
lean_inc(x_218);
x_193 = x_216;
x_194 = x_217;
x_195 = x_218;
goto block_212;
}
else
{
lean_object* x_219; 
x_219 = lean_unsigned_to_nat(0u);
x_193 = x_216;
x_194 = x_217;
x_195 = x_219;
goto block_212;
}
}
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_232 = lean_unsigned_to_nat(1u);
x_233 = lean_nat_add(x_232, x_3);
lean_dec(x_3);
x_234 = lean_nat_add(x_233, x_167);
lean_dec(x_233);
x_235 = lean_nat_add(x_232, x_167);
x_236 = lean_nat_add(x_235, x_180);
lean_dec(x_235);
if (x_162 == 0)
{
lean_ctor_set(x_161, 4, x_164);
lean_ctor_set(x_161, 3, x_7);
lean_ctor_set(x_161, 2, x_166);
lean_ctor_set(x_161, 1, x_165);
lean_ctor_set(x_161, 0, x_236);
x_237 = x_161;
goto block_241;
}
else
{
lean_object* x_242; 
x_242 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_242, 0, x_236);
lean_ctor_set(x_242, 1, x_165);
lean_ctor_set(x_242, 2, x_166);
lean_ctor_set(x_242, 3, x_7);
lean_ctor_set(x_242, 4, x_164);
x_237 = x_242;
goto block_241;
}
block_241:
{
lean_object* x_238; 
if (x_178 == 0)
{
lean_ctor_set(x_177, 4, x_237);
lean_ctor_set(x_177, 0, x_234);
x_238 = x_177;
goto block_239;
}
else
{
lean_object* x_240; 
x_240 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_240, 0, x_234);
lean_ctor_set(x_240, 1, x_4);
lean_ctor_set(x_240, 2, x_5);
lean_ctor_set(x_240, 3, x_6);
lean_ctor_set(x_240, 4, x_237);
x_238 = x_240;
goto block_239;
}
block_239:
{
return x_238;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_250; uint8_t x_251; uint8_t x_275; 
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_275 = !lean_is_exclusive(x_1);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_276 = lean_ctor_get(x_1, 4);
lean_dec(x_276);
x_277 = lean_ctor_get(x_1, 3);
lean_dec(x_277);
x_278 = lean_ctor_get(x_1, 2);
lean_dec(x_278);
x_279 = lean_ctor_get(x_1, 1);
lean_dec(x_279);
x_280 = lean_ctor_get(x_1, 0);
lean_dec(x_280);
x_250 = x_1;
x_251 = x_275;
goto block_274;
}
else
{
lean_dec(x_1);
x_250 = lean_box(0);
x_251 = x_275;
goto block_274;
}
block_274:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_252 = lean_ctor_get(x_163, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_163, 1);
lean_inc(x_253);
lean_dec_ref(x_163);
x_254 = lean_ctor_get(x_7, 0);
x_255 = lean_unsigned_to_nat(1u);
x_256 = lean_nat_add(x_255, x_3);
lean_dec(x_3);
x_257 = lean_nat_add(x_255, x_254);
if (x_162 == 0)
{
lean_ctor_set(x_161, 4, x_164);
lean_ctor_set(x_161, 3, x_7);
lean_ctor_set(x_161, 2, x_253);
lean_ctor_set(x_161, 1, x_252);
lean_ctor_set(x_161, 0, x_257);
x_258 = x_161;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_257);
lean_ctor_set(x_263, 1, x_252);
lean_ctor_set(x_263, 2, x_253);
lean_ctor_set(x_263, 3, x_7);
lean_ctor_set(x_263, 4, x_164);
x_258 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_259; 
if (x_251 == 0)
{
lean_ctor_set(x_250, 4, x_258);
lean_ctor_set(x_250, 0, x_256);
x_259 = x_250;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_261, 0, x_256);
lean_ctor_set(x_261, 1, x_4);
lean_ctor_set(x_261, 2, x_5);
lean_ctor_set(x_261, 3, x_6);
lean_ctor_set(x_261, 4, x_258);
x_259 = x_261;
goto block_260;
}
block_260:
{
return x_259;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_3);
x_264 = lean_ctor_get(x_163, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_163, 1);
lean_inc(x_265);
lean_dec_ref(x_163);
x_266 = lean_unsigned_to_nat(3u);
x_267 = lean_unsigned_to_nat(1u);
if (x_162 == 0)
{
lean_ctor_set(x_161, 4, x_7);
lean_ctor_set(x_161, 3, x_7);
lean_ctor_set(x_161, 2, x_265);
lean_ctor_set(x_161, 1, x_264);
lean_ctor_set(x_161, 0, x_267);
x_268 = x_161;
goto block_272;
}
else
{
lean_object* x_273; 
x_273 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_273, 0, x_267);
lean_ctor_set(x_273, 1, x_264);
lean_ctor_set(x_273, 2, x_265);
lean_ctor_set(x_273, 3, x_7);
lean_ctor_set(x_273, 4, x_7);
x_268 = x_273;
goto block_272;
}
block_272:
{
lean_object* x_269; 
if (x_251 == 0)
{
lean_ctor_set(x_250, 4, x_268);
lean_ctor_set(x_250, 0, x_266);
x_269 = x_250;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_271, 0, x_266);
lean_ctor_set(x_271, 1, x_4);
lean_ctor_set(x_271, 2, x_5);
lean_ctor_set(x_271, 3, x_6);
lean_ctor_set(x_271, 4, x_268);
x_269 = x_271;
goto block_270;
}
block_270:
{
return x_269;
}
}
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_281; uint8_t x_282; uint8_t x_306; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_306 = !lean_is_exclusive(x_1);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_307 = lean_ctor_get(x_1, 4);
lean_dec(x_307);
x_308 = lean_ctor_get(x_1, 3);
lean_dec(x_308);
x_309 = lean_ctor_get(x_1, 2);
lean_dec(x_309);
x_310 = lean_ctor_get(x_1, 1);
lean_dec(x_310);
x_311 = lean_ctor_get(x_1, 0);
lean_dec(x_311);
x_281 = x_1;
x_282 = x_306;
goto block_305;
}
else
{
lean_dec(x_1);
x_281 = lean_box(0);
x_282 = x_306;
goto block_305;
}
block_305:
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; uint8_t x_301; 
x_283 = lean_ctor_get(x_163, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_163, 1);
lean_inc(x_284);
lean_dec_ref(x_163);
x_285 = lean_ctor_get(x_7, 1);
x_286 = lean_ctor_get(x_7, 2);
x_301 = !lean_is_exclusive(x_7);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_7, 4);
lean_dec(x_302);
x_303 = lean_ctor_get(x_7, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_7, 0);
lean_dec(x_304);
x_287 = x_7;
x_288 = x_301;
goto block_300;
}
else
{
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_7);
x_287 = lean_box(0);
x_288 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_unsigned_to_nat(3u);
x_290 = lean_unsigned_to_nat(1u);
if (x_288 == 0)
{
lean_ctor_set(x_287, 4, x_6);
lean_ctor_set(x_287, 3, x_6);
lean_ctor_set(x_287, 2, x_5);
lean_ctor_set(x_287, 1, x_4);
lean_ctor_set(x_287, 0, x_290);
x_291 = x_287;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_299, 0, x_290);
lean_ctor_set(x_299, 1, x_4);
lean_ctor_set(x_299, 2, x_5);
lean_ctor_set(x_299, 3, x_6);
lean_ctor_set(x_299, 4, x_6);
x_291 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_292; 
if (x_162 == 0)
{
lean_ctor_set(x_161, 4, x_6);
lean_ctor_set(x_161, 3, x_6);
lean_ctor_set(x_161, 2, x_284);
lean_ctor_set(x_161, 1, x_283);
lean_ctor_set(x_161, 0, x_290);
x_292 = x_161;
goto block_296;
}
else
{
lean_object* x_297; 
x_297 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_297, 0, x_290);
lean_ctor_set(x_297, 1, x_283);
lean_ctor_set(x_297, 2, x_284);
lean_ctor_set(x_297, 3, x_6);
lean_ctor_set(x_297, 4, x_6);
x_292 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_293; 
if (x_282 == 0)
{
lean_ctor_set(x_281, 4, x_292);
lean_ctor_set(x_281, 3, x_291);
lean_ctor_set(x_281, 2, x_286);
lean_ctor_set(x_281, 1, x_285);
lean_ctor_set(x_281, 0, x_289);
x_293 = x_281;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_295, 0, x_289);
lean_ctor_set(x_295, 1, x_285);
lean_ctor_set(x_295, 2, x_286);
lean_ctor_set(x_295, 3, x_291);
lean_ctor_set(x_295, 4, x_292);
x_293 = x_295;
goto block_294;
}
block_294:
{
return x_293;
}
}
}
}
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_163, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_163, 1);
lean_inc(x_313);
lean_dec_ref(x_163);
x_314 = lean_unsigned_to_nat(2u);
if (x_162 == 0)
{
lean_ctor_set(x_161, 4, x_7);
lean_ctor_set(x_161, 3, x_1);
lean_ctor_set(x_161, 2, x_313);
lean_ctor_set(x_161, 1, x_312);
lean_ctor_set(x_161, 0, x_314);
x_315 = x_161;
goto block_316;
}
else
{
lean_object* x_317; 
x_317 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_312);
lean_ctor_set(x_317, 2, x_313);
lean_ctor_set(x_317, 3, x_1);
lean_ctor_set(x_317, 4, x_7);
x_315 = x_317;
goto block_316;
}
block_316:
{
return x_315;
}
}
}
}
}
}
}
else
{
return x_1;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_glue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_12 = lean_ctor_get(x_3, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 4);
x_18 = lean_nat_dec_lt(x_8, x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; uint8_t x_160; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_160 = !lean_is_exclusive(x_3);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_3, 4);
lean_dec(x_161);
x_162 = lean_ctor_get(x_3, 3);
lean_dec(x_162);
x_163 = lean_ctor_get(x_3, 2);
lean_dec(x_163);
x_164 = lean_ctor_get(x_3, 1);
lean_dec(x_164);
x_165 = lean_ctor_get(x_3, 0);
lean_dec(x_165);
x_19 = x_3;
x_20 = x_160;
goto block_159;
}
else
{
lean_dec(x_3);
x_19 = lean_box(0);
x_20 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_9, x_10, x_11, x_12);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_unsigned_to_nat(3u);
x_27 = lean_nat_mul(x_26, x_25);
x_28 = lean_nat_dec_lt(x_27, x_13);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_16);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_29, x_25);
x_31 = lean_nat_add(x_30, x_13);
lean_dec(x_30);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_4);
lean_ctor_set(x_19, 3, x_22);
lean_ctor_set(x_19, 2, x_24);
lean_ctor_set(x_19, 1, x_23);
lean_ctor_set(x_19, 0, x_31);
x_32 = x_19;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 2, x_24);
lean_ctor_set(x_34, 3, x_22);
lean_ctor_set(x_34, 4, x_4);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
else
{
lean_object* x_35; uint8_t x_36; uint8_t x_91; 
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_91 = !lean_is_exclusive(x_4);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_4, 4);
lean_dec(x_92);
x_93 = lean_ctor_get(x_4, 3);
lean_dec(x_93);
x_94 = lean_ctor_get(x_4, 2);
lean_dec(x_94);
x_95 = lean_ctor_get(x_4, 1);
lean_dec(x_95);
x_96 = lean_ctor_get(x_4, 0);
lean_dec(x_96);
x_35 = x_4;
x_36 = x_91;
goto block_90;
}
else
{
lean_dec(x_4);
x_35 = lean_box(0);
x_36 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
x_39 = lean_ctor_get(x_16, 2);
x_40 = lean_ctor_get(x_16, 3);
x_41 = lean_ctor_get(x_16, 4);
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_mul(x_43, x_42);
x_45 = lean_nat_dec_lt(x_37, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; uint8_t x_74; 
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
x_74 = !lean_is_exclusive(x_16);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_16, 4);
lean_dec(x_75);
x_76 = lean_ctor_get(x_16, 3);
lean_dec(x_76);
x_77 = lean_ctor_get(x_16, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_16, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_16, 0);
lean_dec(x_79);
x_46 = x_16;
x_47 = x_74;
goto block_73;
}
else
{
lean_dec(x_16);
x_46 = lean_box(0);
x_47 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_62; 
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_48, x_25);
x_50 = lean_nat_add(x_49, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_40, 0);
lean_inc(x_71);
x_62 = x_71;
goto block_70;
}
else
{
lean_object* x_72; 
x_72 = lean_unsigned_to_nat(0u);
x_62 = x_72;
goto block_70;
}
block_61:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_nat_add(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
if (x_47 == 0)
{
lean_ctor_set(x_46, 4, x_17);
lean_ctor_set(x_46, 3, x_41);
lean_ctor_set(x_46, 2, x_15);
lean_ctor_set(x_46, 1, x_14);
lean_ctor_set(x_46, 0, x_54);
x_55 = x_46;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_14);
lean_ctor_set(x_60, 2, x_15);
lean_ctor_set(x_60, 3, x_41);
lean_ctor_set(x_60, 4, x_17);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 4, x_55);
lean_ctor_set(x_35, 3, x_51);
lean_ctor_set(x_35, 2, x_39);
lean_ctor_set(x_35, 1, x_38);
lean_ctor_set(x_35, 0, x_50);
x_56 = x_35;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_38);
lean_ctor_set(x_58, 2, x_39);
lean_ctor_set(x_58, 3, x_51);
lean_ctor_set(x_58, 4, x_55);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
block_70:
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_nat_add(x_49, x_62);
lean_dec(x_62);
lean_dec(x_49);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_40);
lean_ctor_set(x_19, 3, x_22);
lean_ctor_set(x_19, 2, x_24);
lean_ctor_set(x_19, 1, x_23);
lean_ctor_set(x_19, 0, x_63);
x_64 = x_19;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_23);
lean_ctor_set(x_69, 2, x_24);
lean_ctor_set(x_69, 3, x_22);
lean_ctor_set(x_69, 4, x_40);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
x_65 = lean_nat_add(x_48, x_42);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_41, 0);
lean_inc(x_66);
x_51 = x_64;
x_52 = x_65;
x_53 = x_66;
goto block_61;
}
else
{
lean_object* x_67; 
x_67 = lean_unsigned_to_nat(0u);
x_51 = x_64;
x_52 = x_65;
x_53 = x_67;
goto block_61;
}
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_80, x_25);
x_82 = lean_nat_add(x_81, x_13);
lean_dec(x_13);
x_83 = lean_nat_add(x_81, x_37);
lean_dec(x_81);
if (x_36 == 0)
{
lean_ctor_set(x_35, 4, x_16);
lean_ctor_set(x_35, 3, x_22);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 0, x_83);
x_84 = x_35;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_23);
lean_ctor_set(x_89, 2, x_24);
lean_ctor_set(x_89, 3, x_22);
lean_ctor_set(x_89, 4, x_16);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 3, x_84);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 0, x_82);
x_85 = x_19;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_14);
lean_ctor_set(x_87, 2, x_15);
lean_ctor_set(x_87, 3, x_84);
lean_ctor_set(x_87, 4, x_17);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
}
}
else
{
lean_object* x_97; uint8_t x_98; uint8_t x_153; 
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_153 = !lean_is_exclusive(x_4);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_4, 4);
lean_dec(x_154);
x_155 = lean_ctor_get(x_4, 3);
lean_dec(x_155);
x_156 = lean_ctor_get(x_4, 2);
lean_dec(x_156);
x_157 = lean_ctor_get(x_4, 1);
lean_dec(x_157);
x_158 = lean_ctor_get(x_4, 0);
lean_dec(x_158);
x_97 = x_4;
x_98 = x_153;
goto block_152;
}
else
{
lean_dec(x_4);
x_97 = lean_box(0);
x_98 = x_153;
goto block_152;
}
block_152:
{
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_21, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_21, 1);
lean_inc(x_100);
lean_dec_ref(x_21);
x_101 = lean_ctor_get(x_16, 0);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_nat_add(x_102, x_13);
lean_dec(x_13);
x_104 = lean_nat_add(x_102, x_101);
if (x_98 == 0)
{
lean_ctor_set(x_97, 4, x_16);
lean_ctor_set(x_97, 3, x_22);
lean_ctor_set(x_97, 2, x_100);
lean_ctor_set(x_97, 1, x_99);
lean_ctor_set(x_97, 0, x_104);
x_105 = x_97;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_99);
lean_ctor_set(x_110, 2, x_100);
lean_ctor_set(x_110, 3, x_22);
lean_ctor_set(x_110, 4, x_16);
x_105 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_106; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 3, x_105);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 0, x_103);
x_106 = x_19;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_14);
lean_ctor_set(x_108, 2, x_15);
lean_ctor_set(x_108, 3, x_105);
lean_ctor_set(x_108, 4, x_17);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_129; 
lean_dec(x_13);
x_111 = lean_ctor_get(x_21, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_21, 1);
lean_inc(x_112);
lean_dec_ref(x_21);
x_113 = lean_ctor_get(x_16, 1);
x_114 = lean_ctor_get(x_16, 2);
x_129 = !lean_is_exclusive(x_16);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_16, 4);
lean_dec(x_130);
x_131 = lean_ctor_get(x_16, 3);
lean_dec(x_131);
x_132 = lean_ctor_get(x_16, 0);
lean_dec(x_132);
x_115 = x_16;
x_116 = x_129;
goto block_128;
}
else
{
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_16);
x_115 = lean_box(0);
x_116 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_unsigned_to_nat(3u);
x_118 = lean_unsigned_to_nat(1u);
if (x_116 == 0)
{
lean_ctor_set(x_115, 4, x_17);
lean_ctor_set(x_115, 3, x_17);
lean_ctor_set(x_115, 2, x_112);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_115, 0, x_118);
x_119 = x_115;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_127, 0, x_118);
lean_ctor_set(x_127, 1, x_111);
lean_ctor_set(x_127, 2, x_112);
lean_ctor_set(x_127, 3, x_17);
lean_ctor_set(x_127, 4, x_17);
x_119 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_120; 
if (x_98 == 0)
{
lean_ctor_set(x_97, 3, x_17);
lean_ctor_set(x_97, 0, x_118);
x_120 = x_97;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_125, 0, x_118);
lean_ctor_set(x_125, 1, x_14);
lean_ctor_set(x_125, 2, x_15);
lean_ctor_set(x_125, 3, x_17);
lean_ctor_set(x_125, 4, x_17);
x_120 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_121; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_120);
lean_ctor_set(x_19, 3, x_119);
lean_ctor_set(x_19, 2, x_114);
lean_ctor_set(x_19, 1, x_113);
lean_ctor_set(x_19, 0, x_117);
x_121 = x_19;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_123, 0, x_117);
lean_ctor_set(x_123, 1, x_113);
lean_ctor_set(x_123, 2, x_114);
lean_ctor_set(x_123, 3, x_119);
lean_ctor_set(x_123, 4, x_120);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_13);
x_133 = lean_ctor_get(x_21, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_21, 1);
lean_inc(x_134);
lean_dec_ref(x_21);
x_135 = lean_unsigned_to_nat(3u);
x_136 = lean_unsigned_to_nat(1u);
if (x_98 == 0)
{
lean_ctor_set(x_97, 4, x_16);
lean_ctor_set(x_97, 2, x_134);
lean_ctor_set(x_97, 1, x_133);
lean_ctor_set(x_97, 0, x_136);
x_137 = x_97;
goto block_141;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_142, 0, x_136);
lean_ctor_set(x_142, 1, x_133);
lean_ctor_set(x_142, 2, x_134);
lean_ctor_set(x_142, 3, x_16);
lean_ctor_set(x_142, 4, x_16);
x_137 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_138; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 3, x_137);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 0, x_135);
x_138 = x_19;
goto block_139;
}
else
{
lean_object* x_140; 
x_140 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_140, 0, x_135);
lean_ctor_set(x_140, 1, x_14);
lean_ctor_set(x_140, 2, x_15);
lean_ctor_set(x_140, 3, x_137);
lean_ctor_set(x_140, 4, x_17);
x_138 = x_140;
goto block_139;
}
block_139:
{
return x_138;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_21, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_21, 1);
lean_inc(x_144);
lean_dec_ref(x_21);
if (x_98 == 0)
{
lean_ctor_set(x_97, 3, x_17);
x_145 = x_97;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_151, 0, x_13);
lean_ctor_set(x_151, 1, x_14);
lean_ctor_set(x_151, 2, x_15);
lean_ctor_set(x_151, 3, x_17);
lean_ctor_set(x_151, 4, x_17);
x_145 = x_151;
goto block_150;
}
block_150:
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_unsigned_to_nat(2u);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_145);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set(x_19, 2, x_144);
lean_ctor_set(x_19, 1, x_143);
lean_ctor_set(x_19, 0, x_146);
x_147 = x_19;
goto block_148;
}
else
{
lean_object* x_149; 
x_149 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_143);
lean_ctor_set(x_149, 2, x_144);
lean_ctor_set(x_149, 3, x_17);
lean_ctor_set(x_149, 4, x_145);
x_147 = x_149;
goto block_148;
}
block_148:
{
return x_147;
}
}
}
}
}
}
}
}
else
{
lean_object* x_166; uint8_t x_167; uint8_t x_324; 
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
x_324 = !lean_is_exclusive(x_4);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_325 = lean_ctor_get(x_4, 4);
lean_dec(x_325);
x_326 = lean_ctor_get(x_4, 3);
lean_dec(x_326);
x_327 = lean_ctor_get(x_4, 2);
lean_dec(x_327);
x_328 = lean_ctor_get(x_4, 1);
lean_dec(x_328);
x_329 = lean_ctor_get(x_4, 0);
lean_dec(x_329);
x_166 = x_4;
x_167 = x_324;
goto block_323;
}
else
{
lean_dec(x_4);
x_166 = lean_box(0);
x_167 = x_324;
goto block_323;
}
block_323:
{
lean_object* x_168; lean_object* x_169; 
x_168 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_14, x_15, x_16, x_17);
x_169 = lean_ctor_get(x_168, 2);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec_ref(x_168);
x_172 = lean_ctor_get(x_169, 0);
x_173 = lean_unsigned_to_nat(3u);
x_174 = lean_nat_mul(x_173, x_172);
x_175 = lean_nat_dec_lt(x_174, x_8);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_12);
x_176 = lean_unsigned_to_nat(1u);
x_177 = lean_nat_add(x_176, x_8);
x_178 = lean_nat_add(x_177, x_172);
lean_dec(x_177);
if (x_167 == 0)
{
lean_ctor_set(x_166, 4, x_169);
lean_ctor_set(x_166, 3, x_3);
lean_ctor_set(x_166, 2, x_171);
lean_ctor_set(x_166, 1, x_170);
lean_ctor_set(x_166, 0, x_178);
x_179 = x_166;
goto block_180;
}
else
{
lean_object* x_181; 
x_181 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_170);
lean_ctor_set(x_181, 2, x_171);
lean_ctor_set(x_181, 3, x_3);
lean_ctor_set(x_181, 4, x_169);
x_179 = x_181;
goto block_180;
}
block_180:
{
return x_179;
}
}
else
{
lean_object* x_182; uint8_t x_183; uint8_t x_249; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_249 = !lean_is_exclusive(x_3);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_3, 4);
lean_dec(x_250);
x_251 = lean_ctor_get(x_3, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_3, 2);
lean_dec(x_252);
x_253 = lean_ctor_get(x_3, 1);
lean_dec(x_253);
x_254 = lean_ctor_get(x_3, 0);
lean_dec(x_254);
x_182 = x_3;
x_183 = x_249;
goto block_248;
}
else
{
lean_dec(x_3);
x_182 = lean_box(0);
x_183 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_184 = lean_ctor_get(x_11, 0);
x_185 = lean_ctor_get(x_12, 0);
x_186 = lean_ctor_get(x_12, 1);
x_187 = lean_ctor_get(x_12, 2);
x_188 = lean_ctor_get(x_12, 3);
x_189 = lean_ctor_get(x_12, 4);
x_190 = lean_unsigned_to_nat(2u);
x_191 = lean_nat_mul(x_190, x_184);
x_192 = lean_nat_dec_lt(x_185, x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; uint8_t x_194; uint8_t x_231; 
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_del_object(x_182);
x_231 = !lean_is_exclusive(x_12);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = lean_ctor_get(x_12, 4);
lean_dec(x_232);
x_233 = lean_ctor_get(x_12, 3);
lean_dec(x_233);
x_234 = lean_ctor_get(x_12, 2);
lean_dec(x_234);
x_235 = lean_ctor_get(x_12, 1);
lean_dec(x_235);
x_236 = lean_ctor_get(x_12, 0);
lean_dec(x_236);
x_193 = x_12;
x_194 = x_231;
goto block_230;
}
else
{
lean_dec(x_12);
x_193 = lean_box(0);
x_194 = x_231;
goto block_230;
}
block_230:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_218; lean_object* x_219; 
x_195 = lean_unsigned_to_nat(1u);
x_196 = lean_nat_add(x_195, x_8);
lean_dec(x_8);
x_197 = lean_nat_add(x_196, x_172);
lean_dec(x_196);
x_218 = lean_nat_add(x_195, x_184);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_188, 0);
lean_inc(x_228);
x_219 = x_228;
goto block_227;
}
else
{
lean_object* x_229; 
x_229 = lean_unsigned_to_nat(0u);
x_219 = x_229;
goto block_227;
}
block_217:
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_nat_add(x_199, x_200);
lean_dec(x_200);
lean_dec(x_199);
lean_inc_ref(x_169);
if (x_194 == 0)
{
lean_ctor_set(x_193, 4, x_169);
lean_ctor_set(x_193, 3, x_189);
lean_ctor_set(x_193, 2, x_171);
lean_ctor_set(x_193, 1, x_170);
lean_ctor_set(x_193, 0, x_201);
x_202 = x_193;
goto block_215;
}
else
{
lean_object* x_216; 
x_216 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_216, 0, x_201);
lean_ctor_set(x_216, 1, x_170);
lean_ctor_set(x_216, 2, x_171);
lean_ctor_set(x_216, 3, x_189);
lean_ctor_set(x_216, 4, x_169);
x_202 = x_216;
goto block_215;
}
block_215:
{
lean_object* x_203; uint8_t x_204; uint8_t x_209; 
x_209 = !lean_is_exclusive(x_169);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_210 = lean_ctor_get(x_169, 4);
lean_dec(x_210);
x_211 = lean_ctor_get(x_169, 3);
lean_dec(x_211);
x_212 = lean_ctor_get(x_169, 2);
lean_dec(x_212);
x_213 = lean_ctor_get(x_169, 1);
lean_dec(x_213);
x_214 = lean_ctor_get(x_169, 0);
lean_dec(x_214);
x_203 = x_169;
x_204 = x_209;
goto block_208;
}
else
{
lean_dec(x_169);
x_203 = lean_box(0);
x_204 = x_209;
goto block_208;
}
block_208:
{
lean_object* x_205; 
if (x_204 == 0)
{
lean_ctor_set(x_203, 4, x_202);
lean_ctor_set(x_203, 3, x_198);
lean_ctor_set(x_203, 2, x_187);
lean_ctor_set(x_203, 1, x_186);
lean_ctor_set(x_203, 0, x_197);
x_205 = x_203;
goto block_206;
}
else
{
lean_object* x_207; 
x_207 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_207, 0, x_197);
lean_ctor_set(x_207, 1, x_186);
lean_ctor_set(x_207, 2, x_187);
lean_ctor_set(x_207, 3, x_198);
lean_ctor_set(x_207, 4, x_202);
x_205 = x_207;
goto block_206;
}
block_206:
{
return x_205;
}
}
}
}
block_227:
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_nat_add(x_218, x_219);
lean_dec(x_219);
lean_dec(x_218);
if (x_167 == 0)
{
lean_ctor_set(x_166, 4, x_188);
lean_ctor_set(x_166, 3, x_11);
lean_ctor_set(x_166, 2, x_10);
lean_ctor_set(x_166, 1, x_9);
lean_ctor_set(x_166, 0, x_220);
x_221 = x_166;
goto block_225;
}
else
{
lean_object* x_226; 
x_226 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_226, 0, x_220);
lean_ctor_set(x_226, 1, x_9);
lean_ctor_set(x_226, 2, x_10);
lean_ctor_set(x_226, 3, x_11);
lean_ctor_set(x_226, 4, x_188);
x_221 = x_226;
goto block_225;
}
block_225:
{
lean_object* x_222; 
x_222 = lean_nat_add(x_195, x_172);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_189, 0);
lean_inc(x_223);
x_198 = x_221;
x_199 = x_222;
x_200 = x_223;
goto block_217;
}
else
{
lean_object* x_224; 
x_224 = lean_unsigned_to_nat(0u);
x_198 = x_221;
x_199 = x_222;
x_200 = x_224;
goto block_217;
}
}
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_237 = lean_unsigned_to_nat(1u);
x_238 = lean_nat_add(x_237, x_8);
lean_dec(x_8);
x_239 = lean_nat_add(x_238, x_172);
lean_dec(x_238);
x_240 = lean_nat_add(x_237, x_172);
x_241 = lean_nat_add(x_240, x_185);
lean_dec(x_240);
if (x_167 == 0)
{
lean_ctor_set(x_166, 4, x_169);
lean_ctor_set(x_166, 3, x_12);
lean_ctor_set(x_166, 2, x_171);
lean_ctor_set(x_166, 1, x_170);
lean_ctor_set(x_166, 0, x_241);
x_242 = x_166;
goto block_246;
}
else
{
lean_object* x_247; 
x_247 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_247, 0, x_241);
lean_ctor_set(x_247, 1, x_170);
lean_ctor_set(x_247, 2, x_171);
lean_ctor_set(x_247, 3, x_12);
lean_ctor_set(x_247, 4, x_169);
x_242 = x_247;
goto block_246;
}
block_246:
{
lean_object* x_243; 
if (x_183 == 0)
{
lean_ctor_set(x_182, 4, x_242);
lean_ctor_set(x_182, 0, x_239);
x_243 = x_182;
goto block_244;
}
else
{
lean_object* x_245; 
x_245 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_245, 0, x_239);
lean_ctor_set(x_245, 1, x_9);
lean_ctor_set(x_245, 2, x_10);
lean_ctor_set(x_245, 3, x_11);
lean_ctor_set(x_245, 4, x_242);
x_243 = x_245;
goto block_244;
}
block_244:
{
return x_243;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_255; uint8_t x_256; uint8_t x_280; 
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_280 = !lean_is_exclusive(x_3);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_281 = lean_ctor_get(x_3, 4);
lean_dec(x_281);
x_282 = lean_ctor_get(x_3, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_3, 2);
lean_dec(x_283);
x_284 = lean_ctor_get(x_3, 1);
lean_dec(x_284);
x_285 = lean_ctor_get(x_3, 0);
lean_dec(x_285);
x_255 = x_3;
x_256 = x_280;
goto block_279;
}
else
{
lean_dec(x_3);
x_255 = lean_box(0);
x_256 = x_280;
goto block_279;
}
block_279:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_257 = lean_ctor_get(x_168, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_168, 1);
lean_inc(x_258);
lean_dec_ref(x_168);
x_259 = lean_ctor_get(x_12, 0);
x_260 = lean_unsigned_to_nat(1u);
x_261 = lean_nat_add(x_260, x_8);
lean_dec(x_8);
x_262 = lean_nat_add(x_260, x_259);
if (x_167 == 0)
{
lean_ctor_set(x_166, 4, x_169);
lean_ctor_set(x_166, 3, x_12);
lean_ctor_set(x_166, 2, x_258);
lean_ctor_set(x_166, 1, x_257);
lean_ctor_set(x_166, 0, x_262);
x_263 = x_166;
goto block_267;
}
else
{
lean_object* x_268; 
x_268 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_268, 0, x_262);
lean_ctor_set(x_268, 1, x_257);
lean_ctor_set(x_268, 2, x_258);
lean_ctor_set(x_268, 3, x_12);
lean_ctor_set(x_268, 4, x_169);
x_263 = x_268;
goto block_267;
}
block_267:
{
lean_object* x_264; 
if (x_256 == 0)
{
lean_ctor_set(x_255, 4, x_263);
lean_ctor_set(x_255, 0, x_261);
x_264 = x_255;
goto block_265;
}
else
{
lean_object* x_266; 
x_266 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_266, 0, x_261);
lean_ctor_set(x_266, 1, x_9);
lean_ctor_set(x_266, 2, x_10);
lean_ctor_set(x_266, 3, x_11);
lean_ctor_set(x_266, 4, x_263);
x_264 = x_266;
goto block_265;
}
block_265:
{
return x_264;
}
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_8);
x_269 = lean_ctor_get(x_168, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_168, 1);
lean_inc(x_270);
lean_dec_ref(x_168);
x_271 = lean_unsigned_to_nat(3u);
x_272 = lean_unsigned_to_nat(1u);
if (x_167 == 0)
{
lean_ctor_set(x_166, 4, x_12);
lean_ctor_set(x_166, 3, x_12);
lean_ctor_set(x_166, 2, x_270);
lean_ctor_set(x_166, 1, x_269);
lean_ctor_set(x_166, 0, x_272);
x_273 = x_166;
goto block_277;
}
else
{
lean_object* x_278; 
x_278 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_278, 0, x_272);
lean_ctor_set(x_278, 1, x_269);
lean_ctor_set(x_278, 2, x_270);
lean_ctor_set(x_278, 3, x_12);
lean_ctor_set(x_278, 4, x_12);
x_273 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_274; 
if (x_256 == 0)
{
lean_ctor_set(x_255, 4, x_273);
lean_ctor_set(x_255, 0, x_271);
x_274 = x_255;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_276, 0, x_271);
lean_ctor_set(x_276, 1, x_9);
lean_ctor_set(x_276, 2, x_10);
lean_ctor_set(x_276, 3, x_11);
lean_ctor_set(x_276, 4, x_273);
x_274 = x_276;
goto block_275;
}
block_275:
{
return x_274;
}
}
}
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_286; uint8_t x_287; uint8_t x_311; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_311 = !lean_is_exclusive(x_3);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_312 = lean_ctor_get(x_3, 4);
lean_dec(x_312);
x_313 = lean_ctor_get(x_3, 3);
lean_dec(x_313);
x_314 = lean_ctor_get(x_3, 2);
lean_dec(x_314);
x_315 = lean_ctor_get(x_3, 1);
lean_dec(x_315);
x_316 = lean_ctor_get(x_3, 0);
lean_dec(x_316);
x_286 = x_3;
x_287 = x_311;
goto block_310;
}
else
{
lean_dec(x_3);
x_286 = lean_box(0);
x_287 = x_311;
goto block_310;
}
block_310:
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; uint8_t x_306; 
x_288 = lean_ctor_get(x_168, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_168, 1);
lean_inc(x_289);
lean_dec_ref(x_168);
x_290 = lean_ctor_get(x_12, 1);
x_291 = lean_ctor_get(x_12, 2);
x_306 = !lean_is_exclusive(x_12);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_12, 4);
lean_dec(x_307);
x_308 = lean_ctor_get(x_12, 3);
lean_dec(x_308);
x_309 = lean_ctor_get(x_12, 0);
lean_dec(x_309);
x_292 = x_12;
x_293 = x_306;
goto block_305;
}
else
{
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_12);
x_292 = lean_box(0);
x_293 = x_306;
goto block_305;
}
block_305:
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_unsigned_to_nat(3u);
x_295 = lean_unsigned_to_nat(1u);
if (x_293 == 0)
{
lean_ctor_set(x_292, 4, x_11);
lean_ctor_set(x_292, 3, x_11);
lean_ctor_set(x_292, 2, x_10);
lean_ctor_set(x_292, 1, x_9);
lean_ctor_set(x_292, 0, x_295);
x_296 = x_292;
goto block_303;
}
else
{
lean_object* x_304; 
x_304 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_304, 0, x_295);
lean_ctor_set(x_304, 1, x_9);
lean_ctor_set(x_304, 2, x_10);
lean_ctor_set(x_304, 3, x_11);
lean_ctor_set(x_304, 4, x_11);
x_296 = x_304;
goto block_303;
}
block_303:
{
lean_object* x_297; 
if (x_167 == 0)
{
lean_ctor_set(x_166, 4, x_11);
lean_ctor_set(x_166, 3, x_11);
lean_ctor_set(x_166, 2, x_289);
lean_ctor_set(x_166, 1, x_288);
lean_ctor_set(x_166, 0, x_295);
x_297 = x_166;
goto block_301;
}
else
{
lean_object* x_302; 
x_302 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_302, 0, x_295);
lean_ctor_set(x_302, 1, x_288);
lean_ctor_set(x_302, 2, x_289);
lean_ctor_set(x_302, 3, x_11);
lean_ctor_set(x_302, 4, x_11);
x_297 = x_302;
goto block_301;
}
block_301:
{
lean_object* x_298; 
if (x_287 == 0)
{
lean_ctor_set(x_286, 4, x_297);
lean_ctor_set(x_286, 3, x_296);
lean_ctor_set(x_286, 2, x_291);
lean_ctor_set(x_286, 1, x_290);
lean_ctor_set(x_286, 0, x_294);
x_298 = x_286;
goto block_299;
}
else
{
lean_object* x_300; 
x_300 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_300, 0, x_294);
lean_ctor_set(x_300, 1, x_290);
lean_ctor_set(x_300, 2, x_291);
lean_ctor_set(x_300, 3, x_296);
lean_ctor_set(x_300, 4, x_297);
x_298 = x_300;
goto block_299;
}
block_299:
{
return x_298;
}
}
}
}
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_317 = lean_ctor_get(x_168, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_168, 1);
lean_inc(x_318);
lean_dec_ref(x_168);
x_319 = lean_unsigned_to_nat(2u);
if (x_167 == 0)
{
lean_ctor_set(x_166, 4, x_12);
lean_ctor_set(x_166, 3, x_3);
lean_ctor_set(x_166, 2, x_318);
lean_ctor_set(x_166, 1, x_317);
lean_ctor_set(x_166, 0, x_319);
x_320 = x_166;
goto block_321;
}
else
{
lean_object* x_322; 
x_322 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_317);
lean_ctor_set(x_322, 2, x_318);
lean_ctor_set(x_322, 3, x_3);
lean_ctor_set(x_322, 4, x_12);
x_320 = x_322;
goto block_321;
}
block_321:
{
return x_320;
}
}
}
}
}
}
}
else
{
return x_3;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0), lean_box(0));
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_2, lean_box(0), lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0), lean_box(0));
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_2, lean_box(0), lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(x_9, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_glue_x21___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_nat_dec_lt(x_3, x_8);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_167; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_167 = !lean_is_exclusive(x_1);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_1, 4);
lean_dec(x_168);
x_169 = lean_ctor_get(x_1, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_1, 2);
lean_dec(x_170);
x_171 = lean_ctor_get(x_1, 1);
lean_dec(x_171);
x_172 = lean_ctor_get(x_1, 0);
lean_dec(x_172);
x_14 = x_1;
x_15 = x_167;
goto block_166;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(x_4, x_5, x_6, x_7);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_mul(x_21, x_20);
x_23 = lean_nat_dec_lt(x_22, x_8);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_24, x_20);
x_26 = lean_nat_add(x_25, x_8);
lean_dec(x_25);
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_2);
lean_ctor_set(x_14, 3, x_17);
lean_ctor_set(x_14, 2, x_19);
lean_ctor_set(x_14, 1, x_18);
lean_ctor_set(x_14, 0, x_26);
x_27 = x_14;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_29, 2, x_19);
lean_ctor_set(x_29, 3, x_17);
lean_ctor_set(x_29, 4, x_2);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
else
{
lean_object* x_30; uint8_t x_31; uint8_t x_92; 
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_92 = !lean_is_exclusive(x_2);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_2, 4);
lean_dec(x_93);
x_94 = lean_ctor_get(x_2, 3);
lean_dec(x_94);
x_95 = lean_ctor_get(x_2, 2);
lean_dec(x_95);
x_96 = lean_ctor_get(x_2, 1);
lean_dec(x_96);
x_97 = lean_ctor_get(x_2, 0);
lean_dec(x_97);
x_30 = x_2;
x_31 = x_92;
goto block_91;
}
else
{
lean_dec(x_2);
x_30 = lean_box(0);
x_31 = x_92;
goto block_91;
}
block_91:
{
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
x_34 = lean_ctor_get(x_11, 2);
x_35 = lean_ctor_get(x_11, 3);
x_36 = lean_ctor_get(x_11, 4);
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_mul(x_38, x_37);
x_40 = lean_nat_dec_lt(x_32, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; uint8_t x_69; 
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_69 = !lean_is_exclusive(x_11);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_11, 4);
lean_dec(x_70);
x_71 = lean_ctor_get(x_11, 3);
lean_dec(x_71);
x_72 = lean_ctor_get(x_11, 2);
lean_dec(x_72);
x_73 = lean_ctor_get(x_11, 1);
lean_dec(x_73);
x_74 = lean_ctor_get(x_11, 0);
lean_dec(x_74);
x_41 = x_11;
x_42 = x_69;
goto block_68;
}
else
{
lean_dec(x_11);
x_41 = lean_box(0);
x_42 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_57; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_43, x_20);
x_45 = lean_nat_add(x_44, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_35, 0);
lean_inc(x_66);
x_57 = x_66;
goto block_65;
}
else
{
lean_object* x_67; 
x_67 = lean_unsigned_to_nat(0u);
x_57 = x_67;
goto block_65;
}
block_56:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_nat_add(x_46, x_48);
lean_dec(x_48);
lean_dec(x_46);
if (x_42 == 0)
{
lean_ctor_set(x_41, 4, x_12);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_10);
lean_ctor_set(x_41, 1, x_9);
lean_ctor_set(x_41, 0, x_49);
x_50 = x_41;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_9);
lean_ctor_set(x_55, 2, x_10);
lean_ctor_set(x_55, 3, x_36);
lean_ctor_set(x_55, 4, x_12);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_50);
lean_ctor_set(x_30, 3, x_47);
lean_ctor_set(x_30, 2, x_34);
lean_ctor_set(x_30, 1, x_33);
lean_ctor_set(x_30, 0, x_45);
x_51 = x_30;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_33);
lean_ctor_set(x_53, 2, x_34);
lean_ctor_set(x_53, 3, x_47);
lean_ctor_set(x_53, 4, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
block_65:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_nat_add(x_44, x_57);
lean_dec(x_57);
lean_dec(x_44);
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_35);
lean_ctor_set(x_14, 3, x_17);
lean_ctor_set(x_14, 2, x_19);
lean_ctor_set(x_14, 1, x_18);
lean_ctor_set(x_14, 0, x_58);
x_59 = x_14;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_18);
lean_ctor_set(x_64, 2, x_19);
lean_ctor_set(x_64, 3, x_17);
lean_ctor_set(x_64, 4, x_35);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
x_60 = lean_nat_add(x_43, x_37);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_36, 0);
lean_inc(x_61);
x_46 = x_60;
x_47 = x_59;
x_48 = x_61;
goto block_56;
}
else
{
lean_object* x_62; 
x_62 = lean_unsigned_to_nat(0u);
x_46 = x_60;
x_47 = x_59;
x_48 = x_62;
goto block_56;
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_75, x_20);
x_77 = lean_nat_add(x_76, x_8);
lean_dec(x_8);
x_78 = lean_nat_add(x_76, x_32);
lean_dec(x_76);
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_11);
lean_ctor_set(x_30, 3, x_17);
lean_ctor_set(x_30, 2, x_19);
lean_ctor_set(x_30, 1, x_18);
lean_ctor_set(x_30, 0, x_78);
x_79 = x_30;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_18);
lean_ctor_set(x_84, 2, x_19);
lean_ctor_set(x_84, 3, x_17);
lean_ctor_set(x_84, 4, x_11);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 3, x_79);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 0, x_77);
x_80 = x_14;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_9);
lean_ctor_set(x_82, 2, x_10);
lean_ctor_set(x_82, 3, x_79);
lean_ctor_set(x_82, 4, x_12);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_11);
lean_del_object(x_30);
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec(x_18);
lean_del_object(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_85 = lean_box(1);
x_86 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3);
x_87 = l_panic___redArg(x_85, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_del_object(x_30);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_del_object(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_88 = lean_box(1);
x_89 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4);
x_90 = l_panic___redArg(x_88, x_89);
return x_90;
}
}
}
}
else
{
lean_inc(x_12);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_98; uint8_t x_99; uint8_t x_135; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_135 = !lean_is_exclusive(x_2);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_2, 4);
lean_dec(x_136);
x_137 = lean_ctor_get(x_2, 3);
lean_dec(x_137);
x_138 = lean_ctor_get(x_2, 2);
lean_dec(x_138);
x_139 = lean_ctor_get(x_2, 1);
lean_dec(x_139);
x_140 = lean_ctor_get(x_2, 0);
lean_dec(x_140);
x_98 = x_2;
x_99 = x_135;
goto block_134;
}
else
{
lean_dec(x_2);
x_98 = lean_box(0);
x_99 = x_135;
goto block_134;
}
block_134:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_16, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_16, 1);
lean_inc(x_101);
lean_dec_ref(x_16);
x_102 = lean_ctor_get(x_11, 0);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_add(x_103, x_8);
lean_dec(x_8);
x_105 = lean_nat_add(x_103, x_102);
if (x_99 == 0)
{
lean_ctor_set(x_98, 4, x_11);
lean_ctor_set(x_98, 3, x_17);
lean_ctor_set(x_98, 2, x_101);
lean_ctor_set(x_98, 1, x_100);
lean_ctor_set(x_98, 0, x_105);
x_106 = x_98;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_100);
lean_ctor_set(x_111, 2, x_101);
lean_ctor_set(x_111, 3, x_17);
lean_ctor_set(x_111, 4, x_11);
x_106 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_107; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 3, x_106);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 0, x_104);
x_107 = x_14;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_9);
lean_ctor_set(x_109, 2, x_10);
lean_ctor_set(x_109, 3, x_106);
lean_ctor_set(x_109, 4, x_12);
x_107 = x_109;
goto block_108;
}
block_108:
{
return x_107;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_130; 
lean_dec(x_8);
x_112 = lean_ctor_get(x_16, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_16, 1);
lean_inc(x_113);
lean_dec_ref(x_16);
x_114 = lean_ctor_get(x_11, 1);
x_115 = lean_ctor_get(x_11, 2);
x_130 = !lean_is_exclusive(x_11);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_11, 4);
lean_dec(x_131);
x_132 = lean_ctor_get(x_11, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_11, 0);
lean_dec(x_133);
x_116 = x_11;
x_117 = x_130;
goto block_129;
}
else
{
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_11);
x_116 = lean_box(0);
x_117 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_unsigned_to_nat(3u);
x_119 = lean_unsigned_to_nat(1u);
if (x_117 == 0)
{
lean_ctor_set(x_116, 4, x_12);
lean_ctor_set(x_116, 3, x_12);
lean_ctor_set(x_116, 2, x_113);
lean_ctor_set(x_116, 1, x_112);
lean_ctor_set(x_116, 0, x_119);
x_120 = x_116;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_128, 0, x_119);
lean_ctor_set(x_128, 1, x_112);
lean_ctor_set(x_128, 2, x_113);
lean_ctor_set(x_128, 3, x_12);
lean_ctor_set(x_128, 4, x_12);
x_120 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_121; 
if (x_99 == 0)
{
lean_ctor_set(x_98, 3, x_12);
lean_ctor_set(x_98, 0, x_119);
x_121 = x_98;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_119);
lean_ctor_set(x_126, 1, x_9);
lean_ctor_set(x_126, 2, x_10);
lean_ctor_set(x_126, 3, x_12);
lean_ctor_set(x_126, 4, x_12);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_121);
lean_ctor_set(x_14, 3, x_120);
lean_ctor_set(x_14, 2, x_115);
lean_ctor_set(x_14, 1, x_114);
lean_ctor_set(x_14, 0, x_118);
x_122 = x_14;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_118);
lean_ctor_set(x_124, 1, x_114);
lean_ctor_set(x_124, 2, x_115);
lean_ctor_set(x_124, 3, x_120);
lean_ctor_set(x_124, 4, x_121);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_141; uint8_t x_142; uint8_t x_154; 
lean_inc(x_10);
lean_inc(x_9);
x_154 = !lean_is_exclusive(x_2);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_155 = lean_ctor_get(x_2, 4);
lean_dec(x_155);
x_156 = lean_ctor_get(x_2, 3);
lean_dec(x_156);
x_157 = lean_ctor_get(x_2, 2);
lean_dec(x_157);
x_158 = lean_ctor_get(x_2, 1);
lean_dec(x_158);
x_159 = lean_ctor_get(x_2, 0);
lean_dec(x_159);
x_141 = x_2;
x_142 = x_154;
goto block_153;
}
else
{
lean_dec(x_2);
x_141 = lean_box(0);
x_142 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_16, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_16, 1);
lean_inc(x_144);
lean_dec_ref(x_16);
x_145 = lean_unsigned_to_nat(3u);
x_146 = lean_unsigned_to_nat(1u);
if (x_142 == 0)
{
lean_ctor_set(x_141, 4, x_11);
lean_ctor_set(x_141, 2, x_144);
lean_ctor_set(x_141, 1, x_143);
lean_ctor_set(x_141, 0, x_146);
x_147 = x_141;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_152, 0, x_146);
lean_ctor_set(x_152, 1, x_143);
lean_ctor_set(x_152, 2, x_144);
lean_ctor_set(x_152, 3, x_11);
lean_ctor_set(x_152, 4, x_11);
x_147 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_148; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 3, x_147);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 0, x_145);
x_148 = x_14;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_150, 0, x_145);
lean_ctor_set(x_150, 1, x_9);
lean_ctor_set(x_150, 2, x_10);
lean_ctor_set(x_150, 3, x_147);
lean_ctor_set(x_150, 4, x_12);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_16, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_16, 1);
lean_inc(x_161);
lean_dec_ref(x_16);
x_162 = lean_unsigned_to_nat(2u);
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_2);
lean_ctor_set(x_14, 3, x_12);
lean_ctor_set(x_14, 2, x_161);
lean_ctor_set(x_14, 1, x_160);
lean_ctor_set(x_14, 0, x_162);
x_163 = x_14;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set(x_165, 2, x_161);
lean_ctor_set(x_165, 3, x_12);
lean_ctor_set(x_165, 4, x_2);
x_163 = x_165;
goto block_164;
}
block_164:
{
return x_163;
}
}
}
}
}
}
else
{
lean_object* x_173; uint8_t x_174; uint8_t x_337; 
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
x_337 = !lean_is_exclusive(x_2);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_338 = lean_ctor_get(x_2, 4);
lean_dec(x_338);
x_339 = lean_ctor_get(x_2, 3);
lean_dec(x_339);
x_340 = lean_ctor_get(x_2, 2);
lean_dec(x_340);
x_341 = lean_ctor_get(x_2, 1);
lean_dec(x_341);
x_342 = lean_ctor_get(x_2, 0);
lean_dec(x_342);
x_173 = x_2;
x_174 = x_337;
goto block_336;
}
else
{
lean_dec(x_2);
x_173 = lean_box(0);
x_174 = x_337;
goto block_336;
}
block_336:
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(x_9, x_10, x_11, x_12);
x_176 = lean_ctor_get(x_175, 2);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec_ref(x_175);
x_179 = lean_ctor_get(x_176, 0);
x_180 = lean_unsigned_to_nat(3u);
x_181 = lean_nat_mul(x_180, x_179);
x_182 = lean_nat_dec_lt(x_181, x_3);
lean_dec(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_7);
x_183 = lean_unsigned_to_nat(1u);
x_184 = lean_nat_add(x_183, x_3);
x_185 = lean_nat_add(x_184, x_179);
lean_dec(x_184);
if (x_174 == 0)
{
lean_ctor_set(x_173, 4, x_176);
lean_ctor_set(x_173, 3, x_1);
lean_ctor_set(x_173, 2, x_178);
lean_ctor_set(x_173, 1, x_177);
lean_ctor_set(x_173, 0, x_185);
x_186 = x_173;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_177);
lean_ctor_set(x_188, 2, x_178);
lean_ctor_set(x_188, 3, x_1);
lean_ctor_set(x_188, 4, x_176);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
else
{
lean_object* x_189; uint8_t x_190; uint8_t x_262; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_262 = !lean_is_exclusive(x_1);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_ctor_get(x_1, 4);
lean_dec(x_263);
x_264 = lean_ctor_get(x_1, 3);
lean_dec(x_264);
x_265 = lean_ctor_get(x_1, 2);
lean_dec(x_265);
x_266 = lean_ctor_get(x_1, 1);
lean_dec(x_266);
x_267 = lean_ctor_get(x_1, 0);
lean_dec(x_267);
x_189 = x_1;
x_190 = x_262;
goto block_261;
}
else
{
lean_dec(x_1);
x_189 = lean_box(0);
x_190 = x_262;
goto block_261;
}
block_261:
{
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_191 = lean_ctor_get(x_6, 0);
x_192 = lean_ctor_get(x_7, 0);
x_193 = lean_ctor_get(x_7, 1);
x_194 = lean_ctor_get(x_7, 2);
x_195 = lean_ctor_get(x_7, 3);
x_196 = lean_ctor_get(x_7, 4);
x_197 = lean_unsigned_to_nat(2u);
x_198 = lean_nat_mul(x_197, x_191);
x_199 = lean_nat_dec_lt(x_192, x_198);
lean_dec(x_198);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; uint8_t x_238; 
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_del_object(x_189);
x_238 = !lean_is_exclusive(x_7);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_239 = lean_ctor_get(x_7, 4);
lean_dec(x_239);
x_240 = lean_ctor_get(x_7, 3);
lean_dec(x_240);
x_241 = lean_ctor_get(x_7, 2);
lean_dec(x_241);
x_242 = lean_ctor_get(x_7, 1);
lean_dec(x_242);
x_243 = lean_ctor_get(x_7, 0);
lean_dec(x_243);
x_200 = x_7;
x_201 = x_238;
goto block_237;
}
else
{
lean_dec(x_7);
x_200 = lean_box(0);
x_201 = x_238;
goto block_237;
}
block_237:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_225; lean_object* x_226; 
x_202 = lean_unsigned_to_nat(1u);
x_203 = lean_nat_add(x_202, x_3);
lean_dec(x_3);
x_204 = lean_nat_add(x_203, x_179);
lean_dec(x_203);
x_225 = lean_nat_add(x_202, x_191);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_195, 0);
lean_inc(x_235);
x_226 = x_235;
goto block_234;
}
else
{
lean_object* x_236; 
x_236 = lean_unsigned_to_nat(0u);
x_226 = x_236;
goto block_234;
}
block_224:
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_nat_add(x_206, x_207);
lean_dec(x_207);
lean_dec(x_206);
lean_inc_ref(x_176);
if (x_201 == 0)
{
lean_ctor_set(x_200, 4, x_176);
lean_ctor_set(x_200, 3, x_196);
lean_ctor_set(x_200, 2, x_178);
lean_ctor_set(x_200, 1, x_177);
lean_ctor_set(x_200, 0, x_208);
x_209 = x_200;
goto block_222;
}
else
{
lean_object* x_223; 
x_223 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_223, 0, x_208);
lean_ctor_set(x_223, 1, x_177);
lean_ctor_set(x_223, 2, x_178);
lean_ctor_set(x_223, 3, x_196);
lean_ctor_set(x_223, 4, x_176);
x_209 = x_223;
goto block_222;
}
block_222:
{
lean_object* x_210; uint8_t x_211; uint8_t x_216; 
x_216 = !lean_is_exclusive(x_176);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_ctor_get(x_176, 4);
lean_dec(x_217);
x_218 = lean_ctor_get(x_176, 3);
lean_dec(x_218);
x_219 = lean_ctor_get(x_176, 2);
lean_dec(x_219);
x_220 = lean_ctor_get(x_176, 1);
lean_dec(x_220);
x_221 = lean_ctor_get(x_176, 0);
lean_dec(x_221);
x_210 = x_176;
x_211 = x_216;
goto block_215;
}
else
{
lean_dec(x_176);
x_210 = lean_box(0);
x_211 = x_216;
goto block_215;
}
block_215:
{
lean_object* x_212; 
if (x_211 == 0)
{
lean_ctor_set(x_210, 4, x_209);
lean_ctor_set(x_210, 3, x_205);
lean_ctor_set(x_210, 2, x_194);
lean_ctor_set(x_210, 1, x_193);
lean_ctor_set(x_210, 0, x_204);
x_212 = x_210;
goto block_213;
}
else
{
lean_object* x_214; 
x_214 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_214, 0, x_204);
lean_ctor_set(x_214, 1, x_193);
lean_ctor_set(x_214, 2, x_194);
lean_ctor_set(x_214, 3, x_205);
lean_ctor_set(x_214, 4, x_209);
x_212 = x_214;
goto block_213;
}
block_213:
{
return x_212;
}
}
}
}
block_234:
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_nat_add(x_225, x_226);
lean_dec(x_226);
lean_dec(x_225);
if (x_174 == 0)
{
lean_ctor_set(x_173, 4, x_195);
lean_ctor_set(x_173, 3, x_6);
lean_ctor_set(x_173, 2, x_5);
lean_ctor_set(x_173, 1, x_4);
lean_ctor_set(x_173, 0, x_227);
x_228 = x_173;
goto block_232;
}
else
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_233, 0, x_227);
lean_ctor_set(x_233, 1, x_4);
lean_ctor_set(x_233, 2, x_5);
lean_ctor_set(x_233, 3, x_6);
lean_ctor_set(x_233, 4, x_195);
x_228 = x_233;
goto block_232;
}
block_232:
{
lean_object* x_229; 
x_229 = lean_nat_add(x_202, x_179);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_196, 0);
lean_inc(x_230);
x_205 = x_228;
x_206 = x_229;
x_207 = x_230;
goto block_224;
}
else
{
lean_object* x_231; 
x_231 = lean_unsigned_to_nat(0u);
x_205 = x_228;
x_206 = x_229;
x_207 = x_231;
goto block_224;
}
}
}
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_244 = lean_unsigned_to_nat(1u);
x_245 = lean_nat_add(x_244, x_3);
lean_dec(x_3);
x_246 = lean_nat_add(x_245, x_179);
lean_dec(x_245);
x_247 = lean_nat_add(x_244, x_179);
x_248 = lean_nat_add(x_247, x_192);
lean_dec(x_247);
if (x_174 == 0)
{
lean_ctor_set(x_173, 4, x_176);
lean_ctor_set(x_173, 3, x_7);
lean_ctor_set(x_173, 2, x_178);
lean_ctor_set(x_173, 1, x_177);
lean_ctor_set(x_173, 0, x_248);
x_249 = x_173;
goto block_253;
}
else
{
lean_object* x_254; 
x_254 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_254, 0, x_248);
lean_ctor_set(x_254, 1, x_177);
lean_ctor_set(x_254, 2, x_178);
lean_ctor_set(x_254, 3, x_7);
lean_ctor_set(x_254, 4, x_176);
x_249 = x_254;
goto block_253;
}
block_253:
{
lean_object* x_250; 
if (x_190 == 0)
{
lean_ctor_set(x_189, 4, x_249);
lean_ctor_set(x_189, 0, x_246);
x_250 = x_189;
goto block_251;
}
else
{
lean_object* x_252; 
x_252 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_252, 0, x_246);
lean_ctor_set(x_252, 1, x_4);
lean_ctor_set(x_252, 2, x_5);
lean_ctor_set(x_252, 3, x_6);
lean_ctor_set(x_252, 4, x_249);
x_250 = x_252;
goto block_251;
}
block_251:
{
return x_250;
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec_ref(x_6);
lean_del_object(x_189);
lean_dec(x_178);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_del_object(x_173);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_255 = lean_box(1);
x_256 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2);
x_257 = l_panic___redArg(x_255, x_256);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_del_object(x_189);
lean_dec(x_178);
lean_dec_ref(x_176);
lean_dec(x_177);
lean_del_object(x_173);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_258 = lean_box(1);
x_259 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3);
x_260 = l_panic___redArg(x_258, x_259);
return x_260;
}
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_268; uint8_t x_269; uint8_t x_293; 
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_293 = !lean_is_exclusive(x_1);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_294 = lean_ctor_get(x_1, 4);
lean_dec(x_294);
x_295 = lean_ctor_get(x_1, 3);
lean_dec(x_295);
x_296 = lean_ctor_get(x_1, 2);
lean_dec(x_296);
x_297 = lean_ctor_get(x_1, 1);
lean_dec(x_297);
x_298 = lean_ctor_get(x_1, 0);
lean_dec(x_298);
x_268 = x_1;
x_269 = x_293;
goto block_292;
}
else
{
lean_dec(x_1);
x_268 = lean_box(0);
x_269 = x_293;
goto block_292;
}
block_292:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_270 = lean_ctor_get(x_175, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_175, 1);
lean_inc(x_271);
lean_dec_ref(x_175);
x_272 = lean_ctor_get(x_7, 0);
x_273 = lean_unsigned_to_nat(1u);
x_274 = lean_nat_add(x_273, x_3);
lean_dec(x_3);
x_275 = lean_nat_add(x_273, x_272);
if (x_174 == 0)
{
lean_ctor_set(x_173, 4, x_176);
lean_ctor_set(x_173, 3, x_7);
lean_ctor_set(x_173, 2, x_271);
lean_ctor_set(x_173, 1, x_270);
lean_ctor_set(x_173, 0, x_275);
x_276 = x_173;
goto block_280;
}
else
{
lean_object* x_281; 
x_281 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_281, 0, x_275);
lean_ctor_set(x_281, 1, x_270);
lean_ctor_set(x_281, 2, x_271);
lean_ctor_set(x_281, 3, x_7);
lean_ctor_set(x_281, 4, x_176);
x_276 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_277; 
if (x_269 == 0)
{
lean_ctor_set(x_268, 4, x_276);
lean_ctor_set(x_268, 0, x_274);
x_277 = x_268;
goto block_278;
}
else
{
lean_object* x_279; 
x_279 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_279, 0, x_274);
lean_ctor_set(x_279, 1, x_4);
lean_ctor_set(x_279, 2, x_5);
lean_ctor_set(x_279, 3, x_6);
lean_ctor_set(x_279, 4, x_276);
x_277 = x_279;
goto block_278;
}
block_278:
{
return x_277;
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_3);
x_282 = lean_ctor_get(x_175, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_175, 1);
lean_inc(x_283);
lean_dec_ref(x_175);
x_284 = lean_unsigned_to_nat(3u);
x_285 = lean_unsigned_to_nat(1u);
if (x_174 == 0)
{
lean_ctor_set(x_173, 4, x_7);
lean_ctor_set(x_173, 3, x_7);
lean_ctor_set(x_173, 2, x_283);
lean_ctor_set(x_173, 1, x_282);
lean_ctor_set(x_173, 0, x_285);
x_286 = x_173;
goto block_290;
}
else
{
lean_object* x_291; 
x_291 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_291, 0, x_285);
lean_ctor_set(x_291, 1, x_282);
lean_ctor_set(x_291, 2, x_283);
lean_ctor_set(x_291, 3, x_7);
lean_ctor_set(x_291, 4, x_7);
x_286 = x_291;
goto block_290;
}
block_290:
{
lean_object* x_287; 
if (x_269 == 0)
{
lean_ctor_set(x_268, 4, x_286);
lean_ctor_set(x_268, 0, x_284);
x_287 = x_268;
goto block_288;
}
else
{
lean_object* x_289; 
x_289 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_289, 0, x_284);
lean_ctor_set(x_289, 1, x_4);
lean_ctor_set(x_289, 2, x_5);
lean_ctor_set(x_289, 3, x_6);
lean_ctor_set(x_289, 4, x_286);
x_287 = x_289;
goto block_288;
}
block_288:
{
return x_287;
}
}
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_299; uint8_t x_300; uint8_t x_324; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_324 = !lean_is_exclusive(x_1);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_325 = lean_ctor_get(x_1, 4);
lean_dec(x_325);
x_326 = lean_ctor_get(x_1, 3);
lean_dec(x_326);
x_327 = lean_ctor_get(x_1, 2);
lean_dec(x_327);
x_328 = lean_ctor_get(x_1, 1);
lean_dec(x_328);
x_329 = lean_ctor_get(x_1, 0);
lean_dec(x_329);
x_299 = x_1;
x_300 = x_324;
goto block_323;
}
else
{
lean_dec(x_1);
x_299 = lean_box(0);
x_300 = x_324;
goto block_323;
}
block_323:
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; uint8_t x_319; 
x_301 = lean_ctor_get(x_175, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_175, 1);
lean_inc(x_302);
lean_dec_ref(x_175);
x_303 = lean_ctor_get(x_7, 1);
x_304 = lean_ctor_get(x_7, 2);
x_319 = !lean_is_exclusive(x_7);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_7, 4);
lean_dec(x_320);
x_321 = lean_ctor_get(x_7, 3);
lean_dec(x_321);
x_322 = lean_ctor_get(x_7, 0);
lean_dec(x_322);
x_305 = x_7;
x_306 = x_319;
goto block_318;
}
else
{
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_7);
x_305 = lean_box(0);
x_306 = x_319;
goto block_318;
}
block_318:
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_unsigned_to_nat(3u);
x_308 = lean_unsigned_to_nat(1u);
if (x_306 == 0)
{
lean_ctor_set(x_305, 4, x_6);
lean_ctor_set(x_305, 3, x_6);
lean_ctor_set(x_305, 2, x_5);
lean_ctor_set(x_305, 1, x_4);
lean_ctor_set(x_305, 0, x_308);
x_309 = x_305;
goto block_316;
}
else
{
lean_object* x_317; 
x_317 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_317, 0, x_308);
lean_ctor_set(x_317, 1, x_4);
lean_ctor_set(x_317, 2, x_5);
lean_ctor_set(x_317, 3, x_6);
lean_ctor_set(x_317, 4, x_6);
x_309 = x_317;
goto block_316;
}
block_316:
{
lean_object* x_310; 
if (x_174 == 0)
{
lean_ctor_set(x_173, 4, x_6);
lean_ctor_set(x_173, 3, x_6);
lean_ctor_set(x_173, 2, x_302);
lean_ctor_set(x_173, 1, x_301);
lean_ctor_set(x_173, 0, x_308);
x_310 = x_173;
goto block_314;
}
else
{
lean_object* x_315; 
x_315 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_315, 0, x_308);
lean_ctor_set(x_315, 1, x_301);
lean_ctor_set(x_315, 2, x_302);
lean_ctor_set(x_315, 3, x_6);
lean_ctor_set(x_315, 4, x_6);
x_310 = x_315;
goto block_314;
}
block_314:
{
lean_object* x_311; 
if (x_300 == 0)
{
lean_ctor_set(x_299, 4, x_310);
lean_ctor_set(x_299, 3, x_309);
lean_ctor_set(x_299, 2, x_304);
lean_ctor_set(x_299, 1, x_303);
lean_ctor_set(x_299, 0, x_307);
x_311 = x_299;
goto block_312;
}
else
{
lean_object* x_313; 
x_313 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_313, 0, x_307);
lean_ctor_set(x_313, 1, x_303);
lean_ctor_set(x_313, 2, x_304);
lean_ctor_set(x_313, 3, x_309);
lean_ctor_set(x_313, 4, x_310);
x_311 = x_313;
goto block_312;
}
block_312:
{
return x_311;
}
}
}
}
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_330 = lean_ctor_get(x_175, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_175, 1);
lean_inc(x_331);
lean_dec_ref(x_175);
x_332 = lean_unsigned_to_nat(2u);
if (x_174 == 0)
{
lean_ctor_set(x_173, 4, x_7);
lean_ctor_set(x_173, 3, x_1);
lean_ctor_set(x_173, 2, x_331);
lean_ctor_set(x_173, 1, x_330);
lean_ctor_set(x_173, 0, x_332);
x_333 = x_173;
goto block_334;
}
else
{
lean_object* x_335; 
x_335 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_335, 0, x_332);
lean_ctor_set(x_335, 1, x_330);
lean_ctor_set(x_335, 2, x_331);
lean_ctor_set(x_335, 3, x_1);
lean_ctor_set(x_335, 4, x_7);
x_333 = x_335;
goto block_334;
}
block_334:
{
return x_333;
}
}
}
}
}
}
}
else
{
return x_1;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_glue_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get(x_3, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 4);
x_15 = lean_nat_dec_lt(x_5, x_10);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_169; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_169 = !lean_is_exclusive(x_3);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_3, 4);
lean_dec(x_170);
x_171 = lean_ctor_get(x_3, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_3, 2);
lean_dec(x_172);
x_173 = lean_ctor_get(x_3, 1);
lean_dec(x_173);
x_174 = lean_ctor_get(x_3, 0);
lean_dec(x_174);
x_16 = x_3;
x_17 = x_169;
goto block_168;
}
else
{
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(x_6, x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_unsigned_to_nat(3u);
x_24 = lean_nat_mul(x_23, x_22);
x_25 = lean_nat_dec_lt(x_24, x_10);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_13);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_26, x_22);
x_28 = lean_nat_add(x_27, x_10);
lean_dec(x_27);
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_4);
lean_ctor_set(x_16, 3, x_19);
lean_ctor_set(x_16, 2, x_21);
lean_ctor_set(x_16, 1, x_20);
lean_ctor_set(x_16, 0, x_28);
x_29 = x_16;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_19);
lean_ctor_set(x_31, 4, x_4);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
else
{
lean_object* x_32; uint8_t x_33; uint8_t x_94; 
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_94 = !lean_is_exclusive(x_4);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_4, 4);
lean_dec(x_95);
x_96 = lean_ctor_get(x_4, 3);
lean_dec(x_96);
x_97 = lean_ctor_get(x_4, 2);
lean_dec(x_97);
x_98 = lean_ctor_get(x_4, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_4, 0);
lean_dec(x_99);
x_32 = x_4;
x_33 = x_94;
goto block_93;
}
else
{
lean_dec(x_4);
x_32 = lean_box(0);
x_33 = x_94;
goto block_93;
}
block_93:
{
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
x_36 = lean_ctor_get(x_13, 2);
x_37 = lean_ctor_get(x_13, 3);
x_38 = lean_ctor_get(x_13, 4);
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_unsigned_to_nat(2u);
x_41 = lean_nat_mul(x_40, x_39);
x_42 = lean_nat_dec_lt(x_34, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; uint8_t x_71; 
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_71 = !lean_is_exclusive(x_13);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_13, 4);
lean_dec(x_72);
x_73 = lean_ctor_get(x_13, 3);
lean_dec(x_73);
x_74 = lean_ctor_get(x_13, 2);
lean_dec(x_74);
x_75 = lean_ctor_get(x_13, 1);
lean_dec(x_75);
x_76 = lean_ctor_get(x_13, 0);
lean_dec(x_76);
x_43 = x_13;
x_44 = x_71;
goto block_70;
}
else
{
lean_dec(x_13);
x_43 = lean_box(0);
x_44 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_59; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_45, x_22);
x_47 = lean_nat_add(x_46, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_37, 0);
lean_inc(x_68);
x_59 = x_68;
goto block_67;
}
else
{
lean_object* x_69; 
x_69 = lean_unsigned_to_nat(0u);
x_59 = x_69;
goto block_67;
}
block_58:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_nat_add(x_48, x_50);
lean_dec(x_50);
lean_dec(x_48);
if (x_44 == 0)
{
lean_ctor_set(x_43, 4, x_14);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_43, 2, x_12);
lean_ctor_set(x_43, 1, x_11);
lean_ctor_set(x_43, 0, x_51);
x_52 = x_43;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_12);
lean_ctor_set(x_57, 3, x_38);
lean_ctor_set(x_57, 4, x_14);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 4, x_52);
lean_ctor_set(x_32, 3, x_49);
lean_ctor_set(x_32, 2, x_36);
lean_ctor_set(x_32, 1, x_35);
lean_ctor_set(x_32, 0, x_47);
x_53 = x_32;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_35);
lean_ctor_set(x_55, 2, x_36);
lean_ctor_set(x_55, 3, x_49);
lean_ctor_set(x_55, 4, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
block_67:
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_nat_add(x_46, x_59);
lean_dec(x_59);
lean_dec(x_46);
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_37);
lean_ctor_set(x_16, 3, x_19);
lean_ctor_set(x_16, 2, x_21);
lean_ctor_set(x_16, 1, x_20);
lean_ctor_set(x_16, 0, x_60);
x_61 = x_16;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_20);
lean_ctor_set(x_66, 2, x_21);
lean_ctor_set(x_66, 3, x_19);
lean_ctor_set(x_66, 4, x_37);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
x_62 = lean_nat_add(x_45, x_39);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
x_48 = x_62;
x_49 = x_61;
x_50 = x_63;
goto block_58;
}
else
{
lean_object* x_64; 
x_64 = lean_unsigned_to_nat(0u);
x_48 = x_62;
x_49 = x_61;
x_50 = x_64;
goto block_58;
}
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_77, x_22);
x_79 = lean_nat_add(x_78, x_10);
lean_dec(x_10);
x_80 = lean_nat_add(x_78, x_34);
lean_dec(x_78);
if (x_33 == 0)
{
lean_ctor_set(x_32, 4, x_13);
lean_ctor_set(x_32, 3, x_19);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set(x_32, 1, x_20);
lean_ctor_set(x_32, 0, x_80);
x_81 = x_32;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_20);
lean_ctor_set(x_86, 2, x_21);
lean_ctor_set(x_86, 3, x_19);
lean_ctor_set(x_86, 4, x_13);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_14);
lean_ctor_set(x_16, 3, x_81);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 0, x_79);
x_82 = x_16;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_11);
lean_ctor_set(x_84, 2, x_12);
lean_ctor_set(x_84, 3, x_81);
lean_ctor_set(x_84, 4, x_14);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_13);
lean_del_object(x_32);
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec(x_20);
lean_del_object(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_87 = lean_box(1);
x_88 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3);
x_89 = l_panic___redArg(x_87, x_88);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_del_object(x_32);
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec(x_20);
lean_del_object(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_90 = lean_box(1);
x_91 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4);
x_92 = l_panic___redArg(x_90, x_91);
return x_92;
}
}
}
}
else
{
lean_inc(x_14);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_100; uint8_t x_101; uint8_t x_137; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_137 = !lean_is_exclusive(x_4);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_4, 4);
lean_dec(x_138);
x_139 = lean_ctor_get(x_4, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_4, 2);
lean_dec(x_140);
x_141 = lean_ctor_get(x_4, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_4, 0);
lean_dec(x_142);
x_100 = x_4;
x_101 = x_137;
goto block_136;
}
else
{
lean_dec(x_4);
x_100 = lean_box(0);
x_101 = x_137;
goto block_136;
}
block_136:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_18, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_18, 1);
lean_inc(x_103);
lean_dec_ref(x_18);
x_104 = lean_ctor_get(x_13, 0);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_105, x_10);
lean_dec(x_10);
x_107 = lean_nat_add(x_105, x_104);
if (x_101 == 0)
{
lean_ctor_set(x_100, 4, x_13);
lean_ctor_set(x_100, 3, x_19);
lean_ctor_set(x_100, 2, x_103);
lean_ctor_set(x_100, 1, x_102);
lean_ctor_set(x_100, 0, x_107);
x_108 = x_100;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_102);
lean_ctor_set(x_113, 2, x_103);
lean_ctor_set(x_113, 3, x_19);
lean_ctor_set(x_113, 4, x_13);
x_108 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_109; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_14);
lean_ctor_set(x_16, 3, x_108);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 0, x_106);
x_109 = x_16;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_11);
lean_ctor_set(x_111, 2, x_12);
lean_ctor_set(x_111, 3, x_108);
lean_ctor_set(x_111, 4, x_14);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_132; 
lean_dec(x_10);
x_114 = lean_ctor_get(x_18, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_18, 1);
lean_inc(x_115);
lean_dec_ref(x_18);
x_116 = lean_ctor_get(x_13, 1);
x_117 = lean_ctor_get(x_13, 2);
x_132 = !lean_is_exclusive(x_13);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_13, 4);
lean_dec(x_133);
x_134 = lean_ctor_get(x_13, 3);
lean_dec(x_134);
x_135 = lean_ctor_get(x_13, 0);
lean_dec(x_135);
x_118 = x_13;
x_119 = x_132;
goto block_131;
}
else
{
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_13);
x_118 = lean_box(0);
x_119 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_unsigned_to_nat(3u);
x_121 = lean_unsigned_to_nat(1u);
if (x_119 == 0)
{
lean_ctor_set(x_118, 4, x_14);
lean_ctor_set(x_118, 3, x_14);
lean_ctor_set(x_118, 2, x_115);
lean_ctor_set(x_118, 1, x_114);
lean_ctor_set(x_118, 0, x_121);
x_122 = x_118;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_130, 0, x_121);
lean_ctor_set(x_130, 1, x_114);
lean_ctor_set(x_130, 2, x_115);
lean_ctor_set(x_130, 3, x_14);
lean_ctor_set(x_130, 4, x_14);
x_122 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_123; 
if (x_101 == 0)
{
lean_ctor_set(x_100, 3, x_14);
lean_ctor_set(x_100, 0, x_121);
x_123 = x_100;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_128, 0, x_121);
lean_ctor_set(x_128, 1, x_11);
lean_ctor_set(x_128, 2, x_12);
lean_ctor_set(x_128, 3, x_14);
lean_ctor_set(x_128, 4, x_14);
x_123 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_124; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_123);
lean_ctor_set(x_16, 3, x_122);
lean_ctor_set(x_16, 2, x_117);
lean_ctor_set(x_16, 1, x_116);
lean_ctor_set(x_16, 0, x_120);
x_124 = x_16;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_120);
lean_ctor_set(x_126, 1, x_116);
lean_ctor_set(x_126, 2, x_117);
lean_ctor_set(x_126, 3, x_122);
lean_ctor_set(x_126, 4, x_123);
x_124 = x_126;
goto block_125;
}
block_125:
{
return x_124;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_143; uint8_t x_144; uint8_t x_156; 
lean_inc(x_12);
lean_inc(x_11);
x_156 = !lean_is_exclusive(x_4);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_4, 4);
lean_dec(x_157);
x_158 = lean_ctor_get(x_4, 3);
lean_dec(x_158);
x_159 = lean_ctor_get(x_4, 2);
lean_dec(x_159);
x_160 = lean_ctor_get(x_4, 1);
lean_dec(x_160);
x_161 = lean_ctor_get(x_4, 0);
lean_dec(x_161);
x_143 = x_4;
x_144 = x_156;
goto block_155;
}
else
{
lean_dec(x_4);
x_143 = lean_box(0);
x_144 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_18, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_18, 1);
lean_inc(x_146);
lean_dec_ref(x_18);
x_147 = lean_unsigned_to_nat(3u);
x_148 = lean_unsigned_to_nat(1u);
if (x_144 == 0)
{
lean_ctor_set(x_143, 4, x_13);
lean_ctor_set(x_143, 2, x_146);
lean_ctor_set(x_143, 1, x_145);
lean_ctor_set(x_143, 0, x_148);
x_149 = x_143;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_145);
lean_ctor_set(x_154, 2, x_146);
lean_ctor_set(x_154, 3, x_13);
lean_ctor_set(x_154, 4, x_13);
x_149 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_150; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_14);
lean_ctor_set(x_16, 3, x_149);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 0, x_147);
x_150 = x_16;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_11);
lean_ctor_set(x_152, 2, x_12);
lean_ctor_set(x_152, 3, x_149);
lean_ctor_set(x_152, 4, x_14);
x_150 = x_152;
goto block_151;
}
block_151:
{
return x_150;
}
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_18, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_18, 1);
lean_inc(x_163);
lean_dec_ref(x_18);
x_164 = lean_unsigned_to_nat(2u);
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_4);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 2, x_163);
lean_ctor_set(x_16, 1, x_162);
lean_ctor_set(x_16, 0, x_164);
x_165 = x_16;
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_162);
lean_ctor_set(x_167, 2, x_163);
lean_ctor_set(x_167, 3, x_14);
lean_ctor_set(x_167, 4, x_4);
x_165 = x_167;
goto block_166;
}
block_166:
{
return x_165;
}
}
}
}
}
}
else
{
lean_object* x_175; uint8_t x_176; uint8_t x_339; 
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
x_339 = !lean_is_exclusive(x_4);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_340 = lean_ctor_get(x_4, 4);
lean_dec(x_340);
x_341 = lean_ctor_get(x_4, 3);
lean_dec(x_341);
x_342 = lean_ctor_get(x_4, 2);
lean_dec(x_342);
x_343 = lean_ctor_get(x_4, 1);
lean_dec(x_343);
x_344 = lean_ctor_get(x_4, 0);
lean_dec(x_344);
x_175 = x_4;
x_176 = x_339;
goto block_338;
}
else
{
lean_dec(x_4);
x_175 = lean_box(0);
x_176 = x_339;
goto block_338;
}
block_338:
{
lean_object* x_177; lean_object* x_178; 
x_177 = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(x_11, x_12, x_13, x_14);
x_178 = lean_ctor_get(x_177, 2);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec_ref(x_177);
x_181 = lean_ctor_get(x_178, 0);
x_182 = lean_unsigned_to_nat(3u);
x_183 = lean_nat_mul(x_182, x_181);
x_184 = lean_nat_dec_lt(x_183, x_5);
lean_dec(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_9);
x_185 = lean_unsigned_to_nat(1u);
x_186 = lean_nat_add(x_185, x_5);
x_187 = lean_nat_add(x_186, x_181);
lean_dec(x_186);
if (x_176 == 0)
{
lean_ctor_set(x_175, 4, x_178);
lean_ctor_set(x_175, 3, x_3);
lean_ctor_set(x_175, 2, x_180);
lean_ctor_set(x_175, 1, x_179);
lean_ctor_set(x_175, 0, x_187);
x_188 = x_175;
goto block_189;
}
else
{
lean_object* x_190; 
x_190 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_179);
lean_ctor_set(x_190, 2, x_180);
lean_ctor_set(x_190, 3, x_3);
lean_ctor_set(x_190, 4, x_178);
x_188 = x_190;
goto block_189;
}
block_189:
{
return x_188;
}
}
else
{
lean_object* x_191; uint8_t x_192; uint8_t x_264; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_264 = !lean_is_exclusive(x_3);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_265 = lean_ctor_get(x_3, 4);
lean_dec(x_265);
x_266 = lean_ctor_get(x_3, 3);
lean_dec(x_266);
x_267 = lean_ctor_get(x_3, 2);
lean_dec(x_267);
x_268 = lean_ctor_get(x_3, 1);
lean_dec(x_268);
x_269 = lean_ctor_get(x_3, 0);
lean_dec(x_269);
x_191 = x_3;
x_192 = x_264;
goto block_263;
}
else
{
lean_dec(x_3);
x_191 = lean_box(0);
x_192 = x_264;
goto block_263;
}
block_263:
{
if (lean_obj_tag(x_8) == 0)
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_193 = lean_ctor_get(x_8, 0);
x_194 = lean_ctor_get(x_9, 0);
x_195 = lean_ctor_get(x_9, 1);
x_196 = lean_ctor_get(x_9, 2);
x_197 = lean_ctor_get(x_9, 3);
x_198 = lean_ctor_get(x_9, 4);
x_199 = lean_unsigned_to_nat(2u);
x_200 = lean_nat_mul(x_199, x_193);
x_201 = lean_nat_dec_lt(x_194, x_200);
lean_dec(x_200);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; uint8_t x_240; 
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_del_object(x_191);
x_240 = !lean_is_exclusive(x_9);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = lean_ctor_get(x_9, 4);
lean_dec(x_241);
x_242 = lean_ctor_get(x_9, 3);
lean_dec(x_242);
x_243 = lean_ctor_get(x_9, 2);
lean_dec(x_243);
x_244 = lean_ctor_get(x_9, 1);
lean_dec(x_244);
x_245 = lean_ctor_get(x_9, 0);
lean_dec(x_245);
x_202 = x_9;
x_203 = x_240;
goto block_239;
}
else
{
lean_dec(x_9);
x_202 = lean_box(0);
x_203 = x_240;
goto block_239;
}
block_239:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_227; lean_object* x_228; 
x_204 = lean_unsigned_to_nat(1u);
x_205 = lean_nat_add(x_204, x_5);
lean_dec(x_5);
x_206 = lean_nat_add(x_205, x_181);
lean_dec(x_205);
x_227 = lean_nat_add(x_204, x_193);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_197, 0);
lean_inc(x_237);
x_228 = x_237;
goto block_236;
}
else
{
lean_object* x_238; 
x_238 = lean_unsigned_to_nat(0u);
x_228 = x_238;
goto block_236;
}
block_226:
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_nat_add(x_208, x_209);
lean_dec(x_209);
lean_dec(x_208);
lean_inc_ref(x_178);
if (x_203 == 0)
{
lean_ctor_set(x_202, 4, x_178);
lean_ctor_set(x_202, 3, x_198);
lean_ctor_set(x_202, 2, x_180);
lean_ctor_set(x_202, 1, x_179);
lean_ctor_set(x_202, 0, x_210);
x_211 = x_202;
goto block_224;
}
else
{
lean_object* x_225; 
x_225 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_225, 0, x_210);
lean_ctor_set(x_225, 1, x_179);
lean_ctor_set(x_225, 2, x_180);
lean_ctor_set(x_225, 3, x_198);
lean_ctor_set(x_225, 4, x_178);
x_211 = x_225;
goto block_224;
}
block_224:
{
lean_object* x_212; uint8_t x_213; uint8_t x_218; 
x_218 = !lean_is_exclusive(x_178);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_219 = lean_ctor_get(x_178, 4);
lean_dec(x_219);
x_220 = lean_ctor_get(x_178, 3);
lean_dec(x_220);
x_221 = lean_ctor_get(x_178, 2);
lean_dec(x_221);
x_222 = lean_ctor_get(x_178, 1);
lean_dec(x_222);
x_223 = lean_ctor_get(x_178, 0);
lean_dec(x_223);
x_212 = x_178;
x_213 = x_218;
goto block_217;
}
else
{
lean_dec(x_178);
x_212 = lean_box(0);
x_213 = x_218;
goto block_217;
}
block_217:
{
lean_object* x_214; 
if (x_213 == 0)
{
lean_ctor_set(x_212, 4, x_211);
lean_ctor_set(x_212, 3, x_207);
lean_ctor_set(x_212, 2, x_196);
lean_ctor_set(x_212, 1, x_195);
lean_ctor_set(x_212, 0, x_206);
x_214 = x_212;
goto block_215;
}
else
{
lean_object* x_216; 
x_216 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_216, 0, x_206);
lean_ctor_set(x_216, 1, x_195);
lean_ctor_set(x_216, 2, x_196);
lean_ctor_set(x_216, 3, x_207);
lean_ctor_set(x_216, 4, x_211);
x_214 = x_216;
goto block_215;
}
block_215:
{
return x_214;
}
}
}
}
block_236:
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_nat_add(x_227, x_228);
lean_dec(x_228);
lean_dec(x_227);
if (x_176 == 0)
{
lean_ctor_set(x_175, 4, x_197);
lean_ctor_set(x_175, 3, x_8);
lean_ctor_set(x_175, 2, x_7);
lean_ctor_set(x_175, 1, x_6);
lean_ctor_set(x_175, 0, x_229);
x_230 = x_175;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_235, 0, x_229);
lean_ctor_set(x_235, 1, x_6);
lean_ctor_set(x_235, 2, x_7);
lean_ctor_set(x_235, 3, x_8);
lean_ctor_set(x_235, 4, x_197);
x_230 = x_235;
goto block_234;
}
block_234:
{
lean_object* x_231; 
x_231 = lean_nat_add(x_204, x_181);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_198, 0);
lean_inc(x_232);
x_207 = x_230;
x_208 = x_231;
x_209 = x_232;
goto block_226;
}
else
{
lean_object* x_233; 
x_233 = lean_unsigned_to_nat(0u);
x_207 = x_230;
x_208 = x_231;
x_209 = x_233;
goto block_226;
}
}
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_246 = lean_unsigned_to_nat(1u);
x_247 = lean_nat_add(x_246, x_5);
lean_dec(x_5);
x_248 = lean_nat_add(x_247, x_181);
lean_dec(x_247);
x_249 = lean_nat_add(x_246, x_181);
x_250 = lean_nat_add(x_249, x_194);
lean_dec(x_249);
if (x_176 == 0)
{
lean_ctor_set(x_175, 4, x_178);
lean_ctor_set(x_175, 3, x_9);
lean_ctor_set(x_175, 2, x_180);
lean_ctor_set(x_175, 1, x_179);
lean_ctor_set(x_175, 0, x_250);
x_251 = x_175;
goto block_255;
}
else
{
lean_object* x_256; 
x_256 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_256, 0, x_250);
lean_ctor_set(x_256, 1, x_179);
lean_ctor_set(x_256, 2, x_180);
lean_ctor_set(x_256, 3, x_9);
lean_ctor_set(x_256, 4, x_178);
x_251 = x_256;
goto block_255;
}
block_255:
{
lean_object* x_252; 
if (x_192 == 0)
{
lean_ctor_set(x_191, 4, x_251);
lean_ctor_set(x_191, 0, x_248);
x_252 = x_191;
goto block_253;
}
else
{
lean_object* x_254; 
x_254 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_254, 0, x_248);
lean_ctor_set(x_254, 1, x_6);
lean_ctor_set(x_254, 2, x_7);
lean_ctor_set(x_254, 3, x_8);
lean_ctor_set(x_254, 4, x_251);
x_252 = x_254;
goto block_253;
}
block_253:
{
return x_252;
}
}
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec_ref(x_8);
lean_del_object(x_191);
lean_dec(x_180);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_del_object(x_175);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_257 = lean_box(1);
x_258 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2);
x_259 = l_panic___redArg(x_257, x_258);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_del_object(x_191);
lean_dec(x_180);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_del_object(x_175);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_260 = lean_box(1);
x_261 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3);
x_262 = l_panic___redArg(x_260, x_261);
return x_262;
}
}
}
}
else
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_270; uint8_t x_271; uint8_t x_295; 
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_295 = !lean_is_exclusive(x_3);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_296 = lean_ctor_get(x_3, 4);
lean_dec(x_296);
x_297 = lean_ctor_get(x_3, 3);
lean_dec(x_297);
x_298 = lean_ctor_get(x_3, 2);
lean_dec(x_298);
x_299 = lean_ctor_get(x_3, 1);
lean_dec(x_299);
x_300 = lean_ctor_get(x_3, 0);
lean_dec(x_300);
x_270 = x_3;
x_271 = x_295;
goto block_294;
}
else
{
lean_dec(x_3);
x_270 = lean_box(0);
x_271 = x_295;
goto block_294;
}
block_294:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_272 = lean_ctor_get(x_177, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_177, 1);
lean_inc(x_273);
lean_dec_ref(x_177);
x_274 = lean_ctor_get(x_9, 0);
x_275 = lean_unsigned_to_nat(1u);
x_276 = lean_nat_add(x_275, x_5);
lean_dec(x_5);
x_277 = lean_nat_add(x_275, x_274);
if (x_176 == 0)
{
lean_ctor_set(x_175, 4, x_178);
lean_ctor_set(x_175, 3, x_9);
lean_ctor_set(x_175, 2, x_273);
lean_ctor_set(x_175, 1, x_272);
lean_ctor_set(x_175, 0, x_277);
x_278 = x_175;
goto block_282;
}
else
{
lean_object* x_283; 
x_283 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_283, 0, x_277);
lean_ctor_set(x_283, 1, x_272);
lean_ctor_set(x_283, 2, x_273);
lean_ctor_set(x_283, 3, x_9);
lean_ctor_set(x_283, 4, x_178);
x_278 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_279; 
if (x_271 == 0)
{
lean_ctor_set(x_270, 4, x_278);
lean_ctor_set(x_270, 0, x_276);
x_279 = x_270;
goto block_280;
}
else
{
lean_object* x_281; 
x_281 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_281, 0, x_276);
lean_ctor_set(x_281, 1, x_6);
lean_ctor_set(x_281, 2, x_7);
lean_ctor_set(x_281, 3, x_8);
lean_ctor_set(x_281, 4, x_278);
x_279 = x_281;
goto block_280;
}
block_280:
{
return x_279;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_5);
x_284 = lean_ctor_get(x_177, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_177, 1);
lean_inc(x_285);
lean_dec_ref(x_177);
x_286 = lean_unsigned_to_nat(3u);
x_287 = lean_unsigned_to_nat(1u);
if (x_176 == 0)
{
lean_ctor_set(x_175, 4, x_9);
lean_ctor_set(x_175, 3, x_9);
lean_ctor_set(x_175, 2, x_285);
lean_ctor_set(x_175, 1, x_284);
lean_ctor_set(x_175, 0, x_287);
x_288 = x_175;
goto block_292;
}
else
{
lean_object* x_293; 
x_293 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_293, 0, x_287);
lean_ctor_set(x_293, 1, x_284);
lean_ctor_set(x_293, 2, x_285);
lean_ctor_set(x_293, 3, x_9);
lean_ctor_set(x_293, 4, x_9);
x_288 = x_293;
goto block_292;
}
block_292:
{
lean_object* x_289; 
if (x_271 == 0)
{
lean_ctor_set(x_270, 4, x_288);
lean_ctor_set(x_270, 0, x_286);
x_289 = x_270;
goto block_290;
}
else
{
lean_object* x_291; 
x_291 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_291, 0, x_286);
lean_ctor_set(x_291, 1, x_6);
lean_ctor_set(x_291, 2, x_7);
lean_ctor_set(x_291, 3, x_8);
lean_ctor_set(x_291, 4, x_288);
x_289 = x_291;
goto block_290;
}
block_290:
{
return x_289;
}
}
}
}
}
else
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_301; uint8_t x_302; uint8_t x_326; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_326 = !lean_is_exclusive(x_3);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_327 = lean_ctor_get(x_3, 4);
lean_dec(x_327);
x_328 = lean_ctor_get(x_3, 3);
lean_dec(x_328);
x_329 = lean_ctor_get(x_3, 2);
lean_dec(x_329);
x_330 = lean_ctor_get(x_3, 1);
lean_dec(x_330);
x_331 = lean_ctor_get(x_3, 0);
lean_dec(x_331);
x_301 = x_3;
x_302 = x_326;
goto block_325;
}
else
{
lean_dec(x_3);
x_301 = lean_box(0);
x_302 = x_326;
goto block_325;
}
block_325:
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; uint8_t x_321; 
x_303 = lean_ctor_get(x_177, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_177, 1);
lean_inc(x_304);
lean_dec_ref(x_177);
x_305 = lean_ctor_get(x_9, 1);
x_306 = lean_ctor_get(x_9, 2);
x_321 = !lean_is_exclusive(x_9);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_9, 4);
lean_dec(x_322);
x_323 = lean_ctor_get(x_9, 3);
lean_dec(x_323);
x_324 = lean_ctor_get(x_9, 0);
lean_dec(x_324);
x_307 = x_9;
x_308 = x_321;
goto block_320;
}
else
{
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_9);
x_307 = lean_box(0);
x_308 = x_321;
goto block_320;
}
block_320:
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_unsigned_to_nat(3u);
x_310 = lean_unsigned_to_nat(1u);
if (x_308 == 0)
{
lean_ctor_set(x_307, 4, x_8);
lean_ctor_set(x_307, 3, x_8);
lean_ctor_set(x_307, 2, x_7);
lean_ctor_set(x_307, 1, x_6);
lean_ctor_set(x_307, 0, x_310);
x_311 = x_307;
goto block_318;
}
else
{
lean_object* x_319; 
x_319 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_319, 0, x_310);
lean_ctor_set(x_319, 1, x_6);
lean_ctor_set(x_319, 2, x_7);
lean_ctor_set(x_319, 3, x_8);
lean_ctor_set(x_319, 4, x_8);
x_311 = x_319;
goto block_318;
}
block_318:
{
lean_object* x_312; 
if (x_176 == 0)
{
lean_ctor_set(x_175, 4, x_8);
lean_ctor_set(x_175, 3, x_8);
lean_ctor_set(x_175, 2, x_304);
lean_ctor_set(x_175, 1, x_303);
lean_ctor_set(x_175, 0, x_310);
x_312 = x_175;
goto block_316;
}
else
{
lean_object* x_317; 
x_317 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_317, 0, x_310);
lean_ctor_set(x_317, 1, x_303);
lean_ctor_set(x_317, 2, x_304);
lean_ctor_set(x_317, 3, x_8);
lean_ctor_set(x_317, 4, x_8);
x_312 = x_317;
goto block_316;
}
block_316:
{
lean_object* x_313; 
if (x_302 == 0)
{
lean_ctor_set(x_301, 4, x_312);
lean_ctor_set(x_301, 3, x_311);
lean_ctor_set(x_301, 2, x_306);
lean_ctor_set(x_301, 1, x_305);
lean_ctor_set(x_301, 0, x_309);
x_313 = x_301;
goto block_314;
}
else
{
lean_object* x_315; 
x_315 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_315, 0, x_309);
lean_ctor_set(x_315, 1, x_305);
lean_ctor_set(x_315, 2, x_306);
lean_ctor_set(x_315, 3, x_311);
lean_ctor_set(x_315, 4, x_312);
x_313 = x_315;
goto block_314;
}
block_314:
{
return x_313;
}
}
}
}
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = lean_ctor_get(x_177, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_177, 1);
lean_inc(x_333);
lean_dec_ref(x_177);
x_334 = lean_unsigned_to_nat(2u);
if (x_176 == 0)
{
lean_ctor_set(x_175, 4, x_9);
lean_ctor_set(x_175, 3, x_3);
lean_ctor_set(x_175, 2, x_333);
lean_ctor_set(x_175, 1, x_332);
lean_ctor_set(x_175, 0, x_334);
x_335 = x_175;
goto block_336;
}
else
{
lean_object* x_337; 
x_337 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_337, 0, x_334);
lean_ctor_set(x_337, 1, x_332);
lean_ctor_set(x_337, 2, x_333);
lean_ctor_set(x_337, 3, x_3);
lean_ctor_set(x_337, 4, x_9);
x_335 = x_337;
goto block_336;
}
block_336:
{
return x_335;
}
}
}
}
}
}
}
else
{
return x_3;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMin___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_148; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_ctor_get(x_3, 3);
x_7 = lean_ctor_get(x_3, 4);
x_148 = !lean_is_exclusive(x_3);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_3, 0);
lean_dec(x_149);
x_8 = x_3;
x_9 = x_148;
goto block_147;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DTreeMap_Internal_Impl_insertMin___redArg(x_1, x_2, x_6);
x_11 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 4);
lean_inc(x_17);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_mul(x_18, x_12);
x_20 = lean_nat_dec_lt(x_19, x_13);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_21 = lean_nat_add(x_11, x_13);
lean_dec(x_13);
x_22 = lean_nat_add(x_21, x_12);
lean_dec(x_21);
if (x_9 == 0)
{
lean_ctor_set(x_8, 3, x_10);
lean_ctor_set(x_8, 0, x_22);
x_23 = x_8;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_5);
lean_ctor_set(x_25, 3, x_10);
lean_ctor_set(x_25, 4, x_7);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
else
{
lean_object* x_26; uint8_t x_27; uint8_t x_91; 
x_91 = !lean_is_exclusive(x_10);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_10, 4);
lean_dec(x_92);
x_93 = lean_ctor_get(x_10, 3);
lean_dec(x_93);
x_94 = lean_ctor_get(x_10, 2);
lean_dec(x_94);
x_95 = lean_ctor_get(x_10, 1);
lean_dec(x_95);
x_96 = lean_ctor_get(x_10, 0);
lean_dec(x_96);
x_26 = x_10;
x_27 = x_91;
goto block_90;
}
else
{
lean_dec(x_10);
x_26 = lean_box(0);
x_27 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
x_31 = lean_ctor_get(x_17, 2);
x_32 = lean_ctor_get(x_17, 3);
x_33 = lean_ctor_get(x_17, 4);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_mul(x_34, x_28);
x_36 = lean_nat_dec_lt(x_29, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; uint8_t x_65; 
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
x_65 = !lean_is_exclusive(x_17);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_17, 4);
lean_dec(x_66);
x_67 = lean_ctor_get(x_17, 3);
lean_dec(x_67);
x_68 = lean_ctor_get(x_17, 2);
lean_dec(x_68);
x_69 = lean_ctor_get(x_17, 1);
lean_dec(x_69);
x_70 = lean_ctor_get(x_17, 0);
lean_dec(x_70);
x_37 = x_17;
x_38 = x_65;
goto block_64;
}
else
{
lean_dec(x_17);
x_37 = lean_box(0);
x_38 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_52; lean_object* x_53; 
x_39 = lean_nat_add(x_11, x_13);
lean_dec(x_13);
x_40 = lean_nat_add(x_39, x_12);
lean_dec(x_39);
x_52 = lean_nat_add(x_11, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_32, 0);
lean_inc(x_62);
x_53 = x_62;
goto block_61;
}
else
{
lean_object* x_63; 
x_63 = lean_unsigned_to_nat(0u);
x_53 = x_63;
goto block_61;
}
block_51:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_nat_add(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_38 == 0)
{
lean_ctor_set(x_37, 4, x_7);
lean_ctor_set(x_37, 3, x_33);
lean_ctor_set(x_37, 2, x_5);
lean_ctor_set(x_37, 1, x_4);
lean_ctor_set(x_37, 0, x_44);
x_45 = x_37;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_4);
lean_ctor_set(x_50, 2, x_5);
lean_ctor_set(x_50, 3, x_33);
lean_ctor_set(x_50, 4, x_7);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_45);
lean_ctor_set(x_26, 3, x_41);
lean_ctor_set(x_26, 2, x_31);
lean_ctor_set(x_26, 1, x_30);
lean_ctor_set(x_26, 0, x_40);
x_46 = x_26;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_30);
lean_ctor_set(x_48, 2, x_31);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set(x_48, 4, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
block_61:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_nat_add(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_32);
lean_ctor_set(x_8, 3, x_16);
lean_ctor_set(x_8, 2, x_15);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_54);
x_55 = x_8;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_14);
lean_ctor_set(x_60, 2, x_15);
lean_ctor_set(x_60, 3, x_16);
lean_ctor_set(x_60, 4, x_32);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
x_56 = lean_nat_add(x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_33, 0);
lean_inc(x_57);
x_41 = x_55;
x_42 = x_56;
x_43 = x_57;
goto block_51;
}
else
{
lean_object* x_58; 
x_58 = lean_unsigned_to_nat(0u);
x_41 = x_55;
x_42 = x_56;
x_43 = x_58;
goto block_51;
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_del_object(x_8);
x_71 = lean_nat_add(x_11, x_13);
lean_dec(x_13);
x_72 = lean_nat_add(x_71, x_12);
lean_dec(x_71);
x_73 = lean_nat_add(x_11, x_12);
x_74 = lean_nat_add(x_73, x_29);
lean_dec(x_73);
lean_inc_ref(x_7);
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_7);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 2, x_5);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 0, x_74);
x_75 = x_26;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_4);
lean_ctor_set(x_89, 2, x_5);
lean_ctor_set(x_89, 3, x_17);
lean_ctor_set(x_89, 4, x_7);
x_75 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_76; uint8_t x_77; uint8_t x_82; 
x_82 = !lean_is_exclusive(x_7);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_7, 4);
lean_dec(x_83);
x_84 = lean_ctor_get(x_7, 3);
lean_dec(x_84);
x_85 = lean_ctor_get(x_7, 2);
lean_dec(x_85);
x_86 = lean_ctor_get(x_7, 1);
lean_dec(x_86);
x_87 = lean_ctor_get(x_7, 0);
lean_dec(x_87);
x_76 = x_7;
x_77 = x_82;
goto block_81;
}
else
{
lean_dec(x_7);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
lean_ctor_set(x_76, 4, x_75);
lean_ctor_set(x_76, 3, x_16);
lean_ctor_set(x_76, 2, x_15);
lean_ctor_set(x_76, 1, x_14);
lean_ctor_set(x_76, 0, x_72);
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_14);
lean_ctor_set(x_80, 2, x_15);
lean_ctor_set(x_80, 3, x_16);
lean_ctor_set(x_80, 4, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
}
}
else
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_10, 3);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_111; 
x_98 = lean_ctor_get(x_10, 4);
x_99 = lean_ctor_get(x_10, 1);
x_100 = lean_ctor_get(x_10, 2);
x_111 = !lean_is_exclusive(x_10);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_10, 3);
lean_dec(x_112);
x_113 = lean_ctor_get(x_10, 0);
lean_dec(x_113);
x_101 = x_10;
x_102 = x_111;
goto block_110;
}
else
{
lean_inc(x_98);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_10);
x_101 = lean_box(0);
x_102 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_unsigned_to_nat(3u);
lean_inc(x_98);
if (x_102 == 0)
{
lean_ctor_set(x_101, 3, x_98);
lean_ctor_set(x_101, 2, x_5);
lean_ctor_set(x_101, 1, x_4);
lean_ctor_set(x_101, 0, x_11);
x_104 = x_101;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_11);
lean_ctor_set(x_109, 1, x_4);
lean_ctor_set(x_109, 2, x_5);
lean_ctor_set(x_109, 3, x_98);
lean_ctor_set(x_109, 4, x_98);
x_104 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_105; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_104);
lean_ctor_set(x_8, 3, x_97);
lean_ctor_set(x_8, 2, x_100);
lean_ctor_set(x_8, 1, x_99);
lean_ctor_set(x_8, 0, x_103);
x_105 = x_8;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_99);
lean_ctor_set(x_107, 2, x_100);
lean_ctor_set(x_107, 3, x_97);
lean_ctor_set(x_107, 4, x_104);
x_105 = x_107;
goto block_106;
}
block_106:
{
return x_105;
}
}
}
}
else
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_10, 4);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_139; 
x_115 = lean_ctor_get(x_10, 1);
x_116 = lean_ctor_get(x_10, 2);
x_139 = !lean_is_exclusive(x_10);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_10, 4);
lean_dec(x_140);
x_141 = lean_ctor_get(x_10, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_10, 0);
lean_dec(x_142);
x_117 = x_10;
x_118 = x_139;
goto block_138;
}
else
{
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_10);
x_117 = lean_box(0);
x_118 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_134; 
x_119 = lean_ctor_get(x_114, 1);
x_120 = lean_ctor_get(x_114, 2);
x_134 = !lean_is_exclusive(x_114);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_114, 4);
lean_dec(x_135);
x_136 = lean_ctor_get(x_114, 3);
lean_dec(x_136);
x_137 = lean_ctor_get(x_114, 0);
lean_dec(x_137);
x_121 = x_114;
x_122 = x_134;
goto block_133;
}
else
{
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_114);
x_121 = lean_box(0);
x_122 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_unsigned_to_nat(3u);
if (x_122 == 0)
{
lean_ctor_set(x_121, 4, x_97);
lean_ctor_set(x_121, 3, x_97);
lean_ctor_set(x_121, 2, x_116);
lean_ctor_set(x_121, 1, x_115);
lean_ctor_set(x_121, 0, x_11);
x_124 = x_121;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_11);
lean_ctor_set(x_132, 1, x_115);
lean_ctor_set(x_132, 2, x_116);
lean_ctor_set(x_132, 3, x_97);
lean_ctor_set(x_132, 4, x_97);
x_124 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_125; 
if (x_118 == 0)
{
lean_ctor_set(x_117, 4, x_97);
lean_ctor_set(x_117, 2, x_5);
lean_ctor_set(x_117, 1, x_4);
lean_ctor_set(x_117, 0, x_11);
x_125 = x_117;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_130, 0, x_11);
lean_ctor_set(x_130, 1, x_4);
lean_ctor_set(x_130, 2, x_5);
lean_ctor_set(x_130, 3, x_97);
lean_ctor_set(x_130, 4, x_97);
x_125 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_126; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_125);
lean_ctor_set(x_8, 3, x_124);
lean_ctor_set(x_8, 2, x_120);
lean_ctor_set(x_8, 1, x_119);
lean_ctor_set(x_8, 0, x_123);
x_126 = x_8;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_128, 0, x_123);
lean_ctor_set(x_128, 1, x_119);
lean_ctor_set(x_128, 2, x_120);
lean_ctor_set(x_128, 3, x_124);
lean_ctor_set(x_128, 4, x_125);
x_126 = x_128;
goto block_127;
}
block_127:
{
return x_126;
}
}
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_unsigned_to_nat(2u);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_114);
lean_ctor_set(x_8, 3, x_10);
lean_ctor_set(x_8, 0, x_143);
x_144 = x_8;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_4);
lean_ctor_set(x_146, 2, x_5);
lean_ctor_set(x_146, 3, x_10);
lean_ctor_set(x_146, 4, x_114);
x_144 = x_146;
goto block_145;
}
block_145:
{
return x_144;
}
}
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_unsigned_to_nat(1u);
x_151 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_1);
lean_ctor_set(x_151, 2, x_2);
lean_ctor_set(x_151, 3, x_3);
lean_ctor_set(x_151, 4, x_3);
return x_151;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_insertMin___redArg(x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMin_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_186; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_ctor_get(x_3, 3);
x_7 = lean_ctor_get(x_3, 4);
x_186 = !lean_is_exclusive(x_3);
if (x_186 == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_3, 0);
lean_dec(x_187);
x_8 = x_3;
x_9 = x_186;
goto block_185;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_186;
goto block_185;
}
block_185:
{
lean_object* x_10; 
x_10 = l_Std_DTreeMap_Internal_Impl_insertMin_x21___redArg(x_1, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 4);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(3u);
x_18 = lean_nat_mul(x_17, x_11);
x_19 = lean_nat_dec_lt(x_18, x_12);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_20, x_12);
lean_dec(x_12);
x_22 = lean_nat_add(x_21, x_11);
lean_dec(x_21);
if (x_9 == 0)
{
lean_ctor_set(x_8, 3, x_10);
lean_ctor_set(x_8, 0, x_22);
x_23 = x_8;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_5);
lean_ctor_set(x_25, 3, x_10);
lean_ctor_set(x_25, 4, x_7);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
else
{
lean_object* x_26; uint8_t x_27; uint8_t x_97; 
x_97 = !lean_is_exclusive(x_10);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_10, 4);
lean_dec(x_98);
x_99 = lean_ctor_get(x_10, 3);
lean_dec(x_99);
x_100 = lean_ctor_get(x_10, 2);
lean_dec(x_100);
x_101 = lean_ctor_get(x_10, 1);
lean_dec(x_101);
x_102 = lean_ctor_get(x_10, 0);
lean_dec(x_102);
x_26 = x_10;
x_27 = x_97;
goto block_96;
}
else
{
lean_dec(x_10);
x_26 = lean_box(0);
x_27 = x_97;
goto block_96;
}
block_96:
{
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
x_31 = lean_ctor_get(x_16, 2);
x_32 = lean_ctor_get(x_16, 3);
x_33 = lean_ctor_get(x_16, 4);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_mul(x_34, x_28);
x_36 = lean_nat_dec_lt(x_29, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; uint8_t x_66; 
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
x_66 = !lean_is_exclusive(x_16);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_16, 4);
lean_dec(x_67);
x_68 = lean_ctor_get(x_16, 3);
lean_dec(x_68);
x_69 = lean_ctor_get(x_16, 2);
lean_dec(x_69);
x_70 = lean_ctor_get(x_16, 1);
lean_dec(x_70);
x_71 = lean_ctor_get(x_16, 0);
lean_dec(x_71);
x_37 = x_16;
x_38 = x_66;
goto block_65;
}
else
{
lean_dec(x_16);
x_37 = lean_box(0);
x_38 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_53; lean_object* x_54; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_39, x_12);
lean_dec(x_12);
x_41 = lean_nat_add(x_40, x_11);
lean_dec(x_40);
x_53 = lean_nat_add(x_39, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_32, 0);
lean_inc(x_63);
x_54 = x_63;
goto block_62;
}
else
{
lean_object* x_64; 
x_64 = lean_unsigned_to_nat(0u);
x_54 = x_64;
goto block_62;
}
block_52:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_nat_add(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_38 == 0)
{
lean_ctor_set(x_37, 4, x_7);
lean_ctor_set(x_37, 3, x_33);
lean_ctor_set(x_37, 2, x_5);
lean_ctor_set(x_37, 1, x_4);
lean_ctor_set(x_37, 0, x_45);
x_46 = x_37;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_4);
lean_ctor_set(x_51, 2, x_5);
lean_ctor_set(x_51, 3, x_33);
lean_ctor_set(x_51, 4, x_7);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_46);
lean_ctor_set(x_26, 3, x_42);
lean_ctor_set(x_26, 2, x_31);
lean_ctor_set(x_26, 1, x_30);
lean_ctor_set(x_26, 0, x_41);
x_47 = x_26;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_30);
lean_ctor_set(x_49, 2, x_31);
lean_ctor_set(x_49, 3, x_42);
lean_ctor_set(x_49, 4, x_46);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
block_62:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_nat_add(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_32);
lean_ctor_set(x_8, 3, x_15);
lean_ctor_set(x_8, 2, x_14);
lean_ctor_set(x_8, 1, x_13);
lean_ctor_set(x_8, 0, x_55);
x_56 = x_8;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_13);
lean_ctor_set(x_61, 2, x_14);
lean_ctor_set(x_61, 3, x_15);
lean_ctor_set(x_61, 4, x_32);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
x_57 = lean_nat_add(x_39, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_33, 0);
lean_inc(x_58);
x_42 = x_56;
x_43 = x_57;
x_44 = x_58;
goto block_52;
}
else
{
lean_object* x_59; 
x_59 = lean_unsigned_to_nat(0u);
x_42 = x_56;
x_43 = x_57;
x_44 = x_59;
goto block_52;
}
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_del_object(x_8);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_add(x_72, x_12);
lean_dec(x_12);
x_74 = lean_nat_add(x_73, x_11);
lean_dec(x_73);
x_75 = lean_nat_add(x_72, x_11);
x_76 = lean_nat_add(x_75, x_29);
lean_dec(x_75);
lean_inc_ref(x_7);
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_7);
lean_ctor_set(x_26, 3, x_16);
lean_ctor_set(x_26, 2, x_5);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 0, x_76);
x_77 = x_26;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_91, 0, x_76);
lean_ctor_set(x_91, 1, x_4);
lean_ctor_set(x_91, 2, x_5);
lean_ctor_set(x_91, 3, x_16);
lean_ctor_set(x_91, 4, x_7);
x_77 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_78; uint8_t x_79; uint8_t x_84; 
x_84 = !lean_is_exclusive(x_7);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_7, 4);
lean_dec(x_85);
x_86 = lean_ctor_get(x_7, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_7, 2);
lean_dec(x_87);
x_88 = lean_ctor_get(x_7, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_7, 0);
lean_dec(x_89);
x_78 = x_7;
x_79 = x_84;
goto block_83;
}
else
{
lean_dec(x_7);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
lean_ctor_set(x_78, 4, x_77);
lean_ctor_set(x_78, 3, x_15);
lean_ctor_set(x_78, 2, x_14);
lean_ctor_set(x_78, 1, x_13);
lean_ctor_set(x_78, 0, x_74);
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_74);
lean_ctor_set(x_82, 1, x_13);
lean_ctor_set(x_82, 2, x_14);
lean_ctor_set(x_82, 3, x_15);
lean_ctor_set(x_82, 4, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_15);
lean_del_object(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_del_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_92 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2);
x_93 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_92);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_del_object(x_26);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_del_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_94 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3);
x_95 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_94);
return x_95;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_7, 0);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_add(x_104, x_103);
if (x_9 == 0)
{
lean_ctor_set(x_8, 3, x_10);
lean_ctor_set(x_8, 0, x_105);
x_106 = x_8;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_4);
lean_ctor_set(x_108, 2, x_5);
lean_ctor_set(x_108, 3, x_10);
lean_ctor_set(x_108, 4, x_7);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
else
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_10, 3);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_10, 4);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_127; 
x_111 = lean_ctor_get(x_10, 0);
x_112 = lean_ctor_get(x_10, 1);
x_113 = lean_ctor_get(x_10, 2);
x_127 = !lean_is_exclusive(x_10);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_10, 4);
lean_dec(x_128);
x_129 = lean_ctor_get(x_10, 3);
lean_dec(x_129);
x_114 = x_10;
x_115 = x_127;
goto block_126;
}
else
{
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_10);
x_114 = lean_box(0);
x_115 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_110, 0);
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_nat_add(x_117, x_111);
lean_dec(x_111);
x_119 = lean_nat_add(x_117, x_116);
if (x_115 == 0)
{
lean_ctor_set(x_114, 4, x_7);
lean_ctor_set(x_114, 3, x_110);
lean_ctor_set(x_114, 2, x_5);
lean_ctor_set(x_114, 1, x_4);
lean_ctor_set(x_114, 0, x_119);
x_120 = x_114;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_125, 0, x_119);
lean_ctor_set(x_125, 1, x_4);
lean_ctor_set(x_125, 2, x_5);
lean_ctor_set(x_125, 3, x_110);
lean_ctor_set(x_125, 4, x_7);
x_120 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_121; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_120);
lean_ctor_set(x_8, 3, x_109);
lean_ctor_set(x_8, 2, x_113);
lean_ctor_set(x_8, 1, x_112);
lean_ctor_set(x_8, 0, x_118);
x_121 = x_8;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_123, 0, x_118);
lean_ctor_set(x_123, 1, x_112);
lean_ctor_set(x_123, 2, x_113);
lean_ctor_set(x_123, 3, x_109);
lean_ctor_set(x_123, 4, x_120);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_143; 
x_130 = lean_ctor_get(x_10, 1);
x_131 = lean_ctor_get(x_10, 2);
x_143 = !lean_is_exclusive(x_10);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_10, 4);
lean_dec(x_144);
x_145 = lean_ctor_get(x_10, 3);
lean_dec(x_145);
x_146 = lean_ctor_get(x_10, 0);
lean_dec(x_146);
x_132 = x_10;
x_133 = x_143;
goto block_142;
}
else
{
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_10);
x_132 = lean_box(0);
x_133 = x_143;
goto block_142;
}
block_142:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_unsigned_to_nat(3u);
x_135 = lean_unsigned_to_nat(1u);
if (x_133 == 0)
{
lean_ctor_set(x_132, 3, x_110);
lean_ctor_set(x_132, 2, x_5);
lean_ctor_set(x_132, 1, x_4);
lean_ctor_set(x_132, 0, x_135);
x_136 = x_132;
goto block_140;
}
else
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set(x_141, 1, x_4);
lean_ctor_set(x_141, 2, x_5);
lean_ctor_set(x_141, 3, x_110);
lean_ctor_set(x_141, 4, x_110);
x_136 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_137; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_136);
lean_ctor_set(x_8, 3, x_109);
lean_ctor_set(x_8, 2, x_131);
lean_ctor_set(x_8, 1, x_130);
lean_ctor_set(x_8, 0, x_134);
x_137 = x_8;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_139, 0, x_134);
lean_ctor_set(x_139, 1, x_130);
lean_ctor_set(x_139, 2, x_131);
lean_ctor_set(x_139, 3, x_109);
lean_ctor_set(x_139, 4, x_136);
x_137 = x_139;
goto block_138;
}
block_138:
{
return x_137;
}
}
}
}
}
else
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_10, 4);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_173; 
x_148 = lean_ctor_get(x_10, 1);
x_149 = lean_ctor_get(x_10, 2);
x_173 = !lean_is_exclusive(x_10);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_10, 4);
lean_dec(x_174);
x_175 = lean_ctor_get(x_10, 3);
lean_dec(x_175);
x_176 = lean_ctor_get(x_10, 0);
lean_dec(x_176);
x_150 = x_10;
x_151 = x_173;
goto block_172;
}
else
{
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_10);
x_150 = lean_box(0);
x_151 = x_173;
goto block_172;
}
block_172:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_168; 
x_152 = lean_ctor_get(x_147, 1);
x_153 = lean_ctor_get(x_147, 2);
x_168 = !lean_is_exclusive(x_147);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_147, 4);
lean_dec(x_169);
x_170 = lean_ctor_get(x_147, 3);
lean_dec(x_170);
x_171 = lean_ctor_get(x_147, 0);
lean_dec(x_171);
x_154 = x_147;
x_155 = x_168;
goto block_167;
}
else
{
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_147);
x_154 = lean_box(0);
x_155 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_unsigned_to_nat(3u);
x_157 = lean_unsigned_to_nat(1u);
if (x_155 == 0)
{
lean_ctor_set(x_154, 4, x_109);
lean_ctor_set(x_154, 3, x_109);
lean_ctor_set(x_154, 2, x_149);
lean_ctor_set(x_154, 1, x_148);
lean_ctor_set(x_154, 0, x_157);
x_158 = x_154;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_166, 0, x_157);
lean_ctor_set(x_166, 1, x_148);
lean_ctor_set(x_166, 2, x_149);
lean_ctor_set(x_166, 3, x_109);
lean_ctor_set(x_166, 4, x_109);
x_158 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_159; 
if (x_151 == 0)
{
lean_ctor_set(x_150, 4, x_109);
lean_ctor_set(x_150, 2, x_5);
lean_ctor_set(x_150, 1, x_4);
lean_ctor_set(x_150, 0, x_157);
x_159 = x_150;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_4);
lean_ctor_set(x_164, 2, x_5);
lean_ctor_set(x_164, 3, x_109);
lean_ctor_set(x_164, 4, x_109);
x_159 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_160; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_159);
lean_ctor_set(x_8, 3, x_158);
lean_ctor_set(x_8, 2, x_153);
lean_ctor_set(x_8, 1, x_152);
lean_ctor_set(x_8, 0, x_156);
x_160 = x_8;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_162, 0, x_156);
lean_ctor_set(x_162, 1, x_152);
lean_ctor_set(x_162, 2, x_153);
lean_ctor_set(x_162, 3, x_158);
lean_ctor_set(x_162, 4, x_159);
x_160 = x_162;
goto block_161;
}
block_161:
{
return x_160;
}
}
}
}
}
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_unsigned_to_nat(2u);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_147);
lean_ctor_set(x_8, 3, x_10);
lean_ctor_set(x_8, 0, x_177);
x_178 = x_8;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_4);
lean_ctor_set(x_180, 2, x_5);
lean_ctor_set(x_180, 3, x_10);
lean_ctor_set(x_180, 4, x_147);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_unsigned_to_nat(1u);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_10);
lean_ctor_set(x_8, 3, x_10);
lean_ctor_set(x_8, 0, x_181);
x_182 = x_8;
goto block_183;
}
else
{
lean_object* x_184; 
x_184 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_4);
lean_ctor_set(x_184, 2, x_5);
lean_ctor_set(x_184, 3, x_10);
lean_ctor_set(x_184, 4, x_10);
x_182 = x_184;
goto block_183;
}
block_183:
{
return x_182;
}
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_unsigned_to_nat(1u);
x_189 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_1);
lean_ctor_set(x_189, 2, x_2);
lean_ctor_set(x_189, 3, x_3);
lean_ctor_set(x_189, 4, x_3);
return x_189;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMin_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insertMin_x21___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMax___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_146; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_ctor_get(x_3, 3);
x_7 = lean_ctor_get(x_3, 4);
x_146 = !lean_is_exclusive(x_3);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_3, 0);
lean_dec(x_147);
x_8 = x_3;
x_9 = x_146;
goto block_145;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DTreeMap_Internal_Impl_insertMax___redArg(x_1, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 4);
lean_inc(x_17);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_mul(x_18, x_12);
x_20 = lean_nat_dec_lt(x_19, x_13);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_21 = lean_nat_add(x_11, x_12);
x_22 = lean_nat_add(x_21, x_13);
lean_dec(x_13);
lean_dec(x_21);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_10);
lean_ctor_set(x_8, 0, x_22);
x_23 = x_8;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_5);
lean_ctor_set(x_25, 3, x_6);
lean_ctor_set(x_25, 4, x_10);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
else
{
lean_object* x_26; uint8_t x_27; uint8_t x_89; 
x_89 = !lean_is_exclusive(x_10);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_10, 4);
lean_dec(x_90);
x_91 = lean_ctor_get(x_10, 3);
lean_dec(x_91);
x_92 = lean_ctor_get(x_10, 2);
lean_dec(x_92);
x_93 = lean_ctor_get(x_10, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_10, 0);
lean_dec(x_94);
x_26 = x_10;
x_27 = x_89;
goto block_88;
}
else
{
lean_dec(x_10);
x_26 = lean_box(0);
x_27 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
x_30 = lean_ctor_get(x_16, 2);
x_31 = lean_ctor_get(x_16, 3);
x_32 = lean_ctor_get(x_16, 4);
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_mul(x_34, x_33);
x_36 = lean_nat_dec_lt(x_28, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; uint8_t x_64; 
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_64 = !lean_is_exclusive(x_16);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_16, 4);
lean_dec(x_65);
x_66 = lean_ctor_get(x_16, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_16, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_16, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_16, 0);
lean_dec(x_69);
x_37 = x_16;
x_38 = x_64;
goto block_63;
}
else
{
lean_dec(x_16);
x_37 = lean_box(0);
x_38 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_52; 
x_39 = lean_nat_add(x_11, x_12);
x_40 = lean_nat_add(x_39, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_31, 0);
lean_inc(x_61);
x_52 = x_61;
goto block_60;
}
else
{
lean_object* x_62; 
x_62 = lean_unsigned_to_nat(0u);
x_52 = x_62;
goto block_60;
}
block_51:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_nat_add(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_38 == 0)
{
lean_ctor_set(x_37, 4, x_17);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 2, x_15);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 0, x_44);
x_45 = x_37;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_14);
lean_ctor_set(x_50, 2, x_15);
lean_ctor_set(x_50, 3, x_32);
lean_ctor_set(x_50, 4, x_17);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_45);
lean_ctor_set(x_26, 3, x_41);
lean_ctor_set(x_26, 2, x_30);
lean_ctor_set(x_26, 1, x_29);
lean_ctor_set(x_26, 0, x_40);
x_46 = x_26;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_29);
lean_ctor_set(x_48, 2, x_30);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set(x_48, 4, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
block_60:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_nat_add(x_39, x_52);
lean_dec(x_52);
lean_dec(x_39);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_31);
lean_ctor_set(x_8, 0, x_53);
x_54 = x_8;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_4);
lean_ctor_set(x_59, 2, x_5);
lean_ctor_set(x_59, 3, x_6);
lean_ctor_set(x_59, 4, x_31);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
x_55 = lean_nat_add(x_11, x_33);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_32, 0);
lean_inc(x_56);
x_41 = x_54;
x_42 = x_55;
x_43 = x_56;
goto block_51;
}
else
{
lean_object* x_57; 
x_57 = lean_unsigned_to_nat(0u);
x_41 = x_54;
x_42 = x_55;
x_43 = x_57;
goto block_51;
}
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_del_object(x_8);
x_70 = lean_nat_add(x_11, x_12);
x_71 = lean_nat_add(x_70, x_13);
lean_dec(x_13);
x_72 = lean_nat_add(x_70, x_28);
lean_dec(x_70);
lean_inc_ref(x_6);
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_16);
lean_ctor_set(x_26, 3, x_6);
lean_ctor_set(x_26, 2, x_5);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 0, x_72);
x_73 = x_26;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_4);
lean_ctor_set(x_87, 2, x_5);
lean_ctor_set(x_87, 3, x_6);
lean_ctor_set(x_87, 4, x_16);
x_73 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_74; uint8_t x_75; uint8_t x_80; 
x_80 = !lean_is_exclusive(x_6);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_6, 4);
lean_dec(x_81);
x_82 = lean_ctor_get(x_6, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_6, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_6, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_6, 0);
lean_dec(x_85);
x_74 = x_6;
x_75 = x_80;
goto block_79;
}
else
{
lean_dec(x_6);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
lean_ctor_set(x_74, 4, x_17);
lean_ctor_set(x_74, 3, x_73);
lean_ctor_set(x_74, 2, x_15);
lean_ctor_set(x_74, 1, x_14);
lean_ctor_set(x_74, 0, x_71);
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_14);
lean_ctor_set(x_78, 2, x_15);
lean_ctor_set(x_78, 3, x_73);
lean_ctor_set(x_78, 4, x_17);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
}
}
else
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_10, 3);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_121; 
x_96 = lean_ctor_get(x_10, 4);
x_97 = lean_ctor_get(x_10, 1);
x_98 = lean_ctor_get(x_10, 2);
x_121 = !lean_is_exclusive(x_10);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_10, 3);
lean_dec(x_122);
x_123 = lean_ctor_get(x_10, 0);
lean_dec(x_123);
x_99 = x_10;
x_100 = x_121;
goto block_120;
}
else
{
lean_inc(x_96);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_10);
x_99 = lean_box(0);
x_100 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_116; 
x_101 = lean_ctor_get(x_95, 1);
x_102 = lean_ctor_get(x_95, 2);
x_116 = !lean_is_exclusive(x_95);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_95, 4);
lean_dec(x_117);
x_118 = lean_ctor_get(x_95, 3);
lean_dec(x_118);
x_119 = lean_ctor_get(x_95, 0);
lean_dec(x_119);
x_103 = x_95;
x_104 = x_116;
goto block_115;
}
else
{
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_95);
x_103 = lean_box(0);
x_104 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_unsigned_to_nat(3u);
lean_inc_n(x_96, 2);
if (x_104 == 0)
{
lean_ctor_set(x_103, 4, x_96);
lean_ctor_set(x_103, 3, x_96);
lean_ctor_set(x_103, 2, x_5);
lean_ctor_set(x_103, 1, x_4);
lean_ctor_set(x_103, 0, x_11);
x_106 = x_103;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_114, 0, x_11);
lean_ctor_set(x_114, 1, x_4);
lean_ctor_set(x_114, 2, x_5);
lean_ctor_set(x_114, 3, x_96);
lean_ctor_set(x_114, 4, x_96);
x_106 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_107; 
lean_inc(x_96);
if (x_100 == 0)
{
lean_ctor_set(x_99, 3, x_96);
lean_ctor_set(x_99, 0, x_11);
x_107 = x_99;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_112, 0, x_11);
lean_ctor_set(x_112, 1, x_97);
lean_ctor_set(x_112, 2, x_98);
lean_ctor_set(x_112, 3, x_96);
lean_ctor_set(x_112, 4, x_96);
x_107 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_108; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_107);
lean_ctor_set(x_8, 3, x_106);
lean_ctor_set(x_8, 2, x_102);
lean_ctor_set(x_8, 1, x_101);
lean_ctor_set(x_8, 0, x_105);
x_108 = x_8;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_101);
lean_ctor_set(x_110, 2, x_102);
lean_ctor_set(x_110, 3, x_106);
lean_ctor_set(x_110, 4, x_107);
x_108 = x_110;
goto block_109;
}
block_109:
{
return x_108;
}
}
}
}
}
}
else
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_10, 4);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_137; 
x_125 = lean_ctor_get(x_10, 1);
x_126 = lean_ctor_get(x_10, 2);
x_137 = !lean_is_exclusive(x_10);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_10, 4);
lean_dec(x_138);
x_139 = lean_ctor_get(x_10, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_10, 0);
lean_dec(x_140);
x_127 = x_10;
x_128 = x_137;
goto block_136;
}
else
{
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_10);
x_127 = lean_box(0);
x_128 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_unsigned_to_nat(3u);
if (x_128 == 0)
{
lean_ctor_set(x_127, 4, x_95);
lean_ctor_set(x_127, 2, x_5);
lean_ctor_set(x_127, 1, x_4);
lean_ctor_set(x_127, 0, x_11);
x_130 = x_127;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_135, 0, x_11);
lean_ctor_set(x_135, 1, x_4);
lean_ctor_set(x_135, 2, x_5);
lean_ctor_set(x_135, 3, x_95);
lean_ctor_set(x_135, 4, x_95);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_124);
lean_ctor_set(x_8, 3, x_130);
lean_ctor_set(x_8, 2, x_126);
lean_ctor_set(x_8, 1, x_125);
lean_ctor_set(x_8, 0, x_129);
x_131 = x_8;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_130);
lean_ctor_set(x_133, 4, x_124);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_unsigned_to_nat(2u);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_10);
lean_ctor_set(x_8, 3, x_124);
lean_ctor_set(x_8, 0, x_141);
x_142 = x_8;
goto block_143;
}
else
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_4);
lean_ctor_set(x_144, 2, x_5);
lean_ctor_set(x_144, 3, x_124);
lean_ctor_set(x_144, 4, x_10);
x_142 = x_144;
goto block_143;
}
block_143:
{
return x_142;
}
}
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_unsigned_to_nat(1u);
x_149 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_1);
lean_ctor_set(x_149, 2, x_2);
lean_ctor_set(x_149, 3, x_3);
lean_ctor_set(x_149, 4, x_3);
return x_149;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_insertMax___redArg(x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMax_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_184; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_ctor_get(x_3, 3);
x_7 = lean_ctor_get(x_3, 4);
x_184 = !lean_is_exclusive(x_3);
if (x_184 == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_3, 0);
lean_dec(x_185);
x_8 = x_3;
x_9 = x_184;
goto block_183;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_184;
goto block_183;
}
block_183:
{
lean_object* x_10; 
x_10 = l_Std_DTreeMap_Internal_Impl_insertMax_x21___redArg(x_1, x_2, x_7);
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 4);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(3u);
x_18 = lean_nat_mul(x_17, x_11);
x_19 = lean_nat_dec_lt(x_18, x_12);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_20, x_11);
x_22 = lean_nat_add(x_21, x_12);
lean_dec(x_12);
lean_dec(x_21);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_10);
lean_ctor_set(x_8, 0, x_22);
x_23 = x_8;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_5);
lean_ctor_set(x_25, 3, x_6);
lean_ctor_set(x_25, 4, x_10);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
else
{
lean_object* x_26; uint8_t x_27; uint8_t x_95; 
x_95 = !lean_is_exclusive(x_10);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_10, 4);
lean_dec(x_96);
x_97 = lean_ctor_get(x_10, 3);
lean_dec(x_97);
x_98 = lean_ctor_get(x_10, 2);
lean_dec(x_98);
x_99 = lean_ctor_get(x_10, 1);
lean_dec(x_99);
x_100 = lean_ctor_get(x_10, 0);
lean_dec(x_100);
x_26 = x_10;
x_27 = x_95;
goto block_94;
}
else
{
lean_dec(x_10);
x_26 = lean_box(0);
x_27 = x_95;
goto block_94;
}
block_94:
{
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
x_30 = lean_ctor_get(x_15, 2);
x_31 = lean_ctor_get(x_15, 3);
x_32 = lean_ctor_get(x_15, 4);
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_mul(x_34, x_33);
x_36 = lean_nat_dec_lt(x_28, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; uint8_t x_65; 
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_65 = !lean_is_exclusive(x_15);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_15, 4);
lean_dec(x_66);
x_67 = lean_ctor_get(x_15, 3);
lean_dec(x_67);
x_68 = lean_ctor_get(x_15, 2);
lean_dec(x_68);
x_69 = lean_ctor_get(x_15, 1);
lean_dec(x_69);
x_70 = lean_ctor_get(x_15, 0);
lean_dec(x_70);
x_37 = x_15;
x_38 = x_65;
goto block_64;
}
else
{
lean_dec(x_15);
x_37 = lean_box(0);
x_38 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_53; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_39, x_11);
x_41 = lean_nat_add(x_40, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_31, 0);
lean_inc(x_62);
x_53 = x_62;
goto block_61;
}
else
{
lean_object* x_63; 
x_63 = lean_unsigned_to_nat(0u);
x_53 = x_63;
goto block_61;
}
block_52:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_nat_add(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_38 == 0)
{
lean_ctor_set(x_37, 4, x_16);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 2, x_14);
lean_ctor_set(x_37, 1, x_13);
lean_ctor_set(x_37, 0, x_45);
x_46 = x_37;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_13);
lean_ctor_set(x_51, 2, x_14);
lean_ctor_set(x_51, 3, x_32);
lean_ctor_set(x_51, 4, x_16);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_46);
lean_ctor_set(x_26, 3, x_42);
lean_ctor_set(x_26, 2, x_30);
lean_ctor_set(x_26, 1, x_29);
lean_ctor_set(x_26, 0, x_41);
x_47 = x_26;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_29);
lean_ctor_set(x_49, 2, x_30);
lean_ctor_set(x_49, 3, x_42);
lean_ctor_set(x_49, 4, x_46);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
block_61:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_nat_add(x_40, x_53);
lean_dec(x_53);
lean_dec(x_40);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_31);
lean_ctor_set(x_8, 0, x_54);
x_55 = x_8;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_4);
lean_ctor_set(x_60, 2, x_5);
lean_ctor_set(x_60, 3, x_6);
lean_ctor_set(x_60, 4, x_31);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
x_56 = lean_nat_add(x_39, x_33);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_32, 0);
lean_inc(x_57);
x_42 = x_55;
x_43 = x_56;
x_44 = x_57;
goto block_52;
}
else
{
lean_object* x_58; 
x_58 = lean_unsigned_to_nat(0u);
x_42 = x_55;
x_43 = x_56;
x_44 = x_58;
goto block_52;
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_del_object(x_8);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_71, x_11);
x_73 = lean_nat_add(x_72, x_12);
lean_dec(x_12);
x_74 = lean_nat_add(x_72, x_28);
lean_dec(x_72);
lean_inc_ref(x_6);
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_15);
lean_ctor_set(x_26, 3, x_6);
lean_ctor_set(x_26, 2, x_5);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 0, x_74);
x_75 = x_26;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_4);
lean_ctor_set(x_89, 2, x_5);
lean_ctor_set(x_89, 3, x_6);
lean_ctor_set(x_89, 4, x_15);
x_75 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_76; uint8_t x_77; uint8_t x_82; 
x_82 = !lean_is_exclusive(x_6);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_6, 4);
lean_dec(x_83);
x_84 = lean_ctor_get(x_6, 3);
lean_dec(x_84);
x_85 = lean_ctor_get(x_6, 2);
lean_dec(x_85);
x_86 = lean_ctor_get(x_6, 1);
lean_dec(x_86);
x_87 = lean_ctor_get(x_6, 0);
lean_dec(x_87);
x_76 = x_6;
x_77 = x_82;
goto block_81;
}
else
{
lean_dec(x_6);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
lean_ctor_set(x_76, 4, x_16);
lean_ctor_set(x_76, 3, x_75);
lean_ctor_set(x_76, 2, x_14);
lean_ctor_set(x_76, 1, x_13);
lean_ctor_set(x_76, 0, x_73);
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_73);
lean_ctor_set(x_80, 1, x_13);
lean_ctor_set(x_80, 2, x_14);
lean_ctor_set(x_80, 3, x_75);
lean_ctor_set(x_80, 4, x_16);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_15);
lean_del_object(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_6);
lean_del_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_90 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3);
x_91 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_90);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_del_object(x_26);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_6);
lean_del_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_92 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4);
x_93 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_92);
return x_93;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_6, 0);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_nat_add(x_102, x_101);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_10);
lean_ctor_set(x_8, 0, x_103);
x_104 = x_8;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_4);
lean_ctor_set(x_106, 2, x_5);
lean_ctor_set(x_106, 3, x_6);
lean_ctor_set(x_106, 4, x_10);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
else
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_10, 3);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_10, 4);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_125; 
x_109 = lean_ctor_get(x_10, 0);
x_110 = lean_ctor_get(x_10, 1);
x_111 = lean_ctor_get(x_10, 2);
x_125 = !lean_is_exclusive(x_10);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_10, 4);
lean_dec(x_126);
x_127 = lean_ctor_get(x_10, 3);
lean_dec(x_127);
x_112 = x_10;
x_113 = x_125;
goto block_124;
}
else
{
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_10);
x_112 = lean_box(0);
x_113 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_107, 0);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_add(x_115, x_109);
lean_dec(x_109);
x_117 = lean_nat_add(x_115, x_114);
if (x_113 == 0)
{
lean_ctor_set(x_112, 4, x_107);
lean_ctor_set(x_112, 3, x_6);
lean_ctor_set(x_112, 2, x_5);
lean_ctor_set(x_112, 1, x_4);
lean_ctor_set(x_112, 0, x_117);
x_118 = x_112;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_123, 0, x_117);
lean_ctor_set(x_123, 1, x_4);
lean_ctor_set(x_123, 2, x_5);
lean_ctor_set(x_123, 3, x_6);
lean_ctor_set(x_123, 4, x_107);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_108);
lean_ctor_set(x_8, 3, x_118);
lean_ctor_set(x_8, 2, x_111);
lean_ctor_set(x_8, 1, x_110);
lean_ctor_set(x_8, 0, x_116);
x_119 = x_8;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_110);
lean_ctor_set(x_121, 2, x_111);
lean_ctor_set(x_121, 3, x_118);
lean_ctor_set(x_121, 4, x_108);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_153; 
x_128 = lean_ctor_get(x_10, 1);
x_129 = lean_ctor_get(x_10, 2);
x_153 = !lean_is_exclusive(x_10);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_10, 4);
lean_dec(x_154);
x_155 = lean_ctor_get(x_10, 3);
lean_dec(x_155);
x_156 = lean_ctor_get(x_10, 0);
lean_dec(x_156);
x_130 = x_10;
x_131 = x_153;
goto block_152;
}
else
{
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_10);
x_130 = lean_box(0);
x_131 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_148; 
x_132 = lean_ctor_get(x_107, 1);
x_133 = lean_ctor_get(x_107, 2);
x_148 = !lean_is_exclusive(x_107);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_107, 4);
lean_dec(x_149);
x_150 = lean_ctor_get(x_107, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_107, 0);
lean_dec(x_151);
x_134 = x_107;
x_135 = x_148;
goto block_147;
}
else
{
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_107);
x_134 = lean_box(0);
x_135 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_unsigned_to_nat(3u);
x_137 = lean_unsigned_to_nat(1u);
if (x_135 == 0)
{
lean_ctor_set(x_134, 4, x_108);
lean_ctor_set(x_134, 3, x_108);
lean_ctor_set(x_134, 2, x_5);
lean_ctor_set(x_134, 1, x_4);
lean_ctor_set(x_134, 0, x_137);
x_138 = x_134;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_146, 0, x_137);
lean_ctor_set(x_146, 1, x_4);
lean_ctor_set(x_146, 2, x_5);
lean_ctor_set(x_146, 3, x_108);
lean_ctor_set(x_146, 4, x_108);
x_138 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_139; 
if (x_131 == 0)
{
lean_ctor_set(x_130, 3, x_108);
lean_ctor_set(x_130, 0, x_137);
x_139 = x_130;
goto block_143;
}
else
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_144, 0, x_137);
lean_ctor_set(x_144, 1, x_128);
lean_ctor_set(x_144, 2, x_129);
lean_ctor_set(x_144, 3, x_108);
lean_ctor_set(x_144, 4, x_108);
x_139 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_140; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_139);
lean_ctor_set(x_8, 3, x_138);
lean_ctor_set(x_8, 2, x_133);
lean_ctor_set(x_8, 1, x_132);
lean_ctor_set(x_8, 0, x_136);
x_140 = x_8;
goto block_141;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_142, 0, x_136);
lean_ctor_set(x_142, 1, x_132);
lean_ctor_set(x_142, 2, x_133);
lean_ctor_set(x_142, 3, x_138);
lean_ctor_set(x_142, 4, x_139);
x_140 = x_142;
goto block_141;
}
block_141:
{
return x_140;
}
}
}
}
}
}
}
else
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_10, 4);
lean_inc(x_157);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_171; 
x_158 = lean_ctor_get(x_10, 1);
x_159 = lean_ctor_get(x_10, 2);
x_171 = !lean_is_exclusive(x_10);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_10, 4);
lean_dec(x_172);
x_173 = lean_ctor_get(x_10, 3);
lean_dec(x_173);
x_174 = lean_ctor_get(x_10, 0);
lean_dec(x_174);
x_160 = x_10;
x_161 = x_171;
goto block_170;
}
else
{
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_10);
x_160 = lean_box(0);
x_161 = x_171;
goto block_170;
}
block_170:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_unsigned_to_nat(3u);
x_163 = lean_unsigned_to_nat(1u);
if (x_161 == 0)
{
lean_ctor_set(x_160, 4, x_107);
lean_ctor_set(x_160, 2, x_5);
lean_ctor_set(x_160, 1, x_4);
lean_ctor_set(x_160, 0, x_163);
x_164 = x_160;
goto block_168;
}
else
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_169, 0, x_163);
lean_ctor_set(x_169, 1, x_4);
lean_ctor_set(x_169, 2, x_5);
lean_ctor_set(x_169, 3, x_107);
lean_ctor_set(x_169, 4, x_107);
x_164 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_165; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_157);
lean_ctor_set(x_8, 3, x_164);
lean_ctor_set(x_8, 2, x_159);
lean_ctor_set(x_8, 1, x_158);
lean_ctor_set(x_8, 0, x_162);
x_165 = x_8;
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_162);
lean_ctor_set(x_167, 1, x_158);
lean_ctor_set(x_167, 2, x_159);
lean_ctor_set(x_167, 3, x_164);
lean_ctor_set(x_167, 4, x_157);
x_165 = x_167;
goto block_166;
}
block_166:
{
return x_165;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_unsigned_to_nat(2u);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_10);
lean_ctor_set(x_8, 3, x_157);
lean_ctor_set(x_8, 0, x_175);
x_176 = x_8;
goto block_177;
}
else
{
lean_object* x_178; 
x_178 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_4);
lean_ctor_set(x_178, 2, x_5);
lean_ctor_set(x_178, 3, x_157);
lean_ctor_set(x_178, 4, x_10);
x_176 = x_178;
goto block_177;
}
block_177:
{
return x_176;
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_unsigned_to_nat(1u);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_10);
lean_ctor_set(x_8, 3, x_10);
lean_ctor_set(x_8, 0, x_179);
x_180 = x_8;
goto block_181;
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_4);
lean_ctor_set(x_182, 2, x_5);
lean_ctor_set(x_182, 3, x_10);
lean_ctor_set(x_182, 4, x_10);
x_180 = x_182;
goto block_181;
}
block_181:
{
return x_180;
}
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_1);
lean_ctor_set(x_187, 2, x_2);
lean_ctor_set(x_187, 3, x_3);
lean_ctor_set(x_187, 4, x_3);
return x_187;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMax_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insertMax_x21___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 4);
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
lean_inc(x_14);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_mul(x_15, x_5);
x_17 = lean_nat_dec_lt(x_16, x_10);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_14);
x_18 = lean_nat_mul(x_15, x_10);
x_19 = lean_nat_dec_lt(x_18, x_5);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
x_22 = lean_nat_add(x_21, x_10);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
lean_ctor_set(x_23, 2, x_2);
lean_ctor_set(x_23, 3, x_3);
lean_ctor_set(x_23, 4, x_4);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; uint8_t x_190; 
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_190 = !lean_is_exclusive(x_3);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_191 = lean_ctor_get(x_3, 4);
lean_dec(x_191);
x_192 = lean_ctor_get(x_3, 3);
lean_dec(x_192);
x_193 = lean_ctor_get(x_3, 2);
lean_dec(x_193);
x_194 = lean_ctor_get(x_3, 1);
lean_dec(x_194);
x_195 = lean_ctor_get(x_3, 0);
lean_dec(x_195);
x_24 = x_3;
x_25 = x_190;
goto block_189;
}
else
{
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Std_DTreeMap_Internal_Impl_link___redArg(x_1, x_2, x_9, x_4);
x_27 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 4);
lean_inc(x_33);
x_34 = lean_nat_mul(x_15, x_28);
x_35 = lean_nat_dec_lt(x_34, x_29);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_36 = lean_nat_add(x_27, x_28);
x_37 = lean_nat_add(x_36, x_29);
lean_dec(x_29);
lean_dec(x_36);
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_26);
lean_ctor_set(x_24, 0, x_37);
x_38 = x_24;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_6);
lean_ctor_set(x_40, 2, x_7);
lean_ctor_set(x_40, 3, x_8);
lean_ctor_set(x_40, 4, x_26);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
else
{
lean_object* x_41; uint8_t x_42; uint8_t x_104; 
x_104 = !lean_is_exclusive(x_26);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_26, 4);
lean_dec(x_105);
x_106 = lean_ctor_get(x_26, 3);
lean_dec(x_106);
x_107 = lean_ctor_get(x_26, 2);
lean_dec(x_107);
x_108 = lean_ctor_get(x_26, 1);
lean_dec(x_108);
x_109 = lean_ctor_get(x_26, 0);
lean_dec(x_109);
x_41 = x_26;
x_42 = x_104;
goto block_103;
}
else
{
lean_dec(x_26);
x_41 = lean_box(0);
x_42 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
x_45 = lean_ctor_get(x_32, 2);
x_46 = lean_ctor_get(x_32, 3);
x_47 = lean_ctor_get(x_32, 4);
x_48 = lean_ctor_get(x_33, 0);
x_49 = lean_unsigned_to_nat(2u);
x_50 = lean_nat_mul(x_49, x_48);
x_51 = lean_nat_dec_lt(x_43, x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; uint8_t x_79; 
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
x_79 = !lean_is_exclusive(x_32);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_32, 4);
lean_dec(x_80);
x_81 = lean_ctor_get(x_32, 3);
lean_dec(x_81);
x_82 = lean_ctor_get(x_32, 2);
lean_dec(x_82);
x_83 = lean_ctor_get(x_32, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_32, 0);
lean_dec(x_84);
x_52 = x_32;
x_53 = x_79;
goto block_78;
}
else
{
lean_dec(x_32);
x_52 = lean_box(0);
x_53 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_67; 
x_54 = lean_nat_add(x_27, x_28);
x_55 = lean_nat_add(x_54, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_46, 0);
lean_inc(x_76);
x_67 = x_76;
goto block_75;
}
else
{
lean_object* x_77; 
x_77 = lean_unsigned_to_nat(0u);
x_67 = x_77;
goto block_75;
}
block_66:
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_nat_add(x_56, x_58);
lean_dec(x_58);
lean_dec(x_56);
if (x_53 == 0)
{
lean_ctor_set(x_52, 4, x_33);
lean_ctor_set(x_52, 3, x_47);
lean_ctor_set(x_52, 2, x_31);
lean_ctor_set(x_52, 1, x_30);
lean_ctor_set(x_52, 0, x_59);
x_60 = x_52;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_30);
lean_ctor_set(x_65, 2, x_31);
lean_ctor_set(x_65, 3, x_47);
lean_ctor_set(x_65, 4, x_33);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_42 == 0)
{
lean_ctor_set(x_41, 4, x_60);
lean_ctor_set(x_41, 3, x_57);
lean_ctor_set(x_41, 2, x_45);
lean_ctor_set(x_41, 1, x_44);
lean_ctor_set(x_41, 0, x_55);
x_61 = x_41;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_55);
lean_ctor_set(x_63, 1, x_44);
lean_ctor_set(x_63, 2, x_45);
lean_ctor_set(x_63, 3, x_57);
lean_ctor_set(x_63, 4, x_60);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
block_75:
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_nat_add(x_54, x_67);
lean_dec(x_67);
lean_dec(x_54);
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_46);
lean_ctor_set(x_24, 0, x_68);
x_69 = x_24;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_6);
lean_ctor_set(x_74, 2, x_7);
lean_ctor_set(x_74, 3, x_8);
lean_ctor_set(x_74, 4, x_46);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
x_70 = lean_nat_add(x_27, x_48);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_47, 0);
lean_inc(x_71);
x_56 = x_70;
x_57 = x_69;
x_58 = x_71;
goto block_66;
}
else
{
lean_object* x_72; 
x_72 = lean_unsigned_to_nat(0u);
x_56 = x_70;
x_57 = x_69;
x_58 = x_72;
goto block_66;
}
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_del_object(x_24);
x_85 = lean_nat_add(x_27, x_28);
x_86 = lean_nat_add(x_85, x_29);
lean_dec(x_29);
x_87 = lean_nat_add(x_85, x_43);
lean_dec(x_85);
lean_inc_ref(x_8);
if (x_42 == 0)
{
lean_ctor_set(x_41, 4, x_32);
lean_ctor_set(x_41, 3, x_8);
lean_ctor_set(x_41, 2, x_7);
lean_ctor_set(x_41, 1, x_6);
lean_ctor_set(x_41, 0, x_87);
x_88 = x_41;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_102, 0, x_87);
lean_ctor_set(x_102, 1, x_6);
lean_ctor_set(x_102, 2, x_7);
lean_ctor_set(x_102, 3, x_8);
lean_ctor_set(x_102, 4, x_32);
x_88 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_89; uint8_t x_90; uint8_t x_95; 
x_95 = !lean_is_exclusive(x_8);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_8, 4);
lean_dec(x_96);
x_97 = lean_ctor_get(x_8, 3);
lean_dec(x_97);
x_98 = lean_ctor_get(x_8, 2);
lean_dec(x_98);
x_99 = lean_ctor_get(x_8, 1);
lean_dec(x_99);
x_100 = lean_ctor_get(x_8, 0);
lean_dec(x_100);
x_89 = x_8;
x_90 = x_95;
goto block_94;
}
else
{
lean_dec(x_8);
x_89 = lean_box(0);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_90 == 0)
{
lean_ctor_set(x_89, 4, x_33);
lean_ctor_set(x_89, 3, x_88);
lean_ctor_set(x_89, 2, x_31);
lean_ctor_set(x_89, 1, x_30);
lean_ctor_set(x_89, 0, x_86);
x_91 = x_89;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_93, 0, x_86);
lean_ctor_set(x_93, 1, x_30);
lean_ctor_set(x_93, 2, x_31);
lean_ctor_set(x_93, 3, x_88);
lean_ctor_set(x_93, 4, x_33);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
}
}
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_26, 3);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_26, 4);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_127; 
x_112 = lean_ctor_get(x_26, 0);
x_113 = lean_ctor_get(x_26, 1);
x_114 = lean_ctor_get(x_26, 2);
x_127 = !lean_is_exclusive(x_26);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_26, 4);
lean_dec(x_128);
x_129 = lean_ctor_get(x_26, 3);
lean_dec(x_129);
x_115 = x_26;
x_116 = x_127;
goto block_126;
}
else
{
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_26);
x_115 = lean_box(0);
x_116 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_110, 0);
x_118 = lean_nat_add(x_27, x_112);
lean_dec(x_112);
x_119 = lean_nat_add(x_27, x_117);
if (x_116 == 0)
{
lean_ctor_set(x_115, 4, x_110);
lean_ctor_set(x_115, 3, x_8);
lean_ctor_set(x_115, 2, x_7);
lean_ctor_set(x_115, 1, x_6);
lean_ctor_set(x_115, 0, x_119);
x_120 = x_115;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_125, 0, x_119);
lean_ctor_set(x_125, 1, x_6);
lean_ctor_set(x_125, 2, x_7);
lean_ctor_set(x_125, 3, x_8);
lean_ctor_set(x_125, 4, x_110);
x_120 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_121; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_111);
lean_ctor_set(x_24, 3, x_120);
lean_ctor_set(x_24, 2, x_114);
lean_ctor_set(x_24, 1, x_113);
lean_ctor_set(x_24, 0, x_118);
x_121 = x_24;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_123, 0, x_118);
lean_ctor_set(x_123, 1, x_113);
lean_ctor_set(x_123, 2, x_114);
lean_ctor_set(x_123, 3, x_120);
lean_ctor_set(x_123, 4, x_111);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_153; 
x_130 = lean_ctor_get(x_26, 1);
x_131 = lean_ctor_get(x_26, 2);
x_153 = !lean_is_exclusive(x_26);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_26, 4);
lean_dec(x_154);
x_155 = lean_ctor_get(x_26, 3);
lean_dec(x_155);
x_156 = lean_ctor_get(x_26, 0);
lean_dec(x_156);
x_132 = x_26;
x_133 = x_153;
goto block_152;
}
else
{
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_26);
x_132 = lean_box(0);
x_133 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_148; 
x_134 = lean_ctor_get(x_110, 1);
x_135 = lean_ctor_get(x_110, 2);
x_148 = !lean_is_exclusive(x_110);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_110, 4);
lean_dec(x_149);
x_150 = lean_ctor_get(x_110, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_110, 0);
lean_dec(x_151);
x_136 = x_110;
x_137 = x_148;
goto block_147;
}
else
{
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_110);
x_136 = lean_box(0);
x_137 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_138; 
if (x_137 == 0)
{
lean_ctor_set(x_136, 4, x_111);
lean_ctor_set(x_136, 3, x_111);
lean_ctor_set(x_136, 2, x_7);
lean_ctor_set(x_136, 1, x_6);
lean_ctor_set(x_136, 0, x_27);
x_138 = x_136;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_146, 0, x_27);
lean_ctor_set(x_146, 1, x_6);
lean_ctor_set(x_146, 2, x_7);
lean_ctor_set(x_146, 3, x_111);
lean_ctor_set(x_146, 4, x_111);
x_138 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_139; 
if (x_133 == 0)
{
lean_ctor_set(x_132, 3, x_111);
lean_ctor_set(x_132, 0, x_27);
x_139 = x_132;
goto block_143;
}
else
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_144, 0, x_27);
lean_ctor_set(x_144, 1, x_130);
lean_ctor_set(x_144, 2, x_131);
lean_ctor_set(x_144, 3, x_111);
lean_ctor_set(x_144, 4, x_111);
x_139 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_140; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_139);
lean_ctor_set(x_24, 3, x_138);
lean_ctor_set(x_24, 2, x_135);
lean_ctor_set(x_24, 1, x_134);
lean_ctor_set(x_24, 0, x_15);
x_140 = x_24;
goto block_141;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_142, 0, x_15);
lean_ctor_set(x_142, 1, x_134);
lean_ctor_set(x_142, 2, x_135);
lean_ctor_set(x_142, 3, x_138);
lean_ctor_set(x_142, 4, x_139);
x_140 = x_142;
goto block_141;
}
block_141:
{
return x_140;
}
}
}
}
}
}
}
else
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_26, 4);
lean_inc(x_157);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_169; 
x_158 = lean_ctor_get(x_26, 1);
x_159 = lean_ctor_get(x_26, 2);
x_169 = !lean_is_exclusive(x_26);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_26, 4);
lean_dec(x_170);
x_171 = lean_ctor_get(x_26, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_26, 0);
lean_dec(x_172);
x_160 = x_26;
x_161 = x_169;
goto block_168;
}
else
{
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_26);
x_160 = lean_box(0);
x_161 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_162; 
if (x_161 == 0)
{
lean_ctor_set(x_160, 4, x_110);
lean_ctor_set(x_160, 2, x_7);
lean_ctor_set(x_160, 1, x_6);
lean_ctor_set(x_160, 0, x_27);
x_162 = x_160;
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_27);
lean_ctor_set(x_167, 1, x_6);
lean_ctor_set(x_167, 2, x_7);
lean_ctor_set(x_167, 3, x_110);
lean_ctor_set(x_167, 4, x_110);
x_162 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_163; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_157);
lean_ctor_set(x_24, 3, x_162);
lean_ctor_set(x_24, 2, x_159);
lean_ctor_set(x_24, 1, x_158);
lean_ctor_set(x_24, 0, x_15);
x_163 = x_24;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_165, 0, x_15);
lean_ctor_set(x_165, 1, x_158);
lean_ctor_set(x_165, 2, x_159);
lean_ctor_set(x_165, 3, x_162);
lean_ctor_set(x_165, 4, x_157);
x_163 = x_165;
goto block_164;
}
block_164:
{
return x_163;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_186; 
x_173 = lean_ctor_get(x_26, 0);
x_174 = lean_ctor_get(x_26, 1);
x_175 = lean_ctor_get(x_26, 2);
x_186 = !lean_is_exclusive(x_26);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_26, 4);
lean_dec(x_187);
x_188 = lean_ctor_get(x_26, 3);
lean_dec(x_188);
x_176 = x_26;
x_177 = x_186;
goto block_185;
}
else
{
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_26);
x_176 = lean_box(0);
x_177 = x_186;
goto block_185;
}
block_185:
{
lean_object* x_178; 
if (x_177 == 0)
{
lean_ctor_set(x_176, 3, x_157);
x_178 = x_176;
goto block_183;
}
else
{
lean_object* x_184; 
x_184 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_184, 0, x_173);
lean_ctor_set(x_184, 1, x_174);
lean_ctor_set(x_184, 2, x_175);
lean_ctor_set(x_184, 3, x_157);
lean_ctor_set(x_184, 4, x_157);
x_178 = x_184;
goto block_183;
}
block_183:
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_unsigned_to_nat(2u);
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_178);
lean_ctor_set(x_24, 3, x_157);
lean_ctor_set(x_24, 0, x_179);
x_180 = x_24;
goto block_181;
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_6);
lean_ctor_set(x_182, 2, x_7);
lean_ctor_set(x_182, 3, x_157);
lean_ctor_set(x_182, 4, x_178);
x_180 = x_182;
goto block_181;
}
block_181:
{
return x_180;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_196; uint8_t x_197; uint8_t x_352; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_8);
x_352 = !lean_is_exclusive(x_4);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_353 = lean_ctor_get(x_4, 4);
lean_dec(x_353);
x_354 = lean_ctor_get(x_4, 3);
lean_dec(x_354);
x_355 = lean_ctor_get(x_4, 2);
lean_dec(x_355);
x_356 = lean_ctor_get(x_4, 1);
lean_dec(x_356);
x_357 = lean_ctor_get(x_4, 0);
lean_dec(x_357);
x_196 = x_4;
x_197 = x_352;
goto block_351;
}
else
{
lean_dec(x_4);
x_196 = lean_box(0);
x_197 = x_352;
goto block_351;
}
block_351:
{
lean_object* x_198; lean_object* x_199; 
x_198 = l_Std_DTreeMap_Internal_Impl_link___redArg(x_1, x_2, x_3, x_13);
x_199 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_200 = lean_ctor_get(x_14, 0);
x_201 = lean_ctor_get(x_198, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_198, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_198, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_198, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_198, 4);
lean_inc(x_205);
x_206 = lean_nat_mul(x_15, x_200);
x_207 = lean_nat_dec_lt(x_206, x_201);
lean_dec(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
x_208 = lean_nat_add(x_199, x_201);
lean_dec(x_201);
x_209 = lean_nat_add(x_208, x_200);
lean_dec(x_208);
if (x_197 == 0)
{
lean_ctor_set(x_196, 3, x_198);
lean_ctor_set(x_196, 0, x_209);
x_210 = x_196;
goto block_211;
}
else
{
lean_object* x_212; 
x_212 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_11);
lean_ctor_set(x_212, 2, x_12);
lean_ctor_set(x_212, 3, x_198);
lean_ctor_set(x_212, 4, x_14);
x_210 = x_212;
goto block_211;
}
block_211:
{
return x_210;
}
}
else
{
lean_object* x_213; uint8_t x_214; uint8_t x_278; 
x_278 = !lean_is_exclusive(x_198);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_ctor_get(x_198, 4);
lean_dec(x_279);
x_280 = lean_ctor_get(x_198, 3);
lean_dec(x_280);
x_281 = lean_ctor_get(x_198, 2);
lean_dec(x_281);
x_282 = lean_ctor_get(x_198, 1);
lean_dec(x_282);
x_283 = lean_ctor_get(x_198, 0);
lean_dec(x_283);
x_213 = x_198;
x_214 = x_278;
goto block_277;
}
else
{
lean_dec(x_198);
x_213 = lean_box(0);
x_214 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_215 = lean_ctor_get(x_204, 0);
x_216 = lean_ctor_get(x_205, 0);
x_217 = lean_ctor_get(x_205, 1);
x_218 = lean_ctor_get(x_205, 2);
x_219 = lean_ctor_get(x_205, 3);
x_220 = lean_ctor_get(x_205, 4);
x_221 = lean_unsigned_to_nat(2u);
x_222 = lean_nat_mul(x_221, x_215);
x_223 = lean_nat_dec_lt(x_216, x_222);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; uint8_t x_225; uint8_t x_252; 
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
x_252 = !lean_is_exclusive(x_205);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_253 = lean_ctor_get(x_205, 4);
lean_dec(x_253);
x_254 = lean_ctor_get(x_205, 3);
lean_dec(x_254);
x_255 = lean_ctor_get(x_205, 2);
lean_dec(x_255);
x_256 = lean_ctor_get(x_205, 1);
lean_dec(x_256);
x_257 = lean_ctor_get(x_205, 0);
lean_dec(x_257);
x_224 = x_205;
x_225 = x_252;
goto block_251;
}
else
{
lean_dec(x_205);
x_224 = lean_box(0);
x_225 = x_252;
goto block_251;
}
block_251:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_239; lean_object* x_240; 
x_226 = lean_nat_add(x_199, x_201);
lean_dec(x_201);
x_227 = lean_nat_add(x_226, x_200);
lean_dec(x_226);
x_239 = lean_nat_add(x_199, x_215);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_219, 0);
lean_inc(x_249);
x_240 = x_249;
goto block_248;
}
else
{
lean_object* x_250; 
x_250 = lean_unsigned_to_nat(0u);
x_240 = x_250;
goto block_248;
}
block_238:
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_nat_add(x_229, x_230);
lean_dec(x_230);
lean_dec(x_229);
if (x_225 == 0)
{
lean_ctor_set(x_224, 4, x_14);
lean_ctor_set(x_224, 3, x_220);
lean_ctor_set(x_224, 2, x_12);
lean_ctor_set(x_224, 1, x_11);
lean_ctor_set(x_224, 0, x_231);
x_232 = x_224;
goto block_236;
}
else
{
lean_object* x_237; 
x_237 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_237, 0, x_231);
lean_ctor_set(x_237, 1, x_11);
lean_ctor_set(x_237, 2, x_12);
lean_ctor_set(x_237, 3, x_220);
lean_ctor_set(x_237, 4, x_14);
x_232 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_233; 
if (x_214 == 0)
{
lean_ctor_set(x_213, 4, x_232);
lean_ctor_set(x_213, 3, x_228);
lean_ctor_set(x_213, 2, x_218);
lean_ctor_set(x_213, 1, x_217);
lean_ctor_set(x_213, 0, x_227);
x_233 = x_213;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_235, 0, x_227);
lean_ctor_set(x_235, 1, x_217);
lean_ctor_set(x_235, 2, x_218);
lean_ctor_set(x_235, 3, x_228);
lean_ctor_set(x_235, 4, x_232);
x_233 = x_235;
goto block_234;
}
block_234:
{
return x_233;
}
}
}
block_248:
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_nat_add(x_239, x_240);
lean_dec(x_240);
lean_dec(x_239);
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_219);
lean_ctor_set(x_196, 3, x_204);
lean_ctor_set(x_196, 2, x_203);
lean_ctor_set(x_196, 1, x_202);
lean_ctor_set(x_196, 0, x_241);
x_242 = x_196;
goto block_246;
}
else
{
lean_object* x_247; 
x_247 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_247, 0, x_241);
lean_ctor_set(x_247, 1, x_202);
lean_ctor_set(x_247, 2, x_203);
lean_ctor_set(x_247, 3, x_204);
lean_ctor_set(x_247, 4, x_219);
x_242 = x_247;
goto block_246;
}
block_246:
{
lean_object* x_243; 
x_243 = lean_nat_add(x_199, x_200);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_244; 
x_244 = lean_ctor_get(x_220, 0);
lean_inc(x_244);
x_228 = x_242;
x_229 = x_243;
x_230 = x_244;
goto block_238;
}
else
{
lean_object* x_245; 
x_245 = lean_unsigned_to_nat(0u);
x_228 = x_242;
x_229 = x_243;
x_230 = x_245;
goto block_238;
}
}
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_del_object(x_196);
x_258 = lean_nat_add(x_199, x_201);
lean_dec(x_201);
x_259 = lean_nat_add(x_258, x_200);
lean_dec(x_258);
x_260 = lean_nat_add(x_199, x_200);
x_261 = lean_nat_add(x_260, x_216);
lean_dec(x_260);
lean_inc_ref(x_14);
if (x_214 == 0)
{
lean_ctor_set(x_213, 4, x_14);
lean_ctor_set(x_213, 3, x_205);
lean_ctor_set(x_213, 2, x_12);
lean_ctor_set(x_213, 1, x_11);
lean_ctor_set(x_213, 0, x_261);
x_262 = x_213;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_276, 0, x_261);
lean_ctor_set(x_276, 1, x_11);
lean_ctor_set(x_276, 2, x_12);
lean_ctor_set(x_276, 3, x_205);
lean_ctor_set(x_276, 4, x_14);
x_262 = x_276;
goto block_275;
}
block_275:
{
lean_object* x_263; uint8_t x_264; uint8_t x_269; 
x_269 = !lean_is_exclusive(x_14);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_ctor_get(x_14, 4);
lean_dec(x_270);
x_271 = lean_ctor_get(x_14, 3);
lean_dec(x_271);
x_272 = lean_ctor_get(x_14, 2);
lean_dec(x_272);
x_273 = lean_ctor_get(x_14, 1);
lean_dec(x_273);
x_274 = lean_ctor_get(x_14, 0);
lean_dec(x_274);
x_263 = x_14;
x_264 = x_269;
goto block_268;
}
else
{
lean_dec(x_14);
x_263 = lean_box(0);
x_264 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_265; 
if (x_264 == 0)
{
lean_ctor_set(x_263, 4, x_262);
lean_ctor_set(x_263, 3, x_204);
lean_ctor_set(x_263, 2, x_203);
lean_ctor_set(x_263, 1, x_202);
lean_ctor_set(x_263, 0, x_259);
x_265 = x_263;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_267, 0, x_259);
lean_ctor_set(x_267, 1, x_202);
lean_ctor_set(x_267, 2, x_203);
lean_ctor_set(x_267, 3, x_204);
lean_ctor_set(x_267, 4, x_262);
x_265 = x_267;
goto block_266;
}
block_266:
{
return x_265;
}
}
}
}
}
}
}
else
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_198, 3);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_198, 4);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; uint8_t x_301; 
x_286 = lean_ctor_get(x_198, 0);
x_287 = lean_ctor_get(x_198, 1);
x_288 = lean_ctor_get(x_198, 2);
x_301 = !lean_is_exclusive(x_198);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_198, 4);
lean_dec(x_302);
x_303 = lean_ctor_get(x_198, 3);
lean_dec(x_303);
x_289 = x_198;
x_290 = x_301;
goto block_300;
}
else
{
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_198);
x_289 = lean_box(0);
x_290 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_291 = lean_ctor_get(x_285, 0);
x_292 = lean_nat_add(x_199, x_286);
lean_dec(x_286);
x_293 = lean_nat_add(x_199, x_291);
if (x_290 == 0)
{
lean_ctor_set(x_289, 4, x_14);
lean_ctor_set(x_289, 3, x_285);
lean_ctor_set(x_289, 2, x_12);
lean_ctor_set(x_289, 1, x_11);
lean_ctor_set(x_289, 0, x_293);
x_294 = x_289;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_299, 0, x_293);
lean_ctor_set(x_299, 1, x_11);
lean_ctor_set(x_299, 2, x_12);
lean_ctor_set(x_299, 3, x_285);
lean_ctor_set(x_299, 4, x_14);
x_294 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_295; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_294);
lean_ctor_set(x_196, 3, x_284);
lean_ctor_set(x_196, 2, x_288);
lean_ctor_set(x_196, 1, x_287);
lean_ctor_set(x_196, 0, x_292);
x_295 = x_196;
goto block_296;
}
else
{
lean_object* x_297; 
x_297 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_297, 0, x_292);
lean_ctor_set(x_297, 1, x_287);
lean_ctor_set(x_297, 2, x_288);
lean_ctor_set(x_297, 3, x_284);
lean_ctor_set(x_297, 4, x_294);
x_295 = x_297;
goto block_296;
}
block_296:
{
return x_295;
}
}
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_315; 
x_304 = lean_ctor_get(x_198, 1);
x_305 = lean_ctor_get(x_198, 2);
x_315 = !lean_is_exclusive(x_198);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_198, 4);
lean_dec(x_316);
x_317 = lean_ctor_get(x_198, 3);
lean_dec(x_317);
x_318 = lean_ctor_get(x_198, 0);
lean_dec(x_318);
x_306 = x_198;
x_307 = x_315;
goto block_314;
}
else
{
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_198);
x_306 = lean_box(0);
x_307 = x_315;
goto block_314;
}
block_314:
{
lean_object* x_308; 
if (x_307 == 0)
{
lean_ctor_set(x_306, 3, x_285);
lean_ctor_set(x_306, 2, x_12);
lean_ctor_set(x_306, 1, x_11);
lean_ctor_set(x_306, 0, x_199);
x_308 = x_306;
goto block_312;
}
else
{
lean_object* x_313; 
x_313 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_313, 0, x_199);
lean_ctor_set(x_313, 1, x_11);
lean_ctor_set(x_313, 2, x_12);
lean_ctor_set(x_313, 3, x_285);
lean_ctor_set(x_313, 4, x_285);
x_308 = x_313;
goto block_312;
}
block_312:
{
lean_object* x_309; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_308);
lean_ctor_set(x_196, 3, x_284);
lean_ctor_set(x_196, 2, x_305);
lean_ctor_set(x_196, 1, x_304);
lean_ctor_set(x_196, 0, x_15);
x_309 = x_196;
goto block_310;
}
else
{
lean_object* x_311; 
x_311 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_311, 0, x_15);
lean_ctor_set(x_311, 1, x_304);
lean_ctor_set(x_311, 2, x_305);
lean_ctor_set(x_311, 3, x_284);
lean_ctor_set(x_311, 4, x_308);
x_309 = x_311;
goto block_310;
}
block_310:
{
return x_309;
}
}
}
}
}
else
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_198, 4);
lean_inc(x_319);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; uint8_t x_343; 
x_320 = lean_ctor_get(x_198, 1);
x_321 = lean_ctor_get(x_198, 2);
x_343 = !lean_is_exclusive(x_198);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_198, 4);
lean_dec(x_344);
x_345 = lean_ctor_get(x_198, 3);
lean_dec(x_345);
x_346 = lean_ctor_get(x_198, 0);
lean_dec(x_346);
x_322 = x_198;
x_323 = x_343;
goto block_342;
}
else
{
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_198);
x_322 = lean_box(0);
x_323 = x_343;
goto block_342;
}
block_342:
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; uint8_t x_338; 
x_324 = lean_ctor_get(x_319, 1);
x_325 = lean_ctor_get(x_319, 2);
x_338 = !lean_is_exclusive(x_319);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_319, 4);
lean_dec(x_339);
x_340 = lean_ctor_get(x_319, 3);
lean_dec(x_340);
x_341 = lean_ctor_get(x_319, 0);
lean_dec(x_341);
x_326 = x_319;
x_327 = x_338;
goto block_337;
}
else
{
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_319);
x_326 = lean_box(0);
x_327 = x_338;
goto block_337;
}
block_337:
{
lean_object* x_328; 
if (x_327 == 0)
{
lean_ctor_set(x_326, 4, x_284);
lean_ctor_set(x_326, 3, x_284);
lean_ctor_set(x_326, 2, x_321);
lean_ctor_set(x_326, 1, x_320);
lean_ctor_set(x_326, 0, x_199);
x_328 = x_326;
goto block_335;
}
else
{
lean_object* x_336; 
x_336 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_336, 0, x_199);
lean_ctor_set(x_336, 1, x_320);
lean_ctor_set(x_336, 2, x_321);
lean_ctor_set(x_336, 3, x_284);
lean_ctor_set(x_336, 4, x_284);
x_328 = x_336;
goto block_335;
}
block_335:
{
lean_object* x_329; 
if (x_323 == 0)
{
lean_ctor_set(x_322, 4, x_284);
lean_ctor_set(x_322, 2, x_12);
lean_ctor_set(x_322, 1, x_11);
lean_ctor_set(x_322, 0, x_199);
x_329 = x_322;
goto block_333;
}
else
{
lean_object* x_334; 
x_334 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_334, 0, x_199);
lean_ctor_set(x_334, 1, x_11);
lean_ctor_set(x_334, 2, x_12);
lean_ctor_set(x_334, 3, x_284);
lean_ctor_set(x_334, 4, x_284);
x_329 = x_334;
goto block_333;
}
block_333:
{
lean_object* x_330; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_329);
lean_ctor_set(x_196, 3, x_328);
lean_ctor_set(x_196, 2, x_325);
lean_ctor_set(x_196, 1, x_324);
lean_ctor_set(x_196, 0, x_15);
x_330 = x_196;
goto block_331;
}
else
{
lean_object* x_332; 
x_332 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_332, 0, x_15);
lean_ctor_set(x_332, 1, x_324);
lean_ctor_set(x_332, 2, x_325);
lean_ctor_set(x_332, 3, x_328);
lean_ctor_set(x_332, 4, x_329);
x_330 = x_332;
goto block_331;
}
block_331:
{
return x_330;
}
}
}
}
}
}
else
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_unsigned_to_nat(2u);
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_319);
lean_ctor_set(x_196, 3, x_198);
lean_ctor_set(x_196, 0, x_347);
x_348 = x_196;
goto block_349;
}
else
{
lean_object* x_350; 
x_350 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_11);
lean_ctor_set(x_350, 2, x_12);
lean_ctor_set(x_350, 3, x_198);
lean_ctor_set(x_350, 4, x_319);
x_348 = x_350;
goto block_349;
}
block_349:
{
return x_348;
}
}
}
}
}
}
}
else
{
lean_object* x_358; 
x_358 = l_Std_DTreeMap_Internal_Impl_insertMax___redArg(x_1, x_2, x_3);
return x_358;
}
}
else
{
lean_object* x_359; 
x_359 = l_Std_DTreeMap_Internal_Impl_insertMin___redArg(x_1, x_2, x_4);
return x_359;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DTreeMap_Internal_Impl_link___redArg(x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_6(x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_1(x_2, lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_3(x_2, x_1, lean_box(0), lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_3(x_11, x_10, lean_box(0), lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_3(x_2, x_1, lean_box(0), lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_3(x_11, x_10, lean_box(0), lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 4);
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
lean_inc(x_14);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_mul(x_15, x_5);
x_17 = lean_nat_dec_lt(x_16, x_10);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_14);
x_18 = lean_nat_mul(x_15, x_10);
x_19 = lean_nat_dec_lt(x_18, x_5);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
x_22 = lean_nat_add(x_21, x_10);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
lean_ctor_set(x_23, 2, x_2);
lean_ctor_set(x_23, 3, x_3);
lean_ctor_set(x_23, 4, x_4);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; uint8_t x_197; 
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_197 = !lean_is_exclusive(x_3);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_198 = lean_ctor_get(x_3, 4);
lean_dec(x_198);
x_199 = lean_ctor_get(x_3, 3);
lean_dec(x_199);
x_200 = lean_ctor_get(x_3, 2);
lean_dec(x_200);
x_201 = lean_ctor_get(x_3, 1);
lean_dec(x_201);
x_202 = lean_ctor_get(x_3, 0);
lean_dec(x_202);
x_24 = x_3;
x_25 = x_197;
goto block_196;
}
else
{
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = x_197;
goto block_196;
}
block_196:
{
lean_object* x_26; 
x_26 = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(x_1, x_2, x_9, x_4);
if (lean_obj_tag(x_8) == 0)
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 4);
lean_inc(x_32);
x_33 = lean_nat_mul(x_15, x_27);
x_34 = lean_nat_dec_lt(x_33, x_28);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_35, x_27);
x_37 = lean_nat_add(x_36, x_28);
lean_dec(x_28);
lean_dec(x_36);
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_26);
lean_ctor_set(x_24, 0, x_37);
x_38 = x_24;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_6);
lean_ctor_set(x_40, 2, x_7);
lean_ctor_set(x_40, 3, x_8);
lean_ctor_set(x_40, 4, x_26);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
else
{
lean_object* x_41; uint8_t x_42; uint8_t x_110; 
x_110 = !lean_is_exclusive(x_26);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_26, 4);
lean_dec(x_111);
x_112 = lean_ctor_get(x_26, 3);
lean_dec(x_112);
x_113 = lean_ctor_get(x_26, 2);
lean_dec(x_113);
x_114 = lean_ctor_get(x_26, 1);
lean_dec(x_114);
x_115 = lean_ctor_get(x_26, 0);
lean_dec(x_115);
x_41 = x_26;
x_42 = x_110;
goto block_109;
}
else
{
lean_dec(x_26);
x_41 = lean_box(0);
x_42 = x_110;
goto block_109;
}
block_109:
{
if (lean_obj_tag(x_31) == 0)
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_43 = lean_ctor_get(x_31, 0);
x_44 = lean_ctor_get(x_31, 1);
x_45 = lean_ctor_get(x_31, 2);
x_46 = lean_ctor_get(x_31, 3);
x_47 = lean_ctor_get(x_31, 4);
x_48 = lean_ctor_get(x_32, 0);
x_49 = lean_unsigned_to_nat(2u);
x_50 = lean_nat_mul(x_49, x_48);
x_51 = lean_nat_dec_lt(x_43, x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; uint8_t x_80; 
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
x_80 = !lean_is_exclusive(x_31);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_31, 4);
lean_dec(x_81);
x_82 = lean_ctor_get(x_31, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_31, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_31, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_31, 0);
lean_dec(x_85);
x_52 = x_31;
x_53 = x_80;
goto block_79;
}
else
{
lean_dec(x_31);
x_52 = lean_box(0);
x_53 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_68; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_54, x_27);
x_56 = lean_nat_add(x_55, x_28);
lean_dec(x_28);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_46, 0);
lean_inc(x_77);
x_68 = x_77;
goto block_76;
}
else
{
lean_object* x_78; 
x_78 = lean_unsigned_to_nat(0u);
x_68 = x_78;
goto block_76;
}
block_67:
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_nat_add(x_57, x_59);
lean_dec(x_59);
lean_dec(x_57);
if (x_53 == 0)
{
lean_ctor_set(x_52, 4, x_32);
lean_ctor_set(x_52, 3, x_47);
lean_ctor_set(x_52, 2, x_30);
lean_ctor_set(x_52, 1, x_29);
lean_ctor_set(x_52, 0, x_60);
x_61 = x_52;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_29);
lean_ctor_set(x_66, 2, x_30);
lean_ctor_set(x_66, 3, x_47);
lean_ctor_set(x_66, 4, x_32);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
if (x_42 == 0)
{
lean_ctor_set(x_41, 4, x_61);
lean_ctor_set(x_41, 3, x_58);
lean_ctor_set(x_41, 2, x_45);
lean_ctor_set(x_41, 1, x_44);
lean_ctor_set(x_41, 0, x_56);
x_62 = x_41;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_44);
lean_ctor_set(x_64, 2, x_45);
lean_ctor_set(x_64, 3, x_58);
lean_ctor_set(x_64, 4, x_61);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
block_76:
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_nat_add(x_55, x_68);
lean_dec(x_68);
lean_dec(x_55);
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_46);
lean_ctor_set(x_24, 0, x_69);
x_70 = x_24;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_6);
lean_ctor_set(x_75, 2, x_7);
lean_ctor_set(x_75, 3, x_8);
lean_ctor_set(x_75, 4, x_46);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
x_71 = lean_nat_add(x_54, x_48);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_47, 0);
lean_inc(x_72);
x_57 = x_71;
x_58 = x_70;
x_59 = x_72;
goto block_67;
}
else
{
lean_object* x_73; 
x_73 = lean_unsigned_to_nat(0u);
x_57 = x_71;
x_58 = x_70;
x_59 = x_73;
goto block_67;
}
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_del_object(x_24);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_add(x_86, x_27);
x_88 = lean_nat_add(x_87, x_28);
lean_dec(x_28);
x_89 = lean_nat_add(x_87, x_43);
lean_dec(x_87);
lean_inc_ref(x_8);
if (x_42 == 0)
{
lean_ctor_set(x_41, 4, x_31);
lean_ctor_set(x_41, 3, x_8);
lean_ctor_set(x_41, 2, x_7);
lean_ctor_set(x_41, 1, x_6);
lean_ctor_set(x_41, 0, x_89);
x_90 = x_41;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_104, 0, x_89);
lean_ctor_set(x_104, 1, x_6);
lean_ctor_set(x_104, 2, x_7);
lean_ctor_set(x_104, 3, x_8);
lean_ctor_set(x_104, 4, x_31);
x_90 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_91; uint8_t x_92; uint8_t x_97; 
x_97 = !lean_is_exclusive(x_8);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_8, 4);
lean_dec(x_98);
x_99 = lean_ctor_get(x_8, 3);
lean_dec(x_99);
x_100 = lean_ctor_get(x_8, 2);
lean_dec(x_100);
x_101 = lean_ctor_get(x_8, 1);
lean_dec(x_101);
x_102 = lean_ctor_get(x_8, 0);
lean_dec(x_102);
x_91 = x_8;
x_92 = x_97;
goto block_96;
}
else
{
lean_dec(x_8);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
lean_ctor_set(x_91, 4, x_32);
lean_ctor_set(x_91, 3, x_90);
lean_ctor_set(x_91, 2, x_30);
lean_ctor_set(x_91, 1, x_29);
lean_ctor_set(x_91, 0, x_88);
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_29);
lean_ctor_set(x_95, 2, x_30);
lean_ctor_set(x_95, 3, x_90);
lean_ctor_set(x_95, 4, x_32);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_31);
lean_del_object(x_41);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_8);
lean_del_object(x_24);
lean_dec(x_7);
lean_dec(x_6);
x_105 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3);
x_106 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_105);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_del_object(x_41);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_8);
lean_del_object(x_24);
lean_dec(x_7);
lean_dec(x_6);
x_107 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4);
x_108 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_107);
return x_108;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_8, 0);
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_nat_add(x_117, x_116);
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_26);
lean_ctor_set(x_24, 0, x_118);
x_119 = x_24;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_6);
lean_ctor_set(x_121, 2, x_7);
lean_ctor_set(x_121, 3, x_8);
lean_ctor_set(x_121, 4, x_26);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
else
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_26, 3);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_26, 4);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_140; 
x_124 = lean_ctor_get(x_26, 0);
x_125 = lean_ctor_get(x_26, 1);
x_126 = lean_ctor_get(x_26, 2);
x_140 = !lean_is_exclusive(x_26);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_26, 4);
lean_dec(x_141);
x_142 = lean_ctor_get(x_26, 3);
lean_dec(x_142);
x_127 = x_26;
x_128 = x_140;
goto block_139;
}
else
{
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_26);
x_127 = lean_box(0);
x_128 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_122, 0);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_add(x_130, x_124);
lean_dec(x_124);
x_132 = lean_nat_add(x_130, x_129);
if (x_128 == 0)
{
lean_ctor_set(x_127, 4, x_122);
lean_ctor_set(x_127, 3, x_8);
lean_ctor_set(x_127, 2, x_7);
lean_ctor_set(x_127, 1, x_6);
lean_ctor_set(x_127, 0, x_132);
x_133 = x_127;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_138, 0, x_132);
lean_ctor_set(x_138, 1, x_6);
lean_ctor_set(x_138, 2, x_7);
lean_ctor_set(x_138, 3, x_8);
lean_ctor_set(x_138, 4, x_122);
x_133 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_134; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_123);
lean_ctor_set(x_24, 3, x_133);
lean_ctor_set(x_24, 2, x_126);
lean_ctor_set(x_24, 1, x_125);
lean_ctor_set(x_24, 0, x_131);
x_134 = x_24;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_136, 0, x_131);
lean_ctor_set(x_136, 1, x_125);
lean_ctor_set(x_136, 2, x_126);
lean_ctor_set(x_136, 3, x_133);
lean_ctor_set(x_136, 4, x_123);
x_134 = x_136;
goto block_135;
}
block_135:
{
return x_134;
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_167; 
x_143 = lean_ctor_get(x_26, 1);
x_144 = lean_ctor_get(x_26, 2);
x_167 = !lean_is_exclusive(x_26);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_26, 4);
lean_dec(x_168);
x_169 = lean_ctor_get(x_26, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_26, 0);
lean_dec(x_170);
x_145 = x_26;
x_146 = x_167;
goto block_166;
}
else
{
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_26);
x_145 = lean_box(0);
x_146 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_162; 
x_147 = lean_ctor_get(x_122, 1);
x_148 = lean_ctor_get(x_122, 2);
x_162 = !lean_is_exclusive(x_122);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_122, 4);
lean_dec(x_163);
x_164 = lean_ctor_get(x_122, 3);
lean_dec(x_164);
x_165 = lean_ctor_get(x_122, 0);
lean_dec(x_165);
x_149 = x_122;
x_150 = x_162;
goto block_161;
}
else
{
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_122);
x_149 = lean_box(0);
x_150 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_unsigned_to_nat(1u);
if (x_150 == 0)
{
lean_ctor_set(x_149, 4, x_123);
lean_ctor_set(x_149, 3, x_123);
lean_ctor_set(x_149, 2, x_7);
lean_ctor_set(x_149, 1, x_6);
lean_ctor_set(x_149, 0, x_151);
x_152 = x_149;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_160, 0, x_151);
lean_ctor_set(x_160, 1, x_6);
lean_ctor_set(x_160, 2, x_7);
lean_ctor_set(x_160, 3, x_123);
lean_ctor_set(x_160, 4, x_123);
x_152 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_153; 
if (x_146 == 0)
{
lean_ctor_set(x_145, 3, x_123);
lean_ctor_set(x_145, 0, x_151);
x_153 = x_145;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_158, 0, x_151);
lean_ctor_set(x_158, 1, x_143);
lean_ctor_set(x_158, 2, x_144);
lean_ctor_set(x_158, 3, x_123);
lean_ctor_set(x_158, 4, x_123);
x_153 = x_158;
goto block_157;
}
block_157:
{
lean_object* x_154; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_153);
lean_ctor_set(x_24, 3, x_152);
lean_ctor_set(x_24, 2, x_148);
lean_ctor_set(x_24, 1, x_147);
lean_ctor_set(x_24, 0, x_15);
x_154 = x_24;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_156, 0, x_15);
lean_ctor_set(x_156, 1, x_147);
lean_ctor_set(x_156, 2, x_148);
lean_ctor_set(x_156, 3, x_152);
lean_ctor_set(x_156, 4, x_153);
x_154 = x_156;
goto block_155;
}
block_155:
{
return x_154;
}
}
}
}
}
}
}
else
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_26, 4);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_184; 
x_172 = lean_ctor_get(x_26, 1);
x_173 = lean_ctor_get(x_26, 2);
x_184 = !lean_is_exclusive(x_26);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_26, 4);
lean_dec(x_185);
x_186 = lean_ctor_get(x_26, 3);
lean_dec(x_186);
x_187 = lean_ctor_get(x_26, 0);
lean_dec(x_187);
x_174 = x_26;
x_175 = x_184;
goto block_183;
}
else
{
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_26);
x_174 = lean_box(0);
x_175 = x_184;
goto block_183;
}
block_183:
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_unsigned_to_nat(1u);
if (x_175 == 0)
{
lean_ctor_set(x_174, 4, x_122);
lean_ctor_set(x_174, 2, x_7);
lean_ctor_set(x_174, 1, x_6);
lean_ctor_set(x_174, 0, x_176);
x_177 = x_174;
goto block_181;
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_182, 0, x_176);
lean_ctor_set(x_182, 1, x_6);
lean_ctor_set(x_182, 2, x_7);
lean_ctor_set(x_182, 3, x_122);
lean_ctor_set(x_182, 4, x_122);
x_177 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_178; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_171);
lean_ctor_set(x_24, 3, x_177);
lean_ctor_set(x_24, 2, x_173);
lean_ctor_set(x_24, 1, x_172);
lean_ctor_set(x_24, 0, x_15);
x_178 = x_24;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_180, 0, x_15);
lean_ctor_set(x_180, 1, x_172);
lean_ctor_set(x_180, 2, x_173);
lean_ctor_set(x_180, 3, x_177);
lean_ctor_set(x_180, 4, x_171);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_unsigned_to_nat(2u);
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_26);
lean_ctor_set(x_24, 3, x_171);
lean_ctor_set(x_24, 0, x_188);
x_189 = x_24;
goto block_190;
}
else
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_6);
lean_ctor_set(x_191, 2, x_7);
lean_ctor_set(x_191, 3, x_171);
lean_ctor_set(x_191, 4, x_26);
x_189 = x_191;
goto block_190;
}
block_190:
{
return x_189;
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_unsigned_to_nat(1u);
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_26);
lean_ctor_set(x_24, 3, x_26);
lean_ctor_set(x_24, 0, x_192);
x_193 = x_24;
goto block_194;
}
else
{
lean_object* x_195; 
x_195 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_6);
lean_ctor_set(x_195, 2, x_7);
lean_ctor_set(x_195, 3, x_26);
lean_ctor_set(x_195, 4, x_26);
x_193 = x_195;
goto block_194;
}
block_194:
{
return x_193;
}
}
}
}
}
}
else
{
lean_object* x_203; uint8_t x_204; uint8_t x_378; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_8);
x_378 = !lean_is_exclusive(x_4);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_379 = lean_ctor_get(x_4, 4);
lean_dec(x_379);
x_380 = lean_ctor_get(x_4, 3);
lean_dec(x_380);
x_381 = lean_ctor_get(x_4, 2);
lean_dec(x_381);
x_382 = lean_ctor_get(x_4, 1);
lean_dec(x_382);
x_383 = lean_ctor_get(x_4, 0);
lean_dec(x_383);
x_203 = x_4;
x_204 = x_378;
goto block_377;
}
else
{
lean_dec(x_4);
x_203 = lean_box(0);
x_204 = x_378;
goto block_377;
}
block_377:
{
lean_object* x_205; 
x_205 = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(x_1, x_2, x_3, x_13);
if (lean_obj_tag(x_14) == 0)
{
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_206 = lean_ctor_get(x_14, 0);
x_207 = lean_ctor_get(x_205, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_205, 2);
lean_inc(x_209);
x_210 = lean_ctor_get(x_205, 3);
lean_inc(x_210);
x_211 = lean_ctor_get(x_205, 4);
lean_inc(x_211);
x_212 = lean_nat_mul(x_15, x_206);
x_213 = lean_nat_dec_lt(x_212, x_207);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
x_214 = lean_unsigned_to_nat(1u);
x_215 = lean_nat_add(x_214, x_207);
lean_dec(x_207);
x_216 = lean_nat_add(x_215, x_206);
lean_dec(x_215);
if (x_204 == 0)
{
lean_ctor_set(x_203, 3, x_205);
lean_ctor_set(x_203, 0, x_216);
x_217 = x_203;
goto block_218;
}
else
{
lean_object* x_219; 
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_11);
lean_ctor_set(x_219, 2, x_12);
lean_ctor_set(x_219, 3, x_205);
lean_ctor_set(x_219, 4, x_14);
x_217 = x_219;
goto block_218;
}
block_218:
{
return x_217;
}
}
else
{
lean_object* x_220; uint8_t x_221; uint8_t x_291; 
x_291 = !lean_is_exclusive(x_205);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_292 = lean_ctor_get(x_205, 4);
lean_dec(x_292);
x_293 = lean_ctor_get(x_205, 3);
lean_dec(x_293);
x_294 = lean_ctor_get(x_205, 2);
lean_dec(x_294);
x_295 = lean_ctor_get(x_205, 1);
lean_dec(x_295);
x_296 = lean_ctor_get(x_205, 0);
lean_dec(x_296);
x_220 = x_205;
x_221 = x_291;
goto block_290;
}
else
{
lean_dec(x_205);
x_220 = lean_box(0);
x_221 = x_291;
goto block_290;
}
block_290:
{
if (lean_obj_tag(x_210) == 0)
{
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_222 = lean_ctor_get(x_210, 0);
x_223 = lean_ctor_get(x_211, 0);
x_224 = lean_ctor_get(x_211, 1);
x_225 = lean_ctor_get(x_211, 2);
x_226 = lean_ctor_get(x_211, 3);
x_227 = lean_ctor_get(x_211, 4);
x_228 = lean_unsigned_to_nat(2u);
x_229 = lean_nat_mul(x_228, x_222);
x_230 = lean_nat_dec_lt(x_223, x_229);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; uint8_t x_232; uint8_t x_260; 
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
x_260 = !lean_is_exclusive(x_211);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_261 = lean_ctor_get(x_211, 4);
lean_dec(x_261);
x_262 = lean_ctor_get(x_211, 3);
lean_dec(x_262);
x_263 = lean_ctor_get(x_211, 2);
lean_dec(x_263);
x_264 = lean_ctor_get(x_211, 1);
lean_dec(x_264);
x_265 = lean_ctor_get(x_211, 0);
lean_dec(x_265);
x_231 = x_211;
x_232 = x_260;
goto block_259;
}
else
{
lean_dec(x_211);
x_231 = lean_box(0);
x_232 = x_260;
goto block_259;
}
block_259:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_247; lean_object* x_248; 
x_233 = lean_unsigned_to_nat(1u);
x_234 = lean_nat_add(x_233, x_207);
lean_dec(x_207);
x_235 = lean_nat_add(x_234, x_206);
lean_dec(x_234);
x_247 = lean_nat_add(x_233, x_222);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_226, 0);
lean_inc(x_257);
x_248 = x_257;
goto block_256;
}
else
{
lean_object* x_258; 
x_258 = lean_unsigned_to_nat(0u);
x_248 = x_258;
goto block_256;
}
block_246:
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_nat_add(x_237, x_238);
lean_dec(x_238);
lean_dec(x_237);
if (x_232 == 0)
{
lean_ctor_set(x_231, 4, x_14);
lean_ctor_set(x_231, 3, x_227);
lean_ctor_set(x_231, 2, x_12);
lean_ctor_set(x_231, 1, x_11);
lean_ctor_set(x_231, 0, x_239);
x_240 = x_231;
goto block_244;
}
else
{
lean_object* x_245; 
x_245 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_245, 0, x_239);
lean_ctor_set(x_245, 1, x_11);
lean_ctor_set(x_245, 2, x_12);
lean_ctor_set(x_245, 3, x_227);
lean_ctor_set(x_245, 4, x_14);
x_240 = x_245;
goto block_244;
}
block_244:
{
lean_object* x_241; 
if (x_221 == 0)
{
lean_ctor_set(x_220, 4, x_240);
lean_ctor_set(x_220, 3, x_236);
lean_ctor_set(x_220, 2, x_225);
lean_ctor_set(x_220, 1, x_224);
lean_ctor_set(x_220, 0, x_235);
x_241 = x_220;
goto block_242;
}
else
{
lean_object* x_243; 
x_243 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_243, 0, x_235);
lean_ctor_set(x_243, 1, x_224);
lean_ctor_set(x_243, 2, x_225);
lean_ctor_set(x_243, 3, x_236);
lean_ctor_set(x_243, 4, x_240);
x_241 = x_243;
goto block_242;
}
block_242:
{
return x_241;
}
}
}
block_256:
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_nat_add(x_247, x_248);
lean_dec(x_248);
lean_dec(x_247);
if (x_204 == 0)
{
lean_ctor_set(x_203, 4, x_226);
lean_ctor_set(x_203, 3, x_210);
lean_ctor_set(x_203, 2, x_209);
lean_ctor_set(x_203, 1, x_208);
lean_ctor_set(x_203, 0, x_249);
x_250 = x_203;
goto block_254;
}
else
{
lean_object* x_255; 
x_255 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_255, 0, x_249);
lean_ctor_set(x_255, 1, x_208);
lean_ctor_set(x_255, 2, x_209);
lean_ctor_set(x_255, 3, x_210);
lean_ctor_set(x_255, 4, x_226);
x_250 = x_255;
goto block_254;
}
block_254:
{
lean_object* x_251; 
x_251 = lean_nat_add(x_233, x_206);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_227, 0);
lean_inc(x_252);
x_236 = x_250;
x_237 = x_251;
x_238 = x_252;
goto block_246;
}
else
{
lean_object* x_253; 
x_253 = lean_unsigned_to_nat(0u);
x_236 = x_250;
x_237 = x_251;
x_238 = x_253;
goto block_246;
}
}
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_del_object(x_203);
x_266 = lean_unsigned_to_nat(1u);
x_267 = lean_nat_add(x_266, x_207);
lean_dec(x_207);
x_268 = lean_nat_add(x_267, x_206);
lean_dec(x_267);
x_269 = lean_nat_add(x_266, x_206);
x_270 = lean_nat_add(x_269, x_223);
lean_dec(x_269);
lean_inc_ref(x_14);
if (x_221 == 0)
{
lean_ctor_set(x_220, 4, x_14);
lean_ctor_set(x_220, 3, x_211);
lean_ctor_set(x_220, 2, x_12);
lean_ctor_set(x_220, 1, x_11);
lean_ctor_set(x_220, 0, x_270);
x_271 = x_220;
goto block_284;
}
else
{
lean_object* x_285; 
x_285 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_285, 0, x_270);
lean_ctor_set(x_285, 1, x_11);
lean_ctor_set(x_285, 2, x_12);
lean_ctor_set(x_285, 3, x_211);
lean_ctor_set(x_285, 4, x_14);
x_271 = x_285;
goto block_284;
}
block_284:
{
lean_object* x_272; uint8_t x_273; uint8_t x_278; 
x_278 = !lean_is_exclusive(x_14);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_ctor_get(x_14, 4);
lean_dec(x_279);
x_280 = lean_ctor_get(x_14, 3);
lean_dec(x_280);
x_281 = lean_ctor_get(x_14, 2);
lean_dec(x_281);
x_282 = lean_ctor_get(x_14, 1);
lean_dec(x_282);
x_283 = lean_ctor_get(x_14, 0);
lean_dec(x_283);
x_272 = x_14;
x_273 = x_278;
goto block_277;
}
else
{
lean_dec(x_14);
x_272 = lean_box(0);
x_273 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_274; 
if (x_273 == 0)
{
lean_ctor_set(x_272, 4, x_271);
lean_ctor_set(x_272, 3, x_210);
lean_ctor_set(x_272, 2, x_209);
lean_ctor_set(x_272, 1, x_208);
lean_ctor_set(x_272, 0, x_268);
x_274 = x_272;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_276, 0, x_268);
lean_ctor_set(x_276, 1, x_208);
lean_ctor_set(x_276, 2, x_209);
lean_ctor_set(x_276, 3, x_210);
lean_ctor_set(x_276, 4, x_271);
x_274 = x_276;
goto block_275;
}
block_275:
{
return x_274;
}
}
}
}
}
else
{
lean_object* x_286; lean_object* x_287; 
lean_dec_ref(x_210);
lean_del_object(x_220);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec_ref(x_14);
lean_del_object(x_203);
lean_dec(x_12);
lean_dec(x_11);
x_286 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2);
x_287 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_286);
return x_287;
}
}
else
{
lean_object* x_288; lean_object* x_289; 
lean_del_object(x_220);
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec_ref(x_14);
lean_del_object(x_203);
lean_dec(x_12);
lean_dec(x_11);
x_288 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3);
x_289 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_288);
return x_289;
}
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_14, 0);
x_298 = lean_unsigned_to_nat(1u);
x_299 = lean_nat_add(x_298, x_297);
if (x_204 == 0)
{
lean_ctor_set(x_203, 3, x_205);
lean_ctor_set(x_203, 0, x_299);
x_300 = x_203;
goto block_301;
}
else
{
lean_object* x_302; 
x_302 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_11);
lean_ctor_set(x_302, 2, x_12);
lean_ctor_set(x_302, 3, x_205);
lean_ctor_set(x_302, 4, x_14);
x_300 = x_302;
goto block_301;
}
block_301:
{
return x_300;
}
}
}
else
{
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_303; 
x_303 = lean_ctor_get(x_205, 3);
lean_inc(x_303);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; 
x_304 = lean_ctor_get(x_205, 4);
lean_inc(x_304);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; uint8_t x_321; 
x_305 = lean_ctor_get(x_205, 0);
x_306 = lean_ctor_get(x_205, 1);
x_307 = lean_ctor_get(x_205, 2);
x_321 = !lean_is_exclusive(x_205);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_205, 4);
lean_dec(x_322);
x_323 = lean_ctor_get(x_205, 3);
lean_dec(x_323);
x_308 = x_205;
x_309 = x_321;
goto block_320;
}
else
{
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_205);
x_308 = lean_box(0);
x_309 = x_321;
goto block_320;
}
block_320:
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_310 = lean_ctor_get(x_304, 0);
x_311 = lean_unsigned_to_nat(1u);
x_312 = lean_nat_add(x_311, x_305);
lean_dec(x_305);
x_313 = lean_nat_add(x_311, x_310);
if (x_309 == 0)
{
lean_ctor_set(x_308, 4, x_14);
lean_ctor_set(x_308, 3, x_304);
lean_ctor_set(x_308, 2, x_12);
lean_ctor_set(x_308, 1, x_11);
lean_ctor_set(x_308, 0, x_313);
x_314 = x_308;
goto block_318;
}
else
{
lean_object* x_319; 
x_319 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_319, 0, x_313);
lean_ctor_set(x_319, 1, x_11);
lean_ctor_set(x_319, 2, x_12);
lean_ctor_set(x_319, 3, x_304);
lean_ctor_set(x_319, 4, x_14);
x_314 = x_319;
goto block_318;
}
block_318:
{
lean_object* x_315; 
if (x_204 == 0)
{
lean_ctor_set(x_203, 4, x_314);
lean_ctor_set(x_203, 3, x_303);
lean_ctor_set(x_203, 2, x_307);
lean_ctor_set(x_203, 1, x_306);
lean_ctor_set(x_203, 0, x_312);
x_315 = x_203;
goto block_316;
}
else
{
lean_object* x_317; 
x_317 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_317, 0, x_312);
lean_ctor_set(x_317, 1, x_306);
lean_ctor_set(x_317, 2, x_307);
lean_ctor_set(x_317, 3, x_303);
lean_ctor_set(x_317, 4, x_314);
x_315 = x_317;
goto block_316;
}
block_316:
{
return x_315;
}
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; uint8_t x_336; 
x_324 = lean_ctor_get(x_205, 1);
x_325 = lean_ctor_get(x_205, 2);
x_336 = !lean_is_exclusive(x_205);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_205, 4);
lean_dec(x_337);
x_338 = lean_ctor_get(x_205, 3);
lean_dec(x_338);
x_339 = lean_ctor_get(x_205, 0);
lean_dec(x_339);
x_326 = x_205;
x_327 = x_336;
goto block_335;
}
else
{
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_205);
x_326 = lean_box(0);
x_327 = x_336;
goto block_335;
}
block_335:
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_unsigned_to_nat(1u);
if (x_327 == 0)
{
lean_ctor_set(x_326, 3, x_304);
lean_ctor_set(x_326, 2, x_12);
lean_ctor_set(x_326, 1, x_11);
lean_ctor_set(x_326, 0, x_328);
x_329 = x_326;
goto block_333;
}
else
{
lean_object* x_334; 
x_334 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_334, 0, x_328);
lean_ctor_set(x_334, 1, x_11);
lean_ctor_set(x_334, 2, x_12);
lean_ctor_set(x_334, 3, x_304);
lean_ctor_set(x_334, 4, x_304);
x_329 = x_334;
goto block_333;
}
block_333:
{
lean_object* x_330; 
if (x_204 == 0)
{
lean_ctor_set(x_203, 4, x_329);
lean_ctor_set(x_203, 3, x_303);
lean_ctor_set(x_203, 2, x_325);
lean_ctor_set(x_203, 1, x_324);
lean_ctor_set(x_203, 0, x_15);
x_330 = x_203;
goto block_331;
}
else
{
lean_object* x_332; 
x_332 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_332, 0, x_15);
lean_ctor_set(x_332, 1, x_324);
lean_ctor_set(x_332, 2, x_325);
lean_ctor_set(x_332, 3, x_303);
lean_ctor_set(x_332, 4, x_329);
x_330 = x_332;
goto block_331;
}
block_331:
{
return x_330;
}
}
}
}
}
else
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_205, 4);
lean_inc(x_340);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; uint8_t x_365; 
x_341 = lean_ctor_get(x_205, 1);
x_342 = lean_ctor_get(x_205, 2);
x_365 = !lean_is_exclusive(x_205);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_205, 4);
lean_dec(x_366);
x_367 = lean_ctor_get(x_205, 3);
lean_dec(x_367);
x_368 = lean_ctor_get(x_205, 0);
lean_dec(x_368);
x_343 = x_205;
x_344 = x_365;
goto block_364;
}
else
{
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_205);
x_343 = lean_box(0);
x_344 = x_365;
goto block_364;
}
block_364:
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; uint8_t x_360; 
x_345 = lean_ctor_get(x_340, 1);
x_346 = lean_ctor_get(x_340, 2);
x_360 = !lean_is_exclusive(x_340);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_340, 4);
lean_dec(x_361);
x_362 = lean_ctor_get(x_340, 3);
lean_dec(x_362);
x_363 = lean_ctor_get(x_340, 0);
lean_dec(x_363);
x_347 = x_340;
x_348 = x_360;
goto block_359;
}
else
{
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_340);
x_347 = lean_box(0);
x_348 = x_360;
goto block_359;
}
block_359:
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_unsigned_to_nat(1u);
if (x_348 == 0)
{
lean_ctor_set(x_347, 4, x_303);
lean_ctor_set(x_347, 3, x_303);
lean_ctor_set(x_347, 2, x_342);
lean_ctor_set(x_347, 1, x_341);
lean_ctor_set(x_347, 0, x_349);
x_350 = x_347;
goto block_357;
}
else
{
lean_object* x_358; 
x_358 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_358, 0, x_349);
lean_ctor_set(x_358, 1, x_341);
lean_ctor_set(x_358, 2, x_342);
lean_ctor_set(x_358, 3, x_303);
lean_ctor_set(x_358, 4, x_303);
x_350 = x_358;
goto block_357;
}
block_357:
{
lean_object* x_351; 
if (x_344 == 0)
{
lean_ctor_set(x_343, 4, x_303);
lean_ctor_set(x_343, 2, x_12);
lean_ctor_set(x_343, 1, x_11);
lean_ctor_set(x_343, 0, x_349);
x_351 = x_343;
goto block_355;
}
else
{
lean_object* x_356; 
x_356 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_356, 0, x_349);
lean_ctor_set(x_356, 1, x_11);
lean_ctor_set(x_356, 2, x_12);
lean_ctor_set(x_356, 3, x_303);
lean_ctor_set(x_356, 4, x_303);
x_351 = x_356;
goto block_355;
}
block_355:
{
lean_object* x_352; 
if (x_204 == 0)
{
lean_ctor_set(x_203, 4, x_351);
lean_ctor_set(x_203, 3, x_350);
lean_ctor_set(x_203, 2, x_346);
lean_ctor_set(x_203, 1, x_345);
lean_ctor_set(x_203, 0, x_15);
x_352 = x_203;
goto block_353;
}
else
{
lean_object* x_354; 
x_354 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_354, 0, x_15);
lean_ctor_set(x_354, 1, x_345);
lean_ctor_set(x_354, 2, x_346);
lean_ctor_set(x_354, 3, x_350);
lean_ctor_set(x_354, 4, x_351);
x_352 = x_354;
goto block_353;
}
block_353:
{
return x_352;
}
}
}
}
}
}
else
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_unsigned_to_nat(2u);
if (x_204 == 0)
{
lean_ctor_set(x_203, 4, x_340);
lean_ctor_set(x_203, 3, x_205);
lean_ctor_set(x_203, 0, x_369);
x_370 = x_203;
goto block_371;
}
else
{
lean_object* x_372; 
x_372 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_11);
lean_ctor_set(x_372, 2, x_12);
lean_ctor_set(x_372, 3, x_205);
lean_ctor_set(x_372, 4, x_340);
x_370 = x_372;
goto block_371;
}
block_371:
{
return x_370;
}
}
}
}
else
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_unsigned_to_nat(1u);
if (x_204 == 0)
{
lean_ctor_set(x_203, 4, x_205);
lean_ctor_set(x_203, 3, x_205);
lean_ctor_set(x_203, 0, x_373);
x_374 = x_203;
goto block_375;
}
else
{
lean_object* x_376; 
x_376 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_376, 0, x_373);
lean_ctor_set(x_376, 1, x_11);
lean_ctor_set(x_376, 2, x_12);
lean_ctor_set(x_376, 3, x_205);
lean_ctor_set(x_376, 4, x_205);
x_374 = x_376;
goto block_375;
}
block_375:
{
return x_374;
}
}
}
}
}
}
else
{
lean_object* x_384; 
x_384 = l_Std_DTreeMap_Internal_Impl_insertMax_x21___redArg(x_1, x_2, x_3);
return x_384;
}
}
else
{
lean_object* x_385; 
x_385 = l_Std_DTreeMap_Internal_Impl_insertMin_x21___redArg(x_1, x_2, x_4);
return x_385;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_apply_5(x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_5, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 4);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_nat_mul(x_13, x_3);
x_15 = lean_nat_dec_lt(x_14, x_8);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_nat_mul(x_13, x_8);
x_17 = lean_nat_dec_lt(x_16, x_3);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_3, x_8);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; uint8_t x_157; 
lean_inc(x_5);
lean_inc(x_4);
x_157 = !lean_is_exclusive(x_1);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_1, 4);
lean_dec(x_158);
x_159 = lean_ctor_get(x_1, 3);
lean_dec(x_159);
x_160 = lean_ctor_get(x_1, 2);
lean_dec(x_160);
x_161 = lean_ctor_get(x_1, 1);
lean_dec(x_161);
x_162 = lean_ctor_get(x_1, 0);
lean_dec(x_162);
x_19 = x_1;
x_20 = x_157;
goto block_156;
}
else
{
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_4, x_5, x_6, x_7);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_nat_mul(x_13, x_25);
x_27 = lean_nat_dec_lt(x_26, x_8);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
lean_dec(x_11);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_28, x_25);
x_30 = lean_nat_add(x_29, x_8);
lean_dec(x_29);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_2);
lean_ctor_set(x_19, 3, x_22);
lean_ctor_set(x_19, 2, x_24);
lean_ctor_set(x_19, 1, x_23);
lean_ctor_set(x_19, 0, x_30);
x_31 = x_19;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_23);
lean_ctor_set(x_33, 2, x_24);
lean_ctor_set(x_33, 3, x_22);
lean_ctor_set(x_33, 4, x_2);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
else
{
lean_object* x_34; uint8_t x_35; uint8_t x_90; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_90 = !lean_is_exclusive(x_2);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_2, 4);
lean_dec(x_91);
x_92 = lean_ctor_get(x_2, 3);
lean_dec(x_92);
x_93 = lean_ctor_get(x_2, 2);
lean_dec(x_93);
x_94 = lean_ctor_get(x_2, 1);
lean_dec(x_94);
x_95 = lean_ctor_get(x_2, 0);
lean_dec(x_95);
x_34 = x_2;
x_35 = x_90;
goto block_89;
}
else
{
lean_dec(x_2);
x_34 = lean_box(0);
x_35 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
x_38 = lean_ctor_get(x_11, 2);
x_39 = lean_ctor_get(x_11, 3);
x_40 = lean_ctor_get(x_11, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_unsigned_to_nat(2u);
x_43 = lean_nat_mul(x_42, x_41);
x_44 = lean_nat_dec_lt(x_36, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; uint8_t x_73; 
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
x_73 = !lean_is_exclusive(x_11);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_11, 4);
lean_dec(x_74);
x_75 = lean_ctor_get(x_11, 3);
lean_dec(x_75);
x_76 = lean_ctor_get(x_11, 2);
lean_dec(x_76);
x_77 = lean_ctor_get(x_11, 1);
lean_dec(x_77);
x_78 = lean_ctor_get(x_11, 0);
lean_dec(x_78);
x_45 = x_11;
x_46 = x_73;
goto block_72;
}
else
{
lean_dec(x_11);
x_45 = lean_box(0);
x_46 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_61; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_47, x_25);
x_49 = lean_nat_add(x_48, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_39, 0);
lean_inc(x_70);
x_61 = x_70;
goto block_69;
}
else
{
lean_object* x_71; 
x_71 = lean_unsigned_to_nat(0u);
x_61 = x_71;
goto block_69;
}
block_60:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_nat_add(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
if (x_46 == 0)
{
lean_ctor_set(x_45, 4, x_12);
lean_ctor_set(x_45, 3, x_40);
lean_ctor_set(x_45, 2, x_10);
lean_ctor_set(x_45, 1, x_9);
lean_ctor_set(x_45, 0, x_53);
x_54 = x_45;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_9);
lean_ctor_set(x_59, 2, x_10);
lean_ctor_set(x_59, 3, x_40);
lean_ctor_set(x_59, 4, x_12);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 4, x_54);
lean_ctor_set(x_34, 3, x_50);
lean_ctor_set(x_34, 2, x_38);
lean_ctor_set(x_34, 1, x_37);
lean_ctor_set(x_34, 0, x_49);
x_55 = x_34;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_37);
lean_ctor_set(x_57, 2, x_38);
lean_ctor_set(x_57, 3, x_50);
lean_ctor_set(x_57, 4, x_54);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
block_69:
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_nat_add(x_48, x_61);
lean_dec(x_61);
lean_dec(x_48);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_39);
lean_ctor_set(x_19, 3, x_22);
lean_ctor_set(x_19, 2, x_24);
lean_ctor_set(x_19, 1, x_23);
lean_ctor_set(x_19, 0, x_62);
x_63 = x_19;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_23);
lean_ctor_set(x_68, 2, x_24);
lean_ctor_set(x_68, 3, x_22);
lean_ctor_set(x_68, 4, x_39);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
x_64 = lean_nat_add(x_47, x_41);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_40, 0);
lean_inc(x_65);
x_50 = x_63;
x_51 = x_64;
x_52 = x_65;
goto block_60;
}
else
{
lean_object* x_66; 
x_66 = lean_unsigned_to_nat(0u);
x_50 = x_63;
x_51 = x_64;
x_52 = x_66;
goto block_60;
}
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_79, x_25);
x_81 = lean_nat_add(x_80, x_8);
lean_dec(x_8);
x_82 = lean_nat_add(x_80, x_36);
lean_dec(x_80);
if (x_35 == 0)
{
lean_ctor_set(x_34, 4, x_11);
lean_ctor_set(x_34, 3, x_22);
lean_ctor_set(x_34, 2, x_24);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 0, x_82);
x_83 = x_34;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_23);
lean_ctor_set(x_88, 2, x_24);
lean_ctor_set(x_88, 3, x_22);
lean_ctor_set(x_88, 4, x_11);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_12);
lean_ctor_set(x_19, 3, x_83);
lean_ctor_set(x_19, 2, x_10);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 0, x_81);
x_84 = x_19;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_9);
lean_ctor_set(x_86, 2, x_10);
lean_ctor_set(x_86, 3, x_83);
lean_ctor_set(x_86, 4, x_12);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
}
}
else
{
lean_object* x_96; uint8_t x_97; uint8_t x_150; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_150 = !lean_is_exclusive(x_2);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_2, 4);
lean_dec(x_151);
x_152 = lean_ctor_get(x_2, 3);
lean_dec(x_152);
x_153 = lean_ctor_get(x_2, 2);
lean_dec(x_153);
x_154 = lean_ctor_get(x_2, 1);
lean_dec(x_154);
x_155 = lean_ctor_get(x_2, 0);
lean_dec(x_155);
x_96 = x_2;
x_97 = x_150;
goto block_149;
}
else
{
lean_dec(x_2);
x_96 = lean_box(0);
x_97 = x_150;
goto block_149;
}
block_149:
{
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_21, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_21, 1);
lean_inc(x_99);
lean_dec_ref(x_21);
x_100 = lean_ctor_get(x_11, 0);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_add(x_101, x_8);
lean_dec(x_8);
x_103 = lean_nat_add(x_101, x_100);
if (x_97 == 0)
{
lean_ctor_set(x_96, 4, x_11);
lean_ctor_set(x_96, 3, x_22);
lean_ctor_set(x_96, 2, x_99);
lean_ctor_set(x_96, 1, x_98);
lean_ctor_set(x_96, 0, x_103);
x_104 = x_96;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_103);
lean_ctor_set(x_109, 1, x_98);
lean_ctor_set(x_109, 2, x_99);
lean_ctor_set(x_109, 3, x_22);
lean_ctor_set(x_109, 4, x_11);
x_104 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_105; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_12);
lean_ctor_set(x_19, 3, x_104);
lean_ctor_set(x_19, 2, x_10);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 0, x_102);
x_105 = x_19;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_107, 0, x_102);
lean_ctor_set(x_107, 1, x_9);
lean_ctor_set(x_107, 2, x_10);
lean_ctor_set(x_107, 3, x_104);
lean_ctor_set(x_107, 4, x_12);
x_105 = x_107;
goto block_106;
}
block_106:
{
return x_105;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_127; 
lean_dec(x_8);
x_110 = lean_ctor_get(x_21, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_21, 1);
lean_inc(x_111);
lean_dec_ref(x_21);
x_112 = lean_ctor_get(x_11, 1);
x_113 = lean_ctor_get(x_11, 2);
x_127 = !lean_is_exclusive(x_11);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_11, 4);
lean_dec(x_128);
x_129 = lean_ctor_get(x_11, 3);
lean_dec(x_129);
x_130 = lean_ctor_get(x_11, 0);
lean_dec(x_130);
x_114 = x_11;
x_115 = x_127;
goto block_126;
}
else
{
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_11);
x_114 = lean_box(0);
x_115 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_unsigned_to_nat(1u);
if (x_115 == 0)
{
lean_ctor_set(x_114, 4, x_12);
lean_ctor_set(x_114, 3, x_12);
lean_ctor_set(x_114, 2, x_111);
lean_ctor_set(x_114, 1, x_110);
lean_ctor_set(x_114, 0, x_116);
x_117 = x_114;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_125, 0, x_116);
lean_ctor_set(x_125, 1, x_110);
lean_ctor_set(x_125, 2, x_111);
lean_ctor_set(x_125, 3, x_12);
lean_ctor_set(x_125, 4, x_12);
x_117 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_118; 
if (x_97 == 0)
{
lean_ctor_set(x_96, 3, x_12);
lean_ctor_set(x_96, 0, x_116);
x_118 = x_96;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_123, 0, x_116);
lean_ctor_set(x_123, 1, x_9);
lean_ctor_set(x_123, 2, x_10);
lean_ctor_set(x_123, 3, x_12);
lean_ctor_set(x_123, 4, x_12);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_118);
lean_ctor_set(x_19, 3, x_117);
lean_ctor_set(x_19, 2, x_113);
lean_ctor_set(x_19, 1, x_112);
lean_ctor_set(x_19, 0, x_13);
x_119 = x_19;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_121, 0, x_13);
lean_ctor_set(x_121, 1, x_112);
lean_ctor_set(x_121, 2, x_113);
lean_ctor_set(x_121, 3, x_117);
lean_ctor_set(x_121, 4, x_118);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_8);
x_131 = lean_ctor_get(x_21, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_21, 1);
lean_inc(x_132);
lean_dec_ref(x_21);
x_133 = lean_unsigned_to_nat(1u);
if (x_97 == 0)
{
lean_ctor_set(x_96, 4, x_11);
lean_ctor_set(x_96, 2, x_132);
lean_ctor_set(x_96, 1, x_131);
lean_ctor_set(x_96, 0, x_133);
x_134 = x_96;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_139, 2, x_132);
lean_ctor_set(x_139, 3, x_11);
lean_ctor_set(x_139, 4, x_11);
x_134 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_135; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_12);
lean_ctor_set(x_19, 3, x_134);
lean_ctor_set(x_19, 2, x_10);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 0, x_13);
x_135 = x_19;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_137, 0, x_13);
lean_ctor_set(x_137, 1, x_9);
lean_ctor_set(x_137, 2, x_10);
lean_ctor_set(x_137, 3, x_134);
lean_ctor_set(x_137, 4, x_12);
x_135 = x_137;
goto block_136;
}
block_136:
{
return x_135;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_21, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_21, 1);
lean_inc(x_141);
lean_dec_ref(x_21);
if (x_97 == 0)
{
lean_ctor_set(x_96, 3, x_12);
x_142 = x_96;
goto block_147;
}
else
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_148, 0, x_8);
lean_ctor_set(x_148, 1, x_9);
lean_ctor_set(x_148, 2, x_10);
lean_ctor_set(x_148, 3, x_12);
lean_ctor_set(x_148, 4, x_12);
x_142 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_unsigned_to_nat(2u);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_142);
lean_ctor_set(x_19, 3, x_12);
lean_ctor_set(x_19, 2, x_141);
lean_ctor_set(x_19, 1, x_140);
lean_ctor_set(x_19, 0, x_143);
x_144 = x_19;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_140);
lean_ctor_set(x_146, 2, x_141);
lean_ctor_set(x_146, 3, x_12);
lean_ctor_set(x_146, 4, x_142);
x_144 = x_146;
goto block_145;
}
block_145:
{
return x_144;
}
}
}
}
}
}
}
}
else
{
lean_object* x_163; uint8_t x_164; uint8_t x_318; 
lean_inc(x_10);
lean_inc(x_9);
x_318 = !lean_is_exclusive(x_2);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_319 = lean_ctor_get(x_2, 4);
lean_dec(x_319);
x_320 = lean_ctor_get(x_2, 3);
lean_dec(x_320);
x_321 = lean_ctor_get(x_2, 2);
lean_dec(x_321);
x_322 = lean_ctor_get(x_2, 1);
lean_dec(x_322);
x_323 = lean_ctor_get(x_2, 0);
lean_dec(x_323);
x_163 = x_2;
x_164 = x_318;
goto block_317;
}
else
{
lean_dec(x_2);
x_163 = lean_box(0);
x_164 = x_318;
goto block_317;
}
block_317:
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_9, x_10, x_11, x_12);
x_166 = lean_ctor_get(x_165, 2);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec_ref(x_165);
x_169 = lean_ctor_get(x_166, 0);
x_170 = lean_nat_mul(x_13, x_169);
x_171 = lean_nat_dec_lt(x_170, x_3);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_7);
lean_dec(x_6);
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_nat_add(x_172, x_3);
x_174 = lean_nat_add(x_173, x_169);
lean_dec(x_173);
if (x_164 == 0)
{
lean_ctor_set(x_163, 4, x_166);
lean_ctor_set(x_163, 3, x_1);
lean_ctor_set(x_163, 2, x_168);
lean_ctor_set(x_163, 1, x_167);
lean_ctor_set(x_163, 0, x_174);
x_175 = x_163;
goto block_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_167);
lean_ctor_set(x_177, 2, x_168);
lean_ctor_set(x_177, 3, x_1);
lean_ctor_set(x_177, 4, x_166);
x_175 = x_177;
goto block_176;
}
block_176:
{
return x_175;
}
}
else
{
lean_object* x_178; uint8_t x_179; uint8_t x_245; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_245 = !lean_is_exclusive(x_1);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_246 = lean_ctor_get(x_1, 4);
lean_dec(x_246);
x_247 = lean_ctor_get(x_1, 3);
lean_dec(x_247);
x_248 = lean_ctor_get(x_1, 2);
lean_dec(x_248);
x_249 = lean_ctor_get(x_1, 1);
lean_dec(x_249);
x_250 = lean_ctor_get(x_1, 0);
lean_dec(x_250);
x_178 = x_1;
x_179 = x_245;
goto block_244;
}
else
{
lean_dec(x_1);
x_178 = lean_box(0);
x_179 = x_245;
goto block_244;
}
block_244:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_180 = lean_ctor_get(x_6, 0);
x_181 = lean_ctor_get(x_7, 0);
x_182 = lean_ctor_get(x_7, 1);
x_183 = lean_ctor_get(x_7, 2);
x_184 = lean_ctor_get(x_7, 3);
x_185 = lean_ctor_get(x_7, 4);
x_186 = lean_unsigned_to_nat(2u);
x_187 = lean_nat_mul(x_186, x_180);
x_188 = lean_nat_dec_lt(x_181, x_187);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; uint8_t x_190; uint8_t x_227; 
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_del_object(x_178);
x_227 = !lean_is_exclusive(x_7);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_228 = lean_ctor_get(x_7, 4);
lean_dec(x_228);
x_229 = lean_ctor_get(x_7, 3);
lean_dec(x_229);
x_230 = lean_ctor_get(x_7, 2);
lean_dec(x_230);
x_231 = lean_ctor_get(x_7, 1);
lean_dec(x_231);
x_232 = lean_ctor_get(x_7, 0);
lean_dec(x_232);
x_189 = x_7;
x_190 = x_227;
goto block_226;
}
else
{
lean_dec(x_7);
x_189 = lean_box(0);
x_190 = x_227;
goto block_226;
}
block_226:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_214; lean_object* x_215; 
x_191 = lean_unsigned_to_nat(1u);
x_192 = lean_nat_add(x_191, x_3);
lean_dec(x_3);
x_193 = lean_nat_add(x_192, x_169);
lean_dec(x_192);
x_214 = lean_nat_add(x_191, x_180);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_184, 0);
lean_inc(x_224);
x_215 = x_224;
goto block_223;
}
else
{
lean_object* x_225; 
x_225 = lean_unsigned_to_nat(0u);
x_215 = x_225;
goto block_223;
}
block_213:
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_nat_add(x_195, x_196);
lean_dec(x_196);
lean_dec(x_195);
lean_inc_ref(x_166);
if (x_190 == 0)
{
lean_ctor_set(x_189, 4, x_166);
lean_ctor_set(x_189, 3, x_185);
lean_ctor_set(x_189, 2, x_168);
lean_ctor_set(x_189, 1, x_167);
lean_ctor_set(x_189, 0, x_197);
x_198 = x_189;
goto block_211;
}
else
{
lean_object* x_212; 
x_212 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_212, 0, x_197);
lean_ctor_set(x_212, 1, x_167);
lean_ctor_set(x_212, 2, x_168);
lean_ctor_set(x_212, 3, x_185);
lean_ctor_set(x_212, 4, x_166);
x_198 = x_212;
goto block_211;
}
block_211:
{
lean_object* x_199; uint8_t x_200; uint8_t x_205; 
x_205 = !lean_is_exclusive(x_166);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_166, 4);
lean_dec(x_206);
x_207 = lean_ctor_get(x_166, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_166, 2);
lean_dec(x_208);
x_209 = lean_ctor_get(x_166, 1);
lean_dec(x_209);
x_210 = lean_ctor_get(x_166, 0);
lean_dec(x_210);
x_199 = x_166;
x_200 = x_205;
goto block_204;
}
else
{
lean_dec(x_166);
x_199 = lean_box(0);
x_200 = x_205;
goto block_204;
}
block_204:
{
lean_object* x_201; 
if (x_200 == 0)
{
lean_ctor_set(x_199, 4, x_198);
lean_ctor_set(x_199, 3, x_194);
lean_ctor_set(x_199, 2, x_183);
lean_ctor_set(x_199, 1, x_182);
lean_ctor_set(x_199, 0, x_193);
x_201 = x_199;
goto block_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_203, 0, x_193);
lean_ctor_set(x_203, 1, x_182);
lean_ctor_set(x_203, 2, x_183);
lean_ctor_set(x_203, 3, x_194);
lean_ctor_set(x_203, 4, x_198);
x_201 = x_203;
goto block_202;
}
block_202:
{
return x_201;
}
}
}
}
block_223:
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_nat_add(x_214, x_215);
lean_dec(x_215);
lean_dec(x_214);
if (x_164 == 0)
{
lean_ctor_set(x_163, 4, x_184);
lean_ctor_set(x_163, 3, x_6);
lean_ctor_set(x_163, 2, x_5);
lean_ctor_set(x_163, 1, x_4);
lean_ctor_set(x_163, 0, x_216);
x_217 = x_163;
goto block_221;
}
else
{
lean_object* x_222; 
x_222 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_222, 0, x_216);
lean_ctor_set(x_222, 1, x_4);
lean_ctor_set(x_222, 2, x_5);
lean_ctor_set(x_222, 3, x_6);
lean_ctor_set(x_222, 4, x_184);
x_217 = x_222;
goto block_221;
}
block_221:
{
lean_object* x_218; 
x_218 = lean_nat_add(x_191, x_169);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_185, 0);
lean_inc(x_219);
x_194 = x_217;
x_195 = x_218;
x_196 = x_219;
goto block_213;
}
else
{
lean_object* x_220; 
x_220 = lean_unsigned_to_nat(0u);
x_194 = x_217;
x_195 = x_218;
x_196 = x_220;
goto block_213;
}
}
}
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_233 = lean_unsigned_to_nat(1u);
x_234 = lean_nat_add(x_233, x_3);
lean_dec(x_3);
x_235 = lean_nat_add(x_234, x_169);
lean_dec(x_234);
x_236 = lean_nat_add(x_233, x_169);
x_237 = lean_nat_add(x_236, x_181);
lean_dec(x_236);
if (x_164 == 0)
{
lean_ctor_set(x_163, 4, x_166);
lean_ctor_set(x_163, 3, x_7);
lean_ctor_set(x_163, 2, x_168);
lean_ctor_set(x_163, 1, x_167);
lean_ctor_set(x_163, 0, x_237);
x_238 = x_163;
goto block_242;
}
else
{
lean_object* x_243; 
x_243 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_243, 0, x_237);
lean_ctor_set(x_243, 1, x_167);
lean_ctor_set(x_243, 2, x_168);
lean_ctor_set(x_243, 3, x_7);
lean_ctor_set(x_243, 4, x_166);
x_238 = x_243;
goto block_242;
}
block_242:
{
lean_object* x_239; 
if (x_179 == 0)
{
lean_ctor_set(x_178, 4, x_238);
lean_ctor_set(x_178, 0, x_235);
x_239 = x_178;
goto block_240;
}
else
{
lean_object* x_241; 
x_241 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_241, 0, x_235);
lean_ctor_set(x_241, 1, x_4);
lean_ctor_set(x_241, 2, x_5);
lean_ctor_set(x_241, 3, x_6);
lean_ctor_set(x_241, 4, x_238);
x_239 = x_241;
goto block_240;
}
block_240:
{
return x_239;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_251; uint8_t x_252; uint8_t x_275; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_275 = !lean_is_exclusive(x_1);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_276 = lean_ctor_get(x_1, 4);
lean_dec(x_276);
x_277 = lean_ctor_get(x_1, 3);
lean_dec(x_277);
x_278 = lean_ctor_get(x_1, 2);
lean_dec(x_278);
x_279 = lean_ctor_get(x_1, 1);
lean_dec(x_279);
x_280 = lean_ctor_get(x_1, 0);
lean_dec(x_280);
x_251 = x_1;
x_252 = x_275;
goto block_274;
}
else
{
lean_dec(x_1);
x_251 = lean_box(0);
x_252 = x_275;
goto block_274;
}
block_274:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_253 = lean_ctor_get(x_165, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_165, 1);
lean_inc(x_254);
lean_dec_ref(x_165);
x_255 = lean_ctor_get(x_7, 0);
x_256 = lean_unsigned_to_nat(1u);
x_257 = lean_nat_add(x_256, x_3);
lean_dec(x_3);
x_258 = lean_nat_add(x_256, x_255);
if (x_164 == 0)
{
lean_ctor_set(x_163, 4, x_166);
lean_ctor_set(x_163, 3, x_7);
lean_ctor_set(x_163, 2, x_254);
lean_ctor_set(x_163, 1, x_253);
lean_ctor_set(x_163, 0, x_258);
x_259 = x_163;
goto block_263;
}
else
{
lean_object* x_264; 
x_264 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_264, 0, x_258);
lean_ctor_set(x_264, 1, x_253);
lean_ctor_set(x_264, 2, x_254);
lean_ctor_set(x_264, 3, x_7);
lean_ctor_set(x_264, 4, x_166);
x_259 = x_264;
goto block_263;
}
block_263:
{
lean_object* x_260; 
if (x_252 == 0)
{
lean_ctor_set(x_251, 4, x_259);
lean_ctor_set(x_251, 0, x_257);
x_260 = x_251;
goto block_261;
}
else
{
lean_object* x_262; 
x_262 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_262, 0, x_257);
lean_ctor_set(x_262, 1, x_4);
lean_ctor_set(x_262, 2, x_5);
lean_ctor_set(x_262, 3, x_6);
lean_ctor_set(x_262, 4, x_259);
x_260 = x_262;
goto block_261;
}
block_261:
{
return x_260;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_3);
x_265 = lean_ctor_get(x_165, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_165, 1);
lean_inc(x_266);
lean_dec_ref(x_165);
x_267 = lean_unsigned_to_nat(1u);
if (x_164 == 0)
{
lean_ctor_set(x_163, 4, x_7);
lean_ctor_set(x_163, 3, x_7);
lean_ctor_set(x_163, 2, x_266);
lean_ctor_set(x_163, 1, x_265);
lean_ctor_set(x_163, 0, x_267);
x_268 = x_163;
goto block_272;
}
else
{
lean_object* x_273; 
x_273 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_273, 0, x_267);
lean_ctor_set(x_273, 1, x_265);
lean_ctor_set(x_273, 2, x_266);
lean_ctor_set(x_273, 3, x_7);
lean_ctor_set(x_273, 4, x_7);
x_268 = x_273;
goto block_272;
}
block_272:
{
lean_object* x_269; 
if (x_252 == 0)
{
lean_ctor_set(x_251, 4, x_268);
lean_ctor_set(x_251, 0, x_13);
x_269 = x_251;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_271, 0, x_13);
lean_ctor_set(x_271, 1, x_4);
lean_ctor_set(x_271, 2, x_5);
lean_ctor_set(x_271, 3, x_6);
lean_ctor_set(x_271, 4, x_268);
x_269 = x_271;
goto block_270;
}
block_270:
{
return x_269;
}
}
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_281; uint8_t x_282; uint8_t x_305; 
lean_inc(x_5);
lean_inc(x_4);
x_305 = !lean_is_exclusive(x_1);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_306 = lean_ctor_get(x_1, 4);
lean_dec(x_306);
x_307 = lean_ctor_get(x_1, 3);
lean_dec(x_307);
x_308 = lean_ctor_get(x_1, 2);
lean_dec(x_308);
x_309 = lean_ctor_get(x_1, 1);
lean_dec(x_309);
x_310 = lean_ctor_get(x_1, 0);
lean_dec(x_310);
x_281 = x_1;
x_282 = x_305;
goto block_304;
}
else
{
lean_dec(x_1);
x_281 = lean_box(0);
x_282 = x_305;
goto block_304;
}
block_304:
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; uint8_t x_300; 
x_283 = lean_ctor_get(x_165, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_165, 1);
lean_inc(x_284);
lean_dec_ref(x_165);
x_285 = lean_ctor_get(x_7, 1);
x_286 = lean_ctor_get(x_7, 2);
x_300 = !lean_is_exclusive(x_7);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_7, 4);
lean_dec(x_301);
x_302 = lean_ctor_get(x_7, 3);
lean_dec(x_302);
x_303 = lean_ctor_get(x_7, 0);
lean_dec(x_303);
x_287 = x_7;
x_288 = x_300;
goto block_299;
}
else
{
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_7);
x_287 = lean_box(0);
x_288 = x_300;
goto block_299;
}
block_299:
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_unsigned_to_nat(1u);
if (x_288 == 0)
{
lean_ctor_set(x_287, 4, x_6);
lean_ctor_set(x_287, 3, x_6);
lean_ctor_set(x_287, 2, x_5);
lean_ctor_set(x_287, 1, x_4);
lean_ctor_set(x_287, 0, x_289);
x_290 = x_287;
goto block_297;
}
else
{
lean_object* x_298; 
x_298 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_298, 0, x_289);
lean_ctor_set(x_298, 1, x_4);
lean_ctor_set(x_298, 2, x_5);
lean_ctor_set(x_298, 3, x_6);
lean_ctor_set(x_298, 4, x_6);
x_290 = x_298;
goto block_297;
}
block_297:
{
lean_object* x_291; 
if (x_164 == 0)
{
lean_ctor_set(x_163, 4, x_6);
lean_ctor_set(x_163, 3, x_6);
lean_ctor_set(x_163, 2, x_284);
lean_ctor_set(x_163, 1, x_283);
lean_ctor_set(x_163, 0, x_289);
x_291 = x_163;
goto block_295;
}
else
{
lean_object* x_296; 
x_296 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_296, 0, x_289);
lean_ctor_set(x_296, 1, x_283);
lean_ctor_set(x_296, 2, x_284);
lean_ctor_set(x_296, 3, x_6);
lean_ctor_set(x_296, 4, x_6);
x_291 = x_296;
goto block_295;
}
block_295:
{
lean_object* x_292; 
if (x_282 == 0)
{
lean_ctor_set(x_281, 4, x_291);
lean_ctor_set(x_281, 3, x_290);
lean_ctor_set(x_281, 2, x_286);
lean_ctor_set(x_281, 1, x_285);
lean_ctor_set(x_281, 0, x_13);
x_292 = x_281;
goto block_293;
}
else
{
lean_object* x_294; 
x_294 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_294, 0, x_13);
lean_ctor_set(x_294, 1, x_285);
lean_ctor_set(x_294, 2, x_286);
lean_ctor_set(x_294, 3, x_290);
lean_ctor_set(x_294, 4, x_291);
x_292 = x_294;
goto block_293;
}
block_293:
{
return x_292;
}
}
}
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_311 = lean_ctor_get(x_165, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_165, 1);
lean_inc(x_312);
lean_dec_ref(x_165);
x_313 = lean_unsigned_to_nat(2u);
if (x_164 == 0)
{
lean_ctor_set(x_163, 4, x_7);
lean_ctor_set(x_163, 3, x_1);
lean_ctor_set(x_163, 2, x_312);
lean_ctor_set(x_163, 1, x_311);
lean_ctor_set(x_163, 0, x_313);
x_314 = x_163;
goto block_315;
}
else
{
lean_object* x_316; 
x_316 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_311);
lean_ctor_set(x_316, 2, x_312);
lean_ctor_set(x_316, 3, x_1);
lean_ctor_set(x_316, 4, x_7);
x_314 = x_316;
goto block_315;
}
block_315:
{
return x_314;
}
}
}
}
}
}
}
else
{
lean_object* x_324; uint8_t x_325; uint8_t x_505; 
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_12);
lean_dec(x_11);
x_505 = !lean_is_exclusive(x_1);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_506 = lean_ctor_get(x_1, 4);
lean_dec(x_506);
x_507 = lean_ctor_get(x_1, 3);
lean_dec(x_507);
x_508 = lean_ctor_get(x_1, 2);
lean_dec(x_508);
x_509 = lean_ctor_get(x_1, 1);
lean_dec(x_509);
x_510 = lean_ctor_get(x_1, 0);
lean_dec(x_510);
x_324 = x_1;
x_325 = x_505;
goto block_504;
}
else
{
lean_dec(x_1);
x_324 = lean_box(0);
x_325 = x_505;
goto block_504;
}
block_504:
{
lean_object* x_326; 
x_326 = l_Std_DTreeMap_Internal_Impl_link2___redArg(x_7, x_2);
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_327 = lean_ctor_get(x_6, 0);
x_328 = lean_ctor_get(x_326, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_326, 1);
lean_inc(x_329);
x_330 = lean_ctor_get(x_326, 2);
lean_inc(x_330);
x_331 = lean_ctor_get(x_326, 3);
lean_inc(x_331);
x_332 = lean_ctor_get(x_326, 4);
lean_inc(x_332);
x_333 = lean_nat_mul(x_13, x_327);
x_334 = lean_nat_dec_lt(x_333, x_328);
lean_dec(x_333);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_329);
x_335 = lean_unsigned_to_nat(1u);
x_336 = lean_nat_add(x_335, x_327);
x_337 = lean_nat_add(x_336, x_328);
lean_dec(x_328);
lean_dec(x_336);
if (x_325 == 0)
{
lean_ctor_set(x_324, 4, x_326);
lean_ctor_set(x_324, 0, x_337);
x_338 = x_324;
goto block_339;
}
else
{
lean_object* x_340; 
x_340 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_4);
lean_ctor_set(x_340, 2, x_5);
lean_ctor_set(x_340, 3, x_6);
lean_ctor_set(x_340, 4, x_326);
x_338 = x_340;
goto block_339;
}
block_339:
{
return x_338;
}
}
else
{
lean_object* x_341; uint8_t x_342; uint8_t x_406; 
x_406 = !lean_is_exclusive(x_326);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_407 = lean_ctor_get(x_326, 4);
lean_dec(x_407);
x_408 = lean_ctor_get(x_326, 3);
lean_dec(x_408);
x_409 = lean_ctor_get(x_326, 2);
lean_dec(x_409);
x_410 = lean_ctor_get(x_326, 1);
lean_dec(x_410);
x_411 = lean_ctor_get(x_326, 0);
lean_dec(x_411);
x_341 = x_326;
x_342 = x_406;
goto block_405;
}
else
{
lean_dec(x_326);
x_341 = lean_box(0);
x_342 = x_406;
goto block_405;
}
block_405:
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
x_343 = lean_ctor_get(x_331, 0);
x_344 = lean_ctor_get(x_331, 1);
x_345 = lean_ctor_get(x_331, 2);
x_346 = lean_ctor_get(x_331, 3);
x_347 = lean_ctor_get(x_331, 4);
x_348 = lean_ctor_get(x_332, 0);
x_349 = lean_unsigned_to_nat(2u);
x_350 = lean_nat_mul(x_349, x_348);
x_351 = lean_nat_dec_lt(x_343, x_350);
lean_dec(x_350);
if (x_351 == 0)
{
lean_object* x_352; uint8_t x_353; uint8_t x_380; 
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
x_380 = !lean_is_exclusive(x_331);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_381 = lean_ctor_get(x_331, 4);
lean_dec(x_381);
x_382 = lean_ctor_get(x_331, 3);
lean_dec(x_382);
x_383 = lean_ctor_get(x_331, 2);
lean_dec(x_383);
x_384 = lean_ctor_get(x_331, 1);
lean_dec(x_384);
x_385 = lean_ctor_get(x_331, 0);
lean_dec(x_385);
x_352 = x_331;
x_353 = x_380;
goto block_379;
}
else
{
lean_dec(x_331);
x_352 = lean_box(0);
x_353 = x_380;
goto block_379;
}
block_379:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_368; 
x_354 = lean_unsigned_to_nat(1u);
x_355 = lean_nat_add(x_354, x_327);
x_356 = lean_nat_add(x_355, x_328);
lean_dec(x_328);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_346, 0);
lean_inc(x_377);
x_368 = x_377;
goto block_376;
}
else
{
lean_object* x_378; 
x_378 = lean_unsigned_to_nat(0u);
x_368 = x_378;
goto block_376;
}
block_367:
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_nat_add(x_358, x_359);
lean_dec(x_359);
lean_dec(x_358);
if (x_353 == 0)
{
lean_ctor_set(x_352, 4, x_332);
lean_ctor_set(x_352, 3, x_347);
lean_ctor_set(x_352, 2, x_330);
lean_ctor_set(x_352, 1, x_329);
lean_ctor_set(x_352, 0, x_360);
x_361 = x_352;
goto block_365;
}
else
{
lean_object* x_366; 
x_366 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_366, 0, x_360);
lean_ctor_set(x_366, 1, x_329);
lean_ctor_set(x_366, 2, x_330);
lean_ctor_set(x_366, 3, x_347);
lean_ctor_set(x_366, 4, x_332);
x_361 = x_366;
goto block_365;
}
block_365:
{
lean_object* x_362; 
if (x_342 == 0)
{
lean_ctor_set(x_341, 4, x_361);
lean_ctor_set(x_341, 3, x_357);
lean_ctor_set(x_341, 2, x_345);
lean_ctor_set(x_341, 1, x_344);
lean_ctor_set(x_341, 0, x_356);
x_362 = x_341;
goto block_363;
}
else
{
lean_object* x_364; 
x_364 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_364, 0, x_356);
lean_ctor_set(x_364, 1, x_344);
lean_ctor_set(x_364, 2, x_345);
lean_ctor_set(x_364, 3, x_357);
lean_ctor_set(x_364, 4, x_361);
x_362 = x_364;
goto block_363;
}
block_363:
{
return x_362;
}
}
}
block_376:
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_nat_add(x_355, x_368);
lean_dec(x_368);
lean_dec(x_355);
if (x_325 == 0)
{
lean_ctor_set(x_324, 4, x_346);
lean_ctor_set(x_324, 0, x_369);
x_370 = x_324;
goto block_374;
}
else
{
lean_object* x_375; 
x_375 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_375, 0, x_369);
lean_ctor_set(x_375, 1, x_4);
lean_ctor_set(x_375, 2, x_5);
lean_ctor_set(x_375, 3, x_6);
lean_ctor_set(x_375, 4, x_346);
x_370 = x_375;
goto block_374;
}
block_374:
{
lean_object* x_371; 
x_371 = lean_nat_add(x_354, x_348);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_372; 
x_372 = lean_ctor_get(x_347, 0);
lean_inc(x_372);
x_357 = x_370;
x_358 = x_371;
x_359 = x_372;
goto block_367;
}
else
{
lean_object* x_373; 
x_373 = lean_unsigned_to_nat(0u);
x_357 = x_370;
x_358 = x_371;
x_359 = x_373;
goto block_367;
}
}
}
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_del_object(x_324);
x_386 = lean_unsigned_to_nat(1u);
x_387 = lean_nat_add(x_386, x_327);
x_388 = lean_nat_add(x_387, x_328);
lean_dec(x_328);
x_389 = lean_nat_add(x_387, x_343);
lean_dec(x_387);
lean_inc_ref(x_6);
if (x_342 == 0)
{
lean_ctor_set(x_341, 4, x_331);
lean_ctor_set(x_341, 3, x_6);
lean_ctor_set(x_341, 2, x_5);
lean_ctor_set(x_341, 1, x_4);
lean_ctor_set(x_341, 0, x_389);
x_390 = x_341;
goto block_403;
}
else
{
lean_object* x_404; 
x_404 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_404, 0, x_389);
lean_ctor_set(x_404, 1, x_4);
lean_ctor_set(x_404, 2, x_5);
lean_ctor_set(x_404, 3, x_6);
lean_ctor_set(x_404, 4, x_331);
x_390 = x_404;
goto block_403;
}
block_403:
{
lean_object* x_391; uint8_t x_392; uint8_t x_397; 
x_397 = !lean_is_exclusive(x_6);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_398 = lean_ctor_get(x_6, 4);
lean_dec(x_398);
x_399 = lean_ctor_get(x_6, 3);
lean_dec(x_399);
x_400 = lean_ctor_get(x_6, 2);
lean_dec(x_400);
x_401 = lean_ctor_get(x_6, 1);
lean_dec(x_401);
x_402 = lean_ctor_get(x_6, 0);
lean_dec(x_402);
x_391 = x_6;
x_392 = x_397;
goto block_396;
}
else
{
lean_dec(x_6);
x_391 = lean_box(0);
x_392 = x_397;
goto block_396;
}
block_396:
{
lean_object* x_393; 
if (x_392 == 0)
{
lean_ctor_set(x_391, 4, x_332);
lean_ctor_set(x_391, 3, x_390);
lean_ctor_set(x_391, 2, x_330);
lean_ctor_set(x_391, 1, x_329);
lean_ctor_set(x_391, 0, x_388);
x_393 = x_391;
goto block_394;
}
else
{
lean_object* x_395; 
x_395 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_395, 0, x_388);
lean_ctor_set(x_395, 1, x_329);
lean_ctor_set(x_395, 2, x_330);
lean_ctor_set(x_395, 3, x_390);
lean_ctor_set(x_395, 4, x_332);
x_393 = x_395;
goto block_394;
}
block_394:
{
return x_393;
}
}
}
}
}
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_412 = lean_ctor_get(x_6, 0);
x_413 = lean_unsigned_to_nat(1u);
x_414 = lean_nat_add(x_413, x_412);
if (x_325 == 0)
{
lean_ctor_set(x_324, 4, x_326);
lean_ctor_set(x_324, 0, x_414);
x_415 = x_324;
goto block_416;
}
else
{
lean_object* x_417; 
x_417 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_4);
lean_ctor_set(x_417, 2, x_5);
lean_ctor_set(x_417, 3, x_6);
lean_ctor_set(x_417, 4, x_326);
x_415 = x_417;
goto block_416;
}
block_416:
{
return x_415;
}
}
}
else
{
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_418; 
x_418 = lean_ctor_get(x_326, 3);
lean_inc(x_418);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; 
x_419 = lean_ctor_get(x_326, 4);
lean_inc(x_419);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; uint8_t x_436; 
x_420 = lean_ctor_get(x_326, 0);
x_421 = lean_ctor_get(x_326, 1);
x_422 = lean_ctor_get(x_326, 2);
x_436 = !lean_is_exclusive(x_326);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_ctor_get(x_326, 4);
lean_dec(x_437);
x_438 = lean_ctor_get(x_326, 3);
lean_dec(x_438);
x_423 = x_326;
x_424 = x_436;
goto block_435;
}
else
{
lean_inc(x_422);
lean_inc(x_421);
lean_inc(x_420);
lean_dec(x_326);
x_423 = lean_box(0);
x_424 = x_436;
goto block_435;
}
block_435:
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_425 = lean_ctor_get(x_418, 0);
x_426 = lean_unsigned_to_nat(1u);
x_427 = lean_nat_add(x_426, x_420);
lean_dec(x_420);
x_428 = lean_nat_add(x_426, x_425);
if (x_424 == 0)
{
lean_ctor_set(x_423, 4, x_418);
lean_ctor_set(x_423, 3, x_6);
lean_ctor_set(x_423, 2, x_5);
lean_ctor_set(x_423, 1, x_4);
lean_ctor_set(x_423, 0, x_428);
x_429 = x_423;
goto block_433;
}
else
{
lean_object* x_434; 
x_434 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_434, 0, x_428);
lean_ctor_set(x_434, 1, x_4);
lean_ctor_set(x_434, 2, x_5);
lean_ctor_set(x_434, 3, x_6);
lean_ctor_set(x_434, 4, x_418);
x_429 = x_434;
goto block_433;
}
block_433:
{
lean_object* x_430; 
if (x_325 == 0)
{
lean_ctor_set(x_324, 4, x_419);
lean_ctor_set(x_324, 3, x_429);
lean_ctor_set(x_324, 2, x_422);
lean_ctor_set(x_324, 1, x_421);
lean_ctor_set(x_324, 0, x_427);
x_430 = x_324;
goto block_431;
}
else
{
lean_object* x_432; 
x_432 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_432, 0, x_427);
lean_ctor_set(x_432, 1, x_421);
lean_ctor_set(x_432, 2, x_422);
lean_ctor_set(x_432, 3, x_429);
lean_ctor_set(x_432, 4, x_419);
x_430 = x_432;
goto block_431;
}
block_431:
{
return x_430;
}
}
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; uint8_t x_463; 
x_439 = lean_ctor_get(x_326, 1);
x_440 = lean_ctor_get(x_326, 2);
x_463 = !lean_is_exclusive(x_326);
if (x_463 == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_326, 4);
lean_dec(x_464);
x_465 = lean_ctor_get(x_326, 3);
lean_dec(x_465);
x_466 = lean_ctor_get(x_326, 0);
lean_dec(x_466);
x_441 = x_326;
x_442 = x_463;
goto block_462;
}
else
{
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_326);
x_441 = lean_box(0);
x_442 = x_463;
goto block_462;
}
block_462:
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; uint8_t x_458; 
x_443 = lean_ctor_get(x_418, 1);
x_444 = lean_ctor_get(x_418, 2);
x_458 = !lean_is_exclusive(x_418);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_418, 4);
lean_dec(x_459);
x_460 = lean_ctor_get(x_418, 3);
lean_dec(x_460);
x_461 = lean_ctor_get(x_418, 0);
lean_dec(x_461);
x_445 = x_418;
x_446 = x_458;
goto block_457;
}
else
{
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_418);
x_445 = lean_box(0);
x_446 = x_458;
goto block_457;
}
block_457:
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_unsigned_to_nat(1u);
if (x_446 == 0)
{
lean_ctor_set(x_445, 4, x_419);
lean_ctor_set(x_445, 3, x_419);
lean_ctor_set(x_445, 2, x_5);
lean_ctor_set(x_445, 1, x_4);
lean_ctor_set(x_445, 0, x_447);
x_448 = x_445;
goto block_455;
}
else
{
lean_object* x_456; 
x_456 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_456, 0, x_447);
lean_ctor_set(x_456, 1, x_4);
lean_ctor_set(x_456, 2, x_5);
lean_ctor_set(x_456, 3, x_419);
lean_ctor_set(x_456, 4, x_419);
x_448 = x_456;
goto block_455;
}
block_455:
{
lean_object* x_449; 
if (x_442 == 0)
{
lean_ctor_set(x_441, 3, x_419);
lean_ctor_set(x_441, 0, x_447);
x_449 = x_441;
goto block_453;
}
else
{
lean_object* x_454; 
x_454 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_454, 0, x_447);
lean_ctor_set(x_454, 1, x_439);
lean_ctor_set(x_454, 2, x_440);
lean_ctor_set(x_454, 3, x_419);
lean_ctor_set(x_454, 4, x_419);
x_449 = x_454;
goto block_453;
}
block_453:
{
lean_object* x_450; 
if (x_325 == 0)
{
lean_ctor_set(x_324, 4, x_449);
lean_ctor_set(x_324, 3, x_448);
lean_ctor_set(x_324, 2, x_444);
lean_ctor_set(x_324, 1, x_443);
lean_ctor_set(x_324, 0, x_13);
x_450 = x_324;
goto block_451;
}
else
{
lean_object* x_452; 
x_452 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_452, 0, x_13);
lean_ctor_set(x_452, 1, x_443);
lean_ctor_set(x_452, 2, x_444);
lean_ctor_set(x_452, 3, x_448);
lean_ctor_set(x_452, 4, x_449);
x_450 = x_452;
goto block_451;
}
block_451:
{
return x_450;
}
}
}
}
}
}
}
else
{
lean_object* x_467; 
x_467 = lean_ctor_get(x_326, 4);
lean_inc(x_467);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; uint8_t x_480; 
x_468 = lean_ctor_get(x_326, 1);
x_469 = lean_ctor_get(x_326, 2);
x_480 = !lean_is_exclusive(x_326);
if (x_480 == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_326, 4);
lean_dec(x_481);
x_482 = lean_ctor_get(x_326, 3);
lean_dec(x_482);
x_483 = lean_ctor_get(x_326, 0);
lean_dec(x_483);
x_470 = x_326;
x_471 = x_480;
goto block_479;
}
else
{
lean_inc(x_469);
lean_inc(x_468);
lean_dec(x_326);
x_470 = lean_box(0);
x_471 = x_480;
goto block_479;
}
block_479:
{
lean_object* x_472; lean_object* x_473; 
x_472 = lean_unsigned_to_nat(1u);
if (x_471 == 0)
{
lean_ctor_set(x_470, 4, x_418);
lean_ctor_set(x_470, 2, x_5);
lean_ctor_set(x_470, 1, x_4);
lean_ctor_set(x_470, 0, x_472);
x_473 = x_470;
goto block_477;
}
else
{
lean_object* x_478; 
x_478 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_478, 0, x_472);
lean_ctor_set(x_478, 1, x_4);
lean_ctor_set(x_478, 2, x_5);
lean_ctor_set(x_478, 3, x_418);
lean_ctor_set(x_478, 4, x_418);
x_473 = x_478;
goto block_477;
}
block_477:
{
lean_object* x_474; 
if (x_325 == 0)
{
lean_ctor_set(x_324, 4, x_467);
lean_ctor_set(x_324, 3, x_473);
lean_ctor_set(x_324, 2, x_469);
lean_ctor_set(x_324, 1, x_468);
lean_ctor_set(x_324, 0, x_13);
x_474 = x_324;
goto block_475;
}
else
{
lean_object* x_476; 
x_476 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_476, 0, x_13);
lean_ctor_set(x_476, 1, x_468);
lean_ctor_set(x_476, 2, x_469);
lean_ctor_set(x_476, 3, x_473);
lean_ctor_set(x_476, 4, x_467);
x_474 = x_476;
goto block_475;
}
block_475:
{
return x_474;
}
}
}
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; uint8_t x_497; 
x_484 = lean_ctor_get(x_326, 0);
x_485 = lean_ctor_get(x_326, 1);
x_486 = lean_ctor_get(x_326, 2);
x_497 = !lean_is_exclusive(x_326);
if (x_497 == 0)
{
lean_object* x_498; lean_object* x_499; 
x_498 = lean_ctor_get(x_326, 4);
lean_dec(x_498);
x_499 = lean_ctor_get(x_326, 3);
lean_dec(x_499);
x_487 = x_326;
x_488 = x_497;
goto block_496;
}
else
{
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_326);
x_487 = lean_box(0);
x_488 = x_497;
goto block_496;
}
block_496:
{
lean_object* x_489; 
if (x_488 == 0)
{
lean_ctor_set(x_487, 3, x_467);
x_489 = x_487;
goto block_494;
}
else
{
lean_object* x_495; 
x_495 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_495, 0, x_484);
lean_ctor_set(x_495, 1, x_485);
lean_ctor_set(x_495, 2, x_486);
lean_ctor_set(x_495, 3, x_467);
lean_ctor_set(x_495, 4, x_467);
x_489 = x_495;
goto block_494;
}
block_494:
{
lean_object* x_490; lean_object* x_491; 
x_490 = lean_unsigned_to_nat(2u);
if (x_325 == 0)
{
lean_ctor_set(x_324, 4, x_489);
lean_ctor_set(x_324, 3, x_467);
lean_ctor_set(x_324, 0, x_490);
x_491 = x_324;
goto block_492;
}
else
{
lean_object* x_493; 
x_493 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_493, 0, x_490);
lean_ctor_set(x_493, 1, x_4);
lean_ctor_set(x_493, 2, x_5);
lean_ctor_set(x_493, 3, x_467);
lean_ctor_set(x_493, 4, x_489);
x_491 = x_493;
goto block_492;
}
block_492:
{
return x_491;
}
}
}
}
}
}
else
{
lean_object* x_500; lean_object* x_501; 
x_500 = lean_unsigned_to_nat(1u);
if (x_325 == 0)
{
lean_ctor_set(x_324, 4, x_326);
lean_ctor_set(x_324, 3, x_326);
lean_ctor_set(x_324, 0, x_500);
x_501 = x_324;
goto block_502;
}
else
{
lean_object* x_503; 
x_503 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_4);
lean_ctor_set(x_503, 2, x_5);
lean_ctor_set(x_503, 3, x_326);
lean_ctor_set(x_503, 4, x_326);
x_501 = x_503;
goto block_502;
}
block_502:
{
return x_501;
}
}
}
}
}
}
else
{
lean_object* x_511; uint8_t x_512; uint8_t x_682; 
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_682 = !lean_is_exclusive(x_2);
if (x_682 == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_683 = lean_ctor_get(x_2, 4);
lean_dec(x_683);
x_684 = lean_ctor_get(x_2, 3);
lean_dec(x_684);
x_685 = lean_ctor_get(x_2, 2);
lean_dec(x_685);
x_686 = lean_ctor_get(x_2, 1);
lean_dec(x_686);
x_687 = lean_ctor_get(x_2, 0);
lean_dec(x_687);
x_511 = x_2;
x_512 = x_682;
goto block_681;
}
else
{
lean_dec(x_2);
x_511 = lean_box(0);
x_512 = x_682;
goto block_681;
}
block_681:
{
lean_object* x_513; 
x_513 = l_Std_DTreeMap_Internal_Impl_link2___redArg(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; 
x_514 = lean_ctor_get(x_12, 0);
x_515 = lean_ctor_get(x_513, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_513, 1);
lean_inc(x_516);
x_517 = lean_ctor_get(x_513, 2);
lean_inc(x_517);
x_518 = lean_ctor_get(x_513, 3);
lean_inc(x_518);
x_519 = lean_ctor_get(x_513, 4);
lean_inc(x_519);
x_520 = lean_nat_mul(x_13, x_514);
x_521 = lean_nat_dec_lt(x_520, x_515);
lean_dec(x_520);
if (x_521 == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec(x_519);
lean_dec(x_518);
lean_dec(x_517);
lean_dec(x_516);
x_522 = lean_unsigned_to_nat(1u);
x_523 = lean_nat_add(x_522, x_515);
lean_dec(x_515);
x_524 = lean_nat_add(x_523, x_514);
lean_dec(x_523);
if (x_512 == 0)
{
lean_ctor_set(x_511, 3, x_513);
lean_ctor_set(x_511, 0, x_524);
x_525 = x_511;
goto block_526;
}
else
{
lean_object* x_527; 
x_527 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_527, 0, x_524);
lean_ctor_set(x_527, 1, x_9);
lean_ctor_set(x_527, 2, x_10);
lean_ctor_set(x_527, 3, x_513);
lean_ctor_set(x_527, 4, x_12);
x_525 = x_527;
goto block_526;
}
block_526:
{
return x_525;
}
}
else
{
lean_object* x_528; uint8_t x_529; uint8_t x_595; 
x_595 = !lean_is_exclusive(x_513);
if (x_595 == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_596 = lean_ctor_get(x_513, 4);
lean_dec(x_596);
x_597 = lean_ctor_get(x_513, 3);
lean_dec(x_597);
x_598 = lean_ctor_get(x_513, 2);
lean_dec(x_598);
x_599 = lean_ctor_get(x_513, 1);
lean_dec(x_599);
x_600 = lean_ctor_get(x_513, 0);
lean_dec(x_600);
x_528 = x_513;
x_529 = x_595;
goto block_594;
}
else
{
lean_dec(x_513);
x_528 = lean_box(0);
x_529 = x_595;
goto block_594;
}
block_594:
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; 
x_530 = lean_ctor_get(x_518, 0);
x_531 = lean_ctor_get(x_519, 0);
x_532 = lean_ctor_get(x_519, 1);
x_533 = lean_ctor_get(x_519, 2);
x_534 = lean_ctor_get(x_519, 3);
x_535 = lean_ctor_get(x_519, 4);
x_536 = lean_unsigned_to_nat(2u);
x_537 = lean_nat_mul(x_536, x_530);
x_538 = lean_nat_dec_lt(x_531, x_537);
lean_dec(x_537);
if (x_538 == 0)
{
lean_object* x_539; uint8_t x_540; uint8_t x_568; 
lean_inc(x_535);
lean_inc(x_534);
lean_inc(x_533);
lean_inc(x_532);
x_568 = !lean_is_exclusive(x_519);
if (x_568 == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_569 = lean_ctor_get(x_519, 4);
lean_dec(x_569);
x_570 = lean_ctor_get(x_519, 3);
lean_dec(x_570);
x_571 = lean_ctor_get(x_519, 2);
lean_dec(x_571);
x_572 = lean_ctor_get(x_519, 1);
lean_dec(x_572);
x_573 = lean_ctor_get(x_519, 0);
lean_dec(x_573);
x_539 = x_519;
x_540 = x_568;
goto block_567;
}
else
{
lean_dec(x_519);
x_539 = lean_box(0);
x_540 = x_568;
goto block_567;
}
block_567:
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_555; lean_object* x_556; 
x_541 = lean_unsigned_to_nat(1u);
x_542 = lean_nat_add(x_541, x_515);
lean_dec(x_515);
x_543 = lean_nat_add(x_542, x_514);
lean_dec(x_542);
x_555 = lean_nat_add(x_541, x_530);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_565; 
x_565 = lean_ctor_get(x_534, 0);
lean_inc(x_565);
x_556 = x_565;
goto block_564;
}
else
{
lean_object* x_566; 
x_566 = lean_unsigned_to_nat(0u);
x_556 = x_566;
goto block_564;
}
block_554:
{
lean_object* x_547; lean_object* x_548; 
x_547 = lean_nat_add(x_544, x_546);
lean_dec(x_546);
lean_dec(x_544);
if (x_540 == 0)
{
lean_ctor_set(x_539, 4, x_12);
lean_ctor_set(x_539, 3, x_535);
lean_ctor_set(x_539, 2, x_10);
lean_ctor_set(x_539, 1, x_9);
lean_ctor_set(x_539, 0, x_547);
x_548 = x_539;
goto block_552;
}
else
{
lean_object* x_553; 
x_553 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_553, 0, x_547);
lean_ctor_set(x_553, 1, x_9);
lean_ctor_set(x_553, 2, x_10);
lean_ctor_set(x_553, 3, x_535);
lean_ctor_set(x_553, 4, x_12);
x_548 = x_553;
goto block_552;
}
block_552:
{
lean_object* x_549; 
if (x_529 == 0)
{
lean_ctor_set(x_528, 4, x_548);
lean_ctor_set(x_528, 3, x_545);
lean_ctor_set(x_528, 2, x_533);
lean_ctor_set(x_528, 1, x_532);
lean_ctor_set(x_528, 0, x_543);
x_549 = x_528;
goto block_550;
}
else
{
lean_object* x_551; 
x_551 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_551, 0, x_543);
lean_ctor_set(x_551, 1, x_532);
lean_ctor_set(x_551, 2, x_533);
lean_ctor_set(x_551, 3, x_545);
lean_ctor_set(x_551, 4, x_548);
x_549 = x_551;
goto block_550;
}
block_550:
{
return x_549;
}
}
}
block_564:
{
lean_object* x_557; lean_object* x_558; 
x_557 = lean_nat_add(x_555, x_556);
lean_dec(x_556);
lean_dec(x_555);
if (x_512 == 0)
{
lean_ctor_set(x_511, 4, x_534);
lean_ctor_set(x_511, 3, x_518);
lean_ctor_set(x_511, 2, x_517);
lean_ctor_set(x_511, 1, x_516);
lean_ctor_set(x_511, 0, x_557);
x_558 = x_511;
goto block_562;
}
else
{
lean_object* x_563; 
x_563 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_563, 0, x_557);
lean_ctor_set(x_563, 1, x_516);
lean_ctor_set(x_563, 2, x_517);
lean_ctor_set(x_563, 3, x_518);
lean_ctor_set(x_563, 4, x_534);
x_558 = x_563;
goto block_562;
}
block_562:
{
lean_object* x_559; 
x_559 = lean_nat_add(x_541, x_514);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_560; 
x_560 = lean_ctor_get(x_535, 0);
lean_inc(x_560);
x_544 = x_559;
x_545 = x_558;
x_546 = x_560;
goto block_554;
}
else
{
lean_object* x_561; 
x_561 = lean_unsigned_to_nat(0u);
x_544 = x_559;
x_545 = x_558;
x_546 = x_561;
goto block_554;
}
}
}
}
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_del_object(x_511);
x_574 = lean_unsigned_to_nat(1u);
x_575 = lean_nat_add(x_574, x_515);
lean_dec(x_515);
x_576 = lean_nat_add(x_575, x_514);
lean_dec(x_575);
x_577 = lean_nat_add(x_574, x_514);
x_578 = lean_nat_add(x_577, x_531);
lean_dec(x_577);
lean_inc_ref(x_12);
if (x_529 == 0)
{
lean_ctor_set(x_528, 4, x_12);
lean_ctor_set(x_528, 3, x_519);
lean_ctor_set(x_528, 2, x_10);
lean_ctor_set(x_528, 1, x_9);
lean_ctor_set(x_528, 0, x_578);
x_579 = x_528;
goto block_592;
}
else
{
lean_object* x_593; 
x_593 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_593, 0, x_578);
lean_ctor_set(x_593, 1, x_9);
lean_ctor_set(x_593, 2, x_10);
lean_ctor_set(x_593, 3, x_519);
lean_ctor_set(x_593, 4, x_12);
x_579 = x_593;
goto block_592;
}
block_592:
{
lean_object* x_580; uint8_t x_581; uint8_t x_586; 
x_586 = !lean_is_exclusive(x_12);
if (x_586 == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_587 = lean_ctor_get(x_12, 4);
lean_dec(x_587);
x_588 = lean_ctor_get(x_12, 3);
lean_dec(x_588);
x_589 = lean_ctor_get(x_12, 2);
lean_dec(x_589);
x_590 = lean_ctor_get(x_12, 1);
lean_dec(x_590);
x_591 = lean_ctor_get(x_12, 0);
lean_dec(x_591);
x_580 = x_12;
x_581 = x_586;
goto block_585;
}
else
{
lean_dec(x_12);
x_580 = lean_box(0);
x_581 = x_586;
goto block_585;
}
block_585:
{
lean_object* x_582; 
if (x_581 == 0)
{
lean_ctor_set(x_580, 4, x_579);
lean_ctor_set(x_580, 3, x_518);
lean_ctor_set(x_580, 2, x_517);
lean_ctor_set(x_580, 1, x_516);
lean_ctor_set(x_580, 0, x_576);
x_582 = x_580;
goto block_583;
}
else
{
lean_object* x_584; 
x_584 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_584, 0, x_576);
lean_ctor_set(x_584, 1, x_516);
lean_ctor_set(x_584, 2, x_517);
lean_ctor_set(x_584, 3, x_518);
lean_ctor_set(x_584, 4, x_579);
x_582 = x_584;
goto block_583;
}
block_583:
{
return x_582;
}
}
}
}
}
}
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_601 = lean_ctor_get(x_12, 0);
x_602 = lean_unsigned_to_nat(1u);
x_603 = lean_nat_add(x_602, x_601);
if (x_512 == 0)
{
lean_ctor_set(x_511, 3, x_513);
lean_ctor_set(x_511, 0, x_603);
x_604 = x_511;
goto block_605;
}
else
{
lean_object* x_606; 
x_606 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_606, 0, x_603);
lean_ctor_set(x_606, 1, x_9);
lean_ctor_set(x_606, 2, x_10);
lean_ctor_set(x_606, 3, x_513);
lean_ctor_set(x_606, 4, x_12);
x_604 = x_606;
goto block_605;
}
block_605:
{
return x_604;
}
}
}
else
{
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_607; 
x_607 = lean_ctor_get(x_513, 3);
lean_inc(x_607);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; 
x_608 = lean_ctor_get(x_513, 4);
lean_inc(x_608);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; uint8_t x_613; uint8_t x_625; 
x_609 = lean_ctor_get(x_513, 0);
x_610 = lean_ctor_get(x_513, 1);
x_611 = lean_ctor_get(x_513, 2);
x_625 = !lean_is_exclusive(x_513);
if (x_625 == 0)
{
lean_object* x_626; lean_object* x_627; 
x_626 = lean_ctor_get(x_513, 4);
lean_dec(x_626);
x_627 = lean_ctor_get(x_513, 3);
lean_dec(x_627);
x_612 = x_513;
x_613 = x_625;
goto block_624;
}
else
{
lean_inc(x_611);
lean_inc(x_610);
lean_inc(x_609);
lean_dec(x_513);
x_612 = lean_box(0);
x_613 = x_625;
goto block_624;
}
block_624:
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_614 = lean_ctor_get(x_608, 0);
x_615 = lean_unsigned_to_nat(1u);
x_616 = lean_nat_add(x_615, x_609);
lean_dec(x_609);
x_617 = lean_nat_add(x_615, x_614);
if (x_613 == 0)
{
lean_ctor_set(x_612, 4, x_12);
lean_ctor_set(x_612, 3, x_608);
lean_ctor_set(x_612, 2, x_10);
lean_ctor_set(x_612, 1, x_9);
lean_ctor_set(x_612, 0, x_617);
x_618 = x_612;
goto block_622;
}
else
{
lean_object* x_623; 
x_623 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_623, 0, x_617);
lean_ctor_set(x_623, 1, x_9);
lean_ctor_set(x_623, 2, x_10);
lean_ctor_set(x_623, 3, x_608);
lean_ctor_set(x_623, 4, x_12);
x_618 = x_623;
goto block_622;
}
block_622:
{
lean_object* x_619; 
if (x_512 == 0)
{
lean_ctor_set(x_511, 4, x_618);
lean_ctor_set(x_511, 3, x_607);
lean_ctor_set(x_511, 2, x_611);
lean_ctor_set(x_511, 1, x_610);
lean_ctor_set(x_511, 0, x_616);
x_619 = x_511;
goto block_620;
}
else
{
lean_object* x_621; 
x_621 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_621, 0, x_616);
lean_ctor_set(x_621, 1, x_610);
lean_ctor_set(x_621, 2, x_611);
lean_ctor_set(x_621, 3, x_607);
lean_ctor_set(x_621, 4, x_618);
x_619 = x_621;
goto block_620;
}
block_620:
{
return x_619;
}
}
}
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; uint8_t x_640; 
x_628 = lean_ctor_get(x_513, 1);
x_629 = lean_ctor_get(x_513, 2);
x_640 = !lean_is_exclusive(x_513);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_513, 4);
lean_dec(x_641);
x_642 = lean_ctor_get(x_513, 3);
lean_dec(x_642);
x_643 = lean_ctor_get(x_513, 0);
lean_dec(x_643);
x_630 = x_513;
x_631 = x_640;
goto block_639;
}
else
{
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_513);
x_630 = lean_box(0);
x_631 = x_640;
goto block_639;
}
block_639:
{
lean_object* x_632; lean_object* x_633; 
x_632 = lean_unsigned_to_nat(1u);
if (x_631 == 0)
{
lean_ctor_set(x_630, 3, x_608);
lean_ctor_set(x_630, 2, x_10);
lean_ctor_set(x_630, 1, x_9);
lean_ctor_set(x_630, 0, x_632);
x_633 = x_630;
goto block_637;
}
else
{
lean_object* x_638; 
x_638 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_638, 0, x_632);
lean_ctor_set(x_638, 1, x_9);
lean_ctor_set(x_638, 2, x_10);
lean_ctor_set(x_638, 3, x_608);
lean_ctor_set(x_638, 4, x_608);
x_633 = x_638;
goto block_637;
}
block_637:
{
lean_object* x_634; 
if (x_512 == 0)
{
lean_ctor_set(x_511, 4, x_633);
lean_ctor_set(x_511, 3, x_607);
lean_ctor_set(x_511, 2, x_629);
lean_ctor_set(x_511, 1, x_628);
lean_ctor_set(x_511, 0, x_13);
x_634 = x_511;
goto block_635;
}
else
{
lean_object* x_636; 
x_636 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_636, 0, x_13);
lean_ctor_set(x_636, 1, x_628);
lean_ctor_set(x_636, 2, x_629);
lean_ctor_set(x_636, 3, x_607);
lean_ctor_set(x_636, 4, x_633);
x_634 = x_636;
goto block_635;
}
block_635:
{
return x_634;
}
}
}
}
}
else
{
lean_object* x_644; 
x_644 = lean_ctor_get(x_513, 4);
lean_inc(x_644);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; uint8_t x_648; uint8_t x_669; 
x_645 = lean_ctor_get(x_513, 1);
x_646 = lean_ctor_get(x_513, 2);
x_669 = !lean_is_exclusive(x_513);
if (x_669 == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_670 = lean_ctor_get(x_513, 4);
lean_dec(x_670);
x_671 = lean_ctor_get(x_513, 3);
lean_dec(x_671);
x_672 = lean_ctor_get(x_513, 0);
lean_dec(x_672);
x_647 = x_513;
x_648 = x_669;
goto block_668;
}
else
{
lean_inc(x_646);
lean_inc(x_645);
lean_dec(x_513);
x_647 = lean_box(0);
x_648 = x_669;
goto block_668;
}
block_668:
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; uint8_t x_652; uint8_t x_664; 
x_649 = lean_ctor_get(x_644, 1);
x_650 = lean_ctor_get(x_644, 2);
x_664 = !lean_is_exclusive(x_644);
if (x_664 == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_644, 4);
lean_dec(x_665);
x_666 = lean_ctor_get(x_644, 3);
lean_dec(x_666);
x_667 = lean_ctor_get(x_644, 0);
lean_dec(x_667);
x_651 = x_644;
x_652 = x_664;
goto block_663;
}
else
{
lean_inc(x_650);
lean_inc(x_649);
lean_dec(x_644);
x_651 = lean_box(0);
x_652 = x_664;
goto block_663;
}
block_663:
{
lean_object* x_653; lean_object* x_654; 
x_653 = lean_unsigned_to_nat(1u);
if (x_652 == 0)
{
lean_ctor_set(x_651, 4, x_607);
lean_ctor_set(x_651, 3, x_607);
lean_ctor_set(x_651, 2, x_646);
lean_ctor_set(x_651, 1, x_645);
lean_ctor_set(x_651, 0, x_653);
x_654 = x_651;
goto block_661;
}
else
{
lean_object* x_662; 
x_662 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_662, 0, x_653);
lean_ctor_set(x_662, 1, x_645);
lean_ctor_set(x_662, 2, x_646);
lean_ctor_set(x_662, 3, x_607);
lean_ctor_set(x_662, 4, x_607);
x_654 = x_662;
goto block_661;
}
block_661:
{
lean_object* x_655; 
if (x_648 == 0)
{
lean_ctor_set(x_647, 4, x_607);
lean_ctor_set(x_647, 2, x_10);
lean_ctor_set(x_647, 1, x_9);
lean_ctor_set(x_647, 0, x_653);
x_655 = x_647;
goto block_659;
}
else
{
lean_object* x_660; 
x_660 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_660, 0, x_653);
lean_ctor_set(x_660, 1, x_9);
lean_ctor_set(x_660, 2, x_10);
lean_ctor_set(x_660, 3, x_607);
lean_ctor_set(x_660, 4, x_607);
x_655 = x_660;
goto block_659;
}
block_659:
{
lean_object* x_656; 
if (x_512 == 0)
{
lean_ctor_set(x_511, 4, x_655);
lean_ctor_set(x_511, 3, x_654);
lean_ctor_set(x_511, 2, x_650);
lean_ctor_set(x_511, 1, x_649);
lean_ctor_set(x_511, 0, x_13);
x_656 = x_511;
goto block_657;
}
else
{
lean_object* x_658; 
x_658 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_658, 0, x_13);
lean_ctor_set(x_658, 1, x_649);
lean_ctor_set(x_658, 2, x_650);
lean_ctor_set(x_658, 3, x_654);
lean_ctor_set(x_658, 4, x_655);
x_656 = x_658;
goto block_657;
}
block_657:
{
return x_656;
}
}
}
}
}
}
else
{
lean_object* x_673; lean_object* x_674; 
x_673 = lean_unsigned_to_nat(2u);
if (x_512 == 0)
{
lean_ctor_set(x_511, 4, x_644);
lean_ctor_set(x_511, 3, x_513);
lean_ctor_set(x_511, 0, x_673);
x_674 = x_511;
goto block_675;
}
else
{
lean_object* x_676; 
x_676 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_676, 0, x_673);
lean_ctor_set(x_676, 1, x_9);
lean_ctor_set(x_676, 2, x_10);
lean_ctor_set(x_676, 3, x_513);
lean_ctor_set(x_676, 4, x_644);
x_674 = x_676;
goto block_675;
}
block_675:
{
return x_674;
}
}
}
}
else
{
lean_object* x_677; lean_object* x_678; 
x_677 = lean_unsigned_to_nat(1u);
if (x_512 == 0)
{
lean_ctor_set(x_511, 4, x_513);
lean_ctor_set(x_511, 3, x_513);
lean_ctor_set(x_511, 0, x_677);
x_678 = x_511;
goto block_679;
}
else
{
lean_object* x_680; 
x_680 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_680, 0, x_677);
lean_ctor_set(x_680, 1, x_9);
lean_ctor_set(x_680, 2, x_10);
lean_ctor_set(x_680, 3, x_513);
lean_ctor_set(x_680, 4, x_513);
x_678 = x_680;
goto block_679;
}
block_679:
{
return x_678;
}
}
}
}
}
}
else
{
return x_1;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_link2___redArg(x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0), lean_box(0));
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_2, lean_box(0), lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_3(x_2, x_1, lean_box(0), lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_3(x_7, x_6, lean_box(0), lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_3(x_2, x_1, lean_box(0), lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_3(x_7, x_6, lean_box(0), lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 4);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_nat_mul(x_13, x_3);
x_15 = lean_nat_dec_lt(x_14, x_8);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_nat_mul(x_13, x_8);
x_17 = lean_nat_dec_lt(x_16, x_3);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_3, x_8);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; uint8_t x_167; 
lean_inc(x_5);
lean_inc(x_4);
x_167 = !lean_is_exclusive(x_1);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_1, 4);
lean_dec(x_168);
x_169 = lean_ctor_get(x_1, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_1, 2);
lean_dec(x_170);
x_171 = lean_ctor_get(x_1, 1);
lean_dec(x_171);
x_172 = lean_ctor_get(x_1, 0);
lean_dec(x_172);
x_19 = x_1;
x_20 = x_167;
goto block_166;
}
else
{
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(x_4, x_5, x_6, x_7);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_nat_mul(x_13, x_25);
x_27 = lean_nat_dec_lt(x_26, x_8);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
lean_dec(x_11);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_28, x_25);
x_30 = lean_nat_add(x_29, x_8);
lean_dec(x_29);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_2);
lean_ctor_set(x_19, 3, x_22);
lean_ctor_set(x_19, 2, x_24);
lean_ctor_set(x_19, 1, x_23);
lean_ctor_set(x_19, 0, x_30);
x_31 = x_19;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_23);
lean_ctor_set(x_33, 2, x_24);
lean_ctor_set(x_33, 3, x_22);
lean_ctor_set(x_33, 4, x_2);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
else
{
lean_object* x_34; uint8_t x_35; uint8_t x_94; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_94 = !lean_is_exclusive(x_2);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_2, 4);
lean_dec(x_95);
x_96 = lean_ctor_get(x_2, 3);
lean_dec(x_96);
x_97 = lean_ctor_get(x_2, 2);
lean_dec(x_97);
x_98 = lean_ctor_get(x_2, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_2, 0);
lean_dec(x_99);
x_34 = x_2;
x_35 = x_94;
goto block_93;
}
else
{
lean_dec(x_2);
x_34 = lean_box(0);
x_35 = x_94;
goto block_93;
}
block_93:
{
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
x_38 = lean_ctor_get(x_11, 2);
x_39 = lean_ctor_get(x_11, 3);
x_40 = lean_ctor_get(x_11, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_unsigned_to_nat(2u);
x_43 = lean_nat_mul(x_42, x_41);
x_44 = lean_nat_dec_lt(x_36, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; uint8_t x_73; 
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
x_73 = !lean_is_exclusive(x_11);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_11, 4);
lean_dec(x_74);
x_75 = lean_ctor_get(x_11, 3);
lean_dec(x_75);
x_76 = lean_ctor_get(x_11, 2);
lean_dec(x_76);
x_77 = lean_ctor_get(x_11, 1);
lean_dec(x_77);
x_78 = lean_ctor_get(x_11, 0);
lean_dec(x_78);
x_45 = x_11;
x_46 = x_73;
goto block_72;
}
else
{
lean_dec(x_11);
x_45 = lean_box(0);
x_46 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_61; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_47, x_25);
x_49 = lean_nat_add(x_48, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_39, 0);
lean_inc(x_70);
x_61 = x_70;
goto block_69;
}
else
{
lean_object* x_71; 
x_71 = lean_unsigned_to_nat(0u);
x_61 = x_71;
goto block_69;
}
block_60:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_nat_add(x_50, x_52);
lean_dec(x_52);
lean_dec(x_50);
if (x_46 == 0)
{
lean_ctor_set(x_45, 4, x_12);
lean_ctor_set(x_45, 3, x_40);
lean_ctor_set(x_45, 2, x_10);
lean_ctor_set(x_45, 1, x_9);
lean_ctor_set(x_45, 0, x_53);
x_54 = x_45;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_9);
lean_ctor_set(x_59, 2, x_10);
lean_ctor_set(x_59, 3, x_40);
lean_ctor_set(x_59, 4, x_12);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 4, x_54);
lean_ctor_set(x_34, 3, x_51);
lean_ctor_set(x_34, 2, x_38);
lean_ctor_set(x_34, 1, x_37);
lean_ctor_set(x_34, 0, x_49);
x_55 = x_34;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_37);
lean_ctor_set(x_57, 2, x_38);
lean_ctor_set(x_57, 3, x_51);
lean_ctor_set(x_57, 4, x_54);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
block_69:
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_nat_add(x_48, x_61);
lean_dec(x_61);
lean_dec(x_48);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_39);
lean_ctor_set(x_19, 3, x_22);
lean_ctor_set(x_19, 2, x_24);
lean_ctor_set(x_19, 1, x_23);
lean_ctor_set(x_19, 0, x_62);
x_63 = x_19;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_23);
lean_ctor_set(x_68, 2, x_24);
lean_ctor_set(x_68, 3, x_22);
lean_ctor_set(x_68, 4, x_39);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
x_64 = lean_nat_add(x_47, x_41);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_40, 0);
lean_inc(x_65);
x_50 = x_64;
x_51 = x_63;
x_52 = x_65;
goto block_60;
}
else
{
lean_object* x_66; 
x_66 = lean_unsigned_to_nat(0u);
x_50 = x_64;
x_51 = x_63;
x_52 = x_66;
goto block_60;
}
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_79, x_25);
x_81 = lean_nat_add(x_80, x_8);
lean_dec(x_8);
x_82 = lean_nat_add(x_80, x_36);
lean_dec(x_80);
if (x_35 == 0)
{
lean_ctor_set(x_34, 4, x_11);
lean_ctor_set(x_34, 3, x_22);
lean_ctor_set(x_34, 2, x_24);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 0, x_82);
x_83 = x_34;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_23);
lean_ctor_set(x_88, 2, x_24);
lean_ctor_set(x_88, 3, x_22);
lean_ctor_set(x_88, 4, x_11);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_12);
lean_ctor_set(x_19, 3, x_83);
lean_ctor_set(x_19, 2, x_10);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 0, x_81);
x_84 = x_19;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_9);
lean_ctor_set(x_86, 2, x_10);
lean_ctor_set(x_86, 3, x_83);
lean_ctor_set(x_86, 4, x_12);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_11);
lean_del_object(x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_del_object(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_89 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3);
x_90 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_89);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_del_object(x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_del_object(x_19);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_91 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4);
x_92 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_91);
return x_92;
}
}
}
}
else
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_100; uint8_t x_101; uint8_t x_136; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_136 = !lean_is_exclusive(x_2);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_2, 4);
lean_dec(x_137);
x_138 = lean_ctor_get(x_2, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_2, 2);
lean_dec(x_139);
x_140 = lean_ctor_get(x_2, 1);
lean_dec(x_140);
x_141 = lean_ctor_get(x_2, 0);
lean_dec(x_141);
x_100 = x_2;
x_101 = x_136;
goto block_135;
}
else
{
lean_dec(x_2);
x_100 = lean_box(0);
x_101 = x_136;
goto block_135;
}
block_135:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_21, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_21, 1);
lean_inc(x_103);
lean_dec_ref(x_21);
x_104 = lean_ctor_get(x_11, 0);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_105, x_8);
lean_dec(x_8);
x_107 = lean_nat_add(x_105, x_104);
if (x_101 == 0)
{
lean_ctor_set(x_100, 4, x_11);
lean_ctor_set(x_100, 3, x_22);
lean_ctor_set(x_100, 2, x_103);
lean_ctor_set(x_100, 1, x_102);
lean_ctor_set(x_100, 0, x_107);
x_108 = x_100;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_102);
lean_ctor_set(x_113, 2, x_103);
lean_ctor_set(x_113, 3, x_22);
lean_ctor_set(x_113, 4, x_11);
x_108 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_109; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_12);
lean_ctor_set(x_19, 3, x_108);
lean_ctor_set(x_19, 2, x_10);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 0, x_106);
x_109 = x_19;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_9);
lean_ctor_set(x_111, 2, x_10);
lean_ctor_set(x_111, 3, x_108);
lean_ctor_set(x_111, 4, x_12);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_131; 
lean_dec(x_8);
x_114 = lean_ctor_get(x_21, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_21, 1);
lean_inc(x_115);
lean_dec_ref(x_21);
x_116 = lean_ctor_get(x_11, 1);
x_117 = lean_ctor_get(x_11, 2);
x_131 = !lean_is_exclusive(x_11);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_11, 4);
lean_dec(x_132);
x_133 = lean_ctor_get(x_11, 3);
lean_dec(x_133);
x_134 = lean_ctor_get(x_11, 0);
lean_dec(x_134);
x_118 = x_11;
x_119 = x_131;
goto block_130;
}
else
{
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_11);
x_118 = lean_box(0);
x_119 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_unsigned_to_nat(1u);
if (x_119 == 0)
{
lean_ctor_set(x_118, 4, x_12);
lean_ctor_set(x_118, 3, x_12);
lean_ctor_set(x_118, 2, x_115);
lean_ctor_set(x_118, 1, x_114);
lean_ctor_set(x_118, 0, x_120);
x_121 = x_118;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_129, 0, x_120);
lean_ctor_set(x_129, 1, x_114);
lean_ctor_set(x_129, 2, x_115);
lean_ctor_set(x_129, 3, x_12);
lean_ctor_set(x_129, 4, x_12);
x_121 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_122; 
if (x_101 == 0)
{
lean_ctor_set(x_100, 3, x_12);
lean_ctor_set(x_100, 0, x_120);
x_122 = x_100;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_127, 0, x_120);
lean_ctor_set(x_127, 1, x_9);
lean_ctor_set(x_127, 2, x_10);
lean_ctor_set(x_127, 3, x_12);
lean_ctor_set(x_127, 4, x_12);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_122);
lean_ctor_set(x_19, 3, x_121);
lean_ctor_set(x_19, 2, x_117);
lean_ctor_set(x_19, 1, x_116);
lean_ctor_set(x_19, 0, x_13);
x_123 = x_19;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_125, 0, x_13);
lean_ctor_set(x_125, 1, x_116);
lean_ctor_set(x_125, 2, x_117);
lean_ctor_set(x_125, 3, x_121);
lean_ctor_set(x_125, 4, x_122);
x_123 = x_125;
goto block_124;
}
block_124:
{
return x_123;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_142; uint8_t x_143; uint8_t x_154; 
lean_inc(x_10);
lean_inc(x_9);
x_154 = !lean_is_exclusive(x_2);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_155 = lean_ctor_get(x_2, 4);
lean_dec(x_155);
x_156 = lean_ctor_get(x_2, 3);
lean_dec(x_156);
x_157 = lean_ctor_get(x_2, 2);
lean_dec(x_157);
x_158 = lean_ctor_get(x_2, 1);
lean_dec(x_158);
x_159 = lean_ctor_get(x_2, 0);
lean_dec(x_159);
x_142 = x_2;
x_143 = x_154;
goto block_153;
}
else
{
lean_dec(x_2);
x_142 = lean_box(0);
x_143 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_21, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_21, 1);
lean_inc(x_145);
lean_dec_ref(x_21);
x_146 = lean_unsigned_to_nat(1u);
if (x_143 == 0)
{
lean_ctor_set(x_142, 4, x_11);
lean_ctor_set(x_142, 2, x_145);
lean_ctor_set(x_142, 1, x_144);
lean_ctor_set(x_142, 0, x_146);
x_147 = x_142;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_152, 0, x_146);
lean_ctor_set(x_152, 1, x_144);
lean_ctor_set(x_152, 2, x_145);
lean_ctor_set(x_152, 3, x_11);
lean_ctor_set(x_152, 4, x_11);
x_147 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_148; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_12);
lean_ctor_set(x_19, 3, x_147);
lean_ctor_set(x_19, 2, x_10);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 0, x_13);
x_148 = x_19;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_150, 0, x_13);
lean_ctor_set(x_150, 1, x_9);
lean_ctor_set(x_150, 2, x_10);
lean_ctor_set(x_150, 3, x_147);
lean_ctor_set(x_150, 4, x_12);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_21, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_21, 1);
lean_inc(x_161);
lean_dec_ref(x_21);
x_162 = lean_unsigned_to_nat(2u);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_2);
lean_ctor_set(x_19, 3, x_12);
lean_ctor_set(x_19, 2, x_161);
lean_ctor_set(x_19, 1, x_160);
lean_ctor_set(x_19, 0, x_162);
x_163 = x_19;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set(x_165, 2, x_161);
lean_ctor_set(x_165, 3, x_12);
lean_ctor_set(x_165, 4, x_2);
x_163 = x_165;
goto block_164;
}
block_164:
{
return x_163;
}
}
}
}
}
}
else
{
lean_object* x_173; uint8_t x_174; uint8_t x_332; 
lean_inc(x_10);
lean_inc(x_9);
x_332 = !lean_is_exclusive(x_2);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_333 = lean_ctor_get(x_2, 4);
lean_dec(x_333);
x_334 = lean_ctor_get(x_2, 3);
lean_dec(x_334);
x_335 = lean_ctor_get(x_2, 2);
lean_dec(x_335);
x_336 = lean_ctor_get(x_2, 1);
lean_dec(x_336);
x_337 = lean_ctor_get(x_2, 0);
lean_dec(x_337);
x_173 = x_2;
x_174 = x_332;
goto block_331;
}
else
{
lean_dec(x_2);
x_173 = lean_box(0);
x_174 = x_332;
goto block_331;
}
block_331:
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(x_9, x_10, x_11, x_12);
x_176 = lean_ctor_get(x_175, 2);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec_ref(x_175);
x_179 = lean_ctor_get(x_176, 0);
x_180 = lean_nat_mul(x_13, x_179);
x_181 = lean_nat_dec_lt(x_180, x_3);
lean_dec(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_7);
lean_dec(x_6);
x_182 = lean_unsigned_to_nat(1u);
x_183 = lean_nat_add(x_182, x_3);
x_184 = lean_nat_add(x_183, x_179);
lean_dec(x_183);
if (x_174 == 0)
{
lean_ctor_set(x_173, 4, x_176);
lean_ctor_set(x_173, 3, x_1);
lean_ctor_set(x_173, 2, x_178);
lean_ctor_set(x_173, 1, x_177);
lean_ctor_set(x_173, 0, x_184);
x_185 = x_173;
goto block_186;
}
else
{
lean_object* x_187; 
x_187 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_177);
lean_ctor_set(x_187, 2, x_178);
lean_ctor_set(x_187, 3, x_1);
lean_ctor_set(x_187, 4, x_176);
x_185 = x_187;
goto block_186;
}
block_186:
{
return x_185;
}
}
else
{
lean_object* x_188; uint8_t x_189; uint8_t x_259; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_259 = !lean_is_exclusive(x_1);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_260 = lean_ctor_get(x_1, 4);
lean_dec(x_260);
x_261 = lean_ctor_get(x_1, 3);
lean_dec(x_261);
x_262 = lean_ctor_get(x_1, 2);
lean_dec(x_262);
x_263 = lean_ctor_get(x_1, 1);
lean_dec(x_263);
x_264 = lean_ctor_get(x_1, 0);
lean_dec(x_264);
x_188 = x_1;
x_189 = x_259;
goto block_258;
}
else
{
lean_dec(x_1);
x_188 = lean_box(0);
x_189 = x_259;
goto block_258;
}
block_258:
{
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_190 = lean_ctor_get(x_6, 0);
x_191 = lean_ctor_get(x_7, 0);
x_192 = lean_ctor_get(x_7, 1);
x_193 = lean_ctor_get(x_7, 2);
x_194 = lean_ctor_get(x_7, 3);
x_195 = lean_ctor_get(x_7, 4);
x_196 = lean_unsigned_to_nat(2u);
x_197 = lean_nat_mul(x_196, x_190);
x_198 = lean_nat_dec_lt(x_191, x_197);
lean_dec(x_197);
if (x_198 == 0)
{
lean_object* x_199; uint8_t x_200; uint8_t x_237; 
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_del_object(x_188);
x_237 = !lean_is_exclusive(x_7);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_238 = lean_ctor_get(x_7, 4);
lean_dec(x_238);
x_239 = lean_ctor_get(x_7, 3);
lean_dec(x_239);
x_240 = lean_ctor_get(x_7, 2);
lean_dec(x_240);
x_241 = lean_ctor_get(x_7, 1);
lean_dec(x_241);
x_242 = lean_ctor_get(x_7, 0);
lean_dec(x_242);
x_199 = x_7;
x_200 = x_237;
goto block_236;
}
else
{
lean_dec(x_7);
x_199 = lean_box(0);
x_200 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_224; lean_object* x_225; 
x_201 = lean_unsigned_to_nat(1u);
x_202 = lean_nat_add(x_201, x_3);
lean_dec(x_3);
x_203 = lean_nat_add(x_202, x_179);
lean_dec(x_202);
x_224 = lean_nat_add(x_201, x_190);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_194, 0);
lean_inc(x_234);
x_225 = x_234;
goto block_233;
}
else
{
lean_object* x_235; 
x_235 = lean_unsigned_to_nat(0u);
x_225 = x_235;
goto block_233;
}
block_223:
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_nat_add(x_204, x_206);
lean_dec(x_206);
lean_dec(x_204);
lean_inc_ref(x_176);
if (x_200 == 0)
{
lean_ctor_set(x_199, 4, x_176);
lean_ctor_set(x_199, 3, x_195);
lean_ctor_set(x_199, 2, x_178);
lean_ctor_set(x_199, 1, x_177);
lean_ctor_set(x_199, 0, x_207);
x_208 = x_199;
goto block_221;
}
else
{
lean_object* x_222; 
x_222 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_222, 0, x_207);
lean_ctor_set(x_222, 1, x_177);
lean_ctor_set(x_222, 2, x_178);
lean_ctor_set(x_222, 3, x_195);
lean_ctor_set(x_222, 4, x_176);
x_208 = x_222;
goto block_221;
}
block_221:
{
lean_object* x_209; uint8_t x_210; uint8_t x_215; 
x_215 = !lean_is_exclusive(x_176);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_ctor_get(x_176, 4);
lean_dec(x_216);
x_217 = lean_ctor_get(x_176, 3);
lean_dec(x_217);
x_218 = lean_ctor_get(x_176, 2);
lean_dec(x_218);
x_219 = lean_ctor_get(x_176, 1);
lean_dec(x_219);
x_220 = lean_ctor_get(x_176, 0);
lean_dec(x_220);
x_209 = x_176;
x_210 = x_215;
goto block_214;
}
else
{
lean_dec(x_176);
x_209 = lean_box(0);
x_210 = x_215;
goto block_214;
}
block_214:
{
lean_object* x_211; 
if (x_210 == 0)
{
lean_ctor_set(x_209, 4, x_208);
lean_ctor_set(x_209, 3, x_205);
lean_ctor_set(x_209, 2, x_193);
lean_ctor_set(x_209, 1, x_192);
lean_ctor_set(x_209, 0, x_203);
x_211 = x_209;
goto block_212;
}
else
{
lean_object* x_213; 
x_213 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_213, 0, x_203);
lean_ctor_set(x_213, 1, x_192);
lean_ctor_set(x_213, 2, x_193);
lean_ctor_set(x_213, 3, x_205);
lean_ctor_set(x_213, 4, x_208);
x_211 = x_213;
goto block_212;
}
block_212:
{
return x_211;
}
}
}
}
block_233:
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_nat_add(x_224, x_225);
lean_dec(x_225);
lean_dec(x_224);
if (x_174 == 0)
{
lean_ctor_set(x_173, 4, x_194);
lean_ctor_set(x_173, 3, x_6);
lean_ctor_set(x_173, 2, x_5);
lean_ctor_set(x_173, 1, x_4);
lean_ctor_set(x_173, 0, x_226);
x_227 = x_173;
goto block_231;
}
else
{
lean_object* x_232; 
x_232 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_232, 0, x_226);
lean_ctor_set(x_232, 1, x_4);
lean_ctor_set(x_232, 2, x_5);
lean_ctor_set(x_232, 3, x_6);
lean_ctor_set(x_232, 4, x_194);
x_227 = x_232;
goto block_231;
}
block_231:
{
lean_object* x_228; 
x_228 = lean_nat_add(x_201, x_179);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_195, 0);
lean_inc(x_229);
x_204 = x_228;
x_205 = x_227;
x_206 = x_229;
goto block_223;
}
else
{
lean_object* x_230; 
x_230 = lean_unsigned_to_nat(0u);
x_204 = x_228;
x_205 = x_227;
x_206 = x_230;
goto block_223;
}
}
}
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_243 = lean_unsigned_to_nat(1u);
x_244 = lean_nat_add(x_243, x_3);
lean_dec(x_3);
x_245 = lean_nat_add(x_244, x_179);
lean_dec(x_244);
x_246 = lean_nat_add(x_243, x_179);
x_247 = lean_nat_add(x_246, x_191);
lean_dec(x_246);
if (x_174 == 0)
{
lean_ctor_set(x_173, 4, x_176);
lean_ctor_set(x_173, 3, x_7);
lean_ctor_set(x_173, 2, x_178);
lean_ctor_set(x_173, 1, x_177);
lean_ctor_set(x_173, 0, x_247);
x_248 = x_173;
goto block_252;
}
else
{
lean_object* x_253; 
x_253 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_253, 0, x_247);
lean_ctor_set(x_253, 1, x_177);
lean_ctor_set(x_253, 2, x_178);
lean_ctor_set(x_253, 3, x_7);
lean_ctor_set(x_253, 4, x_176);
x_248 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_249; 
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_248);
lean_ctor_set(x_188, 0, x_245);
x_249 = x_188;
goto block_250;
}
else
{
lean_object* x_251; 
x_251 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_251, 0, x_245);
lean_ctor_set(x_251, 1, x_4);
lean_ctor_set(x_251, 2, x_5);
lean_ctor_set(x_251, 3, x_6);
lean_ctor_set(x_251, 4, x_248);
x_249 = x_251;
goto block_250;
}
block_250:
{
return x_249;
}
}
}
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_dec_ref(x_6);
lean_del_object(x_188);
lean_dec(x_178);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_del_object(x_173);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_254 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2);
x_255 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_254);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_del_object(x_188);
lean_dec(x_178);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_del_object(x_173);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_256 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3);
x_257 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_256);
return x_257;
}
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_265; uint8_t x_266; uint8_t x_289; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_289 = !lean_is_exclusive(x_1);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_290 = lean_ctor_get(x_1, 4);
lean_dec(x_290);
x_291 = lean_ctor_get(x_1, 3);
lean_dec(x_291);
x_292 = lean_ctor_get(x_1, 2);
lean_dec(x_292);
x_293 = lean_ctor_get(x_1, 1);
lean_dec(x_293);
x_294 = lean_ctor_get(x_1, 0);
lean_dec(x_294);
x_265 = x_1;
x_266 = x_289;
goto block_288;
}
else
{
lean_dec(x_1);
x_265 = lean_box(0);
x_266 = x_289;
goto block_288;
}
block_288:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_267 = lean_ctor_get(x_175, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_175, 1);
lean_inc(x_268);
lean_dec_ref(x_175);
x_269 = lean_ctor_get(x_7, 0);
x_270 = lean_unsigned_to_nat(1u);
x_271 = lean_nat_add(x_270, x_3);
lean_dec(x_3);
x_272 = lean_nat_add(x_270, x_269);
if (x_174 == 0)
{
lean_ctor_set(x_173, 4, x_176);
lean_ctor_set(x_173, 3, x_7);
lean_ctor_set(x_173, 2, x_268);
lean_ctor_set(x_173, 1, x_267);
lean_ctor_set(x_173, 0, x_272);
x_273 = x_173;
goto block_277;
}
else
{
lean_object* x_278; 
x_278 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_278, 0, x_272);
lean_ctor_set(x_278, 1, x_267);
lean_ctor_set(x_278, 2, x_268);
lean_ctor_set(x_278, 3, x_7);
lean_ctor_set(x_278, 4, x_176);
x_273 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_274; 
if (x_266 == 0)
{
lean_ctor_set(x_265, 4, x_273);
lean_ctor_set(x_265, 0, x_271);
x_274 = x_265;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_276, 0, x_271);
lean_ctor_set(x_276, 1, x_4);
lean_ctor_set(x_276, 2, x_5);
lean_ctor_set(x_276, 3, x_6);
lean_ctor_set(x_276, 4, x_273);
x_274 = x_276;
goto block_275;
}
block_275:
{
return x_274;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_3);
x_279 = lean_ctor_get(x_175, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_175, 1);
lean_inc(x_280);
lean_dec_ref(x_175);
x_281 = lean_unsigned_to_nat(1u);
if (x_174 == 0)
{
lean_ctor_set(x_173, 4, x_7);
lean_ctor_set(x_173, 3, x_7);
lean_ctor_set(x_173, 2, x_280);
lean_ctor_set(x_173, 1, x_279);
lean_ctor_set(x_173, 0, x_281);
x_282 = x_173;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_287, 0, x_281);
lean_ctor_set(x_287, 1, x_279);
lean_ctor_set(x_287, 2, x_280);
lean_ctor_set(x_287, 3, x_7);
lean_ctor_set(x_287, 4, x_7);
x_282 = x_287;
goto block_286;
}
block_286:
{
lean_object* x_283; 
if (x_266 == 0)
{
lean_ctor_set(x_265, 4, x_282);
lean_ctor_set(x_265, 0, x_13);
x_283 = x_265;
goto block_284;
}
else
{
lean_object* x_285; 
x_285 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_285, 0, x_13);
lean_ctor_set(x_285, 1, x_4);
lean_ctor_set(x_285, 2, x_5);
lean_ctor_set(x_285, 3, x_6);
lean_ctor_set(x_285, 4, x_282);
x_283 = x_285;
goto block_284;
}
block_284:
{
return x_283;
}
}
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_295; uint8_t x_296; uint8_t x_319; 
lean_inc(x_5);
lean_inc(x_4);
x_319 = !lean_is_exclusive(x_1);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_320 = lean_ctor_get(x_1, 4);
lean_dec(x_320);
x_321 = lean_ctor_get(x_1, 3);
lean_dec(x_321);
x_322 = lean_ctor_get(x_1, 2);
lean_dec(x_322);
x_323 = lean_ctor_get(x_1, 1);
lean_dec(x_323);
x_324 = lean_ctor_get(x_1, 0);
lean_dec(x_324);
x_295 = x_1;
x_296 = x_319;
goto block_318;
}
else
{
lean_dec(x_1);
x_295 = lean_box(0);
x_296 = x_319;
goto block_318;
}
block_318:
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; uint8_t x_314; 
x_297 = lean_ctor_get(x_175, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_175, 1);
lean_inc(x_298);
lean_dec_ref(x_175);
x_299 = lean_ctor_get(x_7, 1);
x_300 = lean_ctor_get(x_7, 2);
x_314 = !lean_is_exclusive(x_7);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_7, 4);
lean_dec(x_315);
x_316 = lean_ctor_get(x_7, 3);
lean_dec(x_316);
x_317 = lean_ctor_get(x_7, 0);
lean_dec(x_317);
x_301 = x_7;
x_302 = x_314;
goto block_313;
}
else
{
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_7);
x_301 = lean_box(0);
x_302 = x_314;
goto block_313;
}
block_313:
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_unsigned_to_nat(1u);
if (x_302 == 0)
{
lean_ctor_set(x_301, 4, x_6);
lean_ctor_set(x_301, 3, x_6);
lean_ctor_set(x_301, 2, x_5);
lean_ctor_set(x_301, 1, x_4);
lean_ctor_set(x_301, 0, x_303);
x_304 = x_301;
goto block_311;
}
else
{
lean_object* x_312; 
x_312 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_312, 0, x_303);
lean_ctor_set(x_312, 1, x_4);
lean_ctor_set(x_312, 2, x_5);
lean_ctor_set(x_312, 3, x_6);
lean_ctor_set(x_312, 4, x_6);
x_304 = x_312;
goto block_311;
}
block_311:
{
lean_object* x_305; 
if (x_174 == 0)
{
lean_ctor_set(x_173, 4, x_6);
lean_ctor_set(x_173, 3, x_6);
lean_ctor_set(x_173, 2, x_298);
lean_ctor_set(x_173, 1, x_297);
lean_ctor_set(x_173, 0, x_303);
x_305 = x_173;
goto block_309;
}
else
{
lean_object* x_310; 
x_310 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_310, 0, x_303);
lean_ctor_set(x_310, 1, x_297);
lean_ctor_set(x_310, 2, x_298);
lean_ctor_set(x_310, 3, x_6);
lean_ctor_set(x_310, 4, x_6);
x_305 = x_310;
goto block_309;
}
block_309:
{
lean_object* x_306; 
if (x_296 == 0)
{
lean_ctor_set(x_295, 4, x_305);
lean_ctor_set(x_295, 3, x_304);
lean_ctor_set(x_295, 2, x_300);
lean_ctor_set(x_295, 1, x_299);
lean_ctor_set(x_295, 0, x_13);
x_306 = x_295;
goto block_307;
}
else
{
lean_object* x_308; 
x_308 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_308, 0, x_13);
lean_ctor_set(x_308, 1, x_299);
lean_ctor_set(x_308, 2, x_300);
lean_ctor_set(x_308, 3, x_304);
lean_ctor_set(x_308, 4, x_305);
x_306 = x_308;
goto block_307;
}
block_307:
{
return x_306;
}
}
}
}
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = lean_ctor_get(x_175, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_175, 1);
lean_inc(x_326);
lean_dec_ref(x_175);
x_327 = lean_unsigned_to_nat(2u);
if (x_174 == 0)
{
lean_ctor_set(x_173, 4, x_7);
lean_ctor_set(x_173, 3, x_1);
lean_ctor_set(x_173, 2, x_326);
lean_ctor_set(x_173, 1, x_325);
lean_ctor_set(x_173, 0, x_327);
x_328 = x_173;
goto block_329;
}
else
{
lean_object* x_330; 
x_330 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_325);
lean_ctor_set(x_330, 2, x_326);
lean_ctor_set(x_330, 3, x_1);
lean_ctor_set(x_330, 4, x_7);
x_328 = x_330;
goto block_329;
}
block_329:
{
return x_328;
}
}
}
}
}
}
}
else
{
lean_object* x_338; uint8_t x_339; uint8_t x_511; 
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_12);
lean_dec(x_11);
x_511 = !lean_is_exclusive(x_1);
if (x_511 == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_512 = lean_ctor_get(x_1, 4);
lean_dec(x_512);
x_513 = lean_ctor_get(x_1, 3);
lean_dec(x_513);
x_514 = lean_ctor_get(x_1, 2);
lean_dec(x_514);
x_515 = lean_ctor_get(x_1, 1);
lean_dec(x_515);
x_516 = lean_ctor_get(x_1, 0);
lean_dec(x_516);
x_338 = x_1;
x_339 = x_511;
goto block_510;
}
else
{
lean_dec(x_1);
x_338 = lean_box(0);
x_339 = x_511;
goto block_510;
}
block_510:
{
lean_object* x_340; 
x_340 = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(x_7, x_2);
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_341 = lean_ctor_get(x_6, 0);
x_342 = lean_ctor_get(x_340, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_340, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_340, 2);
lean_inc(x_344);
x_345 = lean_ctor_get(x_340, 3);
lean_inc(x_345);
x_346 = lean_ctor_get(x_340, 4);
lean_inc(x_346);
x_347 = lean_nat_mul(x_13, x_341);
x_348 = lean_nat_dec_lt(x_347, x_342);
lean_dec(x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
x_349 = lean_unsigned_to_nat(1u);
x_350 = lean_nat_add(x_349, x_341);
x_351 = lean_nat_add(x_350, x_342);
lean_dec(x_342);
lean_dec(x_350);
if (x_339 == 0)
{
lean_ctor_set(x_338, 4, x_340);
lean_ctor_set(x_338, 0, x_351);
x_352 = x_338;
goto block_353;
}
else
{
lean_object* x_354; 
x_354 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_4);
lean_ctor_set(x_354, 2, x_5);
lean_ctor_set(x_354, 3, x_6);
lean_ctor_set(x_354, 4, x_340);
x_352 = x_354;
goto block_353;
}
block_353:
{
return x_352;
}
}
else
{
lean_object* x_355; uint8_t x_356; uint8_t x_424; 
x_424 = !lean_is_exclusive(x_340);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_425 = lean_ctor_get(x_340, 4);
lean_dec(x_425);
x_426 = lean_ctor_get(x_340, 3);
lean_dec(x_426);
x_427 = lean_ctor_get(x_340, 2);
lean_dec(x_427);
x_428 = lean_ctor_get(x_340, 1);
lean_dec(x_428);
x_429 = lean_ctor_get(x_340, 0);
lean_dec(x_429);
x_355 = x_340;
x_356 = x_424;
goto block_423;
}
else
{
lean_dec(x_340);
x_355 = lean_box(0);
x_356 = x_424;
goto block_423;
}
block_423:
{
if (lean_obj_tag(x_345) == 0)
{
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; 
x_357 = lean_ctor_get(x_345, 0);
x_358 = lean_ctor_get(x_345, 1);
x_359 = lean_ctor_get(x_345, 2);
x_360 = lean_ctor_get(x_345, 3);
x_361 = lean_ctor_get(x_345, 4);
x_362 = lean_ctor_get(x_346, 0);
x_363 = lean_unsigned_to_nat(2u);
x_364 = lean_nat_mul(x_363, x_362);
x_365 = lean_nat_dec_lt(x_357, x_364);
lean_dec(x_364);
if (x_365 == 0)
{
lean_object* x_366; uint8_t x_367; uint8_t x_394; 
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
x_394 = !lean_is_exclusive(x_345);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_395 = lean_ctor_get(x_345, 4);
lean_dec(x_395);
x_396 = lean_ctor_get(x_345, 3);
lean_dec(x_396);
x_397 = lean_ctor_get(x_345, 2);
lean_dec(x_397);
x_398 = lean_ctor_get(x_345, 1);
lean_dec(x_398);
x_399 = lean_ctor_get(x_345, 0);
lean_dec(x_399);
x_366 = x_345;
x_367 = x_394;
goto block_393;
}
else
{
lean_dec(x_345);
x_366 = lean_box(0);
x_367 = x_394;
goto block_393;
}
block_393:
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_382; 
x_368 = lean_unsigned_to_nat(1u);
x_369 = lean_nat_add(x_368, x_341);
x_370 = lean_nat_add(x_369, x_342);
lean_dec(x_342);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_391; 
x_391 = lean_ctor_get(x_360, 0);
lean_inc(x_391);
x_382 = x_391;
goto block_390;
}
else
{
lean_object* x_392; 
x_392 = lean_unsigned_to_nat(0u);
x_382 = x_392;
goto block_390;
}
block_381:
{
lean_object* x_374; lean_object* x_375; 
x_374 = lean_nat_add(x_372, x_373);
lean_dec(x_373);
lean_dec(x_372);
if (x_367 == 0)
{
lean_ctor_set(x_366, 4, x_346);
lean_ctor_set(x_366, 3, x_361);
lean_ctor_set(x_366, 2, x_344);
lean_ctor_set(x_366, 1, x_343);
lean_ctor_set(x_366, 0, x_374);
x_375 = x_366;
goto block_379;
}
else
{
lean_object* x_380; 
x_380 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_380, 0, x_374);
lean_ctor_set(x_380, 1, x_343);
lean_ctor_set(x_380, 2, x_344);
lean_ctor_set(x_380, 3, x_361);
lean_ctor_set(x_380, 4, x_346);
x_375 = x_380;
goto block_379;
}
block_379:
{
lean_object* x_376; 
if (x_356 == 0)
{
lean_ctor_set(x_355, 4, x_375);
lean_ctor_set(x_355, 3, x_371);
lean_ctor_set(x_355, 2, x_359);
lean_ctor_set(x_355, 1, x_358);
lean_ctor_set(x_355, 0, x_370);
x_376 = x_355;
goto block_377;
}
else
{
lean_object* x_378; 
x_378 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_378, 0, x_370);
lean_ctor_set(x_378, 1, x_358);
lean_ctor_set(x_378, 2, x_359);
lean_ctor_set(x_378, 3, x_371);
lean_ctor_set(x_378, 4, x_375);
x_376 = x_378;
goto block_377;
}
block_377:
{
return x_376;
}
}
}
block_390:
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_nat_add(x_369, x_382);
lean_dec(x_382);
lean_dec(x_369);
if (x_339 == 0)
{
lean_ctor_set(x_338, 4, x_360);
lean_ctor_set(x_338, 0, x_383);
x_384 = x_338;
goto block_388;
}
else
{
lean_object* x_389; 
x_389 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_389, 0, x_383);
lean_ctor_set(x_389, 1, x_4);
lean_ctor_set(x_389, 2, x_5);
lean_ctor_set(x_389, 3, x_6);
lean_ctor_set(x_389, 4, x_360);
x_384 = x_389;
goto block_388;
}
block_388:
{
lean_object* x_385; 
x_385 = lean_nat_add(x_368, x_362);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_386; 
x_386 = lean_ctor_get(x_361, 0);
lean_inc(x_386);
x_371 = x_384;
x_372 = x_385;
x_373 = x_386;
goto block_381;
}
else
{
lean_object* x_387; 
x_387 = lean_unsigned_to_nat(0u);
x_371 = x_384;
x_372 = x_385;
x_373 = x_387;
goto block_381;
}
}
}
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_del_object(x_338);
x_400 = lean_unsigned_to_nat(1u);
x_401 = lean_nat_add(x_400, x_341);
x_402 = lean_nat_add(x_401, x_342);
lean_dec(x_342);
x_403 = lean_nat_add(x_401, x_357);
lean_dec(x_401);
lean_inc_ref(x_6);
if (x_356 == 0)
{
lean_ctor_set(x_355, 4, x_345);
lean_ctor_set(x_355, 3, x_6);
lean_ctor_set(x_355, 2, x_5);
lean_ctor_set(x_355, 1, x_4);
lean_ctor_set(x_355, 0, x_403);
x_404 = x_355;
goto block_417;
}
else
{
lean_object* x_418; 
x_418 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_418, 0, x_403);
lean_ctor_set(x_418, 1, x_4);
lean_ctor_set(x_418, 2, x_5);
lean_ctor_set(x_418, 3, x_6);
lean_ctor_set(x_418, 4, x_345);
x_404 = x_418;
goto block_417;
}
block_417:
{
lean_object* x_405; uint8_t x_406; uint8_t x_411; 
x_411 = !lean_is_exclusive(x_6);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_412 = lean_ctor_get(x_6, 4);
lean_dec(x_412);
x_413 = lean_ctor_get(x_6, 3);
lean_dec(x_413);
x_414 = lean_ctor_get(x_6, 2);
lean_dec(x_414);
x_415 = lean_ctor_get(x_6, 1);
lean_dec(x_415);
x_416 = lean_ctor_get(x_6, 0);
lean_dec(x_416);
x_405 = x_6;
x_406 = x_411;
goto block_410;
}
else
{
lean_dec(x_6);
x_405 = lean_box(0);
x_406 = x_411;
goto block_410;
}
block_410:
{
lean_object* x_407; 
if (x_406 == 0)
{
lean_ctor_set(x_405, 4, x_346);
lean_ctor_set(x_405, 3, x_404);
lean_ctor_set(x_405, 2, x_344);
lean_ctor_set(x_405, 1, x_343);
lean_ctor_set(x_405, 0, x_402);
x_407 = x_405;
goto block_408;
}
else
{
lean_object* x_409; 
x_409 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_409, 0, x_402);
lean_ctor_set(x_409, 1, x_343);
lean_ctor_set(x_409, 2, x_344);
lean_ctor_set(x_409, 3, x_404);
lean_ctor_set(x_409, 4, x_346);
x_407 = x_409;
goto block_408;
}
block_408:
{
return x_407;
}
}
}
}
}
else
{
lean_object* x_419; lean_object* x_420; 
lean_dec_ref(x_345);
lean_del_object(x_355);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
lean_dec_ref(x_6);
lean_del_object(x_338);
lean_dec(x_5);
lean_dec(x_4);
x_419 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3);
x_420 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_419);
return x_420;
}
}
else
{
lean_object* x_421; lean_object* x_422; 
lean_del_object(x_355);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
lean_dec_ref(x_6);
lean_del_object(x_338);
lean_dec(x_5);
lean_dec(x_4);
x_421 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4);
x_422 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_421);
return x_422;
}
}
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_430 = lean_ctor_get(x_6, 0);
x_431 = lean_unsigned_to_nat(1u);
x_432 = lean_nat_add(x_431, x_430);
if (x_339 == 0)
{
lean_ctor_set(x_338, 4, x_340);
lean_ctor_set(x_338, 0, x_432);
x_433 = x_338;
goto block_434;
}
else
{
lean_object* x_435; 
x_435 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_435, 0, x_432);
lean_ctor_set(x_435, 1, x_4);
lean_ctor_set(x_435, 2, x_5);
lean_ctor_set(x_435, 3, x_6);
lean_ctor_set(x_435, 4, x_340);
x_433 = x_435;
goto block_434;
}
block_434:
{
return x_433;
}
}
}
else
{
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_436; 
x_436 = lean_ctor_get(x_340, 3);
lean_inc(x_436);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; 
x_437 = lean_ctor_get(x_340, 4);
lean_inc(x_437);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; uint8_t x_454; 
x_438 = lean_ctor_get(x_340, 0);
x_439 = lean_ctor_get(x_340, 1);
x_440 = lean_ctor_get(x_340, 2);
x_454 = !lean_is_exclusive(x_340);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; 
x_455 = lean_ctor_get(x_340, 4);
lean_dec(x_455);
x_456 = lean_ctor_get(x_340, 3);
lean_dec(x_456);
x_441 = x_340;
x_442 = x_454;
goto block_453;
}
else
{
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
lean_dec(x_340);
x_441 = lean_box(0);
x_442 = x_454;
goto block_453;
}
block_453:
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_443 = lean_ctor_get(x_436, 0);
x_444 = lean_unsigned_to_nat(1u);
x_445 = lean_nat_add(x_444, x_438);
lean_dec(x_438);
x_446 = lean_nat_add(x_444, x_443);
if (x_442 == 0)
{
lean_ctor_set(x_441, 4, x_436);
lean_ctor_set(x_441, 3, x_6);
lean_ctor_set(x_441, 2, x_5);
lean_ctor_set(x_441, 1, x_4);
lean_ctor_set(x_441, 0, x_446);
x_447 = x_441;
goto block_451;
}
else
{
lean_object* x_452; 
x_452 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_452, 0, x_446);
lean_ctor_set(x_452, 1, x_4);
lean_ctor_set(x_452, 2, x_5);
lean_ctor_set(x_452, 3, x_6);
lean_ctor_set(x_452, 4, x_436);
x_447 = x_452;
goto block_451;
}
block_451:
{
lean_object* x_448; 
if (x_339 == 0)
{
lean_ctor_set(x_338, 4, x_437);
lean_ctor_set(x_338, 3, x_447);
lean_ctor_set(x_338, 2, x_440);
lean_ctor_set(x_338, 1, x_439);
lean_ctor_set(x_338, 0, x_445);
x_448 = x_338;
goto block_449;
}
else
{
lean_object* x_450; 
x_450 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_450, 0, x_445);
lean_ctor_set(x_450, 1, x_439);
lean_ctor_set(x_450, 2, x_440);
lean_ctor_set(x_450, 3, x_447);
lean_ctor_set(x_450, 4, x_437);
x_448 = x_450;
goto block_449;
}
block_449:
{
return x_448;
}
}
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; uint8_t x_460; uint8_t x_481; 
x_457 = lean_ctor_get(x_340, 1);
x_458 = lean_ctor_get(x_340, 2);
x_481 = !lean_is_exclusive(x_340);
if (x_481 == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_340, 4);
lean_dec(x_482);
x_483 = lean_ctor_get(x_340, 3);
lean_dec(x_483);
x_484 = lean_ctor_get(x_340, 0);
lean_dec(x_484);
x_459 = x_340;
x_460 = x_481;
goto block_480;
}
else
{
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_340);
x_459 = lean_box(0);
x_460 = x_481;
goto block_480;
}
block_480:
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; uint8_t x_476; 
x_461 = lean_ctor_get(x_436, 1);
x_462 = lean_ctor_get(x_436, 2);
x_476 = !lean_is_exclusive(x_436);
if (x_476 == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_436, 4);
lean_dec(x_477);
x_478 = lean_ctor_get(x_436, 3);
lean_dec(x_478);
x_479 = lean_ctor_get(x_436, 0);
lean_dec(x_479);
x_463 = x_436;
x_464 = x_476;
goto block_475;
}
else
{
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_436);
x_463 = lean_box(0);
x_464 = x_476;
goto block_475;
}
block_475:
{
lean_object* x_465; lean_object* x_466; 
x_465 = lean_unsigned_to_nat(1u);
if (x_464 == 0)
{
lean_ctor_set(x_463, 4, x_437);
lean_ctor_set(x_463, 3, x_437);
lean_ctor_set(x_463, 2, x_5);
lean_ctor_set(x_463, 1, x_4);
lean_ctor_set(x_463, 0, x_465);
x_466 = x_463;
goto block_473;
}
else
{
lean_object* x_474; 
x_474 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_474, 0, x_465);
lean_ctor_set(x_474, 1, x_4);
lean_ctor_set(x_474, 2, x_5);
lean_ctor_set(x_474, 3, x_437);
lean_ctor_set(x_474, 4, x_437);
x_466 = x_474;
goto block_473;
}
block_473:
{
lean_object* x_467; 
if (x_460 == 0)
{
lean_ctor_set(x_459, 3, x_437);
lean_ctor_set(x_459, 0, x_465);
x_467 = x_459;
goto block_471;
}
else
{
lean_object* x_472; 
x_472 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_472, 0, x_465);
lean_ctor_set(x_472, 1, x_457);
lean_ctor_set(x_472, 2, x_458);
lean_ctor_set(x_472, 3, x_437);
lean_ctor_set(x_472, 4, x_437);
x_467 = x_472;
goto block_471;
}
block_471:
{
lean_object* x_468; 
if (x_339 == 0)
{
lean_ctor_set(x_338, 4, x_467);
lean_ctor_set(x_338, 3, x_466);
lean_ctor_set(x_338, 2, x_462);
lean_ctor_set(x_338, 1, x_461);
lean_ctor_set(x_338, 0, x_13);
x_468 = x_338;
goto block_469;
}
else
{
lean_object* x_470; 
x_470 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_470, 0, x_13);
lean_ctor_set(x_470, 1, x_461);
lean_ctor_set(x_470, 2, x_462);
lean_ctor_set(x_470, 3, x_466);
lean_ctor_set(x_470, 4, x_467);
x_468 = x_470;
goto block_469;
}
block_469:
{
return x_468;
}
}
}
}
}
}
}
else
{
lean_object* x_485; 
x_485 = lean_ctor_get(x_340, 4);
lean_inc(x_485);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; uint8_t x_489; uint8_t x_498; 
x_486 = lean_ctor_get(x_340, 1);
x_487 = lean_ctor_get(x_340, 2);
x_498 = !lean_is_exclusive(x_340);
if (x_498 == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_499 = lean_ctor_get(x_340, 4);
lean_dec(x_499);
x_500 = lean_ctor_get(x_340, 3);
lean_dec(x_500);
x_501 = lean_ctor_get(x_340, 0);
lean_dec(x_501);
x_488 = x_340;
x_489 = x_498;
goto block_497;
}
else
{
lean_inc(x_487);
lean_inc(x_486);
lean_dec(x_340);
x_488 = lean_box(0);
x_489 = x_498;
goto block_497;
}
block_497:
{
lean_object* x_490; lean_object* x_491; 
x_490 = lean_unsigned_to_nat(1u);
if (x_489 == 0)
{
lean_ctor_set(x_488, 4, x_436);
lean_ctor_set(x_488, 2, x_5);
lean_ctor_set(x_488, 1, x_4);
lean_ctor_set(x_488, 0, x_490);
x_491 = x_488;
goto block_495;
}
else
{
lean_object* x_496; 
x_496 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_496, 0, x_490);
lean_ctor_set(x_496, 1, x_4);
lean_ctor_set(x_496, 2, x_5);
lean_ctor_set(x_496, 3, x_436);
lean_ctor_set(x_496, 4, x_436);
x_491 = x_496;
goto block_495;
}
block_495:
{
lean_object* x_492; 
if (x_339 == 0)
{
lean_ctor_set(x_338, 4, x_485);
lean_ctor_set(x_338, 3, x_491);
lean_ctor_set(x_338, 2, x_487);
lean_ctor_set(x_338, 1, x_486);
lean_ctor_set(x_338, 0, x_13);
x_492 = x_338;
goto block_493;
}
else
{
lean_object* x_494; 
x_494 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_494, 0, x_13);
lean_ctor_set(x_494, 1, x_486);
lean_ctor_set(x_494, 2, x_487);
lean_ctor_set(x_494, 3, x_491);
lean_ctor_set(x_494, 4, x_485);
x_492 = x_494;
goto block_493;
}
block_493:
{
return x_492;
}
}
}
}
else
{
lean_object* x_502; lean_object* x_503; 
x_502 = lean_unsigned_to_nat(2u);
if (x_339 == 0)
{
lean_ctor_set(x_338, 4, x_340);
lean_ctor_set(x_338, 3, x_485);
lean_ctor_set(x_338, 0, x_502);
x_503 = x_338;
goto block_504;
}
else
{
lean_object* x_505; 
x_505 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_505, 0, x_502);
lean_ctor_set(x_505, 1, x_4);
lean_ctor_set(x_505, 2, x_5);
lean_ctor_set(x_505, 3, x_485);
lean_ctor_set(x_505, 4, x_340);
x_503 = x_505;
goto block_504;
}
block_504:
{
return x_503;
}
}
}
}
else
{
lean_object* x_506; lean_object* x_507; 
x_506 = lean_unsigned_to_nat(1u);
if (x_339 == 0)
{
lean_ctor_set(x_338, 4, x_340);
lean_ctor_set(x_338, 3, x_340);
lean_ctor_set(x_338, 0, x_506);
x_507 = x_338;
goto block_508;
}
else
{
lean_object* x_509; 
x_509 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_509, 0, x_506);
lean_ctor_set(x_509, 1, x_4);
lean_ctor_set(x_509, 2, x_5);
lean_ctor_set(x_509, 3, x_340);
lean_ctor_set(x_509, 4, x_340);
x_507 = x_509;
goto block_508;
}
block_508:
{
return x_507;
}
}
}
}
}
}
else
{
lean_object* x_517; uint8_t x_518; uint8_t x_692; 
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_692 = !lean_is_exclusive(x_2);
if (x_692 == 0)
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_693 = lean_ctor_get(x_2, 4);
lean_dec(x_693);
x_694 = lean_ctor_get(x_2, 3);
lean_dec(x_694);
x_695 = lean_ctor_get(x_2, 2);
lean_dec(x_695);
x_696 = lean_ctor_get(x_2, 1);
lean_dec(x_696);
x_697 = lean_ctor_get(x_2, 0);
lean_dec(x_697);
x_517 = x_2;
x_518 = x_692;
goto block_691;
}
else
{
lean_dec(x_2);
x_517 = lean_box(0);
x_518 = x_692;
goto block_691;
}
block_691:
{
lean_object* x_519; 
x_519 = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; 
x_520 = lean_ctor_get(x_12, 0);
x_521 = lean_ctor_get(x_519, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_519, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_519, 2);
lean_inc(x_523);
x_524 = lean_ctor_get(x_519, 3);
lean_inc(x_524);
x_525 = lean_ctor_get(x_519, 4);
lean_inc(x_525);
x_526 = lean_nat_mul(x_13, x_520);
x_527 = lean_nat_dec_lt(x_526, x_521);
lean_dec(x_526);
if (x_527 == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_522);
x_528 = lean_unsigned_to_nat(1u);
x_529 = lean_nat_add(x_528, x_521);
lean_dec(x_521);
x_530 = lean_nat_add(x_529, x_520);
lean_dec(x_529);
if (x_518 == 0)
{
lean_ctor_set(x_517, 3, x_519);
lean_ctor_set(x_517, 0, x_530);
x_531 = x_517;
goto block_532;
}
else
{
lean_object* x_533; 
x_533 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_533, 0, x_530);
lean_ctor_set(x_533, 1, x_9);
lean_ctor_set(x_533, 2, x_10);
lean_ctor_set(x_533, 3, x_519);
lean_ctor_set(x_533, 4, x_12);
x_531 = x_533;
goto block_532;
}
block_532:
{
return x_531;
}
}
else
{
lean_object* x_534; uint8_t x_535; uint8_t x_605; 
x_605 = !lean_is_exclusive(x_519);
if (x_605 == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_606 = lean_ctor_get(x_519, 4);
lean_dec(x_606);
x_607 = lean_ctor_get(x_519, 3);
lean_dec(x_607);
x_608 = lean_ctor_get(x_519, 2);
lean_dec(x_608);
x_609 = lean_ctor_get(x_519, 1);
lean_dec(x_609);
x_610 = lean_ctor_get(x_519, 0);
lean_dec(x_610);
x_534 = x_519;
x_535 = x_605;
goto block_604;
}
else
{
lean_dec(x_519);
x_534 = lean_box(0);
x_535 = x_605;
goto block_604;
}
block_604:
{
if (lean_obj_tag(x_524) == 0)
{
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; uint8_t x_544; 
x_536 = lean_ctor_get(x_524, 0);
x_537 = lean_ctor_get(x_525, 0);
x_538 = lean_ctor_get(x_525, 1);
x_539 = lean_ctor_get(x_525, 2);
x_540 = lean_ctor_get(x_525, 3);
x_541 = lean_ctor_get(x_525, 4);
x_542 = lean_unsigned_to_nat(2u);
x_543 = lean_nat_mul(x_542, x_536);
x_544 = lean_nat_dec_lt(x_537, x_543);
lean_dec(x_543);
if (x_544 == 0)
{
lean_object* x_545; uint8_t x_546; uint8_t x_574; 
lean_inc(x_541);
lean_inc(x_540);
lean_inc(x_539);
lean_inc(x_538);
x_574 = !lean_is_exclusive(x_525);
if (x_574 == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_575 = lean_ctor_get(x_525, 4);
lean_dec(x_575);
x_576 = lean_ctor_get(x_525, 3);
lean_dec(x_576);
x_577 = lean_ctor_get(x_525, 2);
lean_dec(x_577);
x_578 = lean_ctor_get(x_525, 1);
lean_dec(x_578);
x_579 = lean_ctor_get(x_525, 0);
lean_dec(x_579);
x_545 = x_525;
x_546 = x_574;
goto block_573;
}
else
{
lean_dec(x_525);
x_545 = lean_box(0);
x_546 = x_574;
goto block_573;
}
block_573:
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_561; lean_object* x_562; 
x_547 = lean_unsigned_to_nat(1u);
x_548 = lean_nat_add(x_547, x_521);
lean_dec(x_521);
x_549 = lean_nat_add(x_548, x_520);
lean_dec(x_548);
x_561 = lean_nat_add(x_547, x_536);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_571; 
x_571 = lean_ctor_get(x_540, 0);
lean_inc(x_571);
x_562 = x_571;
goto block_570;
}
else
{
lean_object* x_572; 
x_572 = lean_unsigned_to_nat(0u);
x_562 = x_572;
goto block_570;
}
block_560:
{
lean_object* x_553; lean_object* x_554; 
x_553 = lean_nat_add(x_550, x_552);
lean_dec(x_552);
lean_dec(x_550);
if (x_546 == 0)
{
lean_ctor_set(x_545, 4, x_12);
lean_ctor_set(x_545, 3, x_541);
lean_ctor_set(x_545, 2, x_10);
lean_ctor_set(x_545, 1, x_9);
lean_ctor_set(x_545, 0, x_553);
x_554 = x_545;
goto block_558;
}
else
{
lean_object* x_559; 
x_559 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_559, 0, x_553);
lean_ctor_set(x_559, 1, x_9);
lean_ctor_set(x_559, 2, x_10);
lean_ctor_set(x_559, 3, x_541);
lean_ctor_set(x_559, 4, x_12);
x_554 = x_559;
goto block_558;
}
block_558:
{
lean_object* x_555; 
if (x_535 == 0)
{
lean_ctor_set(x_534, 4, x_554);
lean_ctor_set(x_534, 3, x_551);
lean_ctor_set(x_534, 2, x_539);
lean_ctor_set(x_534, 1, x_538);
lean_ctor_set(x_534, 0, x_549);
x_555 = x_534;
goto block_556;
}
else
{
lean_object* x_557; 
x_557 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_557, 0, x_549);
lean_ctor_set(x_557, 1, x_538);
lean_ctor_set(x_557, 2, x_539);
lean_ctor_set(x_557, 3, x_551);
lean_ctor_set(x_557, 4, x_554);
x_555 = x_557;
goto block_556;
}
block_556:
{
return x_555;
}
}
}
block_570:
{
lean_object* x_563; lean_object* x_564; 
x_563 = lean_nat_add(x_561, x_562);
lean_dec(x_562);
lean_dec(x_561);
if (x_518 == 0)
{
lean_ctor_set(x_517, 4, x_540);
lean_ctor_set(x_517, 3, x_524);
lean_ctor_set(x_517, 2, x_523);
lean_ctor_set(x_517, 1, x_522);
lean_ctor_set(x_517, 0, x_563);
x_564 = x_517;
goto block_568;
}
else
{
lean_object* x_569; 
x_569 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_569, 0, x_563);
lean_ctor_set(x_569, 1, x_522);
lean_ctor_set(x_569, 2, x_523);
lean_ctor_set(x_569, 3, x_524);
lean_ctor_set(x_569, 4, x_540);
x_564 = x_569;
goto block_568;
}
block_568:
{
lean_object* x_565; 
x_565 = lean_nat_add(x_547, x_520);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_566; 
x_566 = lean_ctor_get(x_541, 0);
lean_inc(x_566);
x_550 = x_565;
x_551 = x_564;
x_552 = x_566;
goto block_560;
}
else
{
lean_object* x_567; 
x_567 = lean_unsigned_to_nat(0u);
x_550 = x_565;
x_551 = x_564;
x_552 = x_567;
goto block_560;
}
}
}
}
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
lean_del_object(x_517);
x_580 = lean_unsigned_to_nat(1u);
x_581 = lean_nat_add(x_580, x_521);
lean_dec(x_521);
x_582 = lean_nat_add(x_581, x_520);
lean_dec(x_581);
x_583 = lean_nat_add(x_580, x_520);
x_584 = lean_nat_add(x_583, x_537);
lean_dec(x_583);
lean_inc_ref(x_12);
if (x_535 == 0)
{
lean_ctor_set(x_534, 4, x_12);
lean_ctor_set(x_534, 3, x_525);
lean_ctor_set(x_534, 2, x_10);
lean_ctor_set(x_534, 1, x_9);
lean_ctor_set(x_534, 0, x_584);
x_585 = x_534;
goto block_598;
}
else
{
lean_object* x_599; 
x_599 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_599, 0, x_584);
lean_ctor_set(x_599, 1, x_9);
lean_ctor_set(x_599, 2, x_10);
lean_ctor_set(x_599, 3, x_525);
lean_ctor_set(x_599, 4, x_12);
x_585 = x_599;
goto block_598;
}
block_598:
{
lean_object* x_586; uint8_t x_587; uint8_t x_592; 
x_592 = !lean_is_exclusive(x_12);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_593 = lean_ctor_get(x_12, 4);
lean_dec(x_593);
x_594 = lean_ctor_get(x_12, 3);
lean_dec(x_594);
x_595 = lean_ctor_get(x_12, 2);
lean_dec(x_595);
x_596 = lean_ctor_get(x_12, 1);
lean_dec(x_596);
x_597 = lean_ctor_get(x_12, 0);
lean_dec(x_597);
x_586 = x_12;
x_587 = x_592;
goto block_591;
}
else
{
lean_dec(x_12);
x_586 = lean_box(0);
x_587 = x_592;
goto block_591;
}
block_591:
{
lean_object* x_588; 
if (x_587 == 0)
{
lean_ctor_set(x_586, 4, x_585);
lean_ctor_set(x_586, 3, x_524);
lean_ctor_set(x_586, 2, x_523);
lean_ctor_set(x_586, 1, x_522);
lean_ctor_set(x_586, 0, x_582);
x_588 = x_586;
goto block_589;
}
else
{
lean_object* x_590; 
x_590 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_590, 0, x_582);
lean_ctor_set(x_590, 1, x_522);
lean_ctor_set(x_590, 2, x_523);
lean_ctor_set(x_590, 3, x_524);
lean_ctor_set(x_590, 4, x_585);
x_588 = x_590;
goto block_589;
}
block_589:
{
return x_588;
}
}
}
}
}
else
{
lean_object* x_600; lean_object* x_601; 
lean_dec_ref(x_524);
lean_del_object(x_534);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_521);
lean_dec_ref(x_12);
lean_del_object(x_517);
lean_dec(x_10);
lean_dec(x_9);
x_600 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2);
x_601 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_600);
return x_601;
}
}
else
{
lean_object* x_602; lean_object* x_603; 
lean_del_object(x_534);
lean_dec(x_525);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_521);
lean_dec_ref(x_12);
lean_del_object(x_517);
lean_dec(x_10);
lean_dec(x_9);
x_602 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3);
x_603 = l_panic___at___00Std_DTreeMap_Internal_Impl_minView_x21_spec__0___redArg(x_602);
return x_603;
}
}
}
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_611 = lean_ctor_get(x_12, 0);
x_612 = lean_unsigned_to_nat(1u);
x_613 = lean_nat_add(x_612, x_611);
if (x_518 == 0)
{
lean_ctor_set(x_517, 3, x_519);
lean_ctor_set(x_517, 0, x_613);
x_614 = x_517;
goto block_615;
}
else
{
lean_object* x_616; 
x_616 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_616, 0, x_613);
lean_ctor_set(x_616, 1, x_9);
lean_ctor_set(x_616, 2, x_10);
lean_ctor_set(x_616, 3, x_519);
lean_ctor_set(x_616, 4, x_12);
x_614 = x_616;
goto block_615;
}
block_615:
{
return x_614;
}
}
}
else
{
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_617; 
x_617 = lean_ctor_get(x_519, 3);
lean_inc(x_617);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; 
x_618 = lean_ctor_get(x_519, 4);
lean_inc(x_618);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; uint8_t x_623; uint8_t x_635; 
x_619 = lean_ctor_get(x_519, 0);
x_620 = lean_ctor_get(x_519, 1);
x_621 = lean_ctor_get(x_519, 2);
x_635 = !lean_is_exclusive(x_519);
if (x_635 == 0)
{
lean_object* x_636; lean_object* x_637; 
x_636 = lean_ctor_get(x_519, 4);
lean_dec(x_636);
x_637 = lean_ctor_get(x_519, 3);
lean_dec(x_637);
x_622 = x_519;
x_623 = x_635;
goto block_634;
}
else
{
lean_inc(x_621);
lean_inc(x_620);
lean_inc(x_619);
lean_dec(x_519);
x_622 = lean_box(0);
x_623 = x_635;
goto block_634;
}
block_634:
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_624 = lean_ctor_get(x_618, 0);
x_625 = lean_unsigned_to_nat(1u);
x_626 = lean_nat_add(x_625, x_619);
lean_dec(x_619);
x_627 = lean_nat_add(x_625, x_624);
if (x_623 == 0)
{
lean_ctor_set(x_622, 4, x_12);
lean_ctor_set(x_622, 3, x_618);
lean_ctor_set(x_622, 2, x_10);
lean_ctor_set(x_622, 1, x_9);
lean_ctor_set(x_622, 0, x_627);
x_628 = x_622;
goto block_632;
}
else
{
lean_object* x_633; 
x_633 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_633, 0, x_627);
lean_ctor_set(x_633, 1, x_9);
lean_ctor_set(x_633, 2, x_10);
lean_ctor_set(x_633, 3, x_618);
lean_ctor_set(x_633, 4, x_12);
x_628 = x_633;
goto block_632;
}
block_632:
{
lean_object* x_629; 
if (x_518 == 0)
{
lean_ctor_set(x_517, 4, x_628);
lean_ctor_set(x_517, 3, x_617);
lean_ctor_set(x_517, 2, x_621);
lean_ctor_set(x_517, 1, x_620);
lean_ctor_set(x_517, 0, x_626);
x_629 = x_517;
goto block_630;
}
else
{
lean_object* x_631; 
x_631 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_631, 0, x_626);
lean_ctor_set(x_631, 1, x_620);
lean_ctor_set(x_631, 2, x_621);
lean_ctor_set(x_631, 3, x_617);
lean_ctor_set(x_631, 4, x_628);
x_629 = x_631;
goto block_630;
}
block_630:
{
return x_629;
}
}
}
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; uint8_t x_641; uint8_t x_650; 
x_638 = lean_ctor_get(x_519, 1);
x_639 = lean_ctor_get(x_519, 2);
x_650 = !lean_is_exclusive(x_519);
if (x_650 == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_651 = lean_ctor_get(x_519, 4);
lean_dec(x_651);
x_652 = lean_ctor_get(x_519, 3);
lean_dec(x_652);
x_653 = lean_ctor_get(x_519, 0);
lean_dec(x_653);
x_640 = x_519;
x_641 = x_650;
goto block_649;
}
else
{
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_519);
x_640 = lean_box(0);
x_641 = x_650;
goto block_649;
}
block_649:
{
lean_object* x_642; lean_object* x_643; 
x_642 = lean_unsigned_to_nat(1u);
if (x_641 == 0)
{
lean_ctor_set(x_640, 3, x_618);
lean_ctor_set(x_640, 2, x_10);
lean_ctor_set(x_640, 1, x_9);
lean_ctor_set(x_640, 0, x_642);
x_643 = x_640;
goto block_647;
}
else
{
lean_object* x_648; 
x_648 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_648, 0, x_642);
lean_ctor_set(x_648, 1, x_9);
lean_ctor_set(x_648, 2, x_10);
lean_ctor_set(x_648, 3, x_618);
lean_ctor_set(x_648, 4, x_618);
x_643 = x_648;
goto block_647;
}
block_647:
{
lean_object* x_644; 
if (x_518 == 0)
{
lean_ctor_set(x_517, 4, x_643);
lean_ctor_set(x_517, 3, x_617);
lean_ctor_set(x_517, 2, x_639);
lean_ctor_set(x_517, 1, x_638);
lean_ctor_set(x_517, 0, x_13);
x_644 = x_517;
goto block_645;
}
else
{
lean_object* x_646; 
x_646 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_646, 0, x_13);
lean_ctor_set(x_646, 1, x_638);
lean_ctor_set(x_646, 2, x_639);
lean_ctor_set(x_646, 3, x_617);
lean_ctor_set(x_646, 4, x_643);
x_644 = x_646;
goto block_645;
}
block_645:
{
return x_644;
}
}
}
}
}
else
{
lean_object* x_654; 
x_654 = lean_ctor_get(x_519, 4);
lean_inc(x_654);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; uint8_t x_658; uint8_t x_679; 
x_655 = lean_ctor_get(x_519, 1);
x_656 = lean_ctor_get(x_519, 2);
x_679 = !lean_is_exclusive(x_519);
if (x_679 == 0)
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_680 = lean_ctor_get(x_519, 4);
lean_dec(x_680);
x_681 = lean_ctor_get(x_519, 3);
lean_dec(x_681);
x_682 = lean_ctor_get(x_519, 0);
lean_dec(x_682);
x_657 = x_519;
x_658 = x_679;
goto block_678;
}
else
{
lean_inc(x_656);
lean_inc(x_655);
lean_dec(x_519);
x_657 = lean_box(0);
x_658 = x_679;
goto block_678;
}
block_678:
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; uint8_t x_662; uint8_t x_674; 
x_659 = lean_ctor_get(x_654, 1);
x_660 = lean_ctor_get(x_654, 2);
x_674 = !lean_is_exclusive(x_654);
if (x_674 == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_675 = lean_ctor_get(x_654, 4);
lean_dec(x_675);
x_676 = lean_ctor_get(x_654, 3);
lean_dec(x_676);
x_677 = lean_ctor_get(x_654, 0);
lean_dec(x_677);
x_661 = x_654;
x_662 = x_674;
goto block_673;
}
else
{
lean_inc(x_660);
lean_inc(x_659);
lean_dec(x_654);
x_661 = lean_box(0);
x_662 = x_674;
goto block_673;
}
block_673:
{
lean_object* x_663; lean_object* x_664; 
x_663 = lean_unsigned_to_nat(1u);
if (x_662 == 0)
{
lean_ctor_set(x_661, 4, x_617);
lean_ctor_set(x_661, 3, x_617);
lean_ctor_set(x_661, 2, x_656);
lean_ctor_set(x_661, 1, x_655);
lean_ctor_set(x_661, 0, x_663);
x_664 = x_661;
goto block_671;
}
else
{
lean_object* x_672; 
x_672 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_672, 0, x_663);
lean_ctor_set(x_672, 1, x_655);
lean_ctor_set(x_672, 2, x_656);
lean_ctor_set(x_672, 3, x_617);
lean_ctor_set(x_672, 4, x_617);
x_664 = x_672;
goto block_671;
}
block_671:
{
lean_object* x_665; 
if (x_658 == 0)
{
lean_ctor_set(x_657, 4, x_617);
lean_ctor_set(x_657, 2, x_10);
lean_ctor_set(x_657, 1, x_9);
lean_ctor_set(x_657, 0, x_663);
x_665 = x_657;
goto block_669;
}
else
{
lean_object* x_670; 
x_670 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_670, 0, x_663);
lean_ctor_set(x_670, 1, x_9);
lean_ctor_set(x_670, 2, x_10);
lean_ctor_set(x_670, 3, x_617);
lean_ctor_set(x_670, 4, x_617);
x_665 = x_670;
goto block_669;
}
block_669:
{
lean_object* x_666; 
if (x_518 == 0)
{
lean_ctor_set(x_517, 4, x_665);
lean_ctor_set(x_517, 3, x_664);
lean_ctor_set(x_517, 2, x_660);
lean_ctor_set(x_517, 1, x_659);
lean_ctor_set(x_517, 0, x_13);
x_666 = x_517;
goto block_667;
}
else
{
lean_object* x_668; 
x_668 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_668, 0, x_13);
lean_ctor_set(x_668, 1, x_659);
lean_ctor_set(x_668, 2, x_660);
lean_ctor_set(x_668, 3, x_664);
lean_ctor_set(x_668, 4, x_665);
x_666 = x_668;
goto block_667;
}
block_667:
{
return x_666;
}
}
}
}
}
}
else
{
lean_object* x_683; lean_object* x_684; 
x_683 = lean_unsigned_to_nat(2u);
if (x_518 == 0)
{
lean_ctor_set(x_517, 4, x_654);
lean_ctor_set(x_517, 3, x_519);
lean_ctor_set(x_517, 0, x_683);
x_684 = x_517;
goto block_685;
}
else
{
lean_object* x_686; 
x_686 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_686, 0, x_683);
lean_ctor_set(x_686, 1, x_9);
lean_ctor_set(x_686, 2, x_10);
lean_ctor_set(x_686, 3, x_519);
lean_ctor_set(x_686, 4, x_654);
x_684 = x_686;
goto block_685;
}
block_685:
{
return x_684;
}
}
}
}
else
{
lean_object* x_687; lean_object* x_688; 
x_687 = lean_unsigned_to_nat(1u);
if (x_518 == 0)
{
lean_ctor_set(x_517, 4, x_519);
lean_ctor_set(x_517, 3, x_519);
lean_ctor_set(x_517, 0, x_687);
x_688 = x_517;
goto block_689;
}
else
{
lean_object* x_690; 
x_690 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_690, 0, x_687);
lean_ctor_set(x_690, 1, x_9);
lean_ctor_set(x_690, 2, x_10);
lean_ctor_set(x_690, 3, x_519);
lean_ctor_set(x_690, 4, x_519);
x_688 = x_690;
goto block_689;
}
block_689:
{
return x_688;
}
}
}
}
}
}
else
{
return x_1;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_link2_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_290; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_290 = !lean_is_exclusive(x_4);
if (x_290 == 0)
{
x_10 = x_4;
x_11 = x_290;
goto block_289;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = x_290;
goto block_289;
}
block_289:
{
lean_object* x_12; uint8_t x_13; 
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_6);
x_13 = lean_unbox(x_12);
switch (x_13) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_2, x_3, x_8);
x_15 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 4);
lean_inc(x_21);
x_22 = lean_unsigned_to_nat(3u);
x_23 = lean_nat_mul(x_22, x_16);
x_24 = lean_nat_dec_lt(x_23, x_17);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_25 = lean_nat_add(x_15, x_17);
lean_dec(x_17);
x_26 = lean_nat_add(x_25, x_16);
lean_dec(x_25);
if (x_11 == 0)
{
lean_ctor_set(x_10, 3, x_14);
lean_ctor_set(x_10, 0, x_26);
x_27 = x_10;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_6);
lean_ctor_set(x_29, 2, x_7);
lean_ctor_set(x_29, 3, x_14);
lean_ctor_set(x_29, 4, x_9);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
else
{
lean_object* x_30; uint8_t x_31; uint8_t x_95; 
x_95 = !lean_is_exclusive(x_14);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_14, 4);
lean_dec(x_96);
x_97 = lean_ctor_get(x_14, 3);
lean_dec(x_97);
x_98 = lean_ctor_get(x_14, 2);
lean_dec(x_98);
x_99 = lean_ctor_get(x_14, 1);
lean_dec(x_99);
x_100 = lean_ctor_get(x_14, 0);
lean_dec(x_100);
x_30 = x_14;
x_31 = x_95;
goto block_94;
}
else
{
lean_dec(x_14);
x_30 = lean_box(0);
x_31 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
x_35 = lean_ctor_get(x_21, 2);
x_36 = lean_ctor_get(x_21, 3);
x_37 = lean_ctor_get(x_21, 4);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_mul(x_38, x_32);
x_40 = lean_nat_dec_lt(x_33, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; uint8_t x_69; 
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
x_69 = !lean_is_exclusive(x_21);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_21, 4);
lean_dec(x_70);
x_71 = lean_ctor_get(x_21, 3);
lean_dec(x_71);
x_72 = lean_ctor_get(x_21, 2);
lean_dec(x_72);
x_73 = lean_ctor_get(x_21, 1);
lean_dec(x_73);
x_74 = lean_ctor_get(x_21, 0);
lean_dec(x_74);
x_41 = x_21;
x_42 = x_69;
goto block_68;
}
else
{
lean_dec(x_21);
x_41 = lean_box(0);
x_42 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_56; lean_object* x_57; 
x_43 = lean_nat_add(x_15, x_17);
lean_dec(x_17);
x_44 = lean_nat_add(x_43, x_16);
lean_dec(x_43);
x_56 = lean_nat_add(x_15, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_36, 0);
lean_inc(x_66);
x_57 = x_66;
goto block_65;
}
else
{
lean_object* x_67; 
x_67 = lean_unsigned_to_nat(0u);
x_57 = x_67;
goto block_65;
}
block_55:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_nat_add(x_45, x_47);
lean_dec(x_47);
lean_dec(x_45);
if (x_42 == 0)
{
lean_ctor_set(x_41, 4, x_9);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 2, x_7);
lean_ctor_set(x_41, 1, x_6);
lean_ctor_set(x_41, 0, x_48);
x_49 = x_41;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_6);
lean_ctor_set(x_54, 2, x_7);
lean_ctor_set(x_54, 3, x_37);
lean_ctor_set(x_54, 4, x_9);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_49);
lean_ctor_set(x_30, 3, x_46);
lean_ctor_set(x_30, 2, x_35);
lean_ctor_set(x_30, 1, x_34);
lean_ctor_set(x_30, 0, x_44);
x_50 = x_30;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_34);
lean_ctor_set(x_52, 2, x_35);
lean_ctor_set(x_52, 3, x_46);
lean_ctor_set(x_52, 4, x_49);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
block_65:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_nat_add(x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_36);
lean_ctor_set(x_10, 3, x_20);
lean_ctor_set(x_10, 2, x_19);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_58);
x_59 = x_10;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_18);
lean_ctor_set(x_64, 2, x_19);
lean_ctor_set(x_64, 3, x_20);
lean_ctor_set(x_64, 4, x_36);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
x_60 = lean_nat_add(x_15, x_16);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_37, 0);
lean_inc(x_61);
x_45 = x_60;
x_46 = x_59;
x_47 = x_61;
goto block_55;
}
else
{
lean_object* x_62; 
x_62 = lean_unsigned_to_nat(0u);
x_45 = x_60;
x_46 = x_59;
x_47 = x_62;
goto block_55;
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_del_object(x_10);
x_75 = lean_nat_add(x_15, x_17);
lean_dec(x_17);
x_76 = lean_nat_add(x_75, x_16);
lean_dec(x_75);
x_77 = lean_nat_add(x_15, x_16);
x_78 = lean_nat_add(x_77, x_33);
lean_dec(x_77);
lean_inc_ref(x_9);
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_9);
lean_ctor_set(x_30, 3, x_21);
lean_ctor_set(x_30, 2, x_7);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set(x_30, 0, x_78);
x_79 = x_30;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_93, 0, x_78);
lean_ctor_set(x_93, 1, x_6);
lean_ctor_set(x_93, 2, x_7);
lean_ctor_set(x_93, 3, x_21);
lean_ctor_set(x_93, 4, x_9);
x_79 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_80; uint8_t x_81; uint8_t x_86; 
x_86 = !lean_is_exclusive(x_9);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_9, 4);
lean_dec(x_87);
x_88 = lean_ctor_get(x_9, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_9, 2);
lean_dec(x_89);
x_90 = lean_ctor_get(x_9, 1);
lean_dec(x_90);
x_91 = lean_ctor_get(x_9, 0);
lean_dec(x_91);
x_80 = x_9;
x_81 = x_86;
goto block_85;
}
else
{
lean_dec(x_9);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
lean_ctor_set(x_80, 4, x_79);
lean_ctor_set(x_80, 3, x_20);
lean_ctor_set(x_80, 2, x_19);
lean_ctor_set(x_80, 1, x_18);
lean_ctor_set(x_80, 0, x_76);
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_18);
lean_ctor_set(x_84, 2, x_19);
lean_ctor_set(x_84, 3, x_20);
lean_ctor_set(x_84, 4, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
}
}
}
else
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_14, 3);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_115; 
x_102 = lean_ctor_get(x_14, 4);
x_103 = lean_ctor_get(x_14, 1);
x_104 = lean_ctor_get(x_14, 2);
x_115 = !lean_is_exclusive(x_14);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_14, 3);
lean_dec(x_116);
x_117 = lean_ctor_get(x_14, 0);
lean_dec(x_117);
x_105 = x_14;
x_106 = x_115;
goto block_114;
}
else
{
lean_inc(x_102);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_14);
x_105 = lean_box(0);
x_106 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_unsigned_to_nat(3u);
lean_inc(x_102);
if (x_106 == 0)
{
lean_ctor_set(x_105, 3, x_102);
lean_ctor_set(x_105, 2, x_7);
lean_ctor_set(x_105, 1, x_6);
lean_ctor_set(x_105, 0, x_15);
x_108 = x_105;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_15);
lean_ctor_set(x_113, 1, x_6);
lean_ctor_set(x_113, 2, x_7);
lean_ctor_set(x_113, 3, x_102);
lean_ctor_set(x_113, 4, x_102);
x_108 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_109; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_108);
lean_ctor_set(x_10, 3, x_101);
lean_ctor_set(x_10, 2, x_104);
lean_ctor_set(x_10, 1, x_103);
lean_ctor_set(x_10, 0, x_107);
x_109 = x_10;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_107);
lean_ctor_set(x_111, 1, x_103);
lean_ctor_set(x_111, 2, x_104);
lean_ctor_set(x_111, 3, x_101);
lean_ctor_set(x_111, 4, x_108);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_14, 4);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_143; 
x_119 = lean_ctor_get(x_14, 1);
x_120 = lean_ctor_get(x_14, 2);
x_143 = !lean_is_exclusive(x_14);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_14, 4);
lean_dec(x_144);
x_145 = lean_ctor_get(x_14, 3);
lean_dec(x_145);
x_146 = lean_ctor_get(x_14, 0);
lean_dec(x_146);
x_121 = x_14;
x_122 = x_143;
goto block_142;
}
else
{
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_14);
x_121 = lean_box(0);
x_122 = x_143;
goto block_142;
}
block_142:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_138; 
x_123 = lean_ctor_get(x_118, 1);
x_124 = lean_ctor_get(x_118, 2);
x_138 = !lean_is_exclusive(x_118);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_118, 4);
lean_dec(x_139);
x_140 = lean_ctor_get(x_118, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_118, 0);
lean_dec(x_141);
x_125 = x_118;
x_126 = x_138;
goto block_137;
}
else
{
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_118);
x_125 = lean_box(0);
x_126 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_unsigned_to_nat(3u);
if (x_126 == 0)
{
lean_ctor_set(x_125, 4, x_101);
lean_ctor_set(x_125, 3, x_101);
lean_ctor_set(x_125, 2, x_120);
lean_ctor_set(x_125, 1, x_119);
lean_ctor_set(x_125, 0, x_15);
x_128 = x_125;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_136, 0, x_15);
lean_ctor_set(x_136, 1, x_119);
lean_ctor_set(x_136, 2, x_120);
lean_ctor_set(x_136, 3, x_101);
lean_ctor_set(x_136, 4, x_101);
x_128 = x_136;
goto block_135;
}
block_135:
{
lean_object* x_129; 
if (x_122 == 0)
{
lean_ctor_set(x_121, 4, x_101);
lean_ctor_set(x_121, 2, x_7);
lean_ctor_set(x_121, 1, x_6);
lean_ctor_set(x_121, 0, x_15);
x_129 = x_121;
goto block_133;
}
else
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_134, 0, x_15);
lean_ctor_set(x_134, 1, x_6);
lean_ctor_set(x_134, 2, x_7);
lean_ctor_set(x_134, 3, x_101);
lean_ctor_set(x_134, 4, x_101);
x_129 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_130; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_129);
lean_ctor_set(x_10, 3, x_128);
lean_ctor_set(x_10, 2, x_124);
lean_ctor_set(x_10, 1, x_123);
lean_ctor_set(x_10, 0, x_127);
x_130 = x_10;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_123);
lean_ctor_set(x_132, 2, x_124);
lean_ctor_set(x_132, 3, x_128);
lean_ctor_set(x_132, 4, x_129);
x_130 = x_132;
goto block_131;
}
block_131:
{
return x_130;
}
}
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_unsigned_to_nat(2u);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_118);
lean_ctor_set(x_10, 3, x_14);
lean_ctor_set(x_10, 0, x_147);
x_148 = x_10;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_6);
lean_ctor_set(x_150, 2, x_7);
lean_ctor_set(x_150, 3, x_14);
lean_ctor_set(x_150, 4, x_118);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
}
}
case 1:
{
lean_object* x_151; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
if (x_11 == 0)
{
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 1, x_2);
x_151 = x_10;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_5);
lean_ctor_set(x_153, 1, x_2);
lean_ctor_set(x_153, 2, x_3);
lean_ctor_set(x_153, 3, x_8);
lean_ctor_set(x_153, 4, x_9);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
default: 
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_5);
x_154 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_2, x_3, x_9);
x_155 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_156 = lean_ctor_get(x_8, 0);
x_157 = lean_ctor_get(x_154, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_154, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_154, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_154, 3);
lean_inc(x_160);
x_161 = lean_ctor_get(x_154, 4);
lean_inc(x_161);
x_162 = lean_unsigned_to_nat(3u);
x_163 = lean_nat_mul(x_162, x_156);
x_164 = lean_nat_dec_lt(x_163, x_157);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
x_165 = lean_nat_add(x_155, x_156);
x_166 = lean_nat_add(x_165, x_157);
lean_dec(x_157);
lean_dec(x_165);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_154);
lean_ctor_set(x_10, 0, x_166);
x_167 = x_10;
goto block_168;
}
else
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_6);
lean_ctor_set(x_169, 2, x_7);
lean_ctor_set(x_169, 3, x_8);
lean_ctor_set(x_169, 4, x_154);
x_167 = x_169;
goto block_168;
}
block_168:
{
return x_167;
}
}
else
{
lean_object* x_170; uint8_t x_171; uint8_t x_233; 
x_233 = !lean_is_exclusive(x_154);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_154, 4);
lean_dec(x_234);
x_235 = lean_ctor_get(x_154, 3);
lean_dec(x_235);
x_236 = lean_ctor_get(x_154, 2);
lean_dec(x_236);
x_237 = lean_ctor_get(x_154, 1);
lean_dec(x_237);
x_238 = lean_ctor_get(x_154, 0);
lean_dec(x_238);
x_170 = x_154;
x_171 = x_233;
goto block_232;
}
else
{
lean_dec(x_154);
x_170 = lean_box(0);
x_171 = x_233;
goto block_232;
}
block_232:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_172 = lean_ctor_get(x_160, 0);
x_173 = lean_ctor_get(x_160, 1);
x_174 = lean_ctor_get(x_160, 2);
x_175 = lean_ctor_get(x_160, 3);
x_176 = lean_ctor_get(x_160, 4);
x_177 = lean_ctor_get(x_161, 0);
x_178 = lean_unsigned_to_nat(2u);
x_179 = lean_nat_mul(x_178, x_177);
x_180 = lean_nat_dec_lt(x_172, x_179);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; uint8_t x_208; 
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
x_208 = !lean_is_exclusive(x_160);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_209 = lean_ctor_get(x_160, 4);
lean_dec(x_209);
x_210 = lean_ctor_get(x_160, 3);
lean_dec(x_210);
x_211 = lean_ctor_get(x_160, 2);
lean_dec(x_211);
x_212 = lean_ctor_get(x_160, 1);
lean_dec(x_212);
x_213 = lean_ctor_get(x_160, 0);
lean_dec(x_213);
x_181 = x_160;
x_182 = x_208;
goto block_207;
}
else
{
lean_dec(x_160);
x_181 = lean_box(0);
x_182 = x_208;
goto block_207;
}
block_207:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_196; 
x_183 = lean_nat_add(x_155, x_156);
x_184 = lean_nat_add(x_183, x_157);
lean_dec(x_157);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_175, 0);
lean_inc(x_205);
x_196 = x_205;
goto block_204;
}
else
{
lean_object* x_206; 
x_206 = lean_unsigned_to_nat(0u);
x_196 = x_206;
goto block_204;
}
block_195:
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_nat_add(x_186, x_187);
lean_dec(x_187);
lean_dec(x_186);
if (x_182 == 0)
{
lean_ctor_set(x_181, 4, x_161);
lean_ctor_set(x_181, 3, x_176);
lean_ctor_set(x_181, 2, x_159);
lean_ctor_set(x_181, 1, x_158);
lean_ctor_set(x_181, 0, x_188);
x_189 = x_181;
goto block_193;
}
else
{
lean_object* x_194; 
x_194 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_194, 0, x_188);
lean_ctor_set(x_194, 1, x_158);
lean_ctor_set(x_194, 2, x_159);
lean_ctor_set(x_194, 3, x_176);
lean_ctor_set(x_194, 4, x_161);
x_189 = x_194;
goto block_193;
}
block_193:
{
lean_object* x_190; 
if (x_171 == 0)
{
lean_ctor_set(x_170, 4, x_189);
lean_ctor_set(x_170, 3, x_185);
lean_ctor_set(x_170, 2, x_174);
lean_ctor_set(x_170, 1, x_173);
lean_ctor_set(x_170, 0, x_184);
x_190 = x_170;
goto block_191;
}
else
{
lean_object* x_192; 
x_192 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_192, 0, x_184);
lean_ctor_set(x_192, 1, x_173);
lean_ctor_set(x_192, 2, x_174);
lean_ctor_set(x_192, 3, x_185);
lean_ctor_set(x_192, 4, x_189);
x_190 = x_192;
goto block_191;
}
block_191:
{
return x_190;
}
}
}
block_204:
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_nat_add(x_183, x_196);
lean_dec(x_196);
lean_dec(x_183);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_175);
lean_ctor_set(x_10, 0, x_197);
x_198 = x_10;
goto block_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_203, 0, x_197);
lean_ctor_set(x_203, 1, x_6);
lean_ctor_set(x_203, 2, x_7);
lean_ctor_set(x_203, 3, x_8);
lean_ctor_set(x_203, 4, x_175);
x_198 = x_203;
goto block_202;
}
block_202:
{
lean_object* x_199; 
x_199 = lean_nat_add(x_155, x_177);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_176, 0);
lean_inc(x_200);
x_185 = x_198;
x_186 = x_199;
x_187 = x_200;
goto block_195;
}
else
{
lean_object* x_201; 
x_201 = lean_unsigned_to_nat(0u);
x_185 = x_198;
x_186 = x_199;
x_187 = x_201;
goto block_195;
}
}
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_del_object(x_10);
x_214 = lean_nat_add(x_155, x_156);
x_215 = lean_nat_add(x_214, x_157);
lean_dec(x_157);
x_216 = lean_nat_add(x_214, x_172);
lean_dec(x_214);
lean_inc_ref(x_8);
if (x_171 == 0)
{
lean_ctor_set(x_170, 4, x_160);
lean_ctor_set(x_170, 3, x_8);
lean_ctor_set(x_170, 2, x_7);
lean_ctor_set(x_170, 1, x_6);
lean_ctor_set(x_170, 0, x_216);
x_217 = x_170;
goto block_230;
}
else
{
lean_object* x_231; 
x_231 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_231, 0, x_216);
lean_ctor_set(x_231, 1, x_6);
lean_ctor_set(x_231, 2, x_7);
lean_ctor_set(x_231, 3, x_8);
lean_ctor_set(x_231, 4, x_160);
x_217 = x_231;
goto block_230;
}
block_230:
{
lean_object* x_218; uint8_t x_219; uint8_t x_224; 
x_224 = !lean_is_exclusive(x_8);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_8, 4);
lean_dec(x_225);
x_226 = lean_ctor_get(x_8, 3);
lean_dec(x_226);
x_227 = lean_ctor_get(x_8, 2);
lean_dec(x_227);
x_228 = lean_ctor_get(x_8, 1);
lean_dec(x_228);
x_229 = lean_ctor_get(x_8, 0);
lean_dec(x_229);
x_218 = x_8;
x_219 = x_224;
goto block_223;
}
else
{
lean_dec(x_8);
x_218 = lean_box(0);
x_219 = x_224;
goto block_223;
}
block_223:
{
lean_object* x_220; 
if (x_219 == 0)
{
lean_ctor_set(x_218, 4, x_161);
lean_ctor_set(x_218, 3, x_217);
lean_ctor_set(x_218, 2, x_159);
lean_ctor_set(x_218, 1, x_158);
lean_ctor_set(x_218, 0, x_215);
x_220 = x_218;
goto block_221;
}
else
{
lean_object* x_222; 
x_222 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_222, 0, x_215);
lean_ctor_set(x_222, 1, x_158);
lean_ctor_set(x_222, 2, x_159);
lean_ctor_set(x_222, 3, x_217);
lean_ctor_set(x_222, 4, x_161);
x_220 = x_222;
goto block_221;
}
block_221:
{
return x_220;
}
}
}
}
}
}
}
else
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_154, 3);
lean_inc(x_239);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_265; 
x_240 = lean_ctor_get(x_154, 4);
x_241 = lean_ctor_get(x_154, 1);
x_242 = lean_ctor_get(x_154, 2);
x_265 = !lean_is_exclusive(x_154);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_154, 3);
lean_dec(x_266);
x_267 = lean_ctor_get(x_154, 0);
lean_dec(x_267);
x_243 = x_154;
x_244 = x_265;
goto block_264;
}
else
{
lean_inc(x_240);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_154);
x_243 = lean_box(0);
x_244 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; uint8_t x_260; 
x_245 = lean_ctor_get(x_239, 1);
x_246 = lean_ctor_get(x_239, 2);
x_260 = !lean_is_exclusive(x_239);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_239, 4);
lean_dec(x_261);
x_262 = lean_ctor_get(x_239, 3);
lean_dec(x_262);
x_263 = lean_ctor_get(x_239, 0);
lean_dec(x_263);
x_247 = x_239;
x_248 = x_260;
goto block_259;
}
else
{
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_239);
x_247 = lean_box(0);
x_248 = x_260;
goto block_259;
}
block_259:
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_unsigned_to_nat(3u);
lean_inc_n(x_240, 2);
if (x_248 == 0)
{
lean_ctor_set(x_247, 4, x_240);
lean_ctor_set(x_247, 3, x_240);
lean_ctor_set(x_247, 2, x_7);
lean_ctor_set(x_247, 1, x_6);
lean_ctor_set(x_247, 0, x_155);
x_250 = x_247;
goto block_257;
}
else
{
lean_object* x_258; 
x_258 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_258, 0, x_155);
lean_ctor_set(x_258, 1, x_6);
lean_ctor_set(x_258, 2, x_7);
lean_ctor_set(x_258, 3, x_240);
lean_ctor_set(x_258, 4, x_240);
x_250 = x_258;
goto block_257;
}
block_257:
{
lean_object* x_251; 
lean_inc(x_240);
if (x_244 == 0)
{
lean_ctor_set(x_243, 3, x_240);
lean_ctor_set(x_243, 0, x_155);
x_251 = x_243;
goto block_255;
}
else
{
lean_object* x_256; 
x_256 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_256, 0, x_155);
lean_ctor_set(x_256, 1, x_241);
lean_ctor_set(x_256, 2, x_242);
lean_ctor_set(x_256, 3, x_240);
lean_ctor_set(x_256, 4, x_240);
x_251 = x_256;
goto block_255;
}
block_255:
{
lean_object* x_252; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_251);
lean_ctor_set(x_10, 3, x_250);
lean_ctor_set(x_10, 2, x_246);
lean_ctor_set(x_10, 1, x_245);
lean_ctor_set(x_10, 0, x_249);
x_252 = x_10;
goto block_253;
}
else
{
lean_object* x_254; 
x_254 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_254, 0, x_249);
lean_ctor_set(x_254, 1, x_245);
lean_ctor_set(x_254, 2, x_246);
lean_ctor_set(x_254, 3, x_250);
lean_ctor_set(x_254, 4, x_251);
x_252 = x_254;
goto block_253;
}
block_253:
{
return x_252;
}
}
}
}
}
}
else
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_154, 4);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; uint8_t x_281; 
x_269 = lean_ctor_get(x_154, 1);
x_270 = lean_ctor_get(x_154, 2);
x_281 = !lean_is_exclusive(x_154);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_154, 4);
lean_dec(x_282);
x_283 = lean_ctor_get(x_154, 3);
lean_dec(x_283);
x_284 = lean_ctor_get(x_154, 0);
lean_dec(x_284);
x_271 = x_154;
x_272 = x_281;
goto block_280;
}
else
{
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_154);
x_271 = lean_box(0);
x_272 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_unsigned_to_nat(3u);
if (x_272 == 0)
{
lean_ctor_set(x_271, 4, x_239);
lean_ctor_set(x_271, 2, x_7);
lean_ctor_set(x_271, 1, x_6);
lean_ctor_set(x_271, 0, x_155);
x_274 = x_271;
goto block_278;
}
else
{
lean_object* x_279; 
x_279 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_279, 0, x_155);
lean_ctor_set(x_279, 1, x_6);
lean_ctor_set(x_279, 2, x_7);
lean_ctor_set(x_279, 3, x_239);
lean_ctor_set(x_279, 4, x_239);
x_274 = x_279;
goto block_278;
}
block_278:
{
lean_object* x_275; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_268);
lean_ctor_set(x_10, 3, x_274);
lean_ctor_set(x_10, 2, x_270);
lean_ctor_set(x_10, 1, x_269);
lean_ctor_set(x_10, 0, x_273);
x_275 = x_10;
goto block_276;
}
else
{
lean_object* x_277; 
x_277 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_277, 0, x_273);
lean_ctor_set(x_277, 1, x_269);
lean_ctor_set(x_277, 2, x_270);
lean_ctor_set(x_277, 3, x_274);
lean_ctor_set(x_277, 4, x_268);
x_275 = x_277;
goto block_276;
}
block_276:
{
return x_275;
}
}
}
}
else
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_unsigned_to_nat(2u);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_154);
lean_ctor_set(x_10, 3, x_268);
lean_ctor_set(x_10, 0, x_285);
x_286 = x_10;
goto block_287;
}
else
{
lean_object* x_288; 
x_288 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_6);
lean_ctor_set(x_288, 2, x_7);
lean_ctor_set(x_288, 3, x_268);
lean_ctor_set(x_288, 4, x_154);
x_286 = x_288;
goto block_287;
}
block_287:
{
return x_286;
}
}
}
}
}
}
}
}
else
{
lean_object* x_291; lean_object* x_292; 
lean_dec_ref(x_1);
x_291 = lean_unsigned_to_nat(1u);
x_292 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_2);
lean_ctor_set(x_292, 2, x_3);
lean_ctor_set(x_292, 3, x_4);
lean_ctor_set(x_292, 4, x_4);
return x_292;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_370; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_370 = !lean_is_exclusive(x_4);
if (x_370 == 0)
{
x_10 = x_4;
x_11 = x_370;
goto block_369;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = x_370;
goto block_369;
}
block_369:
{
lean_object* x_12; uint8_t x_13; 
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_6);
x_13 = lean_unbox(x_12);
switch (x_13) {
case 0:
{
lean_object* x_14; 
lean_dec(x_5);
x_14 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_1, x_2, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 4);
lean_inc(x_20);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_mul(x_21, x_15);
x_23 = lean_nat_dec_lt(x_22, x_16);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_24, x_16);
lean_dec(x_16);
x_26 = lean_nat_add(x_25, x_15);
lean_dec(x_25);
if (x_11 == 0)
{
lean_ctor_set(x_10, 3, x_14);
lean_ctor_set(x_10, 0, x_26);
x_27 = x_10;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_6);
lean_ctor_set(x_29, 2, x_7);
lean_ctor_set(x_29, 3, x_14);
lean_ctor_set(x_29, 4, x_9);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
else
{
lean_object* x_30; uint8_t x_31; uint8_t x_103; 
x_103 = !lean_is_exclusive(x_14);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_14, 4);
lean_dec(x_104);
x_105 = lean_ctor_get(x_14, 3);
lean_dec(x_105);
x_106 = lean_ctor_get(x_14, 2);
lean_dec(x_106);
x_107 = lean_ctor_get(x_14, 1);
lean_dec(x_107);
x_108 = lean_ctor_get(x_14, 0);
lean_dec(x_108);
x_30 = x_14;
x_31 = x_103;
goto block_102;
}
else
{
lean_dec(x_14);
x_30 = lean_box(0);
x_31 = x_103;
goto block_102;
}
block_102:
{
if (lean_obj_tag(x_19) == 0)
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
x_35 = lean_ctor_get(x_20, 2);
x_36 = lean_ctor_get(x_20, 3);
x_37 = lean_ctor_get(x_20, 4);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_mul(x_38, x_32);
x_40 = lean_nat_dec_lt(x_33, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; uint8_t x_70; 
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
x_70 = !lean_is_exclusive(x_20);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_20, 4);
lean_dec(x_71);
x_72 = lean_ctor_get(x_20, 3);
lean_dec(x_72);
x_73 = lean_ctor_get(x_20, 2);
lean_dec(x_73);
x_74 = lean_ctor_get(x_20, 1);
lean_dec(x_74);
x_75 = lean_ctor_get(x_20, 0);
lean_dec(x_75);
x_41 = x_20;
x_42 = x_70;
goto block_69;
}
else
{
lean_dec(x_20);
x_41 = lean_box(0);
x_42 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_57; lean_object* x_58; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_43, x_16);
lean_dec(x_16);
x_45 = lean_nat_add(x_44, x_15);
lean_dec(x_44);
x_57 = lean_nat_add(x_43, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_36, 0);
lean_inc(x_67);
x_58 = x_67;
goto block_66;
}
else
{
lean_object* x_68; 
x_68 = lean_unsigned_to_nat(0u);
x_58 = x_68;
goto block_66;
}
block_56:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_nat_add(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_42 == 0)
{
lean_ctor_set(x_41, 4, x_9);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 2, x_7);
lean_ctor_set(x_41, 1, x_6);
lean_ctor_set(x_41, 0, x_49);
x_50 = x_41;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_6);
lean_ctor_set(x_55, 2, x_7);
lean_ctor_set(x_55, 3, x_37);
lean_ctor_set(x_55, 4, x_9);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_50);
lean_ctor_set(x_30, 3, x_46);
lean_ctor_set(x_30, 2, x_35);
lean_ctor_set(x_30, 1, x_34);
lean_ctor_set(x_30, 0, x_45);
x_51 = x_30;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_34);
lean_ctor_set(x_53, 2, x_35);
lean_ctor_set(x_53, 3, x_46);
lean_ctor_set(x_53, 4, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
block_66:
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_nat_add(x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_36);
lean_ctor_set(x_10, 3, x_19);
lean_ctor_set(x_10, 2, x_18);
lean_ctor_set(x_10, 1, x_17);
lean_ctor_set(x_10, 0, x_59);
x_60 = x_10;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_17);
lean_ctor_set(x_65, 2, x_18);
lean_ctor_set(x_65, 3, x_19);
lean_ctor_set(x_65, 4, x_36);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
x_61 = lean_nat_add(x_43, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_37, 0);
lean_inc(x_62);
x_46 = x_60;
x_47 = x_61;
x_48 = x_62;
goto block_56;
}
else
{
lean_object* x_63; 
x_63 = lean_unsigned_to_nat(0u);
x_46 = x_60;
x_47 = x_61;
x_48 = x_63;
goto block_56;
}
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_del_object(x_10);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_add(x_76, x_16);
lean_dec(x_16);
x_78 = lean_nat_add(x_77, x_15);
lean_dec(x_77);
x_79 = lean_nat_add(x_76, x_15);
x_80 = lean_nat_add(x_79, x_33);
lean_dec(x_79);
lean_inc_ref(x_9);
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_9);
lean_ctor_set(x_30, 3, x_20);
lean_ctor_set(x_30, 2, x_7);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set(x_30, 0, x_80);
x_81 = x_30;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_95, 0, x_80);
lean_ctor_set(x_95, 1, x_6);
lean_ctor_set(x_95, 2, x_7);
lean_ctor_set(x_95, 3, x_20);
lean_ctor_set(x_95, 4, x_9);
x_81 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_82; uint8_t x_83; uint8_t x_88; 
x_88 = !lean_is_exclusive(x_9);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_9, 4);
lean_dec(x_89);
x_90 = lean_ctor_get(x_9, 3);
lean_dec(x_90);
x_91 = lean_ctor_get(x_9, 2);
lean_dec(x_91);
x_92 = lean_ctor_get(x_9, 1);
lean_dec(x_92);
x_93 = lean_ctor_get(x_9, 0);
lean_dec(x_93);
x_82 = x_9;
x_83 = x_88;
goto block_87;
}
else
{
lean_dec(x_9);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
lean_ctor_set(x_82, 4, x_81);
lean_ctor_set(x_82, 3, x_19);
lean_ctor_set(x_82, 2, x_18);
lean_ctor_set(x_82, 1, x_17);
lean_ctor_set(x_82, 0, x_78);
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_86, 0, x_78);
lean_ctor_set(x_86, 1, x_17);
lean_ctor_set(x_86, 2, x_18);
lean_ctor_set(x_86, 3, x_19);
lean_ctor_set(x_86, 4, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec_ref(x_19);
lean_del_object(x_30);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_9);
lean_del_object(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_96 = lean_box(1);
x_97 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2);
x_98 = l_panic___redArg(x_96, x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_del_object(x_30);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_9);
lean_del_object(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_99 = lean_box(1);
x_100 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3);
x_101 = l_panic___redArg(x_99, x_100);
return x_101;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_9, 0);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_add(x_110, x_109);
if (x_11 == 0)
{
lean_ctor_set(x_10, 3, x_14);
lean_ctor_set(x_10, 0, x_111);
x_112 = x_10;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_6);
lean_ctor_set(x_114, 2, x_7);
lean_ctor_set(x_114, 3, x_14);
lean_ctor_set(x_114, 4, x_9);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
}
else
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_14, 3);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_14, 4);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_133; 
x_117 = lean_ctor_get(x_14, 0);
x_118 = lean_ctor_get(x_14, 1);
x_119 = lean_ctor_get(x_14, 2);
x_133 = !lean_is_exclusive(x_14);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_14, 4);
lean_dec(x_134);
x_135 = lean_ctor_get(x_14, 3);
lean_dec(x_135);
x_120 = x_14;
x_121 = x_133;
goto block_132;
}
else
{
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_14);
x_120 = lean_box(0);
x_121 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_116, 0);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_nat_add(x_123, x_117);
lean_dec(x_117);
x_125 = lean_nat_add(x_123, x_122);
if (x_121 == 0)
{
lean_ctor_set(x_120, 4, x_9);
lean_ctor_set(x_120, 3, x_116);
lean_ctor_set(x_120, 2, x_7);
lean_ctor_set(x_120, 1, x_6);
lean_ctor_set(x_120, 0, x_125);
x_126 = x_120;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_131, 0, x_125);
lean_ctor_set(x_131, 1, x_6);
lean_ctor_set(x_131, 2, x_7);
lean_ctor_set(x_131, 3, x_116);
lean_ctor_set(x_131, 4, x_9);
x_126 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_127; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_126);
lean_ctor_set(x_10, 3, x_115);
lean_ctor_set(x_10, 2, x_119);
lean_ctor_set(x_10, 1, x_118);
lean_ctor_set(x_10, 0, x_124);
x_127 = x_10;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set(x_129, 1, x_118);
lean_ctor_set(x_129, 2, x_119);
lean_ctor_set(x_129, 3, x_115);
lean_ctor_set(x_129, 4, x_126);
x_127 = x_129;
goto block_128;
}
block_128:
{
return x_127;
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_149; 
x_136 = lean_ctor_get(x_14, 1);
x_137 = lean_ctor_get(x_14, 2);
x_149 = !lean_is_exclusive(x_14);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_14, 4);
lean_dec(x_150);
x_151 = lean_ctor_get(x_14, 3);
lean_dec(x_151);
x_152 = lean_ctor_get(x_14, 0);
lean_dec(x_152);
x_138 = x_14;
x_139 = x_149;
goto block_148;
}
else
{
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_14);
x_138 = lean_box(0);
x_139 = x_149;
goto block_148;
}
block_148:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_unsigned_to_nat(3u);
x_141 = lean_unsigned_to_nat(1u);
if (x_139 == 0)
{
lean_ctor_set(x_138, 3, x_116);
lean_ctor_set(x_138, 2, x_7);
lean_ctor_set(x_138, 1, x_6);
lean_ctor_set(x_138, 0, x_141);
x_142 = x_138;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_141);
lean_ctor_set(x_147, 1, x_6);
lean_ctor_set(x_147, 2, x_7);
lean_ctor_set(x_147, 3, x_116);
lean_ctor_set(x_147, 4, x_116);
x_142 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_143; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_142);
lean_ctor_set(x_10, 3, x_115);
lean_ctor_set(x_10, 2, x_137);
lean_ctor_set(x_10, 1, x_136);
lean_ctor_set(x_10, 0, x_140);
x_143 = x_10;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_145, 0, x_140);
lean_ctor_set(x_145, 1, x_136);
lean_ctor_set(x_145, 2, x_137);
lean_ctor_set(x_145, 3, x_115);
lean_ctor_set(x_145, 4, x_142);
x_143 = x_145;
goto block_144;
}
block_144:
{
return x_143;
}
}
}
}
}
else
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_14, 4);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_179; 
x_154 = lean_ctor_get(x_14, 1);
x_155 = lean_ctor_get(x_14, 2);
x_179 = !lean_is_exclusive(x_14);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_14, 4);
lean_dec(x_180);
x_181 = lean_ctor_get(x_14, 3);
lean_dec(x_181);
x_182 = lean_ctor_get(x_14, 0);
lean_dec(x_182);
x_156 = x_14;
x_157 = x_179;
goto block_178;
}
else
{
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_14);
x_156 = lean_box(0);
x_157 = x_179;
goto block_178;
}
block_178:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_174; 
x_158 = lean_ctor_get(x_153, 1);
x_159 = lean_ctor_get(x_153, 2);
x_174 = !lean_is_exclusive(x_153);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_153, 4);
lean_dec(x_175);
x_176 = lean_ctor_get(x_153, 3);
lean_dec(x_176);
x_177 = lean_ctor_get(x_153, 0);
lean_dec(x_177);
x_160 = x_153;
x_161 = x_174;
goto block_173;
}
else
{
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_153);
x_160 = lean_box(0);
x_161 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_unsigned_to_nat(3u);
x_163 = lean_unsigned_to_nat(1u);
if (x_161 == 0)
{
lean_ctor_set(x_160, 4, x_115);
lean_ctor_set(x_160, 3, x_115);
lean_ctor_set(x_160, 2, x_155);
lean_ctor_set(x_160, 1, x_154);
lean_ctor_set(x_160, 0, x_163);
x_164 = x_160;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_172, 0, x_163);
lean_ctor_set(x_172, 1, x_154);
lean_ctor_set(x_172, 2, x_155);
lean_ctor_set(x_172, 3, x_115);
lean_ctor_set(x_172, 4, x_115);
x_164 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_165; 
if (x_157 == 0)
{
lean_ctor_set(x_156, 4, x_115);
lean_ctor_set(x_156, 2, x_7);
lean_ctor_set(x_156, 1, x_6);
lean_ctor_set(x_156, 0, x_163);
x_165 = x_156;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_170, 0, x_163);
lean_ctor_set(x_170, 1, x_6);
lean_ctor_set(x_170, 2, x_7);
lean_ctor_set(x_170, 3, x_115);
lean_ctor_set(x_170, 4, x_115);
x_165 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_166; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_165);
lean_ctor_set(x_10, 3, x_164);
lean_ctor_set(x_10, 2, x_159);
lean_ctor_set(x_10, 1, x_158);
lean_ctor_set(x_10, 0, x_162);
x_166 = x_10;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_168, 0, x_162);
lean_ctor_set(x_168, 1, x_158);
lean_ctor_set(x_168, 2, x_159);
lean_ctor_set(x_168, 3, x_164);
lean_ctor_set(x_168, 4, x_165);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_unsigned_to_nat(2u);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_153);
lean_ctor_set(x_10, 3, x_14);
lean_ctor_set(x_10, 0, x_183);
x_184 = x_10;
goto block_185;
}
else
{
lean_object* x_186; 
x_186 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_6);
lean_ctor_set(x_186, 2, x_7);
lean_ctor_set(x_186, 3, x_14);
lean_ctor_set(x_186, 4, x_153);
x_184 = x_186;
goto block_185;
}
block_185:
{
return x_184;
}
}
}
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_unsigned_to_nat(1u);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_14);
lean_ctor_set(x_10, 3, x_14);
lean_ctor_set(x_10, 0, x_187);
x_188 = x_10;
goto block_189;
}
else
{
lean_object* x_190; 
x_190 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_6);
lean_ctor_set(x_190, 2, x_7);
lean_ctor_set(x_190, 3, x_14);
lean_ctor_set(x_190, 4, x_14);
x_188 = x_190;
goto block_189;
}
block_189:
{
return x_188;
}
}
}
}
case 1:
{
lean_object* x_191; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
if (x_11 == 0)
{
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 1, x_2);
x_191 = x_10;
goto block_192;
}
else
{
lean_object* x_193; 
x_193 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_193, 0, x_5);
lean_ctor_set(x_193, 1, x_2);
lean_ctor_set(x_193, 2, x_3);
lean_ctor_set(x_193, 3, x_8);
lean_ctor_set(x_193, 4, x_9);
x_191 = x_193;
goto block_192;
}
block_192:
{
return x_191;
}
}
default: 
{
lean_object* x_194; 
lean_dec(x_5);
x_194 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_1, x_2, x_3, x_9);
if (lean_obj_tag(x_8) == 0)
{
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_195 = lean_ctor_get(x_8, 0);
x_196 = lean_ctor_get(x_194, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_194, 2);
lean_inc(x_198);
x_199 = lean_ctor_get(x_194, 3);
lean_inc(x_199);
x_200 = lean_ctor_get(x_194, 4);
lean_inc(x_200);
x_201 = lean_unsigned_to_nat(3u);
x_202 = lean_nat_mul(x_201, x_195);
x_203 = lean_nat_dec_lt(x_202, x_196);
lean_dec(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
x_204 = lean_unsigned_to_nat(1u);
x_205 = lean_nat_add(x_204, x_195);
x_206 = lean_nat_add(x_205, x_196);
lean_dec(x_196);
lean_dec(x_205);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_194);
lean_ctor_set(x_10, 0, x_206);
x_207 = x_10;
goto block_208;
}
else
{
lean_object* x_209; 
x_209 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_6);
lean_ctor_set(x_209, 2, x_7);
lean_ctor_set(x_209, 3, x_8);
lean_ctor_set(x_209, 4, x_194);
x_207 = x_209;
goto block_208;
}
block_208:
{
return x_207;
}
}
else
{
lean_object* x_210; uint8_t x_211; uint8_t x_281; 
x_281 = !lean_is_exclusive(x_194);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_282 = lean_ctor_get(x_194, 4);
lean_dec(x_282);
x_283 = lean_ctor_get(x_194, 3);
lean_dec(x_283);
x_284 = lean_ctor_get(x_194, 2);
lean_dec(x_284);
x_285 = lean_ctor_get(x_194, 1);
lean_dec(x_285);
x_286 = lean_ctor_get(x_194, 0);
lean_dec(x_286);
x_210 = x_194;
x_211 = x_281;
goto block_280;
}
else
{
lean_dec(x_194);
x_210 = lean_box(0);
x_211 = x_281;
goto block_280;
}
block_280:
{
if (lean_obj_tag(x_199) == 0)
{
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_212 = lean_ctor_get(x_199, 0);
x_213 = lean_ctor_get(x_199, 1);
x_214 = lean_ctor_get(x_199, 2);
x_215 = lean_ctor_get(x_199, 3);
x_216 = lean_ctor_get(x_199, 4);
x_217 = lean_ctor_get(x_200, 0);
x_218 = lean_unsigned_to_nat(2u);
x_219 = lean_nat_mul(x_218, x_217);
x_220 = lean_nat_dec_lt(x_212, x_219);
lean_dec(x_219);
if (x_220 == 0)
{
lean_object* x_221; uint8_t x_222; uint8_t x_249; 
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
x_249 = !lean_is_exclusive(x_199);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_199, 4);
lean_dec(x_250);
x_251 = lean_ctor_get(x_199, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_199, 2);
lean_dec(x_252);
x_253 = lean_ctor_get(x_199, 1);
lean_dec(x_253);
x_254 = lean_ctor_get(x_199, 0);
lean_dec(x_254);
x_221 = x_199;
x_222 = x_249;
goto block_248;
}
else
{
lean_dec(x_199);
x_221 = lean_box(0);
x_222 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_237; 
x_223 = lean_unsigned_to_nat(1u);
x_224 = lean_nat_add(x_223, x_195);
x_225 = lean_nat_add(x_224, x_196);
lean_dec(x_196);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_215, 0);
lean_inc(x_246);
x_237 = x_246;
goto block_245;
}
else
{
lean_object* x_247; 
x_247 = lean_unsigned_to_nat(0u);
x_237 = x_247;
goto block_245;
}
block_236:
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_nat_add(x_227, x_228);
lean_dec(x_228);
lean_dec(x_227);
if (x_222 == 0)
{
lean_ctor_set(x_221, 4, x_200);
lean_ctor_set(x_221, 3, x_216);
lean_ctor_set(x_221, 2, x_198);
lean_ctor_set(x_221, 1, x_197);
lean_ctor_set(x_221, 0, x_229);
x_230 = x_221;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_235, 0, x_229);
lean_ctor_set(x_235, 1, x_197);
lean_ctor_set(x_235, 2, x_198);
lean_ctor_set(x_235, 3, x_216);
lean_ctor_set(x_235, 4, x_200);
x_230 = x_235;
goto block_234;
}
block_234:
{
lean_object* x_231; 
if (x_211 == 0)
{
lean_ctor_set(x_210, 4, x_230);
lean_ctor_set(x_210, 3, x_226);
lean_ctor_set(x_210, 2, x_214);
lean_ctor_set(x_210, 1, x_213);
lean_ctor_set(x_210, 0, x_225);
x_231 = x_210;
goto block_232;
}
else
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_233, 0, x_225);
lean_ctor_set(x_233, 1, x_213);
lean_ctor_set(x_233, 2, x_214);
lean_ctor_set(x_233, 3, x_226);
lean_ctor_set(x_233, 4, x_230);
x_231 = x_233;
goto block_232;
}
block_232:
{
return x_231;
}
}
}
block_245:
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_nat_add(x_224, x_237);
lean_dec(x_237);
lean_dec(x_224);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_215);
lean_ctor_set(x_10, 0, x_238);
x_239 = x_10;
goto block_243;
}
else
{
lean_object* x_244; 
x_244 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_244, 0, x_238);
lean_ctor_set(x_244, 1, x_6);
lean_ctor_set(x_244, 2, x_7);
lean_ctor_set(x_244, 3, x_8);
lean_ctor_set(x_244, 4, x_215);
x_239 = x_244;
goto block_243;
}
block_243:
{
lean_object* x_240; 
x_240 = lean_nat_add(x_223, x_217);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_216, 0);
lean_inc(x_241);
x_226 = x_239;
x_227 = x_240;
x_228 = x_241;
goto block_236;
}
else
{
lean_object* x_242; 
x_242 = lean_unsigned_to_nat(0u);
x_226 = x_239;
x_227 = x_240;
x_228 = x_242;
goto block_236;
}
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_del_object(x_10);
x_255 = lean_unsigned_to_nat(1u);
x_256 = lean_nat_add(x_255, x_195);
x_257 = lean_nat_add(x_256, x_196);
lean_dec(x_196);
x_258 = lean_nat_add(x_256, x_212);
lean_dec(x_256);
lean_inc_ref(x_8);
if (x_211 == 0)
{
lean_ctor_set(x_210, 4, x_199);
lean_ctor_set(x_210, 3, x_8);
lean_ctor_set(x_210, 2, x_7);
lean_ctor_set(x_210, 1, x_6);
lean_ctor_set(x_210, 0, x_258);
x_259 = x_210;
goto block_272;
}
else
{
lean_object* x_273; 
x_273 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_273, 0, x_258);
lean_ctor_set(x_273, 1, x_6);
lean_ctor_set(x_273, 2, x_7);
lean_ctor_set(x_273, 3, x_8);
lean_ctor_set(x_273, 4, x_199);
x_259 = x_273;
goto block_272;
}
block_272:
{
lean_object* x_260; uint8_t x_261; uint8_t x_266; 
x_266 = !lean_is_exclusive(x_8);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_267 = lean_ctor_get(x_8, 4);
lean_dec(x_267);
x_268 = lean_ctor_get(x_8, 3);
lean_dec(x_268);
x_269 = lean_ctor_get(x_8, 2);
lean_dec(x_269);
x_270 = lean_ctor_get(x_8, 1);
lean_dec(x_270);
x_271 = lean_ctor_get(x_8, 0);
lean_dec(x_271);
x_260 = x_8;
x_261 = x_266;
goto block_265;
}
else
{
lean_dec(x_8);
x_260 = lean_box(0);
x_261 = x_266;
goto block_265;
}
block_265:
{
lean_object* x_262; 
if (x_261 == 0)
{
lean_ctor_set(x_260, 4, x_200);
lean_ctor_set(x_260, 3, x_259);
lean_ctor_set(x_260, 2, x_198);
lean_ctor_set(x_260, 1, x_197);
lean_ctor_set(x_260, 0, x_257);
x_262 = x_260;
goto block_263;
}
else
{
lean_object* x_264; 
x_264 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_264, 0, x_257);
lean_ctor_set(x_264, 1, x_197);
lean_ctor_set(x_264, 2, x_198);
lean_ctor_set(x_264, 3, x_259);
lean_ctor_set(x_264, 4, x_200);
x_262 = x_264;
goto block_263;
}
block_263:
{
return x_262;
}
}
}
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec_ref(x_199);
lean_del_object(x_210);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec_ref(x_8);
lean_del_object(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_274 = lean_box(1);
x_275 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3);
x_276 = l_panic___redArg(x_274, x_275);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_del_object(x_210);
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec_ref(x_8);
lean_del_object(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_277 = lean_box(1);
x_278 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4);
x_279 = l_panic___redArg(x_277, x_278);
return x_279;
}
}
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_287 = lean_ctor_get(x_8, 0);
x_288 = lean_unsigned_to_nat(1u);
x_289 = lean_nat_add(x_288, x_287);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_194);
lean_ctor_set(x_10, 0, x_289);
x_290 = x_10;
goto block_291;
}
else
{
lean_object* x_292; 
x_292 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_6);
lean_ctor_set(x_292, 2, x_7);
lean_ctor_set(x_292, 3, x_8);
lean_ctor_set(x_292, 4, x_194);
x_290 = x_292;
goto block_291;
}
block_291:
{
return x_290;
}
}
}
else
{
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_293; 
x_293 = lean_ctor_get(x_194, 3);
lean_inc(x_293);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; 
x_294 = lean_ctor_get(x_194, 4);
lean_inc(x_294);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; uint8_t x_311; 
x_295 = lean_ctor_get(x_194, 0);
x_296 = lean_ctor_get(x_194, 1);
x_297 = lean_ctor_get(x_194, 2);
x_311 = !lean_is_exclusive(x_194);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_194, 4);
lean_dec(x_312);
x_313 = lean_ctor_get(x_194, 3);
lean_dec(x_313);
x_298 = x_194;
x_299 = x_311;
goto block_310;
}
else
{
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_194);
x_298 = lean_box(0);
x_299 = x_311;
goto block_310;
}
block_310:
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_300 = lean_ctor_get(x_293, 0);
x_301 = lean_unsigned_to_nat(1u);
x_302 = lean_nat_add(x_301, x_295);
lean_dec(x_295);
x_303 = lean_nat_add(x_301, x_300);
if (x_299 == 0)
{
lean_ctor_set(x_298, 4, x_293);
lean_ctor_set(x_298, 3, x_8);
lean_ctor_set(x_298, 2, x_7);
lean_ctor_set(x_298, 1, x_6);
lean_ctor_set(x_298, 0, x_303);
x_304 = x_298;
goto block_308;
}
else
{
lean_object* x_309; 
x_309 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_309, 0, x_303);
lean_ctor_set(x_309, 1, x_6);
lean_ctor_set(x_309, 2, x_7);
lean_ctor_set(x_309, 3, x_8);
lean_ctor_set(x_309, 4, x_293);
x_304 = x_309;
goto block_308;
}
block_308:
{
lean_object* x_305; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_294);
lean_ctor_set(x_10, 3, x_304);
lean_ctor_set(x_10, 2, x_297);
lean_ctor_set(x_10, 1, x_296);
lean_ctor_set(x_10, 0, x_302);
x_305 = x_10;
goto block_306;
}
else
{
lean_object* x_307; 
x_307 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_307, 0, x_302);
lean_ctor_set(x_307, 1, x_296);
lean_ctor_set(x_307, 2, x_297);
lean_ctor_set(x_307, 3, x_304);
lean_ctor_set(x_307, 4, x_294);
x_305 = x_307;
goto block_306;
}
block_306:
{
return x_305;
}
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; uint8_t x_339; 
x_314 = lean_ctor_get(x_194, 1);
x_315 = lean_ctor_get(x_194, 2);
x_339 = !lean_is_exclusive(x_194);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_194, 4);
lean_dec(x_340);
x_341 = lean_ctor_get(x_194, 3);
lean_dec(x_341);
x_342 = lean_ctor_get(x_194, 0);
lean_dec(x_342);
x_316 = x_194;
x_317 = x_339;
goto block_338;
}
else
{
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_194);
x_316 = lean_box(0);
x_317 = x_339;
goto block_338;
}
block_338:
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; uint8_t x_334; 
x_318 = lean_ctor_get(x_293, 1);
x_319 = lean_ctor_get(x_293, 2);
x_334 = !lean_is_exclusive(x_293);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_293, 4);
lean_dec(x_335);
x_336 = lean_ctor_get(x_293, 3);
lean_dec(x_336);
x_337 = lean_ctor_get(x_293, 0);
lean_dec(x_337);
x_320 = x_293;
x_321 = x_334;
goto block_333;
}
else
{
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_293);
x_320 = lean_box(0);
x_321 = x_334;
goto block_333;
}
block_333:
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_unsigned_to_nat(3u);
x_323 = lean_unsigned_to_nat(1u);
if (x_321 == 0)
{
lean_ctor_set(x_320, 4, x_294);
lean_ctor_set(x_320, 3, x_294);
lean_ctor_set(x_320, 2, x_7);
lean_ctor_set(x_320, 1, x_6);
lean_ctor_set(x_320, 0, x_323);
x_324 = x_320;
goto block_331;
}
else
{
lean_object* x_332; 
x_332 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_332, 0, x_323);
lean_ctor_set(x_332, 1, x_6);
lean_ctor_set(x_332, 2, x_7);
lean_ctor_set(x_332, 3, x_294);
lean_ctor_set(x_332, 4, x_294);
x_324 = x_332;
goto block_331;
}
block_331:
{
lean_object* x_325; 
if (x_317 == 0)
{
lean_ctor_set(x_316, 3, x_294);
lean_ctor_set(x_316, 0, x_323);
x_325 = x_316;
goto block_329;
}
else
{
lean_object* x_330; 
x_330 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_330, 0, x_323);
lean_ctor_set(x_330, 1, x_314);
lean_ctor_set(x_330, 2, x_315);
lean_ctor_set(x_330, 3, x_294);
lean_ctor_set(x_330, 4, x_294);
x_325 = x_330;
goto block_329;
}
block_329:
{
lean_object* x_326; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_325);
lean_ctor_set(x_10, 3, x_324);
lean_ctor_set(x_10, 2, x_319);
lean_ctor_set(x_10, 1, x_318);
lean_ctor_set(x_10, 0, x_322);
x_326 = x_10;
goto block_327;
}
else
{
lean_object* x_328; 
x_328 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_328, 0, x_322);
lean_ctor_set(x_328, 1, x_318);
lean_ctor_set(x_328, 2, x_319);
lean_ctor_set(x_328, 3, x_324);
lean_ctor_set(x_328, 4, x_325);
x_326 = x_328;
goto block_327;
}
block_327:
{
return x_326;
}
}
}
}
}
}
}
else
{
lean_object* x_343; 
x_343 = lean_ctor_get(x_194, 4);
lean_inc(x_343);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; uint8_t x_357; 
x_344 = lean_ctor_get(x_194, 1);
x_345 = lean_ctor_get(x_194, 2);
x_357 = !lean_is_exclusive(x_194);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_194, 4);
lean_dec(x_358);
x_359 = lean_ctor_get(x_194, 3);
lean_dec(x_359);
x_360 = lean_ctor_get(x_194, 0);
lean_dec(x_360);
x_346 = x_194;
x_347 = x_357;
goto block_356;
}
else
{
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_194);
x_346 = lean_box(0);
x_347 = x_357;
goto block_356;
}
block_356:
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_unsigned_to_nat(3u);
x_349 = lean_unsigned_to_nat(1u);
if (x_347 == 0)
{
lean_ctor_set(x_346, 4, x_293);
lean_ctor_set(x_346, 2, x_7);
lean_ctor_set(x_346, 1, x_6);
lean_ctor_set(x_346, 0, x_349);
x_350 = x_346;
goto block_354;
}
else
{
lean_object* x_355; 
x_355 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_355, 0, x_349);
lean_ctor_set(x_355, 1, x_6);
lean_ctor_set(x_355, 2, x_7);
lean_ctor_set(x_355, 3, x_293);
lean_ctor_set(x_355, 4, x_293);
x_350 = x_355;
goto block_354;
}
block_354:
{
lean_object* x_351; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_343);
lean_ctor_set(x_10, 3, x_350);
lean_ctor_set(x_10, 2, x_345);
lean_ctor_set(x_10, 1, x_344);
lean_ctor_set(x_10, 0, x_348);
x_351 = x_10;
goto block_352;
}
else
{
lean_object* x_353; 
x_353 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_353, 0, x_348);
lean_ctor_set(x_353, 1, x_344);
lean_ctor_set(x_353, 2, x_345);
lean_ctor_set(x_353, 3, x_350);
lean_ctor_set(x_353, 4, x_343);
x_351 = x_353;
goto block_352;
}
block_352:
{
return x_351;
}
}
}
}
else
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_unsigned_to_nat(2u);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_194);
lean_ctor_set(x_10, 3, x_343);
lean_ctor_set(x_10, 0, x_361);
x_362 = x_10;
goto block_363;
}
else
{
lean_object* x_364; 
x_364 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_364, 0, x_361);
lean_ctor_set(x_364, 1, x_6);
lean_ctor_set(x_364, 2, x_7);
lean_ctor_set(x_364, 3, x_343);
lean_ctor_set(x_364, 4, x_194);
x_362 = x_364;
goto block_363;
}
block_363:
{
return x_362;
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_unsigned_to_nat(1u);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_194);
lean_ctor_set(x_10, 3, x_194);
lean_ctor_set(x_10, 0, x_365);
x_366 = x_10;
goto block_367;
}
else
{
lean_object* x_368; 
x_368 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_6);
lean_ctor_set(x_368, 2, x_7);
lean_ctor_set(x_368, 3, x_194);
lean_ctor_set(x_368, 4, x_194);
x_366 = x_368;
goto block_367;
}
block_367:
{
return x_366;
}
}
}
}
}
}
}
else
{
lean_object* x_371; lean_object* x_372; 
lean_dec_ref(x_1);
x_371 = lean_unsigned_to_nat(1u);
x_372 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_2);
lean_ctor_set(x_372, 2, x_3);
lean_ctor_set(x_372, 3, x_4);
lean_ctor_set(x_372, 4, x_4);
return x_372;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_size(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; 
x_5 = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(x_4);
x_6 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_2, x_3, x_4);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_7 = x_12;
goto block_11;
block_11:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_nat_dec_eq(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; 
x_8 = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(x_6);
x_9 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_3, x_4, x_5, x_6);
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
x_10 = x_15;
goto block_14;
block_14:
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_nat_dec_eq(x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(x_4);
x_6 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_7 = x_12;
goto block_11;
}
else
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(0u);
x_7 = x_13;
goto block_11;
}
block_11:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_nat_dec_eq(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(x_6);
x_8 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_9 = x_14;
goto block_13;
}
else
{
lean_object* x_15; 
x_15 = lean_unsigned_to_nat(0u);
x_9 = x_15;
goto block_13;
}
block_13:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_nat_dec_eq(x_7, x_9);
lean_dec(x_9);
lean_dec(x_7);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
lean_inc(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_3, x_4, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
lean_inc(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_7 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_3, x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_3, x_4, x_5, x_6);
return x_8;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsertIfNew___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_2, x_3, x_4);
x_7 = lean_box(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsertIfNew(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
lean_inc(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_3, x_4, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_3, x_4, x_5, x_6);
x_10 = lean_box(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_12 = lean_box(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsertIfNew_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_1, x_2, x_3, x_4);
x_7 = lean_box(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsertIfNew_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
lean_inc(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_7 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_3, x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_3, x_4, x_5, x_6);
x_9 = lean_box(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_11 = lean_box(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_inc(x_2);
lean_inc(x_3);
lean_inc_ref(x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_3, x_4, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_3);
x_9 = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(x_3, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_inc(x_5);
lean_inc(x_6);
lean_inc_ref(x_3);
x_10 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_3, x_6, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_3, x_6, x_7, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_inc(x_2);
lean_inc(x_3);
lean_inc_ref(x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_1, x_3, x_4, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_3);
x_8 = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(x_3, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_inc(x_5);
lean_inc(x_6);
lean_inc_ref(x_3);
x_9 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_3, x_6, x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_3, x_6, x_7, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_662; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_ctor_get(x_3, 3);
x_7 = lean_ctor_get(x_3, 4);
x_662 = !lean_is_exclusive(x_3);
if (x_662 == 0)
{
lean_object* x_663; 
x_663 = lean_ctor_get(x_3, 0);
lean_dec(x_663);
x_8 = x_3;
x_9 = x_662;
goto block_661;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_662;
goto block_661;
}
block_661:
{
lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_10 = lean_apply_2(x_1, x_2, x_4);
x_11 = lean_unbox(x_10);
switch (x_11) {
case 0:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Std_DTreeMap_Internal_Impl_erase___redArg(x_1, x_2, x_6);
x_13 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 2);
x_18 = lean_ctor_get(x_7, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 4);
x_20 = lean_unsigned_to_nat(3u);
x_21 = lean_nat_mul(x_20, x_14);
x_22 = lean_nat_dec_lt(x_21, x_15);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
x_23 = lean_nat_add(x_13, x_14);
lean_dec(x_14);
x_24 = lean_nat_add(x_23, x_15);
lean_dec(x_23);
if (x_9 == 0)
{
lean_ctor_set(x_8, 3, x_12);
lean_ctor_set(x_8, 0, x_24);
x_25 = x_8;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_5);
lean_ctor_set(x_27, 3, x_12);
lean_ctor_set(x_27, 4, x_7);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
else
{
lean_object* x_28; uint8_t x_29; uint8_t x_91; 
lean_inc(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_91 = !lean_is_exclusive(x_7);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_7, 4);
lean_dec(x_92);
x_93 = lean_ctor_get(x_7, 3);
lean_dec(x_93);
x_94 = lean_ctor_get(x_7, 2);
lean_dec(x_94);
x_95 = lean_ctor_get(x_7, 1);
lean_dec(x_95);
x_96 = lean_ctor_get(x_7, 0);
lean_dec(x_96);
x_28 = x_7;
x_29 = x_91;
goto block_90;
}
else
{
lean_dec(x_7);
x_28 = lean_box(0);
x_29 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
x_32 = lean_ctor_get(x_18, 2);
x_33 = lean_ctor_get(x_18, 3);
x_34 = lean_ctor_get(x_18, 4);
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_nat_mul(x_36, x_35);
x_38 = lean_nat_dec_lt(x_30, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; uint8_t x_66; 
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
x_66 = !lean_is_exclusive(x_18);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_18, 4);
lean_dec(x_67);
x_68 = lean_ctor_get(x_18, 3);
lean_dec(x_68);
x_69 = lean_ctor_get(x_18, 2);
lean_dec(x_69);
x_70 = lean_ctor_get(x_18, 1);
lean_dec(x_70);
x_71 = lean_ctor_get(x_18, 0);
lean_dec(x_71);
x_39 = x_18;
x_40 = x_66;
goto block_65;
}
else
{
lean_dec(x_18);
x_39 = lean_box(0);
x_40 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_54; 
x_41 = lean_nat_add(x_13, x_14);
lean_dec(x_14);
x_42 = lean_nat_add(x_41, x_15);
lean_dec(x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_33, 0);
lean_inc(x_63);
x_54 = x_63;
goto block_62;
}
else
{
lean_object* x_64; 
x_64 = lean_unsigned_to_nat(0u);
x_54 = x_64;
goto block_62;
}
block_53:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_nat_add(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (x_40 == 0)
{
lean_ctor_set(x_39, 4, x_19);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 2, x_17);
lean_ctor_set(x_39, 1, x_16);
lean_ctor_set(x_39, 0, x_46);
x_47 = x_39;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_16);
lean_ctor_set(x_52, 2, x_17);
lean_ctor_set(x_52, 3, x_34);
lean_ctor_set(x_52, 4, x_19);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 4, x_47);
lean_ctor_set(x_28, 3, x_43);
lean_ctor_set(x_28, 2, x_32);
lean_ctor_set(x_28, 1, x_31);
lean_ctor_set(x_28, 0, x_42);
x_48 = x_28;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_31);
lean_ctor_set(x_50, 2, x_32);
lean_ctor_set(x_50, 3, x_43);
lean_ctor_set(x_50, 4, x_47);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
block_62:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_nat_add(x_41, x_54);
lean_dec(x_54);
lean_dec(x_41);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_33);
lean_ctor_set(x_8, 3, x_12);
lean_ctor_set(x_8, 0, x_55);
x_56 = x_8;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_4);
lean_ctor_set(x_61, 2, x_5);
lean_ctor_set(x_61, 3, x_12);
lean_ctor_set(x_61, 4, x_33);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
x_57 = lean_nat_add(x_13, x_35);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_34, 0);
lean_inc(x_58);
x_43 = x_56;
x_44 = x_57;
x_45 = x_58;
goto block_53;
}
else
{
lean_object* x_59; 
x_59 = lean_unsigned_to_nat(0u);
x_43 = x_56;
x_44 = x_57;
x_45 = x_59;
goto block_53;
}
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_del_object(x_8);
x_72 = lean_nat_add(x_13, x_14);
lean_dec(x_14);
x_73 = lean_nat_add(x_72, x_15);
lean_dec(x_15);
x_74 = lean_nat_add(x_72, x_30);
lean_dec(x_72);
lean_inc_ref(x_12);
if (x_29 == 0)
{
lean_ctor_set(x_28, 4, x_18);
lean_ctor_set(x_28, 3, x_12);
lean_ctor_set(x_28, 2, x_5);
lean_ctor_set(x_28, 1, x_4);
lean_ctor_set(x_28, 0, x_74);
x_75 = x_28;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_4);
lean_ctor_set(x_89, 2, x_5);
lean_ctor_set(x_89, 3, x_12);
lean_ctor_set(x_89, 4, x_18);
x_75 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_76; uint8_t x_77; uint8_t x_82; 
x_82 = !lean_is_exclusive(x_12);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_12, 4);
lean_dec(x_83);
x_84 = lean_ctor_get(x_12, 3);
lean_dec(x_84);
x_85 = lean_ctor_get(x_12, 2);
lean_dec(x_85);
x_86 = lean_ctor_get(x_12, 1);
lean_dec(x_86);
x_87 = lean_ctor_get(x_12, 0);
lean_dec(x_87);
x_76 = x_12;
x_77 = x_82;
goto block_81;
}
else
{
lean_dec(x_12);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
lean_ctor_set(x_76, 4, x_19);
lean_ctor_set(x_76, 3, x_75);
lean_ctor_set(x_76, 2, x_17);
lean_ctor_set(x_76, 1, x_16);
lean_ctor_set(x_76, 0, x_73);
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_73);
lean_ctor_set(x_80, 1, x_16);
lean_ctor_set(x_80, 2, x_17);
lean_ctor_set(x_80, 3, x_75);
lean_ctor_set(x_80, 4, x_19);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_12, 0);
lean_inc(x_97);
x_98 = lean_nat_add(x_13, x_97);
lean_dec(x_97);
if (x_9 == 0)
{
lean_ctor_set(x_8, 3, x_12);
lean_ctor_set(x_8, 0, x_98);
x_99 = x_8;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_4);
lean_ctor_set(x_101, 2, x_5);
lean_ctor_set(x_101, 3, x_12);
lean_ctor_set(x_101, 4, x_7);
x_99 = x_101;
goto block_100;
}
block_100:
{
return x_99;
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_7, 3);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_7, 4);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_119; 
x_104 = lean_ctor_get(x_7, 0);
x_105 = lean_ctor_get(x_7, 1);
x_106 = lean_ctor_get(x_7, 2);
x_119 = !lean_is_exclusive(x_7);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_7, 4);
lean_dec(x_120);
x_121 = lean_ctor_get(x_7, 3);
lean_dec(x_121);
x_107 = x_7;
x_108 = x_119;
goto block_118;
}
else
{
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_7);
x_107 = lean_box(0);
x_108 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_102, 0);
x_110 = lean_nat_add(x_13, x_104);
lean_dec(x_104);
x_111 = lean_nat_add(x_13, x_109);
if (x_108 == 0)
{
lean_ctor_set(x_107, 4, x_102);
lean_ctor_set(x_107, 3, x_12);
lean_ctor_set(x_107, 2, x_5);
lean_ctor_set(x_107, 1, x_4);
lean_ctor_set(x_107, 0, x_111);
x_112 = x_107;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_111);
lean_ctor_set(x_117, 1, x_4);
lean_ctor_set(x_117, 2, x_5);
lean_ctor_set(x_117, 3, x_12);
lean_ctor_set(x_117, 4, x_102);
x_112 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_113; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_103);
lean_ctor_set(x_8, 3, x_112);
lean_ctor_set(x_8, 2, x_106);
lean_ctor_set(x_8, 1, x_105);
lean_ctor_set(x_8, 0, x_110);
x_113 = x_8;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_105);
lean_ctor_set(x_115, 2, x_106);
lean_ctor_set(x_115, 3, x_112);
lean_ctor_set(x_115, 4, x_103);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_146; 
x_122 = lean_ctor_get(x_7, 1);
x_123 = lean_ctor_get(x_7, 2);
x_146 = !lean_is_exclusive(x_7);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_7, 4);
lean_dec(x_147);
x_148 = lean_ctor_get(x_7, 3);
lean_dec(x_148);
x_149 = lean_ctor_get(x_7, 0);
lean_dec(x_149);
x_124 = x_7;
x_125 = x_146;
goto block_145;
}
else
{
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_7);
x_124 = lean_box(0);
x_125 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_141; 
x_126 = lean_ctor_get(x_102, 1);
x_127 = lean_ctor_get(x_102, 2);
x_141 = !lean_is_exclusive(x_102);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_102, 4);
lean_dec(x_142);
x_143 = lean_ctor_get(x_102, 3);
lean_dec(x_143);
x_144 = lean_ctor_get(x_102, 0);
lean_dec(x_144);
x_128 = x_102;
x_129 = x_141;
goto block_140;
}
else
{
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_102);
x_128 = lean_box(0);
x_129 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_unsigned_to_nat(3u);
if (x_129 == 0)
{
lean_ctor_set(x_128, 4, x_103);
lean_ctor_set(x_128, 3, x_103);
lean_ctor_set(x_128, 2, x_5);
lean_ctor_set(x_128, 1, x_4);
lean_ctor_set(x_128, 0, x_13);
x_131 = x_128;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_139, 0, x_13);
lean_ctor_set(x_139, 1, x_4);
lean_ctor_set(x_139, 2, x_5);
lean_ctor_set(x_139, 3, x_103);
lean_ctor_set(x_139, 4, x_103);
x_131 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_132; 
if (x_125 == 0)
{
lean_ctor_set(x_124, 3, x_103);
lean_ctor_set(x_124, 0, x_13);
x_132 = x_124;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_137, 0, x_13);
lean_ctor_set(x_137, 1, x_122);
lean_ctor_set(x_137, 2, x_123);
lean_ctor_set(x_137, 3, x_103);
lean_ctor_set(x_137, 4, x_103);
x_132 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_133; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_132);
lean_ctor_set(x_8, 3, x_131);
lean_ctor_set(x_8, 2, x_127);
lean_ctor_set(x_8, 1, x_126);
lean_ctor_set(x_8, 0, x_130);
x_133 = x_8;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_126);
lean_ctor_set(x_135, 2, x_127);
lean_ctor_set(x_135, 3, x_131);
lean_ctor_set(x_135, 4, x_132);
x_133 = x_135;
goto block_134;
}
block_134:
{
return x_133;
}
}
}
}
}
}
}
else
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_7, 4);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_163; 
x_151 = lean_ctor_get(x_7, 1);
x_152 = lean_ctor_get(x_7, 2);
x_163 = !lean_is_exclusive(x_7);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_7, 4);
lean_dec(x_164);
x_165 = lean_ctor_get(x_7, 3);
lean_dec(x_165);
x_166 = lean_ctor_get(x_7, 0);
lean_dec(x_166);
x_153 = x_7;
x_154 = x_163;
goto block_162;
}
else
{
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_7);
x_153 = lean_box(0);
x_154 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_unsigned_to_nat(3u);
if (x_154 == 0)
{
lean_ctor_set(x_153, 4, x_102);
lean_ctor_set(x_153, 2, x_5);
lean_ctor_set(x_153, 1, x_4);
lean_ctor_set(x_153, 0, x_13);
x_156 = x_153;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_161, 0, x_13);
lean_ctor_set(x_161, 1, x_4);
lean_ctor_set(x_161, 2, x_5);
lean_ctor_set(x_161, 3, x_102);
lean_ctor_set(x_161, 4, x_102);
x_156 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_157; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_150);
lean_ctor_set(x_8, 3, x_156);
lean_ctor_set(x_8, 2, x_152);
lean_ctor_set(x_8, 1, x_151);
lean_ctor_set(x_8, 0, x_155);
x_157 = x_8;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_151);
lean_ctor_set(x_159, 2, x_152);
lean_ctor_set(x_159, 3, x_156);
lean_ctor_set(x_159, 4, x_150);
x_157 = x_159;
goto block_158;
}
block_158:
{
return x_157;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_180; 
x_167 = lean_ctor_get(x_7, 0);
x_168 = lean_ctor_get(x_7, 1);
x_169 = lean_ctor_get(x_7, 2);
x_180 = !lean_is_exclusive(x_7);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_7, 4);
lean_dec(x_181);
x_182 = lean_ctor_get(x_7, 3);
lean_dec(x_182);
x_170 = x_7;
x_171 = x_180;
goto block_179;
}
else
{
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_7);
x_170 = lean_box(0);
x_171 = x_180;
goto block_179;
}
block_179:
{
lean_object* x_172; 
if (x_171 == 0)
{
lean_ctor_set(x_170, 3, x_150);
x_172 = x_170;
goto block_177;
}
else
{
lean_object* x_178; 
x_178 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_178, 0, x_167);
lean_ctor_set(x_178, 1, x_168);
lean_ctor_set(x_178, 2, x_169);
lean_ctor_set(x_178, 3, x_150);
lean_ctor_set(x_178, 4, x_150);
x_172 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_unsigned_to_nat(2u);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_172);
lean_ctor_set(x_8, 3, x_150);
lean_ctor_set(x_8, 0, x_173);
x_174 = x_8;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_4);
lean_ctor_set(x_176, 2, x_5);
lean_ctor_set(x_176, 3, x_150);
lean_ctor_set(x_176, 4, x_172);
x_174 = x_176;
goto block_175;
}
block_175:
{
return x_174;
}
}
}
}
}
}
else
{
lean_object* x_183; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 3, x_7);
lean_ctor_set(x_8, 0, x_13);
x_183 = x_8;
goto block_184;
}
else
{
lean_object* x_185; 
x_185 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_185, 0, x_13);
lean_ctor_set(x_185, 1, x_4);
lean_ctor_set(x_185, 2, x_5);
lean_ctor_set(x_185, 3, x_7);
lean_ctor_set(x_185, 4, x_7);
x_183 = x_185;
goto block_184;
}
block_184:
{
return x_183;
}
}
}
}
case 1:
{
lean_del_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_186 = lean_ctor_get(x_6, 0);
x_187 = lean_ctor_get(x_6, 1);
x_188 = lean_ctor_get(x_6, 2);
x_189 = lean_ctor_get(x_6, 3);
x_190 = lean_ctor_get(x_6, 4);
lean_inc(x_190);
x_191 = lean_ctor_get(x_7, 0);
x_192 = lean_ctor_get(x_7, 1);
x_193 = lean_ctor_get(x_7, 2);
x_194 = lean_ctor_get(x_7, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_7, 4);
x_196 = lean_unsigned_to_nat(1u);
x_197 = lean_nat_dec_lt(x_186, x_191);
if (x_197 == 0)
{
lean_object* x_198; uint8_t x_199; uint8_t x_333; 
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
x_333 = !lean_is_exclusive(x_6);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_334 = lean_ctor_get(x_6, 4);
lean_dec(x_334);
x_335 = lean_ctor_get(x_6, 3);
lean_dec(x_335);
x_336 = lean_ctor_get(x_6, 2);
lean_dec(x_336);
x_337 = lean_ctor_get(x_6, 1);
lean_dec(x_337);
x_338 = lean_ctor_get(x_6, 0);
lean_dec(x_338);
x_198 = x_6;
x_199 = x_333;
goto block_332;
}
else
{
lean_dec(x_6);
x_198 = lean_box(0);
x_199 = x_333;
goto block_332;
}
block_332:
{
lean_object* x_200; lean_object* x_201; 
x_200 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_187, x_188, x_189, x_190);
x_201 = lean_ctor_get(x_200, 2);
lean_inc(x_201);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_202 = lean_ctor_get(x_200, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_dec_ref(x_200);
x_204 = lean_ctor_get(x_201, 0);
x_205 = lean_unsigned_to_nat(3u);
x_206 = lean_nat_mul(x_205, x_204);
x_207 = lean_nat_dec_lt(x_206, x_191);
lean_dec(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_194);
x_208 = lean_nat_add(x_196, x_204);
x_209 = lean_nat_add(x_208, x_191);
lean_dec(x_208);
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_7);
lean_ctor_set(x_198, 3, x_201);
lean_ctor_set(x_198, 2, x_203);
lean_ctor_set(x_198, 1, x_202);
lean_ctor_set(x_198, 0, x_209);
x_210 = x_198;
goto block_211;
}
else
{
lean_object* x_212; 
x_212 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_202);
lean_ctor_set(x_212, 2, x_203);
lean_ctor_set(x_212, 3, x_201);
lean_ctor_set(x_212, 4, x_7);
x_210 = x_212;
goto block_211;
}
block_211:
{
return x_210;
}
}
else
{
lean_object* x_213; uint8_t x_214; uint8_t x_267; 
lean_inc(x_195);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
x_267 = !lean_is_exclusive(x_7);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_268 = lean_ctor_get(x_7, 4);
lean_dec(x_268);
x_269 = lean_ctor_get(x_7, 3);
lean_dec(x_269);
x_270 = lean_ctor_get(x_7, 2);
lean_dec(x_270);
x_271 = lean_ctor_get(x_7, 1);
lean_dec(x_271);
x_272 = lean_ctor_get(x_7, 0);
lean_dec(x_272);
x_213 = x_7;
x_214 = x_267;
goto block_266;
}
else
{
lean_dec(x_7);
x_213 = lean_box(0);
x_214 = x_267;
goto block_266;
}
block_266:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_215 = lean_ctor_get(x_194, 0);
x_216 = lean_ctor_get(x_194, 1);
x_217 = lean_ctor_get(x_194, 2);
x_218 = lean_ctor_get(x_194, 3);
x_219 = lean_ctor_get(x_194, 4);
x_220 = lean_ctor_get(x_195, 0);
x_221 = lean_unsigned_to_nat(2u);
x_222 = lean_nat_mul(x_221, x_220);
x_223 = lean_nat_dec_lt(x_215, x_222);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; uint8_t x_225; uint8_t x_251; 
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
x_251 = !lean_is_exclusive(x_194);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_194, 4);
lean_dec(x_252);
x_253 = lean_ctor_get(x_194, 3);
lean_dec(x_253);
x_254 = lean_ctor_get(x_194, 2);
lean_dec(x_254);
x_255 = lean_ctor_get(x_194, 1);
lean_dec(x_255);
x_256 = lean_ctor_get(x_194, 0);
lean_dec(x_256);
x_224 = x_194;
x_225 = x_251;
goto block_250;
}
else
{
lean_dec(x_194);
x_224 = lean_box(0);
x_225 = x_251;
goto block_250;
}
block_250:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_239; 
x_226 = lean_nat_add(x_196, x_204);
x_227 = lean_nat_add(x_226, x_191);
lean_dec(x_191);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_218, 0);
lean_inc(x_248);
x_239 = x_248;
goto block_247;
}
else
{
lean_object* x_249; 
x_249 = lean_unsigned_to_nat(0u);
x_239 = x_249;
goto block_247;
}
block_238:
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_nat_add(x_229, x_230);
lean_dec(x_230);
lean_dec(x_229);
if (x_225 == 0)
{
lean_ctor_set(x_224, 4, x_195);
lean_ctor_set(x_224, 3, x_219);
lean_ctor_set(x_224, 2, x_193);
lean_ctor_set(x_224, 1, x_192);
lean_ctor_set(x_224, 0, x_231);
x_232 = x_224;
goto block_236;
}
else
{
lean_object* x_237; 
x_237 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_237, 0, x_231);
lean_ctor_set(x_237, 1, x_192);
lean_ctor_set(x_237, 2, x_193);
lean_ctor_set(x_237, 3, x_219);
lean_ctor_set(x_237, 4, x_195);
x_232 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_233; 
if (x_214 == 0)
{
lean_ctor_set(x_213, 4, x_232);
lean_ctor_set(x_213, 3, x_228);
lean_ctor_set(x_213, 2, x_217);
lean_ctor_set(x_213, 1, x_216);
lean_ctor_set(x_213, 0, x_227);
x_233 = x_213;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_235, 0, x_227);
lean_ctor_set(x_235, 1, x_216);
lean_ctor_set(x_235, 2, x_217);
lean_ctor_set(x_235, 3, x_228);
lean_ctor_set(x_235, 4, x_232);
x_233 = x_235;
goto block_234;
}
block_234:
{
return x_233;
}
}
}
block_247:
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_nat_add(x_226, x_239);
lean_dec(x_239);
lean_dec(x_226);
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_218);
lean_ctor_set(x_198, 3, x_201);
lean_ctor_set(x_198, 2, x_203);
lean_ctor_set(x_198, 1, x_202);
lean_ctor_set(x_198, 0, x_240);
x_241 = x_198;
goto block_245;
}
else
{
lean_object* x_246; 
x_246 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_246, 0, x_240);
lean_ctor_set(x_246, 1, x_202);
lean_ctor_set(x_246, 2, x_203);
lean_ctor_set(x_246, 3, x_201);
lean_ctor_set(x_246, 4, x_218);
x_241 = x_246;
goto block_245;
}
block_245:
{
lean_object* x_242; 
x_242 = lean_nat_add(x_196, x_220);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_219, 0);
lean_inc(x_243);
x_228 = x_241;
x_229 = x_242;
x_230 = x_243;
goto block_238;
}
else
{
lean_object* x_244; 
x_244 = lean_unsigned_to_nat(0u);
x_228 = x_241;
x_229 = x_242;
x_230 = x_244;
goto block_238;
}
}
}
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_257 = lean_nat_add(x_196, x_204);
x_258 = lean_nat_add(x_257, x_191);
lean_dec(x_191);
x_259 = lean_nat_add(x_257, x_215);
lean_dec(x_257);
if (x_214 == 0)
{
lean_ctor_set(x_213, 4, x_194);
lean_ctor_set(x_213, 3, x_201);
lean_ctor_set(x_213, 2, x_203);
lean_ctor_set(x_213, 1, x_202);
lean_ctor_set(x_213, 0, x_259);
x_260 = x_213;
goto block_264;
}
else
{
lean_object* x_265; 
x_265 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_265, 0, x_259);
lean_ctor_set(x_265, 1, x_202);
lean_ctor_set(x_265, 2, x_203);
lean_ctor_set(x_265, 3, x_201);
lean_ctor_set(x_265, 4, x_194);
x_260 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_261; 
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_195);
lean_ctor_set(x_198, 3, x_260);
lean_ctor_set(x_198, 2, x_193);
lean_ctor_set(x_198, 1, x_192);
lean_ctor_set(x_198, 0, x_258);
x_261 = x_198;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_258);
lean_ctor_set(x_263, 1, x_192);
lean_ctor_set(x_263, 2, x_193);
lean_ctor_set(x_263, 3, x_260);
lean_ctor_set(x_263, 4, x_195);
x_261 = x_263;
goto block_262;
}
block_262:
{
return x_261;
}
}
}
}
}
}
else
{
lean_object* x_273; uint8_t x_274; uint8_t x_326; 
lean_inc(x_195);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
x_326 = !lean_is_exclusive(x_7);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_327 = lean_ctor_get(x_7, 4);
lean_dec(x_327);
x_328 = lean_ctor_get(x_7, 3);
lean_dec(x_328);
x_329 = lean_ctor_get(x_7, 2);
lean_dec(x_329);
x_330 = lean_ctor_get(x_7, 1);
lean_dec(x_330);
x_331 = lean_ctor_get(x_7, 0);
lean_dec(x_331);
x_273 = x_7;
x_274 = x_326;
goto block_325;
}
else
{
lean_dec(x_7);
x_273 = lean_box(0);
x_274 = x_326;
goto block_325;
}
block_325:
{
if (lean_obj_tag(x_194) == 0)
{
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_275 = lean_ctor_get(x_200, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_200, 1);
lean_inc(x_276);
lean_dec_ref(x_200);
x_277 = lean_ctor_get(x_194, 0);
x_278 = lean_nat_add(x_196, x_191);
lean_dec(x_191);
x_279 = lean_nat_add(x_196, x_277);
if (x_274 == 0)
{
lean_ctor_set(x_273, 4, x_194);
lean_ctor_set(x_273, 3, x_201);
lean_ctor_set(x_273, 2, x_276);
lean_ctor_set(x_273, 1, x_275);
lean_ctor_set(x_273, 0, x_279);
x_280 = x_273;
goto block_284;
}
else
{
lean_object* x_285; 
x_285 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_275);
lean_ctor_set(x_285, 2, x_276);
lean_ctor_set(x_285, 3, x_201);
lean_ctor_set(x_285, 4, x_194);
x_280 = x_285;
goto block_284;
}
block_284:
{
lean_object* x_281; 
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_195);
lean_ctor_set(x_198, 3, x_280);
lean_ctor_set(x_198, 2, x_193);
lean_ctor_set(x_198, 1, x_192);
lean_ctor_set(x_198, 0, x_278);
x_281 = x_198;
goto block_282;
}
else
{
lean_object* x_283; 
x_283 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_283, 0, x_278);
lean_ctor_set(x_283, 1, x_192);
lean_ctor_set(x_283, 2, x_193);
lean_ctor_set(x_283, 3, x_280);
lean_ctor_set(x_283, 4, x_195);
x_281 = x_283;
goto block_282;
}
block_282:
{
return x_281;
}
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; uint8_t x_303; 
lean_dec(x_191);
x_286 = lean_ctor_get(x_200, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_200, 1);
lean_inc(x_287);
lean_dec_ref(x_200);
x_288 = lean_ctor_get(x_194, 1);
x_289 = lean_ctor_get(x_194, 2);
x_303 = !lean_is_exclusive(x_194);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_194, 4);
lean_dec(x_304);
x_305 = lean_ctor_get(x_194, 3);
lean_dec(x_305);
x_306 = lean_ctor_get(x_194, 0);
lean_dec(x_306);
x_290 = x_194;
x_291 = x_303;
goto block_302;
}
else
{
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_194);
x_290 = lean_box(0);
x_291 = x_303;
goto block_302;
}
block_302:
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_unsigned_to_nat(3u);
if (x_291 == 0)
{
lean_ctor_set(x_290, 4, x_195);
lean_ctor_set(x_290, 3, x_195);
lean_ctor_set(x_290, 2, x_287);
lean_ctor_set(x_290, 1, x_286);
lean_ctor_set(x_290, 0, x_196);
x_293 = x_290;
goto block_300;
}
else
{
lean_object* x_301; 
x_301 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_301, 0, x_196);
lean_ctor_set(x_301, 1, x_286);
lean_ctor_set(x_301, 2, x_287);
lean_ctor_set(x_301, 3, x_195);
lean_ctor_set(x_301, 4, x_195);
x_293 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_294; 
if (x_274 == 0)
{
lean_ctor_set(x_273, 3, x_195);
lean_ctor_set(x_273, 0, x_196);
x_294 = x_273;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_299, 0, x_196);
lean_ctor_set(x_299, 1, x_192);
lean_ctor_set(x_299, 2, x_193);
lean_ctor_set(x_299, 3, x_195);
lean_ctor_set(x_299, 4, x_195);
x_294 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_295; 
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_294);
lean_ctor_set(x_198, 3, x_293);
lean_ctor_set(x_198, 2, x_289);
lean_ctor_set(x_198, 1, x_288);
lean_ctor_set(x_198, 0, x_292);
x_295 = x_198;
goto block_296;
}
else
{
lean_object* x_297; 
x_297 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_297, 0, x_292);
lean_ctor_set(x_297, 1, x_288);
lean_ctor_set(x_297, 2, x_289);
lean_ctor_set(x_297, 3, x_293);
lean_ctor_set(x_297, 4, x_294);
x_295 = x_297;
goto block_296;
}
block_296:
{
return x_295;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_191);
x_307 = lean_ctor_get(x_200, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_200, 1);
lean_inc(x_308);
lean_dec_ref(x_200);
x_309 = lean_unsigned_to_nat(3u);
if (x_274 == 0)
{
lean_ctor_set(x_273, 4, x_194);
lean_ctor_set(x_273, 2, x_308);
lean_ctor_set(x_273, 1, x_307);
lean_ctor_set(x_273, 0, x_196);
x_310 = x_273;
goto block_314;
}
else
{
lean_object* x_315; 
x_315 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_315, 0, x_196);
lean_ctor_set(x_315, 1, x_307);
lean_ctor_set(x_315, 2, x_308);
lean_ctor_set(x_315, 3, x_194);
lean_ctor_set(x_315, 4, x_194);
x_310 = x_315;
goto block_314;
}
block_314:
{
lean_object* x_311; 
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_195);
lean_ctor_set(x_198, 3, x_310);
lean_ctor_set(x_198, 2, x_193);
lean_ctor_set(x_198, 1, x_192);
lean_ctor_set(x_198, 0, x_309);
x_311 = x_198;
goto block_312;
}
else
{
lean_object* x_313; 
x_313 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_313, 0, x_309);
lean_ctor_set(x_313, 1, x_192);
lean_ctor_set(x_313, 2, x_193);
lean_ctor_set(x_313, 3, x_310);
lean_ctor_set(x_313, 4, x_195);
x_311 = x_313;
goto block_312;
}
block_312:
{
return x_311;
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_200, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_200, 1);
lean_inc(x_317);
lean_dec_ref(x_200);
if (x_274 == 0)
{
lean_ctor_set(x_273, 3, x_195);
x_318 = x_273;
goto block_323;
}
else
{
lean_object* x_324; 
x_324 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_324, 0, x_191);
lean_ctor_set(x_324, 1, x_192);
lean_ctor_set(x_324, 2, x_193);
lean_ctor_set(x_324, 3, x_195);
lean_ctor_set(x_324, 4, x_195);
x_318 = x_324;
goto block_323;
}
block_323:
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_unsigned_to_nat(2u);
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_318);
lean_ctor_set(x_198, 3, x_195);
lean_ctor_set(x_198, 2, x_317);
lean_ctor_set(x_198, 1, x_316);
lean_ctor_set(x_198, 0, x_319);
x_320 = x_198;
goto block_321;
}
else
{
lean_object* x_322; 
x_322 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_316);
lean_ctor_set(x_322, 2, x_317);
lean_ctor_set(x_322, 3, x_195);
lean_ctor_set(x_322, 4, x_318);
x_320 = x_322;
goto block_321;
}
block_321:
{
return x_320;
}
}
}
}
}
}
}
}
else
{
lean_object* x_339; uint8_t x_340; uint8_t x_491; 
lean_inc(x_195);
lean_inc(x_193);
lean_inc(x_192);
x_491 = !lean_is_exclusive(x_7);
if (x_491 == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_492 = lean_ctor_get(x_7, 4);
lean_dec(x_492);
x_493 = lean_ctor_get(x_7, 3);
lean_dec(x_493);
x_494 = lean_ctor_get(x_7, 2);
lean_dec(x_494);
x_495 = lean_ctor_get(x_7, 1);
lean_dec(x_495);
x_496 = lean_ctor_get(x_7, 0);
lean_dec(x_496);
x_339 = x_7;
x_340 = x_491;
goto block_490;
}
else
{
lean_dec(x_7);
x_339 = lean_box(0);
x_340 = x_491;
goto block_490;
}
block_490:
{
lean_object* x_341; lean_object* x_342; 
x_341 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_192, x_193, x_194, x_195);
x_342 = lean_ctor_get(x_341, 2);
lean_inc(x_342);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_343 = lean_ctor_get(x_341, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_341, 1);
lean_inc(x_344);
lean_dec_ref(x_341);
x_345 = lean_ctor_get(x_342, 0);
x_346 = lean_unsigned_to_nat(3u);
x_347 = lean_nat_mul(x_346, x_345);
x_348 = lean_nat_dec_lt(x_347, x_186);
lean_dec(x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_190);
x_349 = lean_nat_add(x_196, x_186);
x_350 = lean_nat_add(x_349, x_345);
lean_dec(x_349);
if (x_340 == 0)
{
lean_ctor_set(x_339, 4, x_342);
lean_ctor_set(x_339, 3, x_6);
lean_ctor_set(x_339, 2, x_344);
lean_ctor_set(x_339, 1, x_343);
lean_ctor_set(x_339, 0, x_350);
x_351 = x_339;
goto block_352;
}
else
{
lean_object* x_353; 
x_353 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_343);
lean_ctor_set(x_353, 2, x_344);
lean_ctor_set(x_353, 3, x_6);
lean_ctor_set(x_353, 4, x_342);
x_351 = x_353;
goto block_352;
}
block_352:
{
return x_351;
}
}
else
{
lean_object* x_354; uint8_t x_355; uint8_t x_419; 
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
x_419 = !lean_is_exclusive(x_6);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_420 = lean_ctor_get(x_6, 4);
lean_dec(x_420);
x_421 = lean_ctor_get(x_6, 3);
lean_dec(x_421);
x_422 = lean_ctor_get(x_6, 2);
lean_dec(x_422);
x_423 = lean_ctor_get(x_6, 1);
lean_dec(x_423);
x_424 = lean_ctor_get(x_6, 0);
lean_dec(x_424);
x_354 = x_6;
x_355 = x_419;
goto block_418;
}
else
{
lean_dec(x_6);
x_354 = lean_box(0);
x_355 = x_419;
goto block_418;
}
block_418:
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_356 = lean_ctor_get(x_189, 0);
x_357 = lean_ctor_get(x_190, 0);
x_358 = lean_ctor_get(x_190, 1);
x_359 = lean_ctor_get(x_190, 2);
x_360 = lean_ctor_get(x_190, 3);
x_361 = lean_ctor_get(x_190, 4);
x_362 = lean_unsigned_to_nat(2u);
x_363 = lean_nat_mul(x_362, x_356);
x_364 = lean_nat_dec_lt(x_357, x_363);
lean_dec(x_363);
if (x_364 == 0)
{
lean_object* x_365; uint8_t x_366; uint8_t x_402; 
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_del_object(x_354);
x_402 = !lean_is_exclusive(x_190);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_403 = lean_ctor_get(x_190, 4);
lean_dec(x_403);
x_404 = lean_ctor_get(x_190, 3);
lean_dec(x_404);
x_405 = lean_ctor_get(x_190, 2);
lean_dec(x_405);
x_406 = lean_ctor_get(x_190, 1);
lean_dec(x_406);
x_407 = lean_ctor_get(x_190, 0);
lean_dec(x_407);
x_365 = x_190;
x_366 = x_402;
goto block_401;
}
else
{
lean_dec(x_190);
x_365 = lean_box(0);
x_366 = x_402;
goto block_401;
}
block_401:
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_389; lean_object* x_390; 
x_367 = lean_nat_add(x_196, x_186);
lean_dec(x_186);
x_368 = lean_nat_add(x_367, x_345);
lean_dec(x_367);
x_389 = lean_nat_add(x_196, x_356);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_360, 0);
lean_inc(x_399);
x_390 = x_399;
goto block_398;
}
else
{
lean_object* x_400; 
x_400 = lean_unsigned_to_nat(0u);
x_390 = x_400;
goto block_398;
}
block_388:
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_nat_add(x_370, x_371);
lean_dec(x_371);
lean_dec(x_370);
lean_inc_ref(x_342);
if (x_366 == 0)
{
lean_ctor_set(x_365, 4, x_342);
lean_ctor_set(x_365, 3, x_361);
lean_ctor_set(x_365, 2, x_344);
lean_ctor_set(x_365, 1, x_343);
lean_ctor_set(x_365, 0, x_372);
x_373 = x_365;
goto block_386;
}
else
{
lean_object* x_387; 
x_387 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_387, 0, x_372);
lean_ctor_set(x_387, 1, x_343);
lean_ctor_set(x_387, 2, x_344);
lean_ctor_set(x_387, 3, x_361);
lean_ctor_set(x_387, 4, x_342);
x_373 = x_387;
goto block_386;
}
block_386:
{
lean_object* x_374; uint8_t x_375; uint8_t x_380; 
x_380 = !lean_is_exclusive(x_342);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_381 = lean_ctor_get(x_342, 4);
lean_dec(x_381);
x_382 = lean_ctor_get(x_342, 3);
lean_dec(x_382);
x_383 = lean_ctor_get(x_342, 2);
lean_dec(x_383);
x_384 = lean_ctor_get(x_342, 1);
lean_dec(x_384);
x_385 = lean_ctor_get(x_342, 0);
lean_dec(x_385);
x_374 = x_342;
x_375 = x_380;
goto block_379;
}
else
{
lean_dec(x_342);
x_374 = lean_box(0);
x_375 = x_380;
goto block_379;
}
block_379:
{
lean_object* x_376; 
if (x_375 == 0)
{
lean_ctor_set(x_374, 4, x_373);
lean_ctor_set(x_374, 3, x_369);
lean_ctor_set(x_374, 2, x_359);
lean_ctor_set(x_374, 1, x_358);
lean_ctor_set(x_374, 0, x_368);
x_376 = x_374;
goto block_377;
}
else
{
lean_object* x_378; 
x_378 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_378, 0, x_368);
lean_ctor_set(x_378, 1, x_358);
lean_ctor_set(x_378, 2, x_359);
lean_ctor_set(x_378, 3, x_369);
lean_ctor_set(x_378, 4, x_373);
x_376 = x_378;
goto block_377;
}
block_377:
{
return x_376;
}
}
}
}
block_398:
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_nat_add(x_389, x_390);
lean_dec(x_390);
lean_dec(x_389);
if (x_340 == 0)
{
lean_ctor_set(x_339, 4, x_360);
lean_ctor_set(x_339, 3, x_189);
lean_ctor_set(x_339, 2, x_188);
lean_ctor_set(x_339, 1, x_187);
lean_ctor_set(x_339, 0, x_391);
x_392 = x_339;
goto block_396;
}
else
{
lean_object* x_397; 
x_397 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_397, 0, x_391);
lean_ctor_set(x_397, 1, x_187);
lean_ctor_set(x_397, 2, x_188);
lean_ctor_set(x_397, 3, x_189);
lean_ctor_set(x_397, 4, x_360);
x_392 = x_397;
goto block_396;
}
block_396:
{
lean_object* x_393; 
x_393 = lean_nat_add(x_196, x_345);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_394; 
x_394 = lean_ctor_get(x_361, 0);
lean_inc(x_394);
x_369 = x_392;
x_370 = x_393;
x_371 = x_394;
goto block_388;
}
else
{
lean_object* x_395; 
x_395 = lean_unsigned_to_nat(0u);
x_369 = x_392;
x_370 = x_393;
x_371 = x_395;
goto block_388;
}
}
}
}
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_408 = lean_nat_add(x_196, x_186);
lean_dec(x_186);
x_409 = lean_nat_add(x_408, x_345);
lean_dec(x_408);
x_410 = lean_nat_add(x_196, x_345);
x_411 = lean_nat_add(x_410, x_357);
lean_dec(x_410);
if (x_340 == 0)
{
lean_ctor_set(x_339, 4, x_342);
lean_ctor_set(x_339, 3, x_190);
lean_ctor_set(x_339, 2, x_344);
lean_ctor_set(x_339, 1, x_343);
lean_ctor_set(x_339, 0, x_411);
x_412 = x_339;
goto block_416;
}
else
{
lean_object* x_417; 
x_417 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_417, 0, x_411);
lean_ctor_set(x_417, 1, x_343);
lean_ctor_set(x_417, 2, x_344);
lean_ctor_set(x_417, 3, x_190);
lean_ctor_set(x_417, 4, x_342);
x_412 = x_417;
goto block_416;
}
block_416:
{
lean_object* x_413; 
if (x_355 == 0)
{
lean_ctor_set(x_354, 4, x_412);
lean_ctor_set(x_354, 0, x_409);
x_413 = x_354;
goto block_414;
}
else
{
lean_object* x_415; 
x_415 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_415, 0, x_409);
lean_ctor_set(x_415, 1, x_187);
lean_ctor_set(x_415, 2, x_188);
lean_ctor_set(x_415, 3, x_189);
lean_ctor_set(x_415, 4, x_412);
x_413 = x_415;
goto block_414;
}
block_414:
{
return x_413;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_425; uint8_t x_426; uint8_t x_448; 
lean_inc_ref(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
x_448 = !lean_is_exclusive(x_6);
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_449 = lean_ctor_get(x_6, 4);
lean_dec(x_449);
x_450 = lean_ctor_get(x_6, 3);
lean_dec(x_450);
x_451 = lean_ctor_get(x_6, 2);
lean_dec(x_451);
x_452 = lean_ctor_get(x_6, 1);
lean_dec(x_452);
x_453 = lean_ctor_get(x_6, 0);
lean_dec(x_453);
x_425 = x_6;
x_426 = x_448;
goto block_447;
}
else
{
lean_dec(x_6);
x_425 = lean_box(0);
x_426 = x_448;
goto block_447;
}
block_447:
{
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_427 = lean_ctor_get(x_341, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_341, 1);
lean_inc(x_428);
lean_dec_ref(x_341);
x_429 = lean_ctor_get(x_190, 0);
x_430 = lean_nat_add(x_196, x_186);
lean_dec(x_186);
x_431 = lean_nat_add(x_196, x_429);
if (x_340 == 0)
{
lean_ctor_set(x_339, 4, x_342);
lean_ctor_set(x_339, 3, x_190);
lean_ctor_set(x_339, 2, x_428);
lean_ctor_set(x_339, 1, x_427);
lean_ctor_set(x_339, 0, x_431);
x_432 = x_339;
goto block_436;
}
else
{
lean_object* x_437; 
x_437 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_437, 0, x_431);
lean_ctor_set(x_437, 1, x_427);
lean_ctor_set(x_437, 2, x_428);
lean_ctor_set(x_437, 3, x_190);
lean_ctor_set(x_437, 4, x_342);
x_432 = x_437;
goto block_436;
}
block_436:
{
lean_object* x_433; 
if (x_426 == 0)
{
lean_ctor_set(x_425, 4, x_432);
lean_ctor_set(x_425, 0, x_430);
x_433 = x_425;
goto block_434;
}
else
{
lean_object* x_435; 
x_435 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_435, 0, x_430);
lean_ctor_set(x_435, 1, x_187);
lean_ctor_set(x_435, 2, x_188);
lean_ctor_set(x_435, 3, x_189);
lean_ctor_set(x_435, 4, x_432);
x_433 = x_435;
goto block_434;
}
block_434:
{
return x_433;
}
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_186);
x_438 = lean_ctor_get(x_341, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_341, 1);
lean_inc(x_439);
lean_dec_ref(x_341);
x_440 = lean_unsigned_to_nat(3u);
if (x_340 == 0)
{
lean_ctor_set(x_339, 4, x_190);
lean_ctor_set(x_339, 3, x_190);
lean_ctor_set(x_339, 2, x_439);
lean_ctor_set(x_339, 1, x_438);
lean_ctor_set(x_339, 0, x_196);
x_441 = x_339;
goto block_445;
}
else
{
lean_object* x_446; 
x_446 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_446, 0, x_196);
lean_ctor_set(x_446, 1, x_438);
lean_ctor_set(x_446, 2, x_439);
lean_ctor_set(x_446, 3, x_190);
lean_ctor_set(x_446, 4, x_190);
x_441 = x_446;
goto block_445;
}
block_445:
{
lean_object* x_442; 
if (x_426 == 0)
{
lean_ctor_set(x_425, 4, x_441);
lean_ctor_set(x_425, 0, x_440);
x_442 = x_425;
goto block_443;
}
else
{
lean_object* x_444; 
x_444 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_444, 0, x_440);
lean_ctor_set(x_444, 1, x_187);
lean_ctor_set(x_444, 2, x_188);
lean_ctor_set(x_444, 3, x_189);
lean_ctor_set(x_444, 4, x_441);
x_442 = x_444;
goto block_443;
}
block_443:
{
return x_442;
}
}
}
}
}
else
{
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_454; uint8_t x_455; uint8_t x_478; 
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
x_478 = !lean_is_exclusive(x_6);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_479 = lean_ctor_get(x_6, 4);
lean_dec(x_479);
x_480 = lean_ctor_get(x_6, 3);
lean_dec(x_480);
x_481 = lean_ctor_get(x_6, 2);
lean_dec(x_481);
x_482 = lean_ctor_get(x_6, 1);
lean_dec(x_482);
x_483 = lean_ctor_get(x_6, 0);
lean_dec(x_483);
x_454 = x_6;
x_455 = x_478;
goto block_477;
}
else
{
lean_dec(x_6);
x_454 = lean_box(0);
x_455 = x_478;
goto block_477;
}
block_477:
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; uint8_t x_473; 
x_456 = lean_ctor_get(x_341, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_341, 1);
lean_inc(x_457);
lean_dec_ref(x_341);
x_458 = lean_ctor_get(x_190, 1);
x_459 = lean_ctor_get(x_190, 2);
x_473 = !lean_is_exclusive(x_190);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_474 = lean_ctor_get(x_190, 4);
lean_dec(x_474);
x_475 = lean_ctor_get(x_190, 3);
lean_dec(x_475);
x_476 = lean_ctor_get(x_190, 0);
lean_dec(x_476);
x_460 = x_190;
x_461 = x_473;
goto block_472;
}
else
{
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_190);
x_460 = lean_box(0);
x_461 = x_473;
goto block_472;
}
block_472:
{
lean_object* x_462; lean_object* x_463; 
x_462 = lean_unsigned_to_nat(3u);
if (x_461 == 0)
{
lean_ctor_set(x_460, 4, x_189);
lean_ctor_set(x_460, 3, x_189);
lean_ctor_set(x_460, 2, x_188);
lean_ctor_set(x_460, 1, x_187);
lean_ctor_set(x_460, 0, x_196);
x_463 = x_460;
goto block_470;
}
else
{
lean_object* x_471; 
x_471 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_471, 0, x_196);
lean_ctor_set(x_471, 1, x_187);
lean_ctor_set(x_471, 2, x_188);
lean_ctor_set(x_471, 3, x_189);
lean_ctor_set(x_471, 4, x_189);
x_463 = x_471;
goto block_470;
}
block_470:
{
lean_object* x_464; 
if (x_340 == 0)
{
lean_ctor_set(x_339, 4, x_189);
lean_ctor_set(x_339, 3, x_189);
lean_ctor_set(x_339, 2, x_457);
lean_ctor_set(x_339, 1, x_456);
lean_ctor_set(x_339, 0, x_196);
x_464 = x_339;
goto block_468;
}
else
{
lean_object* x_469; 
x_469 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_469, 0, x_196);
lean_ctor_set(x_469, 1, x_456);
lean_ctor_set(x_469, 2, x_457);
lean_ctor_set(x_469, 3, x_189);
lean_ctor_set(x_469, 4, x_189);
x_464 = x_469;
goto block_468;
}
block_468:
{
lean_object* x_465; 
if (x_455 == 0)
{
lean_ctor_set(x_454, 4, x_464);
lean_ctor_set(x_454, 3, x_463);
lean_ctor_set(x_454, 2, x_459);
lean_ctor_set(x_454, 1, x_458);
lean_ctor_set(x_454, 0, x_462);
x_465 = x_454;
goto block_466;
}
else
{
lean_object* x_467; 
x_467 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_467, 0, x_462);
lean_ctor_set(x_467, 1, x_458);
lean_ctor_set(x_467, 2, x_459);
lean_ctor_set(x_467, 3, x_463);
lean_ctor_set(x_467, 4, x_464);
x_465 = x_467;
goto block_466;
}
block_466:
{
return x_465;
}
}
}
}
}
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_484 = lean_ctor_get(x_341, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_341, 1);
lean_inc(x_485);
lean_dec_ref(x_341);
x_486 = lean_unsigned_to_nat(2u);
if (x_340 == 0)
{
lean_ctor_set(x_339, 4, x_190);
lean_ctor_set(x_339, 3, x_6);
lean_ctor_set(x_339, 2, x_485);
lean_ctor_set(x_339, 1, x_484);
lean_ctor_set(x_339, 0, x_486);
x_487 = x_339;
goto block_488;
}
else
{
lean_object* x_489; 
x_489 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_489, 0, x_486);
lean_ctor_set(x_489, 1, x_484);
lean_ctor_set(x_489, 2, x_485);
lean_ctor_set(x_489, 3, x_6);
lean_ctor_set(x_489, 4, x_190);
x_487 = x_489;
goto block_488;
}
block_488:
{
return x_487;
}
}
}
}
}
}
}
else
{
return x_6;
}
}
else
{
return x_7;
}
}
default: 
{
lean_object* x_497; lean_object* x_498; 
x_497 = l_Std_DTreeMap_Internal_Impl_erase___redArg(x_1, x_2, x_7);
x_498 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_497) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; 
x_499 = lean_ctor_get(x_497, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_6, 0);
x_501 = lean_ctor_get(x_6, 1);
x_502 = lean_ctor_get(x_6, 2);
x_503 = lean_ctor_get(x_6, 3);
x_504 = lean_ctor_get(x_6, 4);
lean_inc(x_504);
x_505 = lean_unsigned_to_nat(3u);
x_506 = lean_nat_mul(x_505, x_499);
x_507 = lean_nat_dec_lt(x_506, x_500);
lean_dec(x_506);
if (x_507 == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_504);
x_508 = lean_nat_add(x_498, x_500);
x_509 = lean_nat_add(x_508, x_499);
lean_dec(x_499);
lean_dec(x_508);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_497);
lean_ctor_set(x_8, 0, x_509);
x_510 = x_8;
goto block_511;
}
else
{
lean_object* x_512; 
x_512 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_512, 0, x_509);
lean_ctor_set(x_512, 1, x_4);
lean_ctor_set(x_512, 2, x_5);
lean_ctor_set(x_512, 3, x_6);
lean_ctor_set(x_512, 4, x_497);
x_510 = x_512;
goto block_511;
}
block_511:
{
return x_510;
}
}
else
{
lean_object* x_513; uint8_t x_514; uint8_t x_578; 
lean_inc(x_503);
lean_inc(x_502);
lean_inc(x_501);
lean_inc(x_500);
x_578 = !lean_is_exclusive(x_6);
if (x_578 == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_579 = lean_ctor_get(x_6, 4);
lean_dec(x_579);
x_580 = lean_ctor_get(x_6, 3);
lean_dec(x_580);
x_581 = lean_ctor_get(x_6, 2);
lean_dec(x_581);
x_582 = lean_ctor_get(x_6, 1);
lean_dec(x_582);
x_583 = lean_ctor_get(x_6, 0);
lean_dec(x_583);
x_513 = x_6;
x_514 = x_578;
goto block_577;
}
else
{
lean_dec(x_6);
x_513 = lean_box(0);
x_514 = x_578;
goto block_577;
}
block_577:
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; uint8_t x_523; 
x_515 = lean_ctor_get(x_503, 0);
x_516 = lean_ctor_get(x_504, 0);
x_517 = lean_ctor_get(x_504, 1);
x_518 = lean_ctor_get(x_504, 2);
x_519 = lean_ctor_get(x_504, 3);
x_520 = lean_ctor_get(x_504, 4);
x_521 = lean_unsigned_to_nat(2u);
x_522 = lean_nat_mul(x_521, x_515);
x_523 = lean_nat_dec_lt(x_516, x_522);
lean_dec(x_522);
if (x_523 == 0)
{
lean_object* x_524; uint8_t x_525; uint8_t x_552; 
lean_inc(x_520);
lean_inc(x_519);
lean_inc(x_518);
lean_inc(x_517);
x_552 = !lean_is_exclusive(x_504);
if (x_552 == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_553 = lean_ctor_get(x_504, 4);
lean_dec(x_553);
x_554 = lean_ctor_get(x_504, 3);
lean_dec(x_554);
x_555 = lean_ctor_get(x_504, 2);
lean_dec(x_555);
x_556 = lean_ctor_get(x_504, 1);
lean_dec(x_556);
x_557 = lean_ctor_get(x_504, 0);
lean_dec(x_557);
x_524 = x_504;
x_525 = x_552;
goto block_551;
}
else
{
lean_dec(x_504);
x_524 = lean_box(0);
x_525 = x_552;
goto block_551;
}
block_551:
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_539; lean_object* x_540; 
x_526 = lean_nat_add(x_498, x_500);
lean_dec(x_500);
x_527 = lean_nat_add(x_526, x_499);
lean_dec(x_526);
x_539 = lean_nat_add(x_498, x_515);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_549; 
x_549 = lean_ctor_get(x_519, 0);
lean_inc(x_549);
x_540 = x_549;
goto block_548;
}
else
{
lean_object* x_550; 
x_550 = lean_unsigned_to_nat(0u);
x_540 = x_550;
goto block_548;
}
block_538:
{
lean_object* x_531; lean_object* x_532; 
x_531 = lean_nat_add(x_529, x_530);
lean_dec(x_530);
lean_dec(x_529);
if (x_525 == 0)
{
lean_ctor_set(x_524, 4, x_497);
lean_ctor_set(x_524, 3, x_520);
lean_ctor_set(x_524, 2, x_5);
lean_ctor_set(x_524, 1, x_4);
lean_ctor_set(x_524, 0, x_531);
x_532 = x_524;
goto block_536;
}
else
{
lean_object* x_537; 
x_537 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_537, 0, x_531);
lean_ctor_set(x_537, 1, x_4);
lean_ctor_set(x_537, 2, x_5);
lean_ctor_set(x_537, 3, x_520);
lean_ctor_set(x_537, 4, x_497);
x_532 = x_537;
goto block_536;
}
block_536:
{
lean_object* x_533; 
if (x_514 == 0)
{
lean_ctor_set(x_513, 4, x_532);
lean_ctor_set(x_513, 3, x_528);
lean_ctor_set(x_513, 2, x_518);
lean_ctor_set(x_513, 1, x_517);
lean_ctor_set(x_513, 0, x_527);
x_533 = x_513;
goto block_534;
}
else
{
lean_object* x_535; 
x_535 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_535, 0, x_527);
lean_ctor_set(x_535, 1, x_517);
lean_ctor_set(x_535, 2, x_518);
lean_ctor_set(x_535, 3, x_528);
lean_ctor_set(x_535, 4, x_532);
x_533 = x_535;
goto block_534;
}
block_534:
{
return x_533;
}
}
}
block_548:
{
lean_object* x_541; lean_object* x_542; 
x_541 = lean_nat_add(x_539, x_540);
lean_dec(x_540);
lean_dec(x_539);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_519);
lean_ctor_set(x_8, 3, x_503);
lean_ctor_set(x_8, 2, x_502);
lean_ctor_set(x_8, 1, x_501);
lean_ctor_set(x_8, 0, x_541);
x_542 = x_8;
goto block_546;
}
else
{
lean_object* x_547; 
x_547 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_547, 0, x_541);
lean_ctor_set(x_547, 1, x_501);
lean_ctor_set(x_547, 2, x_502);
lean_ctor_set(x_547, 3, x_503);
lean_ctor_set(x_547, 4, x_519);
x_542 = x_547;
goto block_546;
}
block_546:
{
lean_object* x_543; 
x_543 = lean_nat_add(x_498, x_499);
lean_dec(x_499);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_544; 
x_544 = lean_ctor_get(x_520, 0);
lean_inc(x_544);
x_528 = x_542;
x_529 = x_543;
x_530 = x_544;
goto block_538;
}
else
{
lean_object* x_545; 
x_545 = lean_unsigned_to_nat(0u);
x_528 = x_542;
x_529 = x_543;
x_530 = x_545;
goto block_538;
}
}
}
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_del_object(x_8);
x_558 = lean_nat_add(x_498, x_500);
lean_dec(x_500);
x_559 = lean_nat_add(x_558, x_499);
lean_dec(x_558);
x_560 = lean_nat_add(x_498, x_499);
lean_dec(x_499);
x_561 = lean_nat_add(x_560, x_516);
lean_dec(x_560);
lean_inc_ref(x_497);
if (x_514 == 0)
{
lean_ctor_set(x_513, 4, x_497);
lean_ctor_set(x_513, 3, x_504);
lean_ctor_set(x_513, 2, x_5);
lean_ctor_set(x_513, 1, x_4);
lean_ctor_set(x_513, 0, x_561);
x_562 = x_513;
goto block_575;
}
else
{
lean_object* x_576; 
x_576 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_576, 0, x_561);
lean_ctor_set(x_576, 1, x_4);
lean_ctor_set(x_576, 2, x_5);
lean_ctor_set(x_576, 3, x_504);
lean_ctor_set(x_576, 4, x_497);
x_562 = x_576;
goto block_575;
}
block_575:
{
lean_object* x_563; uint8_t x_564; uint8_t x_569; 
x_569 = !lean_is_exclusive(x_497);
if (x_569 == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_570 = lean_ctor_get(x_497, 4);
lean_dec(x_570);
x_571 = lean_ctor_get(x_497, 3);
lean_dec(x_571);
x_572 = lean_ctor_get(x_497, 2);
lean_dec(x_572);
x_573 = lean_ctor_get(x_497, 1);
lean_dec(x_573);
x_574 = lean_ctor_get(x_497, 0);
lean_dec(x_574);
x_563 = x_497;
x_564 = x_569;
goto block_568;
}
else
{
lean_dec(x_497);
x_563 = lean_box(0);
x_564 = x_569;
goto block_568;
}
block_568:
{
lean_object* x_565; 
if (x_564 == 0)
{
lean_ctor_set(x_563, 4, x_562);
lean_ctor_set(x_563, 3, x_503);
lean_ctor_set(x_563, 2, x_502);
lean_ctor_set(x_563, 1, x_501);
lean_ctor_set(x_563, 0, x_559);
x_565 = x_563;
goto block_566;
}
else
{
lean_object* x_567; 
x_567 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_567, 0, x_559);
lean_ctor_set(x_567, 1, x_501);
lean_ctor_set(x_567, 2, x_502);
lean_ctor_set(x_567, 3, x_503);
lean_ctor_set(x_567, 4, x_562);
x_565 = x_567;
goto block_566;
}
block_566:
{
return x_565;
}
}
}
}
}
}
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_497, 0);
lean_inc(x_584);
x_585 = lean_nat_add(x_498, x_584);
lean_dec(x_584);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_497);
lean_ctor_set(x_8, 0, x_585);
x_586 = x_8;
goto block_587;
}
else
{
lean_object* x_588; 
x_588 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_588, 0, x_585);
lean_ctor_set(x_588, 1, x_4);
lean_ctor_set(x_588, 2, x_5);
lean_ctor_set(x_588, 3, x_6);
lean_ctor_set(x_588, 4, x_497);
x_586 = x_588;
goto block_587;
}
block_587:
{
return x_586;
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_589; 
x_589 = lean_ctor_get(x_6, 3);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; 
lean_inc_ref(x_589);
x_590 = lean_ctor_get(x_6, 4);
lean_inc(x_590);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; uint8_t x_606; 
x_591 = lean_ctor_get(x_6, 0);
x_592 = lean_ctor_get(x_6, 1);
x_593 = lean_ctor_get(x_6, 2);
x_606 = !lean_is_exclusive(x_6);
if (x_606 == 0)
{
lean_object* x_607; lean_object* x_608; 
x_607 = lean_ctor_get(x_6, 4);
lean_dec(x_607);
x_608 = lean_ctor_get(x_6, 3);
lean_dec(x_608);
x_594 = x_6;
x_595 = x_606;
goto block_605;
}
else
{
lean_inc(x_593);
lean_inc(x_592);
lean_inc(x_591);
lean_dec(x_6);
x_594 = lean_box(0);
x_595 = x_606;
goto block_605;
}
block_605:
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_596 = lean_ctor_get(x_590, 0);
x_597 = lean_nat_add(x_498, x_591);
lean_dec(x_591);
x_598 = lean_nat_add(x_498, x_596);
if (x_595 == 0)
{
lean_ctor_set(x_594, 4, x_497);
lean_ctor_set(x_594, 3, x_590);
lean_ctor_set(x_594, 2, x_5);
lean_ctor_set(x_594, 1, x_4);
lean_ctor_set(x_594, 0, x_598);
x_599 = x_594;
goto block_603;
}
else
{
lean_object* x_604; 
x_604 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_604, 0, x_598);
lean_ctor_set(x_604, 1, x_4);
lean_ctor_set(x_604, 2, x_5);
lean_ctor_set(x_604, 3, x_590);
lean_ctor_set(x_604, 4, x_497);
x_599 = x_604;
goto block_603;
}
block_603:
{
lean_object* x_600; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_599);
lean_ctor_set(x_8, 3, x_589);
lean_ctor_set(x_8, 2, x_593);
lean_ctor_set(x_8, 1, x_592);
lean_ctor_set(x_8, 0, x_597);
x_600 = x_8;
goto block_601;
}
else
{
lean_object* x_602; 
x_602 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_602, 0, x_597);
lean_ctor_set(x_602, 1, x_592);
lean_ctor_set(x_602, 2, x_593);
lean_ctor_set(x_602, 3, x_589);
lean_ctor_set(x_602, 4, x_599);
x_600 = x_602;
goto block_601;
}
block_601:
{
return x_600;
}
}
}
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; uint8_t x_612; uint8_t x_621; 
x_609 = lean_ctor_get(x_6, 1);
x_610 = lean_ctor_get(x_6, 2);
x_621 = !lean_is_exclusive(x_6);
if (x_621 == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_622 = lean_ctor_get(x_6, 4);
lean_dec(x_622);
x_623 = lean_ctor_get(x_6, 3);
lean_dec(x_623);
x_624 = lean_ctor_get(x_6, 0);
lean_dec(x_624);
x_611 = x_6;
x_612 = x_621;
goto block_620;
}
else
{
lean_inc(x_610);
lean_inc(x_609);
lean_dec(x_6);
x_611 = lean_box(0);
x_612 = x_621;
goto block_620;
}
block_620:
{
lean_object* x_613; lean_object* x_614; 
x_613 = lean_unsigned_to_nat(3u);
if (x_612 == 0)
{
lean_ctor_set(x_611, 3, x_590);
lean_ctor_set(x_611, 2, x_5);
lean_ctor_set(x_611, 1, x_4);
lean_ctor_set(x_611, 0, x_498);
x_614 = x_611;
goto block_618;
}
else
{
lean_object* x_619; 
x_619 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_619, 0, x_498);
lean_ctor_set(x_619, 1, x_4);
lean_ctor_set(x_619, 2, x_5);
lean_ctor_set(x_619, 3, x_590);
lean_ctor_set(x_619, 4, x_590);
x_614 = x_619;
goto block_618;
}
block_618:
{
lean_object* x_615; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_614);
lean_ctor_set(x_8, 3, x_589);
lean_ctor_set(x_8, 2, x_610);
lean_ctor_set(x_8, 1, x_609);
lean_ctor_set(x_8, 0, x_613);
x_615 = x_8;
goto block_616;
}
else
{
lean_object* x_617; 
x_617 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_617, 0, x_613);
lean_ctor_set(x_617, 1, x_609);
lean_ctor_set(x_617, 2, x_610);
lean_ctor_set(x_617, 3, x_589);
lean_ctor_set(x_617, 4, x_614);
x_615 = x_617;
goto block_616;
}
block_616:
{
return x_615;
}
}
}
}
}
else
{
lean_object* x_625; 
x_625 = lean_ctor_get(x_6, 4);
lean_inc(x_625);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; uint8_t x_629; uint8_t x_650; 
lean_inc(x_589);
x_626 = lean_ctor_get(x_6, 1);
x_627 = lean_ctor_get(x_6, 2);
x_650 = !lean_is_exclusive(x_6);
if (x_650 == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_651 = lean_ctor_get(x_6, 4);
lean_dec(x_651);
x_652 = lean_ctor_get(x_6, 3);
lean_dec(x_652);
x_653 = lean_ctor_get(x_6, 0);
lean_dec(x_653);
x_628 = x_6;
x_629 = x_650;
goto block_649;
}
else
{
lean_inc(x_627);
lean_inc(x_626);
lean_dec(x_6);
x_628 = lean_box(0);
x_629 = x_650;
goto block_649;
}
block_649:
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; uint8_t x_633; uint8_t x_645; 
x_630 = lean_ctor_get(x_625, 1);
x_631 = lean_ctor_get(x_625, 2);
x_645 = !lean_is_exclusive(x_625);
if (x_645 == 0)
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_646 = lean_ctor_get(x_625, 4);
lean_dec(x_646);
x_647 = lean_ctor_get(x_625, 3);
lean_dec(x_647);
x_648 = lean_ctor_get(x_625, 0);
lean_dec(x_648);
x_632 = x_625;
x_633 = x_645;
goto block_644;
}
else
{
lean_inc(x_631);
lean_inc(x_630);
lean_dec(x_625);
x_632 = lean_box(0);
x_633 = x_645;
goto block_644;
}
block_644:
{
lean_object* x_634; lean_object* x_635; 
x_634 = lean_unsigned_to_nat(3u);
if (x_633 == 0)
{
lean_ctor_set(x_632, 4, x_589);
lean_ctor_set(x_632, 3, x_589);
lean_ctor_set(x_632, 2, x_627);
lean_ctor_set(x_632, 1, x_626);
lean_ctor_set(x_632, 0, x_498);
x_635 = x_632;
goto block_642;
}
else
{
lean_object* x_643; 
x_643 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_643, 0, x_498);
lean_ctor_set(x_643, 1, x_626);
lean_ctor_set(x_643, 2, x_627);
lean_ctor_set(x_643, 3, x_589);
lean_ctor_set(x_643, 4, x_589);
x_635 = x_643;
goto block_642;
}
block_642:
{
lean_object* x_636; 
if (x_629 == 0)
{
lean_ctor_set(x_628, 4, x_589);
lean_ctor_set(x_628, 2, x_5);
lean_ctor_set(x_628, 1, x_4);
lean_ctor_set(x_628, 0, x_498);
x_636 = x_628;
goto block_640;
}
else
{
lean_object* x_641; 
x_641 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_641, 0, x_498);
lean_ctor_set(x_641, 1, x_4);
lean_ctor_set(x_641, 2, x_5);
lean_ctor_set(x_641, 3, x_589);
lean_ctor_set(x_641, 4, x_589);
x_636 = x_641;
goto block_640;
}
block_640:
{
lean_object* x_637; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_636);
lean_ctor_set(x_8, 3, x_635);
lean_ctor_set(x_8, 2, x_631);
lean_ctor_set(x_8, 1, x_630);
lean_ctor_set(x_8, 0, x_634);
x_637 = x_8;
goto block_638;
}
else
{
lean_object* x_639; 
x_639 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_639, 0, x_634);
lean_ctor_set(x_639, 1, x_630);
lean_ctor_set(x_639, 2, x_631);
lean_ctor_set(x_639, 3, x_635);
lean_ctor_set(x_639, 4, x_636);
x_637 = x_639;
goto block_638;
}
block_638:
{
return x_637;
}
}
}
}
}
}
else
{
lean_object* x_654; lean_object* x_655; 
x_654 = lean_unsigned_to_nat(2u);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_625);
lean_ctor_set(x_8, 0, x_654);
x_655 = x_8;
goto block_656;
}
else
{
lean_object* x_657; 
x_657 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_657, 0, x_654);
lean_ctor_set(x_657, 1, x_4);
lean_ctor_set(x_657, 2, x_5);
lean_ctor_set(x_657, 3, x_6);
lean_ctor_set(x_657, 4, x_625);
x_655 = x_657;
goto block_656;
}
block_656:
{
return x_655;
}
}
}
}
else
{
lean_object* x_658; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 0, x_498);
x_658 = x_8;
goto block_659;
}
else
{
lean_object* x_660; 
x_660 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_660, 0, x_498);
lean_ctor_set(x_660, 1, x_4);
lean_ctor_set(x_660, 2, x_5);
lean_ctor_set(x_660, 3, x_6);
lean_ctor_set(x_660, 4, x_6);
x_658 = x_660;
goto block_659;
}
block_659:
{
return x_658;
}
}
}
}
}
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_erase___redArg(x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_705; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_ctor_get(x_3, 3);
x_7 = lean_ctor_get(x_3, 4);
x_705 = !lean_is_exclusive(x_3);
if (x_705 == 0)
{
lean_object* x_706; 
x_706 = lean_ctor_get(x_3, 0);
lean_dec(x_706);
x_8 = x_3;
x_9 = x_705;
goto block_704;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_705;
goto block_704;
}
block_704:
{
lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_10 = lean_apply_2(x_1, x_2, x_4);
x_11 = lean_unbox(x_10);
switch (x_11) {
case 0:
{
lean_object* x_12; 
x_12 = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(x_1, x_2, x_6);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_nat_mul(x_19, x_13);
x_21 = lean_nat_dec_lt(x_20, x_14);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_22, x_13);
lean_dec(x_13);
x_24 = lean_nat_add(x_23, x_14);
lean_dec(x_23);
if (x_9 == 0)
{
lean_ctor_set(x_8, 3, x_12);
lean_ctor_set(x_8, 0, x_24);
x_25 = x_8;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_5);
lean_ctor_set(x_27, 3, x_12);
lean_ctor_set(x_27, 4, x_7);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
else
{
lean_object* x_28; uint8_t x_29; uint8_t x_99; 
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_99 = !lean_is_exclusive(x_7);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_7, 4);
lean_dec(x_100);
x_101 = lean_ctor_get(x_7, 3);
lean_dec(x_101);
x_102 = lean_ctor_get(x_7, 2);
lean_dec(x_102);
x_103 = lean_ctor_get(x_7, 1);
lean_dec(x_103);
x_104 = lean_ctor_get(x_7, 0);
lean_dec(x_104);
x_28 = x_7;
x_29 = x_99;
goto block_98;
}
else
{
lean_dec(x_7);
x_28 = lean_box(0);
x_29 = x_99;
goto block_98;
}
block_98:
{
if (lean_obj_tag(x_17) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
x_32 = lean_ctor_get(x_17, 2);
x_33 = lean_ctor_get(x_17, 3);
x_34 = lean_ctor_get(x_17, 4);
x_35 = lean_ctor_get(x_18, 0);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_nat_mul(x_36, x_35);
x_38 = lean_nat_dec_lt(x_30, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; uint8_t x_67; 
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
x_67 = !lean_is_exclusive(x_17);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_17, 4);
lean_dec(x_68);
x_69 = lean_ctor_get(x_17, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_17, 2);
lean_dec(x_70);
x_71 = lean_ctor_get(x_17, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_17, 0);
lean_dec(x_72);
x_39 = x_17;
x_40 = x_67;
goto block_66;
}
else
{
lean_dec(x_17);
x_39 = lean_box(0);
x_40 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_55; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_41, x_13);
lean_dec(x_13);
x_43 = lean_nat_add(x_42, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_33, 0);
lean_inc(x_64);
x_55 = x_64;
goto block_63;
}
else
{
lean_object* x_65; 
x_65 = lean_unsigned_to_nat(0u);
x_55 = x_65;
goto block_63;
}
block_54:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_nat_add(x_44, x_46);
lean_dec(x_46);
lean_dec(x_44);
if (x_40 == 0)
{
lean_ctor_set(x_39, 4, x_18);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 2, x_16);
lean_ctor_set(x_39, 1, x_15);
lean_ctor_set(x_39, 0, x_47);
x_48 = x_39;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_15);
lean_ctor_set(x_53, 2, x_16);
lean_ctor_set(x_53, 3, x_34);
lean_ctor_set(x_53, 4, x_18);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 4, x_48);
lean_ctor_set(x_28, 3, x_45);
lean_ctor_set(x_28, 2, x_32);
lean_ctor_set(x_28, 1, x_31);
lean_ctor_set(x_28, 0, x_43);
x_49 = x_28;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_31);
lean_ctor_set(x_51, 2, x_32);
lean_ctor_set(x_51, 3, x_45);
lean_ctor_set(x_51, 4, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
block_63:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_nat_add(x_42, x_55);
lean_dec(x_55);
lean_dec(x_42);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_33);
lean_ctor_set(x_8, 3, x_12);
lean_ctor_set(x_8, 0, x_56);
x_57 = x_8;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_4);
lean_ctor_set(x_62, 2, x_5);
lean_ctor_set(x_62, 3, x_12);
lean_ctor_set(x_62, 4, x_33);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
x_58 = lean_nat_add(x_41, x_35);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_34, 0);
lean_inc(x_59);
x_44 = x_58;
x_45 = x_57;
x_46 = x_59;
goto block_54;
}
else
{
lean_object* x_60; 
x_60 = lean_unsigned_to_nat(0u);
x_44 = x_58;
x_45 = x_57;
x_46 = x_60;
goto block_54;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_del_object(x_8);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_73, x_13);
lean_dec(x_13);
x_75 = lean_nat_add(x_74, x_14);
lean_dec(x_14);
x_76 = lean_nat_add(x_74, x_30);
lean_dec(x_74);
lean_inc_ref(x_12);
if (x_29 == 0)
{
lean_ctor_set(x_28, 4, x_17);
lean_ctor_set(x_28, 3, x_12);
lean_ctor_set(x_28, 2, x_5);
lean_ctor_set(x_28, 1, x_4);
lean_ctor_set(x_28, 0, x_76);
x_77 = x_28;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_91, 0, x_76);
lean_ctor_set(x_91, 1, x_4);
lean_ctor_set(x_91, 2, x_5);
lean_ctor_set(x_91, 3, x_12);
lean_ctor_set(x_91, 4, x_17);
x_77 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_78; uint8_t x_79; uint8_t x_84; 
x_84 = !lean_is_exclusive(x_12);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_12, 4);
lean_dec(x_85);
x_86 = lean_ctor_get(x_12, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_12, 2);
lean_dec(x_87);
x_88 = lean_ctor_get(x_12, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_12, 0);
lean_dec(x_89);
x_78 = x_12;
x_79 = x_84;
goto block_83;
}
else
{
lean_dec(x_12);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
lean_ctor_set(x_78, 4, x_18);
lean_ctor_set(x_78, 3, x_77);
lean_ctor_set(x_78, 2, x_16);
lean_ctor_set(x_78, 1, x_15);
lean_ctor_set(x_78, 0, x_75);
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_15);
lean_ctor_set(x_82, 2, x_16);
lean_ctor_set(x_82, 3, x_77);
lean_ctor_set(x_82, 4, x_18);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_17);
lean_del_object(x_28);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_del_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_92 = lean_box(1);
x_93 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3);
x_94 = l_panic___redArg(x_92, x_93);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_del_object(x_28);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_del_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_95 = lean_box(1);
x_96 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4);
x_97 = l_panic___redArg(x_95, x_96);
return x_97;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_12, 0);
lean_inc(x_105);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_106, x_105);
lean_dec(x_105);
if (x_9 == 0)
{
lean_ctor_set(x_8, 3, x_12);
lean_ctor_set(x_8, 0, x_107);
x_108 = x_8;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_4);
lean_ctor_set(x_110, 2, x_5);
lean_ctor_set(x_110, 3, x_12);
lean_ctor_set(x_110, 4, x_7);
x_108 = x_110;
goto block_109;
}
block_109:
{
return x_108;
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_7, 3);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_7, 4);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_129; 
x_113 = lean_ctor_get(x_7, 0);
x_114 = lean_ctor_get(x_7, 1);
x_115 = lean_ctor_get(x_7, 2);
x_129 = !lean_is_exclusive(x_7);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_7, 4);
lean_dec(x_130);
x_131 = lean_ctor_get(x_7, 3);
lean_dec(x_131);
x_116 = x_7;
x_117 = x_129;
goto block_128;
}
else
{
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_7);
x_116 = lean_box(0);
x_117 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_111, 0);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_nat_add(x_119, x_113);
lean_dec(x_113);
x_121 = lean_nat_add(x_119, x_118);
if (x_117 == 0)
{
lean_ctor_set(x_116, 4, x_111);
lean_ctor_set(x_116, 3, x_12);
lean_ctor_set(x_116, 2, x_5);
lean_ctor_set(x_116, 1, x_4);
lean_ctor_set(x_116, 0, x_121);
x_122 = x_116;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_127, 0, x_121);
lean_ctor_set(x_127, 1, x_4);
lean_ctor_set(x_127, 2, x_5);
lean_ctor_set(x_127, 3, x_12);
lean_ctor_set(x_127, 4, x_111);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_112);
lean_ctor_set(x_8, 3, x_122);
lean_ctor_set(x_8, 2, x_115);
lean_ctor_set(x_8, 1, x_114);
lean_ctor_set(x_8, 0, x_120);
x_123 = x_8;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_114);
lean_ctor_set(x_125, 2, x_115);
lean_ctor_set(x_125, 3, x_122);
lean_ctor_set(x_125, 4, x_112);
x_123 = x_125;
goto block_124;
}
block_124:
{
return x_123;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_157; 
x_132 = lean_ctor_get(x_7, 1);
x_133 = lean_ctor_get(x_7, 2);
x_157 = !lean_is_exclusive(x_7);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_7, 4);
lean_dec(x_158);
x_159 = lean_ctor_get(x_7, 3);
lean_dec(x_159);
x_160 = lean_ctor_get(x_7, 0);
lean_dec(x_160);
x_134 = x_7;
x_135 = x_157;
goto block_156;
}
else
{
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_7);
x_134 = lean_box(0);
x_135 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_152; 
x_136 = lean_ctor_get(x_111, 1);
x_137 = lean_ctor_get(x_111, 2);
x_152 = !lean_is_exclusive(x_111);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_111, 4);
lean_dec(x_153);
x_154 = lean_ctor_get(x_111, 3);
lean_dec(x_154);
x_155 = lean_ctor_get(x_111, 0);
lean_dec(x_155);
x_138 = x_111;
x_139 = x_152;
goto block_151;
}
else
{
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_111);
x_138 = lean_box(0);
x_139 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_unsigned_to_nat(3u);
x_141 = lean_unsigned_to_nat(1u);
if (x_139 == 0)
{
lean_ctor_set(x_138, 4, x_112);
lean_ctor_set(x_138, 3, x_112);
lean_ctor_set(x_138, 2, x_5);
lean_ctor_set(x_138, 1, x_4);
lean_ctor_set(x_138, 0, x_141);
x_142 = x_138;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_150, 0, x_141);
lean_ctor_set(x_150, 1, x_4);
lean_ctor_set(x_150, 2, x_5);
lean_ctor_set(x_150, 3, x_112);
lean_ctor_set(x_150, 4, x_112);
x_142 = x_150;
goto block_149;
}
block_149:
{
lean_object* x_143; 
if (x_135 == 0)
{
lean_ctor_set(x_134, 3, x_112);
lean_ctor_set(x_134, 0, x_141);
x_143 = x_134;
goto block_147;
}
else
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_148, 0, x_141);
lean_ctor_set(x_148, 1, x_132);
lean_ctor_set(x_148, 2, x_133);
lean_ctor_set(x_148, 3, x_112);
lean_ctor_set(x_148, 4, x_112);
x_143 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_144; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_143);
lean_ctor_set(x_8, 3, x_142);
lean_ctor_set(x_8, 2, x_137);
lean_ctor_set(x_8, 1, x_136);
lean_ctor_set(x_8, 0, x_140);
x_144 = x_8;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_136);
lean_ctor_set(x_146, 2, x_137);
lean_ctor_set(x_146, 3, x_142);
lean_ctor_set(x_146, 4, x_143);
x_144 = x_146;
goto block_145;
}
block_145:
{
return x_144;
}
}
}
}
}
}
}
else
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_7, 4);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_175; 
x_162 = lean_ctor_get(x_7, 1);
x_163 = lean_ctor_get(x_7, 2);
x_175 = !lean_is_exclusive(x_7);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_7, 4);
lean_dec(x_176);
x_177 = lean_ctor_get(x_7, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_7, 0);
lean_dec(x_178);
x_164 = x_7;
x_165 = x_175;
goto block_174;
}
else
{
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_7);
x_164 = lean_box(0);
x_165 = x_175;
goto block_174;
}
block_174:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_unsigned_to_nat(3u);
x_167 = lean_unsigned_to_nat(1u);
if (x_165 == 0)
{
lean_ctor_set(x_164, 4, x_111);
lean_ctor_set(x_164, 2, x_5);
lean_ctor_set(x_164, 1, x_4);
lean_ctor_set(x_164, 0, x_167);
x_168 = x_164;
goto block_172;
}
else
{
lean_object* x_173; 
x_173 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_173, 0, x_167);
lean_ctor_set(x_173, 1, x_4);
lean_ctor_set(x_173, 2, x_5);
lean_ctor_set(x_173, 3, x_111);
lean_ctor_set(x_173, 4, x_111);
x_168 = x_173;
goto block_172;
}
block_172:
{
lean_object* x_169; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_161);
lean_ctor_set(x_8, 3, x_168);
lean_ctor_set(x_8, 2, x_163);
lean_ctor_set(x_8, 1, x_162);
lean_ctor_set(x_8, 0, x_166);
x_169 = x_8;
goto block_170;
}
else
{
lean_object* x_171; 
x_171 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_171, 0, x_166);
lean_ctor_set(x_171, 1, x_162);
lean_ctor_set(x_171, 2, x_163);
lean_ctor_set(x_171, 3, x_168);
lean_ctor_set(x_171, 4, x_161);
x_169 = x_171;
goto block_170;
}
block_170:
{
return x_169;
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_unsigned_to_nat(2u);
if (x_9 == 0)
{
lean_ctor_set(x_8, 3, x_161);
lean_ctor_set(x_8, 0, x_179);
x_180 = x_8;
goto block_181;
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_4);
lean_ctor_set(x_182, 2, x_5);
lean_ctor_set(x_182, 3, x_161);
lean_ctor_set(x_182, 4, x_7);
x_180 = x_182;
goto block_181;
}
block_181:
{
return x_180;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_unsigned_to_nat(1u);
if (x_9 == 0)
{
lean_ctor_set(x_8, 3, x_7);
lean_ctor_set(x_8, 0, x_183);
x_184 = x_8;
goto block_185;
}
else
{
lean_object* x_186; 
x_186 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_4);
lean_ctor_set(x_186, 2, x_5);
lean_ctor_set(x_186, 3, x_7);
lean_ctor_set(x_186, 4, x_7);
x_184 = x_186;
goto block_185;
}
block_185:
{
return x_184;
}
}
}
}
case 1:
{
lean_del_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_187 = lean_ctor_get(x_6, 0);
x_188 = lean_ctor_get(x_6, 1);
x_189 = lean_ctor_get(x_6, 2);
x_190 = lean_ctor_get(x_6, 3);
x_191 = lean_ctor_get(x_6, 4);
lean_inc(x_191);
x_192 = lean_ctor_get(x_7, 0);
x_193 = lean_ctor_get(x_7, 1);
x_194 = lean_ctor_get(x_7, 2);
x_195 = lean_ctor_get(x_7, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_7, 4);
x_197 = lean_nat_dec_lt(x_187, x_192);
if (x_197 == 0)
{
lean_object* x_198; uint8_t x_199; uint8_t x_351; 
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
x_351 = !lean_is_exclusive(x_6);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_352 = lean_ctor_get(x_6, 4);
lean_dec(x_352);
x_353 = lean_ctor_get(x_6, 3);
lean_dec(x_353);
x_354 = lean_ctor_get(x_6, 2);
lean_dec(x_354);
x_355 = lean_ctor_get(x_6, 1);
lean_dec(x_355);
x_356 = lean_ctor_get(x_6, 0);
lean_dec(x_356);
x_198 = x_6;
x_199 = x_351;
goto block_350;
}
else
{
lean_dec(x_6);
x_198 = lean_box(0);
x_199 = x_351;
goto block_350;
}
block_350:
{
lean_object* x_200; lean_object* x_201; 
x_200 = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(x_188, x_189, x_190, x_191);
x_201 = lean_ctor_get(x_200, 2);
lean_inc(x_201);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_202 = lean_ctor_get(x_200, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_dec_ref(x_200);
x_204 = lean_ctor_get(x_201, 0);
x_205 = lean_unsigned_to_nat(3u);
x_206 = lean_nat_mul(x_205, x_204);
x_207 = lean_nat_dec_lt(x_206, x_192);
lean_dec(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_195);
x_208 = lean_unsigned_to_nat(1u);
x_209 = lean_nat_add(x_208, x_204);
x_210 = lean_nat_add(x_209, x_192);
lean_dec(x_209);
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_7);
lean_ctor_set(x_198, 3, x_201);
lean_ctor_set(x_198, 2, x_203);
lean_ctor_set(x_198, 1, x_202);
lean_ctor_set(x_198, 0, x_210);
x_211 = x_198;
goto block_212;
}
else
{
lean_object* x_213; 
x_213 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_202);
lean_ctor_set(x_213, 2, x_203);
lean_ctor_set(x_213, 3, x_201);
lean_ctor_set(x_213, 4, x_7);
x_211 = x_213;
goto block_212;
}
block_212:
{
return x_211;
}
}
else
{
lean_object* x_214; uint8_t x_215; uint8_t x_276; 
lean_inc(x_196);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
x_276 = !lean_is_exclusive(x_7);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_277 = lean_ctor_get(x_7, 4);
lean_dec(x_277);
x_278 = lean_ctor_get(x_7, 3);
lean_dec(x_278);
x_279 = lean_ctor_get(x_7, 2);
lean_dec(x_279);
x_280 = lean_ctor_get(x_7, 1);
lean_dec(x_280);
x_281 = lean_ctor_get(x_7, 0);
lean_dec(x_281);
x_214 = x_7;
x_215 = x_276;
goto block_275;
}
else
{
lean_dec(x_7);
x_214 = lean_box(0);
x_215 = x_276;
goto block_275;
}
block_275:
{
if (lean_obj_tag(x_195) == 0)
{
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_216 = lean_ctor_get(x_195, 0);
x_217 = lean_ctor_get(x_195, 1);
x_218 = lean_ctor_get(x_195, 2);
x_219 = lean_ctor_get(x_195, 3);
x_220 = lean_ctor_get(x_195, 4);
x_221 = lean_ctor_get(x_196, 0);
x_222 = lean_unsigned_to_nat(2u);
x_223 = lean_nat_mul(x_222, x_221);
x_224 = lean_nat_dec_lt(x_216, x_223);
lean_dec(x_223);
if (x_224 == 0)
{
lean_object* x_225; uint8_t x_226; uint8_t x_253; 
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
x_253 = !lean_is_exclusive(x_195);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_254 = lean_ctor_get(x_195, 4);
lean_dec(x_254);
x_255 = lean_ctor_get(x_195, 3);
lean_dec(x_255);
x_256 = lean_ctor_get(x_195, 2);
lean_dec(x_256);
x_257 = lean_ctor_get(x_195, 1);
lean_dec(x_257);
x_258 = lean_ctor_get(x_195, 0);
lean_dec(x_258);
x_225 = x_195;
x_226 = x_253;
goto block_252;
}
else
{
lean_dec(x_195);
x_225 = lean_box(0);
x_226 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_241; 
x_227 = lean_unsigned_to_nat(1u);
x_228 = lean_nat_add(x_227, x_204);
x_229 = lean_nat_add(x_228, x_192);
lean_dec(x_192);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_219, 0);
lean_inc(x_250);
x_241 = x_250;
goto block_249;
}
else
{
lean_object* x_251; 
x_251 = lean_unsigned_to_nat(0u);
x_241 = x_251;
goto block_249;
}
block_240:
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_nat_add(x_231, x_232);
lean_dec(x_232);
lean_dec(x_231);
if (x_226 == 0)
{
lean_ctor_set(x_225, 4, x_196);
lean_ctor_set(x_225, 3, x_220);
lean_ctor_set(x_225, 2, x_194);
lean_ctor_set(x_225, 1, x_193);
lean_ctor_set(x_225, 0, x_233);
x_234 = x_225;
goto block_238;
}
else
{
lean_object* x_239; 
x_239 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_239, 0, x_233);
lean_ctor_set(x_239, 1, x_193);
lean_ctor_set(x_239, 2, x_194);
lean_ctor_set(x_239, 3, x_220);
lean_ctor_set(x_239, 4, x_196);
x_234 = x_239;
goto block_238;
}
block_238:
{
lean_object* x_235; 
if (x_215 == 0)
{
lean_ctor_set(x_214, 4, x_234);
lean_ctor_set(x_214, 3, x_230);
lean_ctor_set(x_214, 2, x_218);
lean_ctor_set(x_214, 1, x_217);
lean_ctor_set(x_214, 0, x_229);
x_235 = x_214;
goto block_236;
}
else
{
lean_object* x_237; 
x_237 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_237, 0, x_229);
lean_ctor_set(x_237, 1, x_217);
lean_ctor_set(x_237, 2, x_218);
lean_ctor_set(x_237, 3, x_230);
lean_ctor_set(x_237, 4, x_234);
x_235 = x_237;
goto block_236;
}
block_236:
{
return x_235;
}
}
}
block_249:
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_nat_add(x_228, x_241);
lean_dec(x_241);
lean_dec(x_228);
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_219);
lean_ctor_set(x_198, 3, x_201);
lean_ctor_set(x_198, 2, x_203);
lean_ctor_set(x_198, 1, x_202);
lean_ctor_set(x_198, 0, x_242);
x_243 = x_198;
goto block_247;
}
else
{
lean_object* x_248; 
x_248 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_248, 0, x_242);
lean_ctor_set(x_248, 1, x_202);
lean_ctor_set(x_248, 2, x_203);
lean_ctor_set(x_248, 3, x_201);
lean_ctor_set(x_248, 4, x_219);
x_243 = x_248;
goto block_247;
}
block_247:
{
lean_object* x_244; 
x_244 = lean_nat_add(x_227, x_221);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_220, 0);
lean_inc(x_245);
x_230 = x_243;
x_231 = x_244;
x_232 = x_245;
goto block_240;
}
else
{
lean_object* x_246; 
x_246 = lean_unsigned_to_nat(0u);
x_230 = x_243;
x_231 = x_244;
x_232 = x_246;
goto block_240;
}
}
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_259 = lean_unsigned_to_nat(1u);
x_260 = lean_nat_add(x_259, x_204);
x_261 = lean_nat_add(x_260, x_192);
lean_dec(x_192);
x_262 = lean_nat_add(x_260, x_216);
lean_dec(x_260);
if (x_215 == 0)
{
lean_ctor_set(x_214, 4, x_195);
lean_ctor_set(x_214, 3, x_201);
lean_ctor_set(x_214, 2, x_203);
lean_ctor_set(x_214, 1, x_202);
lean_ctor_set(x_214, 0, x_262);
x_263 = x_214;
goto block_267;
}
else
{
lean_object* x_268; 
x_268 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_268, 0, x_262);
lean_ctor_set(x_268, 1, x_202);
lean_ctor_set(x_268, 2, x_203);
lean_ctor_set(x_268, 3, x_201);
lean_ctor_set(x_268, 4, x_195);
x_263 = x_268;
goto block_267;
}
block_267:
{
lean_object* x_264; 
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_196);
lean_ctor_set(x_198, 3, x_263);
lean_ctor_set(x_198, 2, x_194);
lean_ctor_set(x_198, 1, x_193);
lean_ctor_set(x_198, 0, x_261);
x_264 = x_198;
goto block_265;
}
else
{
lean_object* x_266; 
x_266 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_266, 0, x_261);
lean_ctor_set(x_266, 1, x_193);
lean_ctor_set(x_266, 2, x_194);
lean_ctor_set(x_266, 3, x_263);
lean_ctor_set(x_266, 4, x_196);
x_264 = x_266;
goto block_265;
}
block_265:
{
return x_264;
}
}
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec_ref(x_195);
lean_del_object(x_214);
lean_dec(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_del_object(x_198);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
x_269 = lean_box(1);
x_270 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3);
x_271 = l_panic___redArg(x_269, x_270);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_del_object(x_214);
lean_dec(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_del_object(x_198);
lean_dec(x_196);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
x_272 = lean_box(1);
x_273 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4);
x_274 = l_panic___redArg(x_272, x_273);
return x_274;
}
}
}
}
else
{
lean_inc(x_196);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_282; uint8_t x_283; uint8_t x_319; 
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
x_319 = !lean_is_exclusive(x_7);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_320 = lean_ctor_get(x_7, 4);
lean_dec(x_320);
x_321 = lean_ctor_get(x_7, 3);
lean_dec(x_321);
x_322 = lean_ctor_get(x_7, 2);
lean_dec(x_322);
x_323 = lean_ctor_get(x_7, 1);
lean_dec(x_323);
x_324 = lean_ctor_get(x_7, 0);
lean_dec(x_324);
x_282 = x_7;
x_283 = x_319;
goto block_318;
}
else
{
lean_dec(x_7);
x_282 = lean_box(0);
x_283 = x_319;
goto block_318;
}
block_318:
{
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_284 = lean_ctor_get(x_200, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_200, 1);
lean_inc(x_285);
lean_dec_ref(x_200);
x_286 = lean_ctor_get(x_195, 0);
x_287 = lean_unsigned_to_nat(1u);
x_288 = lean_nat_add(x_287, x_192);
lean_dec(x_192);
x_289 = lean_nat_add(x_287, x_286);
if (x_283 == 0)
{
lean_ctor_set(x_282, 4, x_195);
lean_ctor_set(x_282, 3, x_201);
lean_ctor_set(x_282, 2, x_285);
lean_ctor_set(x_282, 1, x_284);
lean_ctor_set(x_282, 0, x_289);
x_290 = x_282;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_295, 0, x_289);
lean_ctor_set(x_295, 1, x_284);
lean_ctor_set(x_295, 2, x_285);
lean_ctor_set(x_295, 3, x_201);
lean_ctor_set(x_295, 4, x_195);
x_290 = x_295;
goto block_294;
}
block_294:
{
lean_object* x_291; 
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_196);
lean_ctor_set(x_198, 3, x_290);
lean_ctor_set(x_198, 2, x_194);
lean_ctor_set(x_198, 1, x_193);
lean_ctor_set(x_198, 0, x_288);
x_291 = x_198;
goto block_292;
}
else
{
lean_object* x_293; 
x_293 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_293, 0, x_288);
lean_ctor_set(x_293, 1, x_193);
lean_ctor_set(x_293, 2, x_194);
lean_ctor_set(x_293, 3, x_290);
lean_ctor_set(x_293, 4, x_196);
x_291 = x_293;
goto block_292;
}
block_292:
{
return x_291;
}
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; uint8_t x_314; 
lean_dec(x_192);
x_296 = lean_ctor_get(x_200, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_200, 1);
lean_inc(x_297);
lean_dec_ref(x_200);
x_298 = lean_ctor_get(x_195, 1);
x_299 = lean_ctor_get(x_195, 2);
x_314 = !lean_is_exclusive(x_195);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_195, 4);
lean_dec(x_315);
x_316 = lean_ctor_get(x_195, 3);
lean_dec(x_316);
x_317 = lean_ctor_get(x_195, 0);
lean_dec(x_317);
x_300 = x_195;
x_301 = x_314;
goto block_313;
}
else
{
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_195);
x_300 = lean_box(0);
x_301 = x_314;
goto block_313;
}
block_313:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_unsigned_to_nat(3u);
x_303 = lean_unsigned_to_nat(1u);
if (x_301 == 0)
{
lean_ctor_set(x_300, 4, x_196);
lean_ctor_set(x_300, 3, x_196);
lean_ctor_set(x_300, 2, x_297);
lean_ctor_set(x_300, 1, x_296);
lean_ctor_set(x_300, 0, x_303);
x_304 = x_300;
goto block_311;
}
else
{
lean_object* x_312; 
x_312 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_312, 0, x_303);
lean_ctor_set(x_312, 1, x_296);
lean_ctor_set(x_312, 2, x_297);
lean_ctor_set(x_312, 3, x_196);
lean_ctor_set(x_312, 4, x_196);
x_304 = x_312;
goto block_311;
}
block_311:
{
lean_object* x_305; 
if (x_283 == 0)
{
lean_ctor_set(x_282, 3, x_196);
lean_ctor_set(x_282, 0, x_303);
x_305 = x_282;
goto block_309;
}
else
{
lean_object* x_310; 
x_310 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_310, 0, x_303);
lean_ctor_set(x_310, 1, x_193);
lean_ctor_set(x_310, 2, x_194);
lean_ctor_set(x_310, 3, x_196);
lean_ctor_set(x_310, 4, x_196);
x_305 = x_310;
goto block_309;
}
block_309:
{
lean_object* x_306; 
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_305);
lean_ctor_set(x_198, 3, x_304);
lean_ctor_set(x_198, 2, x_299);
lean_ctor_set(x_198, 1, x_298);
lean_ctor_set(x_198, 0, x_302);
x_306 = x_198;
goto block_307;
}
else
{
lean_object* x_308; 
x_308 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_308, 0, x_302);
lean_ctor_set(x_308, 1, x_298);
lean_ctor_set(x_308, 2, x_299);
lean_ctor_set(x_308, 3, x_304);
lean_ctor_set(x_308, 4, x_305);
x_306 = x_308;
goto block_307;
}
block_307:
{
return x_306;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_325; uint8_t x_326; uint8_t x_338; 
lean_inc(x_194);
lean_inc(x_193);
x_338 = !lean_is_exclusive(x_7);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_339 = lean_ctor_get(x_7, 4);
lean_dec(x_339);
x_340 = lean_ctor_get(x_7, 3);
lean_dec(x_340);
x_341 = lean_ctor_get(x_7, 2);
lean_dec(x_341);
x_342 = lean_ctor_get(x_7, 1);
lean_dec(x_342);
x_343 = lean_ctor_get(x_7, 0);
lean_dec(x_343);
x_325 = x_7;
x_326 = x_338;
goto block_337;
}
else
{
lean_dec(x_7);
x_325 = lean_box(0);
x_326 = x_338;
goto block_337;
}
block_337:
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_327 = lean_ctor_get(x_200, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_200, 1);
lean_inc(x_328);
lean_dec_ref(x_200);
x_329 = lean_unsigned_to_nat(3u);
x_330 = lean_unsigned_to_nat(1u);
if (x_326 == 0)
{
lean_ctor_set(x_325, 4, x_195);
lean_ctor_set(x_325, 2, x_328);
lean_ctor_set(x_325, 1, x_327);
lean_ctor_set(x_325, 0, x_330);
x_331 = x_325;
goto block_335;
}
else
{
lean_object* x_336; 
x_336 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_336, 0, x_330);
lean_ctor_set(x_336, 1, x_327);
lean_ctor_set(x_336, 2, x_328);
lean_ctor_set(x_336, 3, x_195);
lean_ctor_set(x_336, 4, x_195);
x_331 = x_336;
goto block_335;
}
block_335:
{
lean_object* x_332; 
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_196);
lean_ctor_set(x_198, 3, x_331);
lean_ctor_set(x_198, 2, x_194);
lean_ctor_set(x_198, 1, x_193);
lean_ctor_set(x_198, 0, x_329);
x_332 = x_198;
goto block_333;
}
else
{
lean_object* x_334; 
x_334 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_334, 0, x_329);
lean_ctor_set(x_334, 1, x_193);
lean_ctor_set(x_334, 2, x_194);
lean_ctor_set(x_334, 3, x_331);
lean_ctor_set(x_334, 4, x_196);
x_332 = x_334;
goto block_333;
}
block_333:
{
return x_332;
}
}
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_344 = lean_ctor_get(x_200, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_200, 1);
lean_inc(x_345);
lean_dec_ref(x_200);
x_346 = lean_unsigned_to_nat(2u);
if (x_199 == 0)
{
lean_ctor_set(x_198, 4, x_7);
lean_ctor_set(x_198, 3, x_196);
lean_ctor_set(x_198, 2, x_345);
lean_ctor_set(x_198, 1, x_344);
lean_ctor_set(x_198, 0, x_346);
x_347 = x_198;
goto block_348;
}
else
{
lean_object* x_349; 
x_349 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_349, 0, x_346);
lean_ctor_set(x_349, 1, x_344);
lean_ctor_set(x_349, 2, x_345);
lean_ctor_set(x_349, 3, x_196);
lean_ctor_set(x_349, 4, x_7);
x_347 = x_349;
goto block_348;
}
block_348:
{
return x_347;
}
}
}
}
}
}
else
{
lean_object* x_357; uint8_t x_358; uint8_t x_521; 
lean_inc(x_196);
lean_inc(x_194);
lean_inc(x_193);
x_521 = !lean_is_exclusive(x_7);
if (x_521 == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_522 = lean_ctor_get(x_7, 4);
lean_dec(x_522);
x_523 = lean_ctor_get(x_7, 3);
lean_dec(x_523);
x_524 = lean_ctor_get(x_7, 2);
lean_dec(x_524);
x_525 = lean_ctor_get(x_7, 1);
lean_dec(x_525);
x_526 = lean_ctor_get(x_7, 0);
lean_dec(x_526);
x_357 = x_7;
x_358 = x_521;
goto block_520;
}
else
{
lean_dec(x_7);
x_357 = lean_box(0);
x_358 = x_521;
goto block_520;
}
block_520:
{
lean_object* x_359; lean_object* x_360; 
x_359 = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(x_193, x_194, x_195, x_196);
x_360 = lean_ctor_get(x_359, 2);
lean_inc(x_360);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_361 = lean_ctor_get(x_359, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_359, 1);
lean_inc(x_362);
lean_dec_ref(x_359);
x_363 = lean_ctor_get(x_360, 0);
x_364 = lean_unsigned_to_nat(3u);
x_365 = lean_nat_mul(x_364, x_363);
x_366 = lean_nat_dec_lt(x_365, x_187);
lean_dec(x_365);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_191);
x_367 = lean_unsigned_to_nat(1u);
x_368 = lean_nat_add(x_367, x_187);
x_369 = lean_nat_add(x_368, x_363);
lean_dec(x_368);
if (x_358 == 0)
{
lean_ctor_set(x_357, 4, x_360);
lean_ctor_set(x_357, 3, x_6);
lean_ctor_set(x_357, 2, x_362);
lean_ctor_set(x_357, 1, x_361);
lean_ctor_set(x_357, 0, x_369);
x_370 = x_357;
goto block_371;
}
else
{
lean_object* x_372; 
x_372 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_361);
lean_ctor_set(x_372, 2, x_362);
lean_ctor_set(x_372, 3, x_6);
lean_ctor_set(x_372, 4, x_360);
x_370 = x_372;
goto block_371;
}
block_371:
{
return x_370;
}
}
else
{
lean_object* x_373; uint8_t x_374; uint8_t x_446; 
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
x_446 = !lean_is_exclusive(x_6);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_447 = lean_ctor_get(x_6, 4);
lean_dec(x_447);
x_448 = lean_ctor_get(x_6, 3);
lean_dec(x_448);
x_449 = lean_ctor_get(x_6, 2);
lean_dec(x_449);
x_450 = lean_ctor_get(x_6, 1);
lean_dec(x_450);
x_451 = lean_ctor_get(x_6, 0);
lean_dec(x_451);
x_373 = x_6;
x_374 = x_446;
goto block_445;
}
else
{
lean_dec(x_6);
x_373 = lean_box(0);
x_374 = x_446;
goto block_445;
}
block_445:
{
if (lean_obj_tag(x_190) == 0)
{
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; 
x_375 = lean_ctor_get(x_190, 0);
x_376 = lean_ctor_get(x_191, 0);
x_377 = lean_ctor_get(x_191, 1);
x_378 = lean_ctor_get(x_191, 2);
x_379 = lean_ctor_get(x_191, 3);
x_380 = lean_ctor_get(x_191, 4);
x_381 = lean_unsigned_to_nat(2u);
x_382 = lean_nat_mul(x_381, x_375);
x_383 = lean_nat_dec_lt(x_376, x_382);
lean_dec(x_382);
if (x_383 == 0)
{
lean_object* x_384; uint8_t x_385; uint8_t x_422; 
lean_inc(x_380);
lean_inc(x_379);
lean_inc(x_378);
lean_inc(x_377);
lean_del_object(x_373);
x_422 = !lean_is_exclusive(x_191);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_423 = lean_ctor_get(x_191, 4);
lean_dec(x_423);
x_424 = lean_ctor_get(x_191, 3);
lean_dec(x_424);
x_425 = lean_ctor_get(x_191, 2);
lean_dec(x_425);
x_426 = lean_ctor_get(x_191, 1);
lean_dec(x_426);
x_427 = lean_ctor_get(x_191, 0);
lean_dec(x_427);
x_384 = x_191;
x_385 = x_422;
goto block_421;
}
else
{
lean_dec(x_191);
x_384 = lean_box(0);
x_385 = x_422;
goto block_421;
}
block_421:
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_409; lean_object* x_410; 
x_386 = lean_unsigned_to_nat(1u);
x_387 = lean_nat_add(x_386, x_187);
lean_dec(x_187);
x_388 = lean_nat_add(x_387, x_363);
lean_dec(x_387);
x_409 = lean_nat_add(x_386, x_375);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_419; 
x_419 = lean_ctor_get(x_379, 0);
lean_inc(x_419);
x_410 = x_419;
goto block_418;
}
else
{
lean_object* x_420; 
x_420 = lean_unsigned_to_nat(0u);
x_410 = x_420;
goto block_418;
}
block_408:
{
lean_object* x_392; lean_object* x_393; 
x_392 = lean_nat_add(x_389, x_391);
lean_dec(x_391);
lean_dec(x_389);
lean_inc_ref(x_360);
if (x_385 == 0)
{
lean_ctor_set(x_384, 4, x_360);
lean_ctor_set(x_384, 3, x_380);
lean_ctor_set(x_384, 2, x_362);
lean_ctor_set(x_384, 1, x_361);
lean_ctor_set(x_384, 0, x_392);
x_393 = x_384;
goto block_406;
}
else
{
lean_object* x_407; 
x_407 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_407, 0, x_392);
lean_ctor_set(x_407, 1, x_361);
lean_ctor_set(x_407, 2, x_362);
lean_ctor_set(x_407, 3, x_380);
lean_ctor_set(x_407, 4, x_360);
x_393 = x_407;
goto block_406;
}
block_406:
{
lean_object* x_394; uint8_t x_395; uint8_t x_400; 
x_400 = !lean_is_exclusive(x_360);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_401 = lean_ctor_get(x_360, 4);
lean_dec(x_401);
x_402 = lean_ctor_get(x_360, 3);
lean_dec(x_402);
x_403 = lean_ctor_get(x_360, 2);
lean_dec(x_403);
x_404 = lean_ctor_get(x_360, 1);
lean_dec(x_404);
x_405 = lean_ctor_get(x_360, 0);
lean_dec(x_405);
x_394 = x_360;
x_395 = x_400;
goto block_399;
}
else
{
lean_dec(x_360);
x_394 = lean_box(0);
x_395 = x_400;
goto block_399;
}
block_399:
{
lean_object* x_396; 
if (x_395 == 0)
{
lean_ctor_set(x_394, 4, x_393);
lean_ctor_set(x_394, 3, x_390);
lean_ctor_set(x_394, 2, x_378);
lean_ctor_set(x_394, 1, x_377);
lean_ctor_set(x_394, 0, x_388);
x_396 = x_394;
goto block_397;
}
else
{
lean_object* x_398; 
x_398 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_398, 0, x_388);
lean_ctor_set(x_398, 1, x_377);
lean_ctor_set(x_398, 2, x_378);
lean_ctor_set(x_398, 3, x_390);
lean_ctor_set(x_398, 4, x_393);
x_396 = x_398;
goto block_397;
}
block_397:
{
return x_396;
}
}
}
}
block_418:
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_nat_add(x_409, x_410);
lean_dec(x_410);
lean_dec(x_409);
if (x_358 == 0)
{
lean_ctor_set(x_357, 4, x_379);
lean_ctor_set(x_357, 3, x_190);
lean_ctor_set(x_357, 2, x_189);
lean_ctor_set(x_357, 1, x_188);
lean_ctor_set(x_357, 0, x_411);
x_412 = x_357;
goto block_416;
}
else
{
lean_object* x_417; 
x_417 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_417, 0, x_411);
lean_ctor_set(x_417, 1, x_188);
lean_ctor_set(x_417, 2, x_189);
lean_ctor_set(x_417, 3, x_190);
lean_ctor_set(x_417, 4, x_379);
x_412 = x_417;
goto block_416;
}
block_416:
{
lean_object* x_413; 
x_413 = lean_nat_add(x_386, x_363);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_414; 
x_414 = lean_ctor_get(x_380, 0);
lean_inc(x_414);
x_389 = x_413;
x_390 = x_412;
x_391 = x_414;
goto block_408;
}
else
{
lean_object* x_415; 
x_415 = lean_unsigned_to_nat(0u);
x_389 = x_413;
x_390 = x_412;
x_391 = x_415;
goto block_408;
}
}
}
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_428 = lean_unsigned_to_nat(1u);
x_429 = lean_nat_add(x_428, x_187);
lean_dec(x_187);
x_430 = lean_nat_add(x_429, x_363);
lean_dec(x_429);
x_431 = lean_nat_add(x_428, x_363);
x_432 = lean_nat_add(x_431, x_376);
lean_dec(x_431);
if (x_358 == 0)
{
lean_ctor_set(x_357, 4, x_360);
lean_ctor_set(x_357, 3, x_191);
lean_ctor_set(x_357, 2, x_362);
lean_ctor_set(x_357, 1, x_361);
lean_ctor_set(x_357, 0, x_432);
x_433 = x_357;
goto block_437;
}
else
{
lean_object* x_438; 
x_438 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_438, 0, x_432);
lean_ctor_set(x_438, 1, x_361);
lean_ctor_set(x_438, 2, x_362);
lean_ctor_set(x_438, 3, x_191);
lean_ctor_set(x_438, 4, x_360);
x_433 = x_438;
goto block_437;
}
block_437:
{
lean_object* x_434; 
if (x_374 == 0)
{
lean_ctor_set(x_373, 4, x_433);
lean_ctor_set(x_373, 0, x_430);
x_434 = x_373;
goto block_435;
}
else
{
lean_object* x_436; 
x_436 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_436, 0, x_430);
lean_ctor_set(x_436, 1, x_188);
lean_ctor_set(x_436, 2, x_189);
lean_ctor_set(x_436, 3, x_190);
lean_ctor_set(x_436, 4, x_433);
x_434 = x_436;
goto block_435;
}
block_435:
{
return x_434;
}
}
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec_ref(x_190);
lean_del_object(x_373);
lean_dec(x_362);
lean_dec_ref(x_360);
lean_dec(x_361);
lean_del_object(x_357);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
x_439 = lean_box(1);
x_440 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2);
x_441 = l_panic___redArg(x_439, x_440);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_del_object(x_373);
lean_dec(x_362);
lean_dec_ref(x_360);
lean_dec(x_361);
lean_del_object(x_357);
lean_dec(x_191);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
x_442 = lean_box(1);
x_443 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3);
x_444 = l_panic___redArg(x_442, x_443);
return x_444;
}
}
}
}
else
{
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_452; uint8_t x_453; uint8_t x_477; 
lean_inc_ref(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
x_477 = !lean_is_exclusive(x_6);
if (x_477 == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_478 = lean_ctor_get(x_6, 4);
lean_dec(x_478);
x_479 = lean_ctor_get(x_6, 3);
lean_dec(x_479);
x_480 = lean_ctor_get(x_6, 2);
lean_dec(x_480);
x_481 = lean_ctor_get(x_6, 1);
lean_dec(x_481);
x_482 = lean_ctor_get(x_6, 0);
lean_dec(x_482);
x_452 = x_6;
x_453 = x_477;
goto block_476;
}
else
{
lean_dec(x_6);
x_452 = lean_box(0);
x_453 = x_477;
goto block_476;
}
block_476:
{
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_454 = lean_ctor_get(x_359, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_359, 1);
lean_inc(x_455);
lean_dec_ref(x_359);
x_456 = lean_ctor_get(x_191, 0);
x_457 = lean_unsigned_to_nat(1u);
x_458 = lean_nat_add(x_457, x_187);
lean_dec(x_187);
x_459 = lean_nat_add(x_457, x_456);
if (x_358 == 0)
{
lean_ctor_set(x_357, 4, x_360);
lean_ctor_set(x_357, 3, x_191);
lean_ctor_set(x_357, 2, x_455);
lean_ctor_set(x_357, 1, x_454);
lean_ctor_set(x_357, 0, x_459);
x_460 = x_357;
goto block_464;
}
else
{
lean_object* x_465; 
x_465 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_465, 0, x_459);
lean_ctor_set(x_465, 1, x_454);
lean_ctor_set(x_465, 2, x_455);
lean_ctor_set(x_465, 3, x_191);
lean_ctor_set(x_465, 4, x_360);
x_460 = x_465;
goto block_464;
}
block_464:
{
lean_object* x_461; 
if (x_453 == 0)
{
lean_ctor_set(x_452, 4, x_460);
lean_ctor_set(x_452, 0, x_458);
x_461 = x_452;
goto block_462;
}
else
{
lean_object* x_463; 
x_463 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_463, 0, x_458);
lean_ctor_set(x_463, 1, x_188);
lean_ctor_set(x_463, 2, x_189);
lean_ctor_set(x_463, 3, x_190);
lean_ctor_set(x_463, 4, x_460);
x_461 = x_463;
goto block_462;
}
block_462:
{
return x_461;
}
}
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_187);
x_466 = lean_ctor_get(x_359, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_359, 1);
lean_inc(x_467);
lean_dec_ref(x_359);
x_468 = lean_unsigned_to_nat(3u);
x_469 = lean_unsigned_to_nat(1u);
if (x_358 == 0)
{
lean_ctor_set(x_357, 4, x_191);
lean_ctor_set(x_357, 3, x_191);
lean_ctor_set(x_357, 2, x_467);
lean_ctor_set(x_357, 1, x_466);
lean_ctor_set(x_357, 0, x_469);
x_470 = x_357;
goto block_474;
}
else
{
lean_object* x_475; 
x_475 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_475, 0, x_469);
lean_ctor_set(x_475, 1, x_466);
lean_ctor_set(x_475, 2, x_467);
lean_ctor_set(x_475, 3, x_191);
lean_ctor_set(x_475, 4, x_191);
x_470 = x_475;
goto block_474;
}
block_474:
{
lean_object* x_471; 
if (x_453 == 0)
{
lean_ctor_set(x_452, 4, x_470);
lean_ctor_set(x_452, 0, x_468);
x_471 = x_452;
goto block_472;
}
else
{
lean_object* x_473; 
x_473 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_473, 0, x_468);
lean_ctor_set(x_473, 1, x_188);
lean_ctor_set(x_473, 2, x_189);
lean_ctor_set(x_473, 3, x_190);
lean_ctor_set(x_473, 4, x_470);
x_471 = x_473;
goto block_472;
}
block_472:
{
return x_471;
}
}
}
}
}
else
{
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_483; uint8_t x_484; uint8_t x_508; 
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
x_508 = !lean_is_exclusive(x_6);
if (x_508 == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_509 = lean_ctor_get(x_6, 4);
lean_dec(x_509);
x_510 = lean_ctor_get(x_6, 3);
lean_dec(x_510);
x_511 = lean_ctor_get(x_6, 2);
lean_dec(x_511);
x_512 = lean_ctor_get(x_6, 1);
lean_dec(x_512);
x_513 = lean_ctor_get(x_6, 0);
lean_dec(x_513);
x_483 = x_6;
x_484 = x_508;
goto block_507;
}
else
{
lean_dec(x_6);
x_483 = lean_box(0);
x_484 = x_508;
goto block_507;
}
block_507:
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; uint8_t x_503; 
x_485 = lean_ctor_get(x_359, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_359, 1);
lean_inc(x_486);
lean_dec_ref(x_359);
x_487 = lean_ctor_get(x_191, 1);
x_488 = lean_ctor_get(x_191, 2);
x_503 = !lean_is_exclusive(x_191);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_191, 4);
lean_dec(x_504);
x_505 = lean_ctor_get(x_191, 3);
lean_dec(x_505);
x_506 = lean_ctor_get(x_191, 0);
lean_dec(x_506);
x_489 = x_191;
x_490 = x_503;
goto block_502;
}
else
{
lean_inc(x_488);
lean_inc(x_487);
lean_dec(x_191);
x_489 = lean_box(0);
x_490 = x_503;
goto block_502;
}
block_502:
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_unsigned_to_nat(3u);
x_492 = lean_unsigned_to_nat(1u);
if (x_490 == 0)
{
lean_ctor_set(x_489, 4, x_190);
lean_ctor_set(x_489, 3, x_190);
lean_ctor_set(x_489, 2, x_189);
lean_ctor_set(x_489, 1, x_188);
lean_ctor_set(x_489, 0, x_492);
x_493 = x_489;
goto block_500;
}
else
{
lean_object* x_501; 
x_501 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_501, 0, x_492);
lean_ctor_set(x_501, 1, x_188);
lean_ctor_set(x_501, 2, x_189);
lean_ctor_set(x_501, 3, x_190);
lean_ctor_set(x_501, 4, x_190);
x_493 = x_501;
goto block_500;
}
block_500:
{
lean_object* x_494; 
if (x_358 == 0)
{
lean_ctor_set(x_357, 4, x_190);
lean_ctor_set(x_357, 3, x_190);
lean_ctor_set(x_357, 2, x_486);
lean_ctor_set(x_357, 1, x_485);
lean_ctor_set(x_357, 0, x_492);
x_494 = x_357;
goto block_498;
}
else
{
lean_object* x_499; 
x_499 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_499, 0, x_492);
lean_ctor_set(x_499, 1, x_485);
lean_ctor_set(x_499, 2, x_486);
lean_ctor_set(x_499, 3, x_190);
lean_ctor_set(x_499, 4, x_190);
x_494 = x_499;
goto block_498;
}
block_498:
{
lean_object* x_495; 
if (x_484 == 0)
{
lean_ctor_set(x_483, 4, x_494);
lean_ctor_set(x_483, 3, x_493);
lean_ctor_set(x_483, 2, x_488);
lean_ctor_set(x_483, 1, x_487);
lean_ctor_set(x_483, 0, x_491);
x_495 = x_483;
goto block_496;
}
else
{
lean_object* x_497; 
x_497 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_497, 0, x_491);
lean_ctor_set(x_497, 1, x_487);
lean_ctor_set(x_497, 2, x_488);
lean_ctor_set(x_497, 3, x_493);
lean_ctor_set(x_497, 4, x_494);
x_495 = x_497;
goto block_496;
}
block_496:
{
return x_495;
}
}
}
}
}
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_514 = lean_ctor_get(x_359, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_359, 1);
lean_inc(x_515);
lean_dec_ref(x_359);
x_516 = lean_unsigned_to_nat(2u);
if (x_358 == 0)
{
lean_ctor_set(x_357, 4, x_191);
lean_ctor_set(x_357, 3, x_6);
lean_ctor_set(x_357, 2, x_515);
lean_ctor_set(x_357, 1, x_514);
lean_ctor_set(x_357, 0, x_516);
x_517 = x_357;
goto block_518;
}
else
{
lean_object* x_519; 
x_519 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_519, 0, x_516);
lean_ctor_set(x_519, 1, x_514);
lean_ctor_set(x_519, 2, x_515);
lean_ctor_set(x_519, 3, x_6);
lean_ctor_set(x_519, 4, x_191);
x_517 = x_519;
goto block_518;
}
block_518:
{
return x_517;
}
}
}
}
}
}
}
else
{
return x_6;
}
}
else
{
return x_7;
}
}
default: 
{
lean_object* x_527; 
x_527 = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(x_1, x_2, x_7);
if (lean_obj_tag(x_527) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_6, 0);
x_530 = lean_ctor_get(x_6, 1);
x_531 = lean_ctor_get(x_6, 2);
x_532 = lean_ctor_get(x_6, 3);
x_533 = lean_ctor_get(x_6, 4);
lean_inc(x_533);
x_534 = lean_unsigned_to_nat(3u);
x_535 = lean_nat_mul(x_534, x_528);
x_536 = lean_nat_dec_lt(x_535, x_529);
lean_dec(x_535);
if (x_536 == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_533);
x_537 = lean_unsigned_to_nat(1u);
x_538 = lean_nat_add(x_537, x_529);
x_539 = lean_nat_add(x_538, x_528);
lean_dec(x_528);
lean_dec(x_538);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_527);
lean_ctor_set(x_8, 0, x_539);
x_540 = x_8;
goto block_541;
}
else
{
lean_object* x_542; 
x_542 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_542, 0, x_539);
lean_ctor_set(x_542, 1, x_4);
lean_ctor_set(x_542, 2, x_5);
lean_ctor_set(x_542, 3, x_6);
lean_ctor_set(x_542, 4, x_527);
x_540 = x_542;
goto block_541;
}
block_541:
{
return x_540;
}
}
else
{
lean_object* x_543; uint8_t x_544; uint8_t x_616; 
lean_inc(x_532);
lean_inc(x_531);
lean_inc(x_530);
lean_inc(x_529);
x_616 = !lean_is_exclusive(x_6);
if (x_616 == 0)
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_617 = lean_ctor_get(x_6, 4);
lean_dec(x_617);
x_618 = lean_ctor_get(x_6, 3);
lean_dec(x_618);
x_619 = lean_ctor_get(x_6, 2);
lean_dec(x_619);
x_620 = lean_ctor_get(x_6, 1);
lean_dec(x_620);
x_621 = lean_ctor_get(x_6, 0);
lean_dec(x_621);
x_543 = x_6;
x_544 = x_616;
goto block_615;
}
else
{
lean_dec(x_6);
x_543 = lean_box(0);
x_544 = x_616;
goto block_615;
}
block_615:
{
if (lean_obj_tag(x_532) == 0)
{
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; 
x_545 = lean_ctor_get(x_532, 0);
x_546 = lean_ctor_get(x_533, 0);
x_547 = lean_ctor_get(x_533, 1);
x_548 = lean_ctor_get(x_533, 2);
x_549 = lean_ctor_get(x_533, 3);
x_550 = lean_ctor_get(x_533, 4);
x_551 = lean_unsigned_to_nat(2u);
x_552 = lean_nat_mul(x_551, x_545);
x_553 = lean_nat_dec_lt(x_546, x_552);
lean_dec(x_552);
if (x_553 == 0)
{
lean_object* x_554; uint8_t x_555; uint8_t x_583; 
lean_inc(x_550);
lean_inc(x_549);
lean_inc(x_548);
lean_inc(x_547);
x_583 = !lean_is_exclusive(x_533);
if (x_583 == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_584 = lean_ctor_get(x_533, 4);
lean_dec(x_584);
x_585 = lean_ctor_get(x_533, 3);
lean_dec(x_585);
x_586 = lean_ctor_get(x_533, 2);
lean_dec(x_586);
x_587 = lean_ctor_get(x_533, 1);
lean_dec(x_587);
x_588 = lean_ctor_get(x_533, 0);
lean_dec(x_588);
x_554 = x_533;
x_555 = x_583;
goto block_582;
}
else
{
lean_dec(x_533);
x_554 = lean_box(0);
x_555 = x_583;
goto block_582;
}
block_582:
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_570; lean_object* x_571; 
x_556 = lean_unsigned_to_nat(1u);
x_557 = lean_nat_add(x_556, x_529);
lean_dec(x_529);
x_558 = lean_nat_add(x_557, x_528);
lean_dec(x_557);
x_570 = lean_nat_add(x_556, x_545);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_580; 
x_580 = lean_ctor_get(x_549, 0);
lean_inc(x_580);
x_571 = x_580;
goto block_579;
}
else
{
lean_object* x_581; 
x_581 = lean_unsigned_to_nat(0u);
x_571 = x_581;
goto block_579;
}
block_569:
{
lean_object* x_562; lean_object* x_563; 
x_562 = lean_nat_add(x_559, x_561);
lean_dec(x_561);
lean_dec(x_559);
if (x_555 == 0)
{
lean_ctor_set(x_554, 4, x_527);
lean_ctor_set(x_554, 3, x_550);
lean_ctor_set(x_554, 2, x_5);
lean_ctor_set(x_554, 1, x_4);
lean_ctor_set(x_554, 0, x_562);
x_563 = x_554;
goto block_567;
}
else
{
lean_object* x_568; 
x_568 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_568, 0, x_562);
lean_ctor_set(x_568, 1, x_4);
lean_ctor_set(x_568, 2, x_5);
lean_ctor_set(x_568, 3, x_550);
lean_ctor_set(x_568, 4, x_527);
x_563 = x_568;
goto block_567;
}
block_567:
{
lean_object* x_564; 
if (x_544 == 0)
{
lean_ctor_set(x_543, 4, x_563);
lean_ctor_set(x_543, 3, x_560);
lean_ctor_set(x_543, 2, x_548);
lean_ctor_set(x_543, 1, x_547);
lean_ctor_set(x_543, 0, x_558);
x_564 = x_543;
goto block_565;
}
else
{
lean_object* x_566; 
x_566 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_566, 0, x_558);
lean_ctor_set(x_566, 1, x_547);
lean_ctor_set(x_566, 2, x_548);
lean_ctor_set(x_566, 3, x_560);
lean_ctor_set(x_566, 4, x_563);
x_564 = x_566;
goto block_565;
}
block_565:
{
return x_564;
}
}
}
block_579:
{
lean_object* x_572; lean_object* x_573; 
x_572 = lean_nat_add(x_570, x_571);
lean_dec(x_571);
lean_dec(x_570);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_549);
lean_ctor_set(x_8, 3, x_532);
lean_ctor_set(x_8, 2, x_531);
lean_ctor_set(x_8, 1, x_530);
lean_ctor_set(x_8, 0, x_572);
x_573 = x_8;
goto block_577;
}
else
{
lean_object* x_578; 
x_578 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_578, 0, x_572);
lean_ctor_set(x_578, 1, x_530);
lean_ctor_set(x_578, 2, x_531);
lean_ctor_set(x_578, 3, x_532);
lean_ctor_set(x_578, 4, x_549);
x_573 = x_578;
goto block_577;
}
block_577:
{
lean_object* x_574; 
x_574 = lean_nat_add(x_556, x_528);
lean_dec(x_528);
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_575; 
x_575 = lean_ctor_get(x_550, 0);
lean_inc(x_575);
x_559 = x_574;
x_560 = x_573;
x_561 = x_575;
goto block_569;
}
else
{
lean_object* x_576; 
x_576 = lean_unsigned_to_nat(0u);
x_559 = x_574;
x_560 = x_573;
x_561 = x_576;
goto block_569;
}
}
}
}
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_del_object(x_8);
x_589 = lean_unsigned_to_nat(1u);
x_590 = lean_nat_add(x_589, x_529);
lean_dec(x_529);
x_591 = lean_nat_add(x_590, x_528);
lean_dec(x_590);
x_592 = lean_nat_add(x_589, x_528);
lean_dec(x_528);
x_593 = lean_nat_add(x_592, x_546);
lean_dec(x_592);
lean_inc_ref(x_527);
if (x_544 == 0)
{
lean_ctor_set(x_543, 4, x_527);
lean_ctor_set(x_543, 3, x_533);
lean_ctor_set(x_543, 2, x_5);
lean_ctor_set(x_543, 1, x_4);
lean_ctor_set(x_543, 0, x_593);
x_594 = x_543;
goto block_607;
}
else
{
lean_object* x_608; 
x_608 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_608, 0, x_593);
lean_ctor_set(x_608, 1, x_4);
lean_ctor_set(x_608, 2, x_5);
lean_ctor_set(x_608, 3, x_533);
lean_ctor_set(x_608, 4, x_527);
x_594 = x_608;
goto block_607;
}
block_607:
{
lean_object* x_595; uint8_t x_596; uint8_t x_601; 
x_601 = !lean_is_exclusive(x_527);
if (x_601 == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_602 = lean_ctor_get(x_527, 4);
lean_dec(x_602);
x_603 = lean_ctor_get(x_527, 3);
lean_dec(x_603);
x_604 = lean_ctor_get(x_527, 2);
lean_dec(x_604);
x_605 = lean_ctor_get(x_527, 1);
lean_dec(x_605);
x_606 = lean_ctor_get(x_527, 0);
lean_dec(x_606);
x_595 = x_527;
x_596 = x_601;
goto block_600;
}
else
{
lean_dec(x_527);
x_595 = lean_box(0);
x_596 = x_601;
goto block_600;
}
block_600:
{
lean_object* x_597; 
if (x_596 == 0)
{
lean_ctor_set(x_595, 4, x_594);
lean_ctor_set(x_595, 3, x_532);
lean_ctor_set(x_595, 2, x_531);
lean_ctor_set(x_595, 1, x_530);
lean_ctor_set(x_595, 0, x_591);
x_597 = x_595;
goto block_598;
}
else
{
lean_object* x_599; 
x_599 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_599, 0, x_591);
lean_ctor_set(x_599, 1, x_530);
lean_ctor_set(x_599, 2, x_531);
lean_ctor_set(x_599, 3, x_532);
lean_ctor_set(x_599, 4, x_594);
x_597 = x_599;
goto block_598;
}
block_598:
{
return x_597;
}
}
}
}
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec_ref(x_532);
lean_del_object(x_543);
lean_dec(x_531);
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_528);
lean_dec_ref(x_527);
lean_del_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_609 = lean_box(1);
x_610 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2);
x_611 = l_panic___redArg(x_609, x_610);
return x_611;
}
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; 
lean_del_object(x_543);
lean_dec(x_533);
lean_dec(x_531);
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_528);
lean_dec_ref(x_527);
lean_del_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_612 = lean_box(1);
x_613 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3);
x_614 = l_panic___redArg(x_612, x_613);
return x_614;
}
}
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_622 = lean_ctor_get(x_527, 0);
lean_inc(x_622);
x_623 = lean_unsigned_to_nat(1u);
x_624 = lean_nat_add(x_623, x_622);
lean_dec(x_622);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_527);
lean_ctor_set(x_8, 0, x_624);
x_625 = x_8;
goto block_626;
}
else
{
lean_object* x_627; 
x_627 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_627, 0, x_624);
lean_ctor_set(x_627, 1, x_4);
lean_ctor_set(x_627, 2, x_5);
lean_ctor_set(x_627, 3, x_6);
lean_ctor_set(x_627, 4, x_527);
x_625 = x_627;
goto block_626;
}
block_626:
{
return x_625;
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_628; 
x_628 = lean_ctor_get(x_6, 3);
if (lean_obj_tag(x_628) == 0)
{
lean_object* x_629; 
lean_inc_ref(x_628);
x_629 = lean_ctor_get(x_6, 4);
lean_inc(x_629);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; uint8_t x_634; uint8_t x_646; 
x_630 = lean_ctor_get(x_6, 0);
x_631 = lean_ctor_get(x_6, 1);
x_632 = lean_ctor_get(x_6, 2);
x_646 = !lean_is_exclusive(x_6);
if (x_646 == 0)
{
lean_object* x_647; lean_object* x_648; 
x_647 = lean_ctor_get(x_6, 4);
lean_dec(x_647);
x_648 = lean_ctor_get(x_6, 3);
lean_dec(x_648);
x_633 = x_6;
x_634 = x_646;
goto block_645;
}
else
{
lean_inc(x_632);
lean_inc(x_631);
lean_inc(x_630);
lean_dec(x_6);
x_633 = lean_box(0);
x_634 = x_646;
goto block_645;
}
block_645:
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_635 = lean_ctor_get(x_629, 0);
x_636 = lean_unsigned_to_nat(1u);
x_637 = lean_nat_add(x_636, x_630);
lean_dec(x_630);
x_638 = lean_nat_add(x_636, x_635);
if (x_634 == 0)
{
lean_ctor_set(x_633, 4, x_527);
lean_ctor_set(x_633, 3, x_629);
lean_ctor_set(x_633, 2, x_5);
lean_ctor_set(x_633, 1, x_4);
lean_ctor_set(x_633, 0, x_638);
x_639 = x_633;
goto block_643;
}
else
{
lean_object* x_644; 
x_644 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_644, 0, x_638);
lean_ctor_set(x_644, 1, x_4);
lean_ctor_set(x_644, 2, x_5);
lean_ctor_set(x_644, 3, x_629);
lean_ctor_set(x_644, 4, x_527);
x_639 = x_644;
goto block_643;
}
block_643:
{
lean_object* x_640; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_639);
lean_ctor_set(x_8, 3, x_628);
lean_ctor_set(x_8, 2, x_632);
lean_ctor_set(x_8, 1, x_631);
lean_ctor_set(x_8, 0, x_637);
x_640 = x_8;
goto block_641;
}
else
{
lean_object* x_642; 
x_642 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_642, 0, x_637);
lean_ctor_set(x_642, 1, x_631);
lean_ctor_set(x_642, 2, x_632);
lean_ctor_set(x_642, 3, x_628);
lean_ctor_set(x_642, 4, x_639);
x_640 = x_642;
goto block_641;
}
block_641:
{
return x_640;
}
}
}
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; uint8_t x_652; uint8_t x_662; 
x_649 = lean_ctor_get(x_6, 1);
x_650 = lean_ctor_get(x_6, 2);
x_662 = !lean_is_exclusive(x_6);
if (x_662 == 0)
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_663 = lean_ctor_get(x_6, 4);
lean_dec(x_663);
x_664 = lean_ctor_get(x_6, 3);
lean_dec(x_664);
x_665 = lean_ctor_get(x_6, 0);
lean_dec(x_665);
x_651 = x_6;
x_652 = x_662;
goto block_661;
}
else
{
lean_inc(x_650);
lean_inc(x_649);
lean_dec(x_6);
x_651 = lean_box(0);
x_652 = x_662;
goto block_661;
}
block_661:
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_653 = lean_unsigned_to_nat(3u);
x_654 = lean_unsigned_to_nat(1u);
if (x_652 == 0)
{
lean_ctor_set(x_651, 3, x_629);
lean_ctor_set(x_651, 2, x_5);
lean_ctor_set(x_651, 1, x_4);
lean_ctor_set(x_651, 0, x_654);
x_655 = x_651;
goto block_659;
}
else
{
lean_object* x_660; 
x_660 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_660, 0, x_654);
lean_ctor_set(x_660, 1, x_4);
lean_ctor_set(x_660, 2, x_5);
lean_ctor_set(x_660, 3, x_629);
lean_ctor_set(x_660, 4, x_629);
x_655 = x_660;
goto block_659;
}
block_659:
{
lean_object* x_656; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_655);
lean_ctor_set(x_8, 3, x_628);
lean_ctor_set(x_8, 2, x_650);
lean_ctor_set(x_8, 1, x_649);
lean_ctor_set(x_8, 0, x_653);
x_656 = x_8;
goto block_657;
}
else
{
lean_object* x_658; 
x_658 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_658, 0, x_653);
lean_ctor_set(x_658, 1, x_649);
lean_ctor_set(x_658, 2, x_650);
lean_ctor_set(x_658, 3, x_628);
lean_ctor_set(x_658, 4, x_655);
x_656 = x_658;
goto block_657;
}
block_657:
{
return x_656;
}
}
}
}
}
else
{
lean_object* x_666; 
x_666 = lean_ctor_get(x_6, 4);
lean_inc(x_666);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; uint8_t x_670; uint8_t x_692; 
lean_inc(x_628);
x_667 = lean_ctor_get(x_6, 1);
x_668 = lean_ctor_get(x_6, 2);
x_692 = !lean_is_exclusive(x_6);
if (x_692 == 0)
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_693 = lean_ctor_get(x_6, 4);
lean_dec(x_693);
x_694 = lean_ctor_get(x_6, 3);
lean_dec(x_694);
x_695 = lean_ctor_get(x_6, 0);
lean_dec(x_695);
x_669 = x_6;
x_670 = x_692;
goto block_691;
}
else
{
lean_inc(x_668);
lean_inc(x_667);
lean_dec(x_6);
x_669 = lean_box(0);
x_670 = x_692;
goto block_691;
}
block_691:
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; uint8_t x_674; uint8_t x_687; 
x_671 = lean_ctor_get(x_666, 1);
x_672 = lean_ctor_get(x_666, 2);
x_687 = !lean_is_exclusive(x_666);
if (x_687 == 0)
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_688 = lean_ctor_get(x_666, 4);
lean_dec(x_688);
x_689 = lean_ctor_get(x_666, 3);
lean_dec(x_689);
x_690 = lean_ctor_get(x_666, 0);
lean_dec(x_690);
x_673 = x_666;
x_674 = x_687;
goto block_686;
}
else
{
lean_inc(x_672);
lean_inc(x_671);
lean_dec(x_666);
x_673 = lean_box(0);
x_674 = x_687;
goto block_686;
}
block_686:
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_675 = lean_unsigned_to_nat(3u);
x_676 = lean_unsigned_to_nat(1u);
if (x_674 == 0)
{
lean_ctor_set(x_673, 4, x_628);
lean_ctor_set(x_673, 3, x_628);
lean_ctor_set(x_673, 2, x_668);
lean_ctor_set(x_673, 1, x_667);
lean_ctor_set(x_673, 0, x_676);
x_677 = x_673;
goto block_684;
}
else
{
lean_object* x_685; 
x_685 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_685, 0, x_676);
lean_ctor_set(x_685, 1, x_667);
lean_ctor_set(x_685, 2, x_668);
lean_ctor_set(x_685, 3, x_628);
lean_ctor_set(x_685, 4, x_628);
x_677 = x_685;
goto block_684;
}
block_684:
{
lean_object* x_678; 
if (x_670 == 0)
{
lean_ctor_set(x_669, 4, x_628);
lean_ctor_set(x_669, 2, x_5);
lean_ctor_set(x_669, 1, x_4);
lean_ctor_set(x_669, 0, x_676);
x_678 = x_669;
goto block_682;
}
else
{
lean_object* x_683; 
x_683 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_683, 0, x_676);
lean_ctor_set(x_683, 1, x_4);
lean_ctor_set(x_683, 2, x_5);
lean_ctor_set(x_683, 3, x_628);
lean_ctor_set(x_683, 4, x_628);
x_678 = x_683;
goto block_682;
}
block_682:
{
lean_object* x_679; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_678);
lean_ctor_set(x_8, 3, x_677);
lean_ctor_set(x_8, 2, x_672);
lean_ctor_set(x_8, 1, x_671);
lean_ctor_set(x_8, 0, x_675);
x_679 = x_8;
goto block_680;
}
else
{
lean_object* x_681; 
x_681 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_681, 0, x_675);
lean_ctor_set(x_681, 1, x_671);
lean_ctor_set(x_681, 2, x_672);
lean_ctor_set(x_681, 3, x_677);
lean_ctor_set(x_681, 4, x_678);
x_679 = x_681;
goto block_680;
}
block_680:
{
return x_679;
}
}
}
}
}
}
else
{
lean_object* x_696; lean_object* x_697; 
x_696 = lean_unsigned_to_nat(2u);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_666);
lean_ctor_set(x_8, 0, x_696);
x_697 = x_8;
goto block_698;
}
else
{
lean_object* x_699; 
x_699 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_699, 0, x_696);
lean_ctor_set(x_699, 1, x_4);
lean_ctor_set(x_699, 2, x_5);
lean_ctor_set(x_699, 3, x_6);
lean_ctor_set(x_699, 4, x_666);
x_697 = x_699;
goto block_698;
}
block_698:
{
return x_697;
}
}
}
}
else
{
lean_object* x_700; lean_object* x_701; 
x_700 = lean_unsigned_to_nat(1u);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 0, x_700);
x_701 = x_8;
goto block_702;
}
else
{
lean_object* x_703; 
x_703 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_703, 0, x_700);
lean_ctor_set(x_703, 1, x_4);
lean_ctor_set(x_703, 2, x_5);
lean_ctor_set(x_703, 3, x_6);
lean_ctor_set(x_703, 4, x_6);
x_701 = x_703;
goto block_702;
}
block_702:
{
return x_701;
}
}
}
}
}
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseMany___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_erase___redArg(x_1, x_2, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseMany___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_2, lean_box(0), x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseMany(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = lean_apply_4(x_5, lean_box(0), x_7, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseMany_x21___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(x_1, x_2, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseMany_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_eraseMany_x21___redArg___lam__0), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_2, lean_box(0), x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseMany_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_eraseMany_x21___redArg___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_apply_4(x_5, lean_box(0), x_7, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseManyEntries___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Std_DTreeMap_Internal_Impl_erase___redArg(x_1, x_4, x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseManyEntries___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_eraseManyEntries___redArg___lam__0), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_2, lean_box(0), x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseManyEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_eraseManyEntries___redArg___lam__0), 3, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = lean_apply_4(x_5, lean_box(0), x_7, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseManyEntries_x21___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(x_1, x_4, x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseManyEntries_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_eraseManyEntries_x21___redArg___lam__0), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_2, lean_box(0), x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_eraseManyEntries_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_eraseManyEntries_x21___redArg___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_apply_4(x_5, lean_box(0), x_7, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMany___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_4, x_5, x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMany___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_2, lean_box(0), x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMany(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = lean_apply_4(x_5, lean_box(0), x_7, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertManyIfNew___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
lean_inc(x_3);
lean_inc(x_4);
lean_inc_ref(x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_4, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_4, x_5, x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertManyIfNew___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_insertManyIfNew___redArg___lam__0), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_2, lean_box(0), x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertManyIfNew(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_insertManyIfNew___redArg___lam__0), 3, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = lean_apply_4(x_5, lean_box(0), x_7, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_2, x_3, x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_16; 
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_union___redArg___lam__0), 4, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_union___redArg___lam__1), 4, 1);
lean_closure_set(x_5, 0, x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_16 = x_20;
goto block_19;
}
else
{
lean_object* x_21; 
x_21 = lean_unsigned_to_nat(0u);
x_16 = x_21;
goto block_19;
}
block_15:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
x_9 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_10 = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(x_9, x_5, x_2, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_5);
x_12 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_13 = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(x_12, x_4, x_3, x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
return x_14;
}
}
block_19:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_6 = x_16;
x_7 = x_17;
goto block_15;
}
else
{
lean_object* x_18; 
x_18 = lean_unsigned_to_nat(0u);
x_6 = x_16;
x_7 = x_18;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_union___redArg(x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMany_x21___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_1, x_4, x_5, x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMany_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_insertMany_x21___redArg___lam__0), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_2, lean_box(0), x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertMany_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_insertMany_x21___redArg___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_apply_4(x_5, lean_box(0), x_7, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertManyIfNew_x21___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
lean_inc(x_3);
lean_inc(x_4);
lean_inc_ref(x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_4, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_1, x_4, x_5, x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertManyIfNew_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_insertManyIfNew_x21___redArg___lam__0), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_2, lean_box(0), x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertManyIfNew_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_insertManyIfNew_x21___redArg___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_apply_4(x_5, lean_box(0), x_7, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_1, x_2, x_3, x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_16; 
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_union_x21___redArg___lam__0), 4, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_union_x21___redArg___lam__1), 4, 1);
lean_closure_set(x_5, 0, x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_16 = x_20;
goto block_19;
}
else
{
lean_object* x_21; 
x_21 = lean_unsigned_to_nat(0u);
x_16 = x_21;
goto block_19;
}
block_15:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
x_9 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_10 = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(x_9, x_5, x_2, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_5);
x_12 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_13 = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(x_12, x_4, x_3, x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
return x_14;
}
}
block_19:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_6 = x_16;
x_7 = x_17;
goto block_15;
}
else
{
lean_object* x_18; 
x_18 = lean_unsigned_to_nat(0u);
x_6 = x_16;
x_7 = x_18;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_union_x21___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertMany___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_4, x_5, x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertMany___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_2, lean_box(0), x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertMany(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = lean_apply_4(x_5, lean_box(0), x_7, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertMany_x21___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_1, x_4, x_5, x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertMany_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_insertMany_x21___redArg___lam__0), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_2, lean_box(0), x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertMany_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_insertMany_x21___redArg___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_apply_4(x_5, lean_box(0), x_7, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_4 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_2, x_5, x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_2, lean_box(0), x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_apply_4(x_4, lean_box(0), x_6, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit_x21___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_4 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_1, x_2, x_5, x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit_x21___redArg___lam__0), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_2, lean_box(0), x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_insertManyIfNewUnit_x21___redArg___lam__0), 3, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = lean_apply_4(x_4, lean_box(0), x_6, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_SizedBalancedTree_toBalancedTree___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_SizedBalancedTree_toBalancedTree___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_SizedBalancedTree_toBalancedTree___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_SizedBalancedTree_toBalancedTree(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_SizedBalancedTree_toBalancedTree___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_SizedBalancedTree_toBalancedTree(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ofArray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_5, x_6, x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ofArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_ofArray___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_5 = lean_box(1);
x_6 = lean_array_size(x_2);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_4, x_2, x_3, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ofArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_ofArray___redArg___lam__0), 4, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_7 = lean_box(1);
x_8 = lean_array_size(x_4);
x_9 = 0;
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_6, x_4, x_5, x_8, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ofList___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_ofArray___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_5 = lean_box(1);
x_6 = l_List_forIn_x27_loop___redArg(x_4, x_3, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ofList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_ofArray___redArg___lam__0), 4, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_7 = lean_box(1);
x_8 = l_List_forIn_x27_loop___redArg(x_6, x_5, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_inc(x_2);
lean_inc(x_3);
lean_inc_ref(x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_3, x_4, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_inc(x_4);
lean_inc(x_5);
lean_inc_ref(x_3);
x_9 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_3, x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_3, x_5, x_6, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_inc(x_2);
lean_inc(x_3);
lean_inc_ref(x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_1, x_3, x_4, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_7 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_inc(x_4);
lean_inc(x_5);
lean_inc_ref(x_3);
x_8 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_3, x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_3, x_5, x_6, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_ofArray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_5, x_6, x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_ofArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_ofArray___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_5 = lean_box(1);
x_6 = lean_array_size(x_2);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_4, x_2, x_3, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_ofArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_ofArray___redArg___lam__0), 4, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_7 = lean_box(1);
x_8 = lean_array_size(x_4);
x_9 = 0;
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_6, x_4, x_5, x_8, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_ofList___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_ofArray___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_5 = lean_box(1);
x_6 = l_List_forIn_x27_loop___redArg(x_4, x_3, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_ofList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_ofArray___redArg___lam__0), 4, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_7 = lean_box(1);
x_8 = l_List_forIn_x27_loop___redArg(x_6, x_5, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_unitOfArray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_2, x_6, x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_unitOfArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_unitOfArray___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_5 = lean_box(1);
x_6 = lean_array_size(x_2);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_4, x_2, x_3, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_unitOfArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_unitOfArray___redArg___lam__0), 4, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_6 = lean_box(1);
x_7 = lean_array_size(x_3);
x_8 = 0;
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_5, x_3, x_4, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_unitOfList___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_unitOfArray___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_5 = lean_box(1);
x_6 = l_List_forIn_x27_loop___redArg(x_4, x_3, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_unitOfList(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_unitOfArray___redArg___lam__0), 4, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_6 = lean_box(1);
x_7 = l_List_forIn_x27_loop___redArg(x_5, x_4, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_3);
x_7 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_inc_ref(x_1);
x_8 = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(x_1, x_5);
x_9 = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(x_1, x_6);
x_10 = l_Std_DTreeMap_Internal_Impl_link2___redArg(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
lean_inc_ref(x_1);
x_12 = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(x_1, x_5);
x_13 = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(x_1, x_6);
x_14 = l_Std_DTreeMap_Internal_Impl_link___redArg(x_3, x_11, x_12, x_13);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec_ref(x_1);
x_15 = lean_box(1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_filterMap(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_3);
x_7 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_inc_ref(x_1);
x_8 = l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(x_1, x_5);
x_9 = l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(x_1, x_6);
x_10 = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
lean_inc_ref(x_1);
x_12 = l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(x_1, x_5);
x_13 = l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(x_1, x_6);
x_14 = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(x_3, x_11, x_12, x_13);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec_ref(x_1);
x_15 = lean_box(1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_filterMap_x21(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_17; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
x_8 = x_2;
x_9 = x_17;
goto block_16;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
lean_inc(x_4);
x_10 = lean_apply_2(x_1, x_4, x_5);
lean_inc(x_1);
x_11 = l_Std_DTreeMap_Internal_Impl_map___redArg(x_1, x_6);
x_12 = l_Std_DTreeMap_Internal_Impl_map___redArg(x_1, x_7);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_12);
lean_ctor_set(x_8, 3, x_11);
lean_ctor_set(x_8, 2, x_10);
x_13 = x_8;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_4);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_box(1);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_map___redArg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_map(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mapM___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mapM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mapM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_mapM___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mapM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 4);
lean_inc(x_10);
lean_dec_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_11 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_mapM___redArg___lam__0), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_10);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_mapM___redArg___lam__1), 4, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_9);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_mapM___redArg___lam__2), 4, 3);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_7);
lean_closure_set(x_13, 2, x_8);
x_14 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_mapM___redArg___lam__3), 5, 2);
lean_closure_set(x_14, 0, x_6);
lean_closure_set(x_14, 1, x_7);
x_15 = lean_apply_2(x_4, lean_box(0), x_14);
lean_inc(x_5);
x_16 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_15, x_13);
lean_inc(x_5);
x_17 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_16, x_12);
x_18 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_17, x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec_ref(x_1);
x_20 = lean_box(1);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mapM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_mapM___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mapM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_mapM___redArg(x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_apply_2(x_1, x_3, x_4);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_inc_ref(x_1);
x_9 = l_Std_DTreeMap_Internal_Impl_filter___redArg(x_1, x_5);
x_10 = l_Std_DTreeMap_Internal_Impl_filter___redArg(x_1, x_6);
x_11 = l_Std_DTreeMap_Internal_Impl_link2___redArg(x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc_ref(x_1);
x_12 = l_Std_DTreeMap_Internal_Impl_filter___redArg(x_1, x_5);
x_13 = l_Std_DTreeMap_Internal_Impl_filter___redArg(x_1, x_6);
x_14 = l_Std_DTreeMap_Internal_Impl_link___redArg(x_3, x_4, x_12, x_13);
return x_14;
}
}
else
{
lean_dec_ref(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_filter___redArg(x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_filter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_apply_2(x_1, x_3, x_4);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_inc_ref(x_1);
x_9 = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(x_1, x_5);
x_10 = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(x_1, x_6);
x_11 = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc_ref(x_1);
x_12 = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(x_1, x_5);
x_13 = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(x_1, x_6);
x_14 = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(x_3, x_4, x_12, x_13);
return x_14;
}
}
else
{
lean_dec_ref(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_filter_x21(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmallerFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_7, x_8, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmallerFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_3);
x_7 = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(x_3, x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec_ref(x_3);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_3, x_9, x_10, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc_ref(x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(x_1, x_2, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_8, x_9, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_interSmaller___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_interSmaller___redArg___lam__0___boxed), 5, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_box(1);
x_6 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_interSmaller___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_inter___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_3, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_inter___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_11; 
lean_inc(x_3);
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_inter___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_11 = x_15;
goto block_14;
}
else
{
lean_object* x_16; 
x_16 = lean_unsigned_to_nat(0u);
x_11 = x_16;
goto block_14;
}
block_10:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_4);
x_8 = l_Std_DTreeMap_Internal_Impl_interSmaller___redArg(x_1, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_9 = l_Std_DTreeMap_Internal_Impl_filter___redArg(x_4, x_2);
return x_9;
}
}
block_14:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_5 = x_11;
x_6 = x_12;
goto block_10;
}
else
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(0u);
x_5 = x_11;
x_6 = x_13;
goto block_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_inter___redArg(x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_11; 
lean_inc(x_3);
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_inter___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_11 = x_15;
goto block_14;
}
else
{
lean_object* x_16; 
x_16 = lean_unsigned_to_nat(0u);
x_11 = x_16;
goto block_14;
}
block_10:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_4);
x_8 = l_Std_DTreeMap_Internal_Impl_interSmaller___redArg(x_1, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_9 = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(x_4, x_2);
return x_9;
}
}
block_14:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_5 = x_11;
x_6 = x_12;
goto block_10;
}
else
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(0u);
x_5 = x_11;
x_6 = x_13;
goto block_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_inter_x21___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_beq___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_6);
x_9 = lean_apply_1(x_1, x_6);
x_10 = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(x_2, x_3, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_7);
x_12 = l_Option_instBEq_beq___redArg(x_9, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_5);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_5);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_beq___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DTreeMap_Internal_Impl_beq___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_beq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_11; lean_object* x_12; lean_object* x_21; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_21 = x_25;
goto block_24;
}
else
{
lean_object* x_26; 
x_26 = lean_unsigned_to_nat(0u);
x_21 = x_26;
goto block_24;
}
block_10:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
return x_9;
}
}
block_20:
{
uint8_t x_13; 
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_15 = lean_box(0);
x_16 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_beq___redArg___closed__0));
x_17 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_beq___redArg___lam__0___boxed), 8, 5);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_15);
lean_closure_set(x_17, 4, x_16);
x_18 = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(x_14, x_17, x_16, x_3);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_5 = x_19;
goto block_10;
}
}
block_24:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
x_11 = x_21;
x_12 = x_22;
goto block_20;
}
else
{
lean_object* x_23; 
x_23 = lean_unsigned_to_nat(0u);
x_11 = x_21;
x_12 = x_23;
goto block_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_beq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_beq___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_beq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_beq___redArg(x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_beq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Std_DTreeMap_Internal_Impl_beq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_diff___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_1, x_3, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_diff___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___redArg(x_1, x_2, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_diff___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; 
lean_inc(x_3);
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_diff___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_diff___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_14 = x_18;
goto block_17;
}
else
{
lean_object* x_19; 
x_19 = lean_unsigned_to_nat(0u);
x_14 = x_19;
goto block_17;
}
block_13:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
x_9 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_10 = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(x_9, x_5, x_2, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_5);
lean_dec(x_3);
x_12 = l_Std_DTreeMap_Internal_Impl_filter___redArg(x_4, x_2);
return x_12;
}
}
block_17:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_6 = x_14;
x_7 = x_15;
goto block_13;
}
else
{
lean_object* x_16; 
x_16 = lean_unsigned_to_nat(0u);
x_6 = x_14;
x_7 = x_16;
goto block_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_diff___redArg(x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(x_1, x_2, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_diff_x21___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; 
lean_inc(x_3);
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_diff___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_diff_x21___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_14 = x_18;
goto block_17;
}
else
{
lean_object* x_19; 
x_19 = lean_unsigned_to_nat(0u);
x_14 = x_19;
goto block_17;
}
block_13:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
x_9 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_10 = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(x_9, x_5, x_2, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_5);
lean_dec(x_3);
x_12 = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(x_4, x_2);
return x_12;
}
}
block_17:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_6 = x_14;
x_7 = x_15;
goto block_13;
}
else
{
lean_object* x_16; 
x_16 = lean_unsigned_to_nat(0u);
x_6 = x_14;
x_7 = x_16;
goto block_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_diff_x21___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_alter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_336; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_336 = !lean_is_exclusive(x_4);
if (x_336 == 0)
{
x_10 = x_4;
x_11 = x_336;
goto block_335;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = x_336;
goto block_335;
}
block_335:
{
lean_object* x_12; uint8_t x_13; 
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_6);
x_13 = lean_unbox(x_12);
switch (x_13) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_del_object(x_10);
lean_dec(x_5);
x_14 = l_Std_DTreeMap_Internal_Impl_alter___redArg(x_1, x_2, x_3, x_8);
x_15 = l_Std_DTreeMap_Internal_Impl_balance___redArg(x_6, x_7, x_14, x_9);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_7);
x_17 = lean_apply_1(x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_del_object(x_10);
lean_dec(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_8) == 0)
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
x_22 = lean_ctor_get(x_8, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
x_25 = lean_ctor_get(x_9, 2);
x_26 = lean_ctor_get(x_9, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_9, 4);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_dec_lt(x_18, x_23);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; uint8_t x_165; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_165 = !lean_is_exclusive(x_8);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_8, 4);
lean_dec(x_166);
x_167 = lean_ctor_get(x_8, 3);
lean_dec(x_167);
x_168 = lean_ctor_get(x_8, 2);
lean_dec(x_168);
x_169 = lean_ctor_get(x_8, 1);
lean_dec(x_169);
x_170 = lean_ctor_get(x_8, 0);
lean_dec(x_170);
x_30 = x_8;
x_31 = x_165;
goto block_164;
}
else
{
lean_dec(x_8);
x_30 = lean_box(0);
x_31 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_19, x_20, x_21, x_22);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_unsigned_to_nat(3u);
x_38 = lean_nat_mul(x_37, x_36);
x_39 = lean_nat_dec_lt(x_38, x_23);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_26);
x_40 = lean_nat_add(x_28, x_36);
x_41 = lean_nat_add(x_40, x_23);
lean_dec(x_40);
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_9);
lean_ctor_set(x_30, 3, x_33);
lean_ctor_set(x_30, 2, x_35);
lean_ctor_set(x_30, 1, x_34);
lean_ctor_set(x_30, 0, x_41);
x_42 = x_30;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 3, x_33);
lean_ctor_set(x_44, 4, x_9);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
else
{
lean_object* x_45; uint8_t x_46; uint8_t x_99; 
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_99 = !lean_is_exclusive(x_9);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_9, 4);
lean_dec(x_100);
x_101 = lean_ctor_get(x_9, 3);
lean_dec(x_101);
x_102 = lean_ctor_get(x_9, 2);
lean_dec(x_102);
x_103 = lean_ctor_get(x_9, 1);
lean_dec(x_103);
x_104 = lean_ctor_get(x_9, 0);
lean_dec(x_104);
x_45 = x_9;
x_46 = x_99;
goto block_98;
}
else
{
lean_dec(x_9);
x_45 = lean_box(0);
x_46 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_47 = lean_ctor_get(x_26, 0);
x_48 = lean_ctor_get(x_26, 1);
x_49 = lean_ctor_get(x_26, 2);
x_50 = lean_ctor_get(x_26, 3);
x_51 = lean_ctor_get(x_26, 4);
x_52 = lean_ctor_get(x_27, 0);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_mul(x_53, x_52);
x_55 = lean_nat_dec_lt(x_47, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; uint8_t x_83; 
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_83 = !lean_is_exclusive(x_26);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_26, 4);
lean_dec(x_84);
x_85 = lean_ctor_get(x_26, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_26, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_26, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_26, 0);
lean_dec(x_88);
x_56 = x_26;
x_57 = x_83;
goto block_82;
}
else
{
lean_dec(x_26);
x_56 = lean_box(0);
x_57 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_71; 
x_58 = lean_nat_add(x_28, x_36);
x_59 = lean_nat_add(x_58, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_50, 0);
lean_inc(x_80);
x_71 = x_80;
goto block_79;
}
else
{
lean_object* x_81; 
x_81 = lean_unsigned_to_nat(0u);
x_71 = x_81;
goto block_79;
}
block_70:
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_nat_add(x_60, x_62);
lean_dec(x_62);
lean_dec(x_60);
if (x_57 == 0)
{
lean_ctor_set(x_56, 4, x_27);
lean_ctor_set(x_56, 3, x_51);
lean_ctor_set(x_56, 2, x_25);
lean_ctor_set(x_56, 1, x_24);
lean_ctor_set(x_56, 0, x_63);
x_64 = x_56;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_24);
lean_ctor_set(x_69, 2, x_25);
lean_ctor_set(x_69, 3, x_51);
lean_ctor_set(x_69, 4, x_27);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_46 == 0)
{
lean_ctor_set(x_45, 4, x_64);
lean_ctor_set(x_45, 3, x_61);
lean_ctor_set(x_45, 2, x_49);
lean_ctor_set(x_45, 1, x_48);
lean_ctor_set(x_45, 0, x_59);
x_65 = x_45;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_48);
lean_ctor_set(x_67, 2, x_49);
lean_ctor_set(x_67, 3, x_61);
lean_ctor_set(x_67, 4, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
block_79:
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_nat_add(x_58, x_71);
lean_dec(x_71);
lean_dec(x_58);
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_50);
lean_ctor_set(x_30, 3, x_33);
lean_ctor_set(x_30, 2, x_35);
lean_ctor_set(x_30, 1, x_34);
lean_ctor_set(x_30, 0, x_72);
x_73 = x_30;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_34);
lean_ctor_set(x_78, 2, x_35);
lean_ctor_set(x_78, 3, x_33);
lean_ctor_set(x_78, 4, x_50);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
x_74 = lean_nat_add(x_28, x_52);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_51, 0);
lean_inc(x_75);
x_60 = x_74;
x_61 = x_73;
x_62 = x_75;
goto block_70;
}
else
{
lean_object* x_76; 
x_76 = lean_unsigned_to_nat(0u);
x_60 = x_74;
x_61 = x_73;
x_62 = x_76;
goto block_70;
}
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_nat_add(x_28, x_36);
x_90 = lean_nat_add(x_89, x_23);
lean_dec(x_23);
x_91 = lean_nat_add(x_89, x_47);
lean_dec(x_89);
if (x_46 == 0)
{
lean_ctor_set(x_45, 4, x_26);
lean_ctor_set(x_45, 3, x_33);
lean_ctor_set(x_45, 2, x_35);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_45, 0, x_91);
x_92 = x_45;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set(x_97, 1, x_34);
lean_ctor_set(x_97, 2, x_35);
lean_ctor_set(x_97, 3, x_33);
lean_ctor_set(x_97, 4, x_26);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_27);
lean_ctor_set(x_30, 3, x_92);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 0, x_90);
x_93 = x_30;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_24);
lean_ctor_set(x_95, 2, x_25);
lean_ctor_set(x_95, 3, x_92);
lean_ctor_set(x_95, 4, x_27);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
}
}
else
{
lean_object* x_105; uint8_t x_106; uint8_t x_158; 
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_158 = !lean_is_exclusive(x_9);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = lean_ctor_get(x_9, 4);
lean_dec(x_159);
x_160 = lean_ctor_get(x_9, 3);
lean_dec(x_160);
x_161 = lean_ctor_get(x_9, 2);
lean_dec(x_161);
x_162 = lean_ctor_get(x_9, 1);
lean_dec(x_162);
x_163 = lean_ctor_get(x_9, 0);
lean_dec(x_163);
x_105 = x_9;
x_106 = x_158;
goto block_157;
}
else
{
lean_dec(x_9);
x_105 = lean_box(0);
x_106 = x_158;
goto block_157;
}
block_157:
{
if (lean_obj_tag(x_26) == 0)
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_32, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_32, 1);
lean_inc(x_108);
lean_dec_ref(x_32);
x_109 = lean_ctor_get(x_26, 0);
x_110 = lean_nat_add(x_28, x_23);
lean_dec(x_23);
x_111 = lean_nat_add(x_28, x_109);
if (x_106 == 0)
{
lean_ctor_set(x_105, 4, x_26);
lean_ctor_set(x_105, 3, x_33);
lean_ctor_set(x_105, 2, x_108);
lean_ctor_set(x_105, 1, x_107);
lean_ctor_set(x_105, 0, x_111);
x_112 = x_105;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_111);
lean_ctor_set(x_117, 1, x_107);
lean_ctor_set(x_117, 2, x_108);
lean_ctor_set(x_117, 3, x_33);
lean_ctor_set(x_117, 4, x_26);
x_112 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_113; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_27);
lean_ctor_set(x_30, 3, x_112);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 0, x_110);
x_113 = x_30;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_24);
lean_ctor_set(x_115, 2, x_25);
lean_ctor_set(x_115, 3, x_112);
lean_ctor_set(x_115, 4, x_27);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_135; 
lean_dec(x_23);
x_118 = lean_ctor_get(x_32, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_32, 1);
lean_inc(x_119);
lean_dec_ref(x_32);
x_120 = lean_ctor_get(x_26, 1);
x_121 = lean_ctor_get(x_26, 2);
x_135 = !lean_is_exclusive(x_26);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_26, 4);
lean_dec(x_136);
x_137 = lean_ctor_get(x_26, 3);
lean_dec(x_137);
x_138 = lean_ctor_get(x_26, 0);
lean_dec(x_138);
x_122 = x_26;
x_123 = x_135;
goto block_134;
}
else
{
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_26);
x_122 = lean_box(0);
x_123 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_unsigned_to_nat(3u);
if (x_123 == 0)
{
lean_ctor_set(x_122, 4, x_27);
lean_ctor_set(x_122, 3, x_27);
lean_ctor_set(x_122, 2, x_119);
lean_ctor_set(x_122, 1, x_118);
lean_ctor_set(x_122, 0, x_28);
x_125 = x_122;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_133, 0, x_28);
lean_ctor_set(x_133, 1, x_118);
lean_ctor_set(x_133, 2, x_119);
lean_ctor_set(x_133, 3, x_27);
lean_ctor_set(x_133, 4, x_27);
x_125 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_126; 
if (x_106 == 0)
{
lean_ctor_set(x_105, 3, x_27);
lean_ctor_set(x_105, 0, x_28);
x_126 = x_105;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_131, 0, x_28);
lean_ctor_set(x_131, 1, x_24);
lean_ctor_set(x_131, 2, x_25);
lean_ctor_set(x_131, 3, x_27);
lean_ctor_set(x_131, 4, x_27);
x_126 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_127; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_126);
lean_ctor_set(x_30, 3, x_125);
lean_ctor_set(x_30, 2, x_121);
lean_ctor_set(x_30, 1, x_120);
lean_ctor_set(x_30, 0, x_124);
x_127 = x_30;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set(x_129, 1, x_120);
lean_ctor_set(x_129, 2, x_121);
lean_ctor_set(x_129, 3, x_125);
lean_ctor_set(x_129, 4, x_126);
x_127 = x_129;
goto block_128;
}
block_128:
{
return x_127;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_23);
x_139 = lean_ctor_get(x_32, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_32, 1);
lean_inc(x_140);
lean_dec_ref(x_32);
x_141 = lean_unsigned_to_nat(3u);
if (x_106 == 0)
{
lean_ctor_set(x_105, 4, x_26);
lean_ctor_set(x_105, 2, x_140);
lean_ctor_set(x_105, 1, x_139);
lean_ctor_set(x_105, 0, x_28);
x_142 = x_105;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_28);
lean_ctor_set(x_147, 1, x_139);
lean_ctor_set(x_147, 2, x_140);
lean_ctor_set(x_147, 3, x_26);
lean_ctor_set(x_147, 4, x_26);
x_142 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_143; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_27);
lean_ctor_set(x_30, 3, x_142);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 0, x_141);
x_143 = x_30;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_145, 0, x_141);
lean_ctor_set(x_145, 1, x_24);
lean_ctor_set(x_145, 2, x_25);
lean_ctor_set(x_145, 3, x_142);
lean_ctor_set(x_145, 4, x_27);
x_143 = x_145;
goto block_144;
}
block_144:
{
return x_143;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_32, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_32, 1);
lean_inc(x_149);
lean_dec_ref(x_32);
if (x_106 == 0)
{
lean_ctor_set(x_105, 3, x_27);
x_150 = x_105;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_156, 0, x_23);
lean_ctor_set(x_156, 1, x_24);
lean_ctor_set(x_156, 2, x_25);
lean_ctor_set(x_156, 3, x_27);
lean_ctor_set(x_156, 4, x_27);
x_150 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_unsigned_to_nat(2u);
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_150);
lean_ctor_set(x_30, 3, x_27);
lean_ctor_set(x_30, 2, x_149);
lean_ctor_set(x_30, 1, x_148);
lean_ctor_set(x_30, 0, x_151);
x_152 = x_30;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_148);
lean_ctor_set(x_154, 2, x_149);
lean_ctor_set(x_154, 3, x_27);
lean_ctor_set(x_154, 4, x_150);
x_152 = x_154;
goto block_153;
}
block_153:
{
return x_152;
}
}
}
}
}
}
}
}
else
{
lean_object* x_171; uint8_t x_172; uint8_t x_323; 
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
x_323 = !lean_is_exclusive(x_9);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_324 = lean_ctor_get(x_9, 4);
lean_dec(x_324);
x_325 = lean_ctor_get(x_9, 3);
lean_dec(x_325);
x_326 = lean_ctor_get(x_9, 2);
lean_dec(x_326);
x_327 = lean_ctor_get(x_9, 1);
lean_dec(x_327);
x_328 = lean_ctor_get(x_9, 0);
lean_dec(x_328);
x_171 = x_9;
x_172 = x_323;
goto block_322;
}
else
{
lean_dec(x_9);
x_171 = lean_box(0);
x_172 = x_323;
goto block_322;
}
block_322:
{
lean_object* x_173; lean_object* x_174; 
x_173 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_24, x_25, x_26, x_27);
x_174 = lean_ctor_get(x_173, 2);
lean_inc(x_174);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec_ref(x_173);
x_177 = lean_ctor_get(x_174, 0);
x_178 = lean_unsigned_to_nat(3u);
x_179 = lean_nat_mul(x_178, x_177);
x_180 = lean_nat_dec_lt(x_179, x_18);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_22);
x_181 = lean_nat_add(x_28, x_18);
x_182 = lean_nat_add(x_181, x_177);
lean_dec(x_181);
if (x_172 == 0)
{
lean_ctor_set(x_171, 4, x_174);
lean_ctor_set(x_171, 3, x_8);
lean_ctor_set(x_171, 2, x_176);
lean_ctor_set(x_171, 1, x_175);
lean_ctor_set(x_171, 0, x_182);
x_183 = x_171;
goto block_184;
}
else
{
lean_object* x_185; 
x_185 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_175);
lean_ctor_set(x_185, 2, x_176);
lean_ctor_set(x_185, 3, x_8);
lean_ctor_set(x_185, 4, x_174);
x_183 = x_185;
goto block_184;
}
block_184:
{
return x_183;
}
}
else
{
lean_object* x_186; uint8_t x_187; uint8_t x_251; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_251 = !lean_is_exclusive(x_8);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_8, 4);
lean_dec(x_252);
x_253 = lean_ctor_get(x_8, 3);
lean_dec(x_253);
x_254 = lean_ctor_get(x_8, 2);
lean_dec(x_254);
x_255 = lean_ctor_get(x_8, 1);
lean_dec(x_255);
x_256 = lean_ctor_get(x_8, 0);
lean_dec(x_256);
x_186 = x_8;
x_187 = x_251;
goto block_250;
}
else
{
lean_dec(x_8);
x_186 = lean_box(0);
x_187 = x_251;
goto block_250;
}
block_250:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_188 = lean_ctor_get(x_21, 0);
x_189 = lean_ctor_get(x_22, 0);
x_190 = lean_ctor_get(x_22, 1);
x_191 = lean_ctor_get(x_22, 2);
x_192 = lean_ctor_get(x_22, 3);
x_193 = lean_ctor_get(x_22, 4);
x_194 = lean_unsigned_to_nat(2u);
x_195 = lean_nat_mul(x_194, x_188);
x_196 = lean_nat_dec_lt(x_189, x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; uint8_t x_198; uint8_t x_234; 
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_del_object(x_186);
x_234 = !lean_is_exclusive(x_22);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_235 = lean_ctor_get(x_22, 4);
lean_dec(x_235);
x_236 = lean_ctor_get(x_22, 3);
lean_dec(x_236);
x_237 = lean_ctor_get(x_22, 2);
lean_dec(x_237);
x_238 = lean_ctor_get(x_22, 1);
lean_dec(x_238);
x_239 = lean_ctor_get(x_22, 0);
lean_dec(x_239);
x_197 = x_22;
x_198 = x_234;
goto block_233;
}
else
{
lean_dec(x_22);
x_197 = lean_box(0);
x_198 = x_234;
goto block_233;
}
block_233:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_221; lean_object* x_222; 
x_199 = lean_nat_add(x_28, x_18);
lean_dec(x_18);
x_200 = lean_nat_add(x_199, x_177);
lean_dec(x_199);
x_221 = lean_nat_add(x_28, x_188);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_192, 0);
lean_inc(x_231);
x_222 = x_231;
goto block_230;
}
else
{
lean_object* x_232; 
x_232 = lean_unsigned_to_nat(0u);
x_222 = x_232;
goto block_230;
}
block_220:
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_nat_add(x_201, x_203);
lean_dec(x_203);
lean_dec(x_201);
lean_inc_ref(x_174);
if (x_198 == 0)
{
lean_ctor_set(x_197, 4, x_174);
lean_ctor_set(x_197, 3, x_193);
lean_ctor_set(x_197, 2, x_176);
lean_ctor_set(x_197, 1, x_175);
lean_ctor_set(x_197, 0, x_204);
x_205 = x_197;
goto block_218;
}
else
{
lean_object* x_219; 
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_204);
lean_ctor_set(x_219, 1, x_175);
lean_ctor_set(x_219, 2, x_176);
lean_ctor_set(x_219, 3, x_193);
lean_ctor_set(x_219, 4, x_174);
x_205 = x_219;
goto block_218;
}
block_218:
{
lean_object* x_206; uint8_t x_207; uint8_t x_212; 
x_212 = !lean_is_exclusive(x_174);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_213 = lean_ctor_get(x_174, 4);
lean_dec(x_213);
x_214 = lean_ctor_get(x_174, 3);
lean_dec(x_214);
x_215 = lean_ctor_get(x_174, 2);
lean_dec(x_215);
x_216 = lean_ctor_get(x_174, 1);
lean_dec(x_216);
x_217 = lean_ctor_get(x_174, 0);
lean_dec(x_217);
x_206 = x_174;
x_207 = x_212;
goto block_211;
}
else
{
lean_dec(x_174);
x_206 = lean_box(0);
x_207 = x_212;
goto block_211;
}
block_211:
{
lean_object* x_208; 
if (x_207 == 0)
{
lean_ctor_set(x_206, 4, x_205);
lean_ctor_set(x_206, 3, x_202);
lean_ctor_set(x_206, 2, x_191);
lean_ctor_set(x_206, 1, x_190);
lean_ctor_set(x_206, 0, x_200);
x_208 = x_206;
goto block_209;
}
else
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_210, 0, x_200);
lean_ctor_set(x_210, 1, x_190);
lean_ctor_set(x_210, 2, x_191);
lean_ctor_set(x_210, 3, x_202);
lean_ctor_set(x_210, 4, x_205);
x_208 = x_210;
goto block_209;
}
block_209:
{
return x_208;
}
}
}
}
block_230:
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_nat_add(x_221, x_222);
lean_dec(x_222);
lean_dec(x_221);
if (x_172 == 0)
{
lean_ctor_set(x_171, 4, x_192);
lean_ctor_set(x_171, 3, x_21);
lean_ctor_set(x_171, 2, x_20);
lean_ctor_set(x_171, 1, x_19);
lean_ctor_set(x_171, 0, x_223);
x_224 = x_171;
goto block_228;
}
else
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_229, 0, x_223);
lean_ctor_set(x_229, 1, x_19);
lean_ctor_set(x_229, 2, x_20);
lean_ctor_set(x_229, 3, x_21);
lean_ctor_set(x_229, 4, x_192);
x_224 = x_229;
goto block_228;
}
block_228:
{
lean_object* x_225; 
x_225 = lean_nat_add(x_28, x_177);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_193, 0);
lean_inc(x_226);
x_201 = x_225;
x_202 = x_224;
x_203 = x_226;
goto block_220;
}
else
{
lean_object* x_227; 
x_227 = lean_unsigned_to_nat(0u);
x_201 = x_225;
x_202 = x_224;
x_203 = x_227;
goto block_220;
}
}
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_240 = lean_nat_add(x_28, x_18);
lean_dec(x_18);
x_241 = lean_nat_add(x_240, x_177);
lean_dec(x_240);
x_242 = lean_nat_add(x_28, x_177);
x_243 = lean_nat_add(x_242, x_189);
lean_dec(x_242);
if (x_172 == 0)
{
lean_ctor_set(x_171, 4, x_174);
lean_ctor_set(x_171, 3, x_22);
lean_ctor_set(x_171, 2, x_176);
lean_ctor_set(x_171, 1, x_175);
lean_ctor_set(x_171, 0, x_243);
x_244 = x_171;
goto block_248;
}
else
{
lean_object* x_249; 
x_249 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_249, 0, x_243);
lean_ctor_set(x_249, 1, x_175);
lean_ctor_set(x_249, 2, x_176);
lean_ctor_set(x_249, 3, x_22);
lean_ctor_set(x_249, 4, x_174);
x_244 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_245; 
if (x_187 == 0)
{
lean_ctor_set(x_186, 4, x_244);
lean_ctor_set(x_186, 0, x_241);
x_245 = x_186;
goto block_246;
}
else
{
lean_object* x_247; 
x_247 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_247, 0, x_241);
lean_ctor_set(x_247, 1, x_19);
lean_ctor_set(x_247, 2, x_20);
lean_ctor_set(x_247, 3, x_21);
lean_ctor_set(x_247, 4, x_244);
x_245 = x_247;
goto block_246;
}
block_246:
{
return x_245;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_257; uint8_t x_258; uint8_t x_280; 
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_280 = !lean_is_exclusive(x_8);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_281 = lean_ctor_get(x_8, 4);
lean_dec(x_281);
x_282 = lean_ctor_get(x_8, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_8, 2);
lean_dec(x_283);
x_284 = lean_ctor_get(x_8, 1);
lean_dec(x_284);
x_285 = lean_ctor_get(x_8, 0);
lean_dec(x_285);
x_257 = x_8;
x_258 = x_280;
goto block_279;
}
else
{
lean_dec(x_8);
x_257 = lean_box(0);
x_258 = x_280;
goto block_279;
}
block_279:
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_259 = lean_ctor_get(x_173, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_173, 1);
lean_inc(x_260);
lean_dec_ref(x_173);
x_261 = lean_ctor_get(x_22, 0);
x_262 = lean_nat_add(x_28, x_18);
lean_dec(x_18);
x_263 = lean_nat_add(x_28, x_261);
if (x_172 == 0)
{
lean_ctor_set(x_171, 4, x_174);
lean_ctor_set(x_171, 3, x_22);
lean_ctor_set(x_171, 2, x_260);
lean_ctor_set(x_171, 1, x_259);
lean_ctor_set(x_171, 0, x_263);
x_264 = x_171;
goto block_268;
}
else
{
lean_object* x_269; 
x_269 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_269, 0, x_263);
lean_ctor_set(x_269, 1, x_259);
lean_ctor_set(x_269, 2, x_260);
lean_ctor_set(x_269, 3, x_22);
lean_ctor_set(x_269, 4, x_174);
x_264 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_265; 
if (x_258 == 0)
{
lean_ctor_set(x_257, 4, x_264);
lean_ctor_set(x_257, 0, x_262);
x_265 = x_257;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_267, 0, x_262);
lean_ctor_set(x_267, 1, x_19);
lean_ctor_set(x_267, 2, x_20);
lean_ctor_set(x_267, 3, x_21);
lean_ctor_set(x_267, 4, x_264);
x_265 = x_267;
goto block_266;
}
block_266:
{
return x_265;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_18);
x_270 = lean_ctor_get(x_173, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_173, 1);
lean_inc(x_271);
lean_dec_ref(x_173);
x_272 = lean_unsigned_to_nat(3u);
if (x_172 == 0)
{
lean_ctor_set(x_171, 4, x_22);
lean_ctor_set(x_171, 3, x_22);
lean_ctor_set(x_171, 2, x_271);
lean_ctor_set(x_171, 1, x_270);
lean_ctor_set(x_171, 0, x_28);
x_273 = x_171;
goto block_277;
}
else
{
lean_object* x_278; 
x_278 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_278, 0, x_28);
lean_ctor_set(x_278, 1, x_270);
lean_ctor_set(x_278, 2, x_271);
lean_ctor_set(x_278, 3, x_22);
lean_ctor_set(x_278, 4, x_22);
x_273 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_274; 
if (x_258 == 0)
{
lean_ctor_set(x_257, 4, x_273);
lean_ctor_set(x_257, 0, x_272);
x_274 = x_257;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_276, 0, x_272);
lean_ctor_set(x_276, 1, x_19);
lean_ctor_set(x_276, 2, x_20);
lean_ctor_set(x_276, 3, x_21);
lean_ctor_set(x_276, 4, x_273);
x_274 = x_276;
goto block_275;
}
block_275:
{
return x_274;
}
}
}
}
}
else
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_286; uint8_t x_287; uint8_t x_310; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_310 = !lean_is_exclusive(x_8);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_311 = lean_ctor_get(x_8, 4);
lean_dec(x_311);
x_312 = lean_ctor_get(x_8, 3);
lean_dec(x_312);
x_313 = lean_ctor_get(x_8, 2);
lean_dec(x_313);
x_314 = lean_ctor_get(x_8, 1);
lean_dec(x_314);
x_315 = lean_ctor_get(x_8, 0);
lean_dec(x_315);
x_286 = x_8;
x_287 = x_310;
goto block_309;
}
else
{
lean_dec(x_8);
x_286 = lean_box(0);
x_287 = x_310;
goto block_309;
}
block_309:
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; uint8_t x_305; 
x_288 = lean_ctor_get(x_173, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_173, 1);
lean_inc(x_289);
lean_dec_ref(x_173);
x_290 = lean_ctor_get(x_22, 1);
x_291 = lean_ctor_get(x_22, 2);
x_305 = !lean_is_exclusive(x_22);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_22, 4);
lean_dec(x_306);
x_307 = lean_ctor_get(x_22, 3);
lean_dec(x_307);
x_308 = lean_ctor_get(x_22, 0);
lean_dec(x_308);
x_292 = x_22;
x_293 = x_305;
goto block_304;
}
else
{
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_22);
x_292 = lean_box(0);
x_293 = x_305;
goto block_304;
}
block_304:
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_unsigned_to_nat(3u);
if (x_293 == 0)
{
lean_ctor_set(x_292, 4, x_21);
lean_ctor_set(x_292, 3, x_21);
lean_ctor_set(x_292, 2, x_20);
lean_ctor_set(x_292, 1, x_19);
lean_ctor_set(x_292, 0, x_28);
x_295 = x_292;
goto block_302;
}
else
{
lean_object* x_303; 
x_303 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_303, 0, x_28);
lean_ctor_set(x_303, 1, x_19);
lean_ctor_set(x_303, 2, x_20);
lean_ctor_set(x_303, 3, x_21);
lean_ctor_set(x_303, 4, x_21);
x_295 = x_303;
goto block_302;
}
block_302:
{
lean_object* x_296; 
if (x_172 == 0)
{
lean_ctor_set(x_171, 4, x_21);
lean_ctor_set(x_171, 3, x_21);
lean_ctor_set(x_171, 2, x_289);
lean_ctor_set(x_171, 1, x_288);
lean_ctor_set(x_171, 0, x_28);
x_296 = x_171;
goto block_300;
}
else
{
lean_object* x_301; 
x_301 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_301, 0, x_28);
lean_ctor_set(x_301, 1, x_288);
lean_ctor_set(x_301, 2, x_289);
lean_ctor_set(x_301, 3, x_21);
lean_ctor_set(x_301, 4, x_21);
x_296 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_297; 
if (x_287 == 0)
{
lean_ctor_set(x_286, 4, x_296);
lean_ctor_set(x_286, 3, x_295);
lean_ctor_set(x_286, 2, x_291);
lean_ctor_set(x_286, 1, x_290);
lean_ctor_set(x_286, 0, x_294);
x_297 = x_286;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_299, 0, x_294);
lean_ctor_set(x_299, 1, x_290);
lean_ctor_set(x_299, 2, x_291);
lean_ctor_set(x_299, 3, x_295);
lean_ctor_set(x_299, 4, x_296);
x_297 = x_299;
goto block_298;
}
block_298:
{
return x_297;
}
}
}
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_316 = lean_ctor_get(x_173, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_173, 1);
lean_inc(x_317);
lean_dec_ref(x_173);
x_318 = lean_unsigned_to_nat(2u);
if (x_172 == 0)
{
lean_ctor_set(x_171, 4, x_22);
lean_ctor_set(x_171, 3, x_8);
lean_ctor_set(x_171, 2, x_317);
lean_ctor_set(x_171, 1, x_316);
lean_ctor_set(x_171, 0, x_318);
x_319 = x_171;
goto block_320;
}
else
{
lean_object* x_321; 
x_321 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_316);
lean_ctor_set(x_321, 2, x_317);
lean_ctor_set(x_321, 3, x_8);
lean_ctor_set(x_321, 4, x_22);
x_319 = x_321;
goto block_320;
}
block_320:
{
return x_319;
}
}
}
}
}
}
}
else
{
return x_8;
}
}
else
{
return x_9;
}
}
else
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_17, 0);
lean_inc(x_329);
lean_dec_ref(x_17);
if (x_11 == 0)
{
lean_ctor_set(x_10, 2, x_329);
lean_ctor_set(x_10, 1, x_2);
x_330 = x_10;
goto block_331;
}
else
{
lean_object* x_332; 
x_332 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_332, 0, x_5);
lean_ctor_set(x_332, 1, x_2);
lean_ctor_set(x_332, 2, x_329);
lean_ctor_set(x_332, 3, x_8);
lean_ctor_set(x_332, 4, x_9);
x_330 = x_332;
goto block_331;
}
block_331:
{
return x_330;
}
}
}
default: 
{
lean_object* x_333; lean_object* x_334; 
lean_del_object(x_10);
lean_dec(x_5);
x_333 = l_Std_DTreeMap_Internal_Impl_alter___redArg(x_1, x_2, x_3, x_9);
x_334 = l_Std_DTreeMap_Internal_Impl_balance___redArg(x_6, x_7, x_8, x_333);
return x_334;
}
}
}
}
else
{
lean_object* x_337; lean_object* x_338; 
lean_dec_ref(x_1);
x_337 = lean_box(0);
x_338 = lean_apply_1(x_3, x_337);
if (lean_obj_tag(x_338) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
x_340 = lean_unsigned_to_nat(1u);
x_341 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_2);
lean_ctor_set(x_341, 2, x_339);
lean_ctor_set(x_341, 3, x_4);
lean_ctor_set(x_341, 4, x_4);
return x_341;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_alter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DTreeMap_Internal_Impl_alter___redArg(x_3, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_365; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_365 = !lean_is_exclusive(x_4);
if (x_365 == 0)
{
x_10 = x_4;
x_11 = x_365;
goto block_364;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = x_365;
goto block_364;
}
block_364:
{
lean_object* x_12; uint8_t x_13; 
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_6);
x_13 = lean_unbox(x_12);
switch (x_13) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_del_object(x_10);
lean_dec(x_5);
x_14 = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(x_1, x_2, x_3, x_8);
x_15 = l_Std_DTreeMap_Internal_Impl_balance_x21___redArg(x_6, x_7, x_14, x_9);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_7);
x_17 = lean_apply_1(x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_del_object(x_10);
lean_dec(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_8) == 0)
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
x_22 = lean_ctor_get(x_8, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
x_25 = lean_ctor_get(x_9, 2);
x_26 = lean_ctor_get(x_9, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_9, 4);
x_28 = lean_nat_dec_lt(x_18, x_23);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_182; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_182 = !lean_is_exclusive(x_8);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_ctor_get(x_8, 4);
lean_dec(x_183);
x_184 = lean_ctor_get(x_8, 3);
lean_dec(x_184);
x_185 = lean_ctor_get(x_8, 2);
lean_dec(x_185);
x_186 = lean_ctor_get(x_8, 1);
lean_dec(x_186);
x_187 = lean_ctor_get(x_8, 0);
lean_dec(x_187);
x_29 = x_8;
x_30 = x_182;
goto block_181;
}
else
{
lean_dec(x_8);
x_29 = lean_box(0);
x_30 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(x_19, x_20, x_21, x_22);
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec_ref(x_31);
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_mul(x_36, x_35);
x_38 = lean_nat_dec_lt(x_37, x_23);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_26);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_39, x_35);
x_41 = lean_nat_add(x_40, x_23);
lean_dec(x_40);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_9);
lean_ctor_set(x_29, 3, x_32);
lean_ctor_set(x_29, 2, x_34);
lean_ctor_set(x_29, 1, x_33);
lean_ctor_set(x_29, 0, x_41);
x_42 = x_29;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_33);
lean_ctor_set(x_44, 2, x_34);
lean_ctor_set(x_44, 3, x_32);
lean_ctor_set(x_44, 4, x_9);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
else
{
lean_object* x_45; uint8_t x_46; uint8_t x_107; 
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_107 = !lean_is_exclusive(x_9);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_9, 4);
lean_dec(x_108);
x_109 = lean_ctor_get(x_9, 3);
lean_dec(x_109);
x_110 = lean_ctor_get(x_9, 2);
lean_dec(x_110);
x_111 = lean_ctor_get(x_9, 1);
lean_dec(x_111);
x_112 = lean_ctor_get(x_9, 0);
lean_dec(x_112);
x_45 = x_9;
x_46 = x_107;
goto block_106;
}
else
{
lean_dec(x_9);
x_45 = lean_box(0);
x_46 = x_107;
goto block_106;
}
block_106:
{
if (lean_obj_tag(x_26) == 0)
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_47 = lean_ctor_get(x_26, 0);
x_48 = lean_ctor_get(x_26, 1);
x_49 = lean_ctor_get(x_26, 2);
x_50 = lean_ctor_get(x_26, 3);
x_51 = lean_ctor_get(x_26, 4);
x_52 = lean_ctor_get(x_27, 0);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_mul(x_53, x_52);
x_55 = lean_nat_dec_lt(x_47, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; uint8_t x_84; 
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_84 = !lean_is_exclusive(x_26);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_26, 4);
lean_dec(x_85);
x_86 = lean_ctor_get(x_26, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_26, 2);
lean_dec(x_87);
x_88 = lean_ctor_get(x_26, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_26, 0);
lean_dec(x_89);
x_56 = x_26;
x_57 = x_84;
goto block_83;
}
else
{
lean_dec(x_26);
x_56 = lean_box(0);
x_57 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_72; 
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_58, x_35);
x_60 = lean_nat_add(x_59, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_50, 0);
lean_inc(x_81);
x_72 = x_81;
goto block_80;
}
else
{
lean_object* x_82; 
x_82 = lean_unsigned_to_nat(0u);
x_72 = x_82;
goto block_80;
}
block_71:
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_nat_add(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_57 == 0)
{
lean_ctor_set(x_56, 4, x_27);
lean_ctor_set(x_56, 3, x_51);
lean_ctor_set(x_56, 2, x_25);
lean_ctor_set(x_56, 1, x_24);
lean_ctor_set(x_56, 0, x_64);
x_65 = x_56;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_24);
lean_ctor_set(x_70, 2, x_25);
lean_ctor_set(x_70, 3, x_51);
lean_ctor_set(x_70, 4, x_27);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_46 == 0)
{
lean_ctor_set(x_45, 4, x_65);
lean_ctor_set(x_45, 3, x_61);
lean_ctor_set(x_45, 2, x_49);
lean_ctor_set(x_45, 1, x_48);
lean_ctor_set(x_45, 0, x_60);
x_66 = x_45;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_48);
lean_ctor_set(x_68, 2, x_49);
lean_ctor_set(x_68, 3, x_61);
lean_ctor_set(x_68, 4, x_65);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
block_80:
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_nat_add(x_59, x_72);
lean_dec(x_72);
lean_dec(x_59);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_50);
lean_ctor_set(x_29, 3, x_32);
lean_ctor_set(x_29, 2, x_34);
lean_ctor_set(x_29, 1, x_33);
lean_ctor_set(x_29, 0, x_73);
x_74 = x_29;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_33);
lean_ctor_set(x_79, 2, x_34);
lean_ctor_set(x_79, 3, x_32);
lean_ctor_set(x_79, 4, x_50);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
x_75 = lean_nat_add(x_58, x_52);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_51, 0);
lean_inc(x_76);
x_61 = x_74;
x_62 = x_75;
x_63 = x_76;
goto block_71;
}
else
{
lean_object* x_77; 
x_77 = lean_unsigned_to_nat(0u);
x_61 = x_74;
x_62 = x_75;
x_63 = x_77;
goto block_71;
}
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_add(x_90, x_35);
x_92 = lean_nat_add(x_91, x_23);
lean_dec(x_23);
x_93 = lean_nat_add(x_91, x_47);
lean_dec(x_91);
if (x_46 == 0)
{
lean_ctor_set(x_45, 4, x_26);
lean_ctor_set(x_45, 3, x_32);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 0, x_93);
x_94 = x_45;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_93);
lean_ctor_set(x_99, 1, x_33);
lean_ctor_set(x_99, 2, x_34);
lean_ctor_set(x_99, 3, x_32);
lean_ctor_set(x_99, 4, x_26);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set(x_29, 3, x_94);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 0, x_92);
x_95 = x_29;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_24);
lean_ctor_set(x_97, 2, x_25);
lean_ctor_set(x_97, 3, x_94);
lean_ctor_set(x_97, 4, x_27);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_26);
lean_del_object(x_45);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_33);
lean_del_object(x_29);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_100 = lean_box(1);
x_101 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3);
x_102 = l_panic___redArg(x_100, x_101);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_del_object(x_45);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_33);
lean_del_object(x_29);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_103 = lean_box(1);
x_104 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4);
x_105 = l_panic___redArg(x_103, x_104);
return x_105;
}
}
}
}
else
{
lean_inc(x_27);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_113; uint8_t x_114; uint8_t x_150; 
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_150 = !lean_is_exclusive(x_9);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_9, 4);
lean_dec(x_151);
x_152 = lean_ctor_get(x_9, 3);
lean_dec(x_152);
x_153 = lean_ctor_get(x_9, 2);
lean_dec(x_153);
x_154 = lean_ctor_get(x_9, 1);
lean_dec(x_154);
x_155 = lean_ctor_get(x_9, 0);
lean_dec(x_155);
x_113 = x_9;
x_114 = x_150;
goto block_149;
}
else
{
lean_dec(x_9);
x_113 = lean_box(0);
x_114 = x_150;
goto block_149;
}
block_149:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_31, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_31, 1);
lean_inc(x_116);
lean_dec_ref(x_31);
x_117 = lean_ctor_get(x_26, 0);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_118, x_23);
lean_dec(x_23);
x_120 = lean_nat_add(x_118, x_117);
if (x_114 == 0)
{
lean_ctor_set(x_113, 4, x_26);
lean_ctor_set(x_113, 3, x_32);
lean_ctor_set(x_113, 2, x_116);
lean_ctor_set(x_113, 1, x_115);
lean_ctor_set(x_113, 0, x_120);
x_121 = x_113;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_120);
lean_ctor_set(x_126, 1, x_115);
lean_ctor_set(x_126, 2, x_116);
lean_ctor_set(x_126, 3, x_32);
lean_ctor_set(x_126, 4, x_26);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set(x_29, 3, x_121);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 0, x_119);
x_122 = x_29;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_119);
lean_ctor_set(x_124, 1, x_24);
lean_ctor_set(x_124, 2, x_25);
lean_ctor_set(x_124, 3, x_121);
lean_ctor_set(x_124, 4, x_27);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_145; 
lean_dec(x_23);
x_127 = lean_ctor_get(x_31, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_31, 1);
lean_inc(x_128);
lean_dec_ref(x_31);
x_129 = lean_ctor_get(x_26, 1);
x_130 = lean_ctor_get(x_26, 2);
x_145 = !lean_is_exclusive(x_26);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_26, 4);
lean_dec(x_146);
x_147 = lean_ctor_get(x_26, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_26, 0);
lean_dec(x_148);
x_131 = x_26;
x_132 = x_145;
goto block_144;
}
else
{
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_26);
x_131 = lean_box(0);
x_132 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_unsigned_to_nat(3u);
x_134 = lean_unsigned_to_nat(1u);
if (x_132 == 0)
{
lean_ctor_set(x_131, 4, x_27);
lean_ctor_set(x_131, 3, x_27);
lean_ctor_set(x_131, 2, x_128);
lean_ctor_set(x_131, 1, x_127);
lean_ctor_set(x_131, 0, x_134);
x_135 = x_131;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_143, 0, x_134);
lean_ctor_set(x_143, 1, x_127);
lean_ctor_set(x_143, 2, x_128);
lean_ctor_set(x_143, 3, x_27);
lean_ctor_set(x_143, 4, x_27);
x_135 = x_143;
goto block_142;
}
block_142:
{
lean_object* x_136; 
if (x_114 == 0)
{
lean_ctor_set(x_113, 3, x_27);
lean_ctor_set(x_113, 0, x_134);
x_136 = x_113;
goto block_140;
}
else
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_141, 0, x_134);
lean_ctor_set(x_141, 1, x_24);
lean_ctor_set(x_141, 2, x_25);
lean_ctor_set(x_141, 3, x_27);
lean_ctor_set(x_141, 4, x_27);
x_136 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_137; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_136);
lean_ctor_set(x_29, 3, x_135);
lean_ctor_set(x_29, 2, x_130);
lean_ctor_set(x_29, 1, x_129);
lean_ctor_set(x_29, 0, x_133);
x_137 = x_29;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_129);
lean_ctor_set(x_139, 2, x_130);
lean_ctor_set(x_139, 3, x_135);
lean_ctor_set(x_139, 4, x_136);
x_137 = x_139;
goto block_138;
}
block_138:
{
return x_137;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_156; uint8_t x_157; uint8_t x_169; 
lean_inc(x_25);
lean_inc(x_24);
x_169 = !lean_is_exclusive(x_9);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_9, 4);
lean_dec(x_170);
x_171 = lean_ctor_get(x_9, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_9, 2);
lean_dec(x_172);
x_173 = lean_ctor_get(x_9, 1);
lean_dec(x_173);
x_174 = lean_ctor_get(x_9, 0);
lean_dec(x_174);
x_156 = x_9;
x_157 = x_169;
goto block_168;
}
else
{
lean_dec(x_9);
x_156 = lean_box(0);
x_157 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_31, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_31, 1);
lean_inc(x_159);
lean_dec_ref(x_31);
x_160 = lean_unsigned_to_nat(3u);
x_161 = lean_unsigned_to_nat(1u);
if (x_157 == 0)
{
lean_ctor_set(x_156, 4, x_26);
lean_ctor_set(x_156, 2, x_159);
lean_ctor_set(x_156, 1, x_158);
lean_ctor_set(x_156, 0, x_161);
x_162 = x_156;
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_161);
lean_ctor_set(x_167, 1, x_158);
lean_ctor_set(x_167, 2, x_159);
lean_ctor_set(x_167, 3, x_26);
lean_ctor_set(x_167, 4, x_26);
x_162 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_163; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set(x_29, 3, x_162);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 0, x_160);
x_163 = x_29;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_24);
lean_ctor_set(x_165, 2, x_25);
lean_ctor_set(x_165, 3, x_162);
lean_ctor_set(x_165, 4, x_27);
x_163 = x_165;
goto block_164;
}
block_164:
{
return x_163;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_31, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_31, 1);
lean_inc(x_176);
lean_dec_ref(x_31);
x_177 = lean_unsigned_to_nat(2u);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_9);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 2, x_176);
lean_ctor_set(x_29, 1, x_175);
lean_ctor_set(x_29, 0, x_177);
x_178 = x_29;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_175);
lean_ctor_set(x_180, 2, x_176);
lean_ctor_set(x_180, 3, x_27);
lean_ctor_set(x_180, 4, x_9);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
}
}
else
{
lean_object* x_188; uint8_t x_189; uint8_t x_352; 
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
x_352 = !lean_is_exclusive(x_9);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_353 = lean_ctor_get(x_9, 4);
lean_dec(x_353);
x_354 = lean_ctor_get(x_9, 3);
lean_dec(x_354);
x_355 = lean_ctor_get(x_9, 2);
lean_dec(x_355);
x_356 = lean_ctor_get(x_9, 1);
lean_dec(x_356);
x_357 = lean_ctor_get(x_9, 0);
lean_dec(x_357);
x_188 = x_9;
x_189 = x_352;
goto block_351;
}
else
{
lean_dec(x_9);
x_188 = lean_box(0);
x_189 = x_352;
goto block_351;
}
block_351:
{
lean_object* x_190; lean_object* x_191; 
x_190 = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(x_24, x_25, x_26, x_27);
x_191 = lean_ctor_get(x_190, 2);
lean_inc(x_191);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_dec_ref(x_190);
x_194 = lean_ctor_get(x_191, 0);
x_195 = lean_unsigned_to_nat(3u);
x_196 = lean_nat_mul(x_195, x_194);
x_197 = lean_nat_dec_lt(x_196, x_18);
lean_dec(x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_22);
x_198 = lean_unsigned_to_nat(1u);
x_199 = lean_nat_add(x_198, x_18);
x_200 = lean_nat_add(x_199, x_194);
lean_dec(x_199);
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_191);
lean_ctor_set(x_188, 3, x_8);
lean_ctor_set(x_188, 2, x_193);
lean_ctor_set(x_188, 1, x_192);
lean_ctor_set(x_188, 0, x_200);
x_201 = x_188;
goto block_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_192);
lean_ctor_set(x_203, 2, x_193);
lean_ctor_set(x_203, 3, x_8);
lean_ctor_set(x_203, 4, x_191);
x_201 = x_203;
goto block_202;
}
block_202:
{
return x_201;
}
}
else
{
lean_object* x_204; uint8_t x_205; uint8_t x_277; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_277 = !lean_is_exclusive(x_8);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_278 = lean_ctor_get(x_8, 4);
lean_dec(x_278);
x_279 = lean_ctor_get(x_8, 3);
lean_dec(x_279);
x_280 = lean_ctor_get(x_8, 2);
lean_dec(x_280);
x_281 = lean_ctor_get(x_8, 1);
lean_dec(x_281);
x_282 = lean_ctor_get(x_8, 0);
lean_dec(x_282);
x_204 = x_8;
x_205 = x_277;
goto block_276;
}
else
{
lean_dec(x_8);
x_204 = lean_box(0);
x_205 = x_277;
goto block_276;
}
block_276:
{
if (lean_obj_tag(x_21) == 0)
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_206 = lean_ctor_get(x_21, 0);
x_207 = lean_ctor_get(x_22, 0);
x_208 = lean_ctor_get(x_22, 1);
x_209 = lean_ctor_get(x_22, 2);
x_210 = lean_ctor_get(x_22, 3);
x_211 = lean_ctor_get(x_22, 4);
x_212 = lean_unsigned_to_nat(2u);
x_213 = lean_nat_mul(x_212, x_206);
x_214 = lean_nat_dec_lt(x_207, x_213);
lean_dec(x_213);
if (x_214 == 0)
{
lean_object* x_215; uint8_t x_216; uint8_t x_253; 
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_del_object(x_204);
x_253 = !lean_is_exclusive(x_22);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_254 = lean_ctor_get(x_22, 4);
lean_dec(x_254);
x_255 = lean_ctor_get(x_22, 3);
lean_dec(x_255);
x_256 = lean_ctor_get(x_22, 2);
lean_dec(x_256);
x_257 = lean_ctor_get(x_22, 1);
lean_dec(x_257);
x_258 = lean_ctor_get(x_22, 0);
lean_dec(x_258);
x_215 = x_22;
x_216 = x_253;
goto block_252;
}
else
{
lean_dec(x_22);
x_215 = lean_box(0);
x_216 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_240; lean_object* x_241; 
x_217 = lean_unsigned_to_nat(1u);
x_218 = lean_nat_add(x_217, x_18);
lean_dec(x_18);
x_219 = lean_nat_add(x_218, x_194);
lean_dec(x_218);
x_240 = lean_nat_add(x_217, x_206);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_210, 0);
lean_inc(x_250);
x_241 = x_250;
goto block_249;
}
else
{
lean_object* x_251; 
x_251 = lean_unsigned_to_nat(0u);
x_241 = x_251;
goto block_249;
}
block_239:
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_nat_add(x_221, x_222);
lean_dec(x_222);
lean_dec(x_221);
lean_inc_ref(x_191);
if (x_216 == 0)
{
lean_ctor_set(x_215, 4, x_191);
lean_ctor_set(x_215, 3, x_211);
lean_ctor_set(x_215, 2, x_193);
lean_ctor_set(x_215, 1, x_192);
lean_ctor_set(x_215, 0, x_223);
x_224 = x_215;
goto block_237;
}
else
{
lean_object* x_238; 
x_238 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_238, 0, x_223);
lean_ctor_set(x_238, 1, x_192);
lean_ctor_set(x_238, 2, x_193);
lean_ctor_set(x_238, 3, x_211);
lean_ctor_set(x_238, 4, x_191);
x_224 = x_238;
goto block_237;
}
block_237:
{
lean_object* x_225; uint8_t x_226; uint8_t x_231; 
x_231 = !lean_is_exclusive(x_191);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = lean_ctor_get(x_191, 4);
lean_dec(x_232);
x_233 = lean_ctor_get(x_191, 3);
lean_dec(x_233);
x_234 = lean_ctor_get(x_191, 2);
lean_dec(x_234);
x_235 = lean_ctor_get(x_191, 1);
lean_dec(x_235);
x_236 = lean_ctor_get(x_191, 0);
lean_dec(x_236);
x_225 = x_191;
x_226 = x_231;
goto block_230;
}
else
{
lean_dec(x_191);
x_225 = lean_box(0);
x_226 = x_231;
goto block_230;
}
block_230:
{
lean_object* x_227; 
if (x_226 == 0)
{
lean_ctor_set(x_225, 4, x_224);
lean_ctor_set(x_225, 3, x_220);
lean_ctor_set(x_225, 2, x_209);
lean_ctor_set(x_225, 1, x_208);
lean_ctor_set(x_225, 0, x_219);
x_227 = x_225;
goto block_228;
}
else
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_229, 0, x_219);
lean_ctor_set(x_229, 1, x_208);
lean_ctor_set(x_229, 2, x_209);
lean_ctor_set(x_229, 3, x_220);
lean_ctor_set(x_229, 4, x_224);
x_227 = x_229;
goto block_228;
}
block_228:
{
return x_227;
}
}
}
}
block_249:
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_nat_add(x_240, x_241);
lean_dec(x_241);
lean_dec(x_240);
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_210);
lean_ctor_set(x_188, 3, x_21);
lean_ctor_set(x_188, 2, x_20);
lean_ctor_set(x_188, 1, x_19);
lean_ctor_set(x_188, 0, x_242);
x_243 = x_188;
goto block_247;
}
else
{
lean_object* x_248; 
x_248 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_248, 0, x_242);
lean_ctor_set(x_248, 1, x_19);
lean_ctor_set(x_248, 2, x_20);
lean_ctor_set(x_248, 3, x_21);
lean_ctor_set(x_248, 4, x_210);
x_243 = x_248;
goto block_247;
}
block_247:
{
lean_object* x_244; 
x_244 = lean_nat_add(x_217, x_194);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_211, 0);
lean_inc(x_245);
x_220 = x_243;
x_221 = x_244;
x_222 = x_245;
goto block_239;
}
else
{
lean_object* x_246; 
x_246 = lean_unsigned_to_nat(0u);
x_220 = x_243;
x_221 = x_244;
x_222 = x_246;
goto block_239;
}
}
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_259 = lean_unsigned_to_nat(1u);
x_260 = lean_nat_add(x_259, x_18);
lean_dec(x_18);
x_261 = lean_nat_add(x_260, x_194);
lean_dec(x_260);
x_262 = lean_nat_add(x_259, x_194);
x_263 = lean_nat_add(x_262, x_207);
lean_dec(x_262);
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_191);
lean_ctor_set(x_188, 3, x_22);
lean_ctor_set(x_188, 2, x_193);
lean_ctor_set(x_188, 1, x_192);
lean_ctor_set(x_188, 0, x_263);
x_264 = x_188;
goto block_268;
}
else
{
lean_object* x_269; 
x_269 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_269, 0, x_263);
lean_ctor_set(x_269, 1, x_192);
lean_ctor_set(x_269, 2, x_193);
lean_ctor_set(x_269, 3, x_22);
lean_ctor_set(x_269, 4, x_191);
x_264 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_265; 
if (x_205 == 0)
{
lean_ctor_set(x_204, 4, x_264);
lean_ctor_set(x_204, 0, x_261);
x_265 = x_204;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_267, 0, x_261);
lean_ctor_set(x_267, 1, x_19);
lean_ctor_set(x_267, 2, x_20);
lean_ctor_set(x_267, 3, x_21);
lean_ctor_set(x_267, 4, x_264);
x_265 = x_267;
goto block_266;
}
block_266:
{
return x_265;
}
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec_ref(x_21);
lean_del_object(x_204);
lean_dec(x_193);
lean_dec_ref(x_191);
lean_dec(x_192);
lean_del_object(x_188);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_270 = lean_box(1);
x_271 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2);
x_272 = l_panic___redArg(x_270, x_271);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_del_object(x_204);
lean_dec(x_193);
lean_dec(x_192);
lean_dec_ref(x_191);
lean_del_object(x_188);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_273 = lean_box(1);
x_274 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3);
x_275 = l_panic___redArg(x_273, x_274);
return x_275;
}
}
}
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_283; uint8_t x_284; uint8_t x_308; 
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_308 = !lean_is_exclusive(x_8);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_309 = lean_ctor_get(x_8, 4);
lean_dec(x_309);
x_310 = lean_ctor_get(x_8, 3);
lean_dec(x_310);
x_311 = lean_ctor_get(x_8, 2);
lean_dec(x_311);
x_312 = lean_ctor_get(x_8, 1);
lean_dec(x_312);
x_313 = lean_ctor_get(x_8, 0);
lean_dec(x_313);
x_283 = x_8;
x_284 = x_308;
goto block_307;
}
else
{
lean_dec(x_8);
x_283 = lean_box(0);
x_284 = x_308;
goto block_307;
}
block_307:
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_285 = lean_ctor_get(x_190, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_190, 1);
lean_inc(x_286);
lean_dec_ref(x_190);
x_287 = lean_ctor_get(x_22, 0);
x_288 = lean_unsigned_to_nat(1u);
x_289 = lean_nat_add(x_288, x_18);
lean_dec(x_18);
x_290 = lean_nat_add(x_288, x_287);
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_191);
lean_ctor_set(x_188, 3, x_22);
lean_ctor_set(x_188, 2, x_286);
lean_ctor_set(x_188, 1, x_285);
lean_ctor_set(x_188, 0, x_290);
x_291 = x_188;
goto block_295;
}
else
{
lean_object* x_296; 
x_296 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_296, 0, x_290);
lean_ctor_set(x_296, 1, x_285);
lean_ctor_set(x_296, 2, x_286);
lean_ctor_set(x_296, 3, x_22);
lean_ctor_set(x_296, 4, x_191);
x_291 = x_296;
goto block_295;
}
block_295:
{
lean_object* x_292; 
if (x_284 == 0)
{
lean_ctor_set(x_283, 4, x_291);
lean_ctor_set(x_283, 0, x_289);
x_292 = x_283;
goto block_293;
}
else
{
lean_object* x_294; 
x_294 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_294, 0, x_289);
lean_ctor_set(x_294, 1, x_19);
lean_ctor_set(x_294, 2, x_20);
lean_ctor_set(x_294, 3, x_21);
lean_ctor_set(x_294, 4, x_291);
x_292 = x_294;
goto block_293;
}
block_293:
{
return x_292;
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_18);
x_297 = lean_ctor_get(x_190, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_190, 1);
lean_inc(x_298);
lean_dec_ref(x_190);
x_299 = lean_unsigned_to_nat(3u);
x_300 = lean_unsigned_to_nat(1u);
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_22);
lean_ctor_set(x_188, 3, x_22);
lean_ctor_set(x_188, 2, x_298);
lean_ctor_set(x_188, 1, x_297);
lean_ctor_set(x_188, 0, x_300);
x_301 = x_188;
goto block_305;
}
else
{
lean_object* x_306; 
x_306 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_306, 0, x_300);
lean_ctor_set(x_306, 1, x_297);
lean_ctor_set(x_306, 2, x_298);
lean_ctor_set(x_306, 3, x_22);
lean_ctor_set(x_306, 4, x_22);
x_301 = x_306;
goto block_305;
}
block_305:
{
lean_object* x_302; 
if (x_284 == 0)
{
lean_ctor_set(x_283, 4, x_301);
lean_ctor_set(x_283, 0, x_299);
x_302 = x_283;
goto block_303;
}
else
{
lean_object* x_304; 
x_304 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_304, 0, x_299);
lean_ctor_set(x_304, 1, x_19);
lean_ctor_set(x_304, 2, x_20);
lean_ctor_set(x_304, 3, x_21);
lean_ctor_set(x_304, 4, x_301);
x_302 = x_304;
goto block_303;
}
block_303:
{
return x_302;
}
}
}
}
}
else
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_314; uint8_t x_315; uint8_t x_339; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_339 = !lean_is_exclusive(x_8);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_340 = lean_ctor_get(x_8, 4);
lean_dec(x_340);
x_341 = lean_ctor_get(x_8, 3);
lean_dec(x_341);
x_342 = lean_ctor_get(x_8, 2);
lean_dec(x_342);
x_343 = lean_ctor_get(x_8, 1);
lean_dec(x_343);
x_344 = lean_ctor_get(x_8, 0);
lean_dec(x_344);
x_314 = x_8;
x_315 = x_339;
goto block_338;
}
else
{
lean_dec(x_8);
x_314 = lean_box(0);
x_315 = x_339;
goto block_338;
}
block_338:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; uint8_t x_334; 
x_316 = lean_ctor_get(x_190, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_190, 1);
lean_inc(x_317);
lean_dec_ref(x_190);
x_318 = lean_ctor_get(x_22, 1);
x_319 = lean_ctor_get(x_22, 2);
x_334 = !lean_is_exclusive(x_22);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_22, 4);
lean_dec(x_335);
x_336 = lean_ctor_get(x_22, 3);
lean_dec(x_336);
x_337 = lean_ctor_get(x_22, 0);
lean_dec(x_337);
x_320 = x_22;
x_321 = x_334;
goto block_333;
}
else
{
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_22);
x_320 = lean_box(0);
x_321 = x_334;
goto block_333;
}
block_333:
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_unsigned_to_nat(3u);
x_323 = lean_unsigned_to_nat(1u);
if (x_321 == 0)
{
lean_ctor_set(x_320, 4, x_21);
lean_ctor_set(x_320, 3, x_21);
lean_ctor_set(x_320, 2, x_20);
lean_ctor_set(x_320, 1, x_19);
lean_ctor_set(x_320, 0, x_323);
x_324 = x_320;
goto block_331;
}
else
{
lean_object* x_332; 
x_332 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_332, 0, x_323);
lean_ctor_set(x_332, 1, x_19);
lean_ctor_set(x_332, 2, x_20);
lean_ctor_set(x_332, 3, x_21);
lean_ctor_set(x_332, 4, x_21);
x_324 = x_332;
goto block_331;
}
block_331:
{
lean_object* x_325; 
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_21);
lean_ctor_set(x_188, 3, x_21);
lean_ctor_set(x_188, 2, x_317);
lean_ctor_set(x_188, 1, x_316);
lean_ctor_set(x_188, 0, x_323);
x_325 = x_188;
goto block_329;
}
else
{
lean_object* x_330; 
x_330 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_330, 0, x_323);
lean_ctor_set(x_330, 1, x_316);
lean_ctor_set(x_330, 2, x_317);
lean_ctor_set(x_330, 3, x_21);
lean_ctor_set(x_330, 4, x_21);
x_325 = x_330;
goto block_329;
}
block_329:
{
lean_object* x_326; 
if (x_315 == 0)
{
lean_ctor_set(x_314, 4, x_325);
lean_ctor_set(x_314, 3, x_324);
lean_ctor_set(x_314, 2, x_319);
lean_ctor_set(x_314, 1, x_318);
lean_ctor_set(x_314, 0, x_322);
x_326 = x_314;
goto block_327;
}
else
{
lean_object* x_328; 
x_328 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_328, 0, x_322);
lean_ctor_set(x_328, 1, x_318);
lean_ctor_set(x_328, 2, x_319);
lean_ctor_set(x_328, 3, x_324);
lean_ctor_set(x_328, 4, x_325);
x_326 = x_328;
goto block_327;
}
block_327:
{
return x_326;
}
}
}
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_345 = lean_ctor_get(x_190, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_190, 1);
lean_inc(x_346);
lean_dec_ref(x_190);
x_347 = lean_unsigned_to_nat(2u);
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_22);
lean_ctor_set(x_188, 3, x_8);
lean_ctor_set(x_188, 2, x_346);
lean_ctor_set(x_188, 1, x_345);
lean_ctor_set(x_188, 0, x_347);
x_348 = x_188;
goto block_349;
}
else
{
lean_object* x_350; 
x_350 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_345);
lean_ctor_set(x_350, 2, x_346);
lean_ctor_set(x_350, 3, x_8);
lean_ctor_set(x_350, 4, x_22);
x_348 = x_350;
goto block_349;
}
block_349:
{
return x_348;
}
}
}
}
}
}
}
else
{
return x_8;
}
}
else
{
return x_9;
}
}
else
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_17, 0);
lean_inc(x_358);
lean_dec_ref(x_17);
if (x_11 == 0)
{
lean_ctor_set(x_10, 2, x_358);
lean_ctor_set(x_10, 1, x_2);
x_359 = x_10;
goto block_360;
}
else
{
lean_object* x_361; 
x_361 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_361, 0, x_5);
lean_ctor_set(x_361, 1, x_2);
lean_ctor_set(x_361, 2, x_358);
lean_ctor_set(x_361, 3, x_8);
lean_ctor_set(x_361, 4, x_9);
x_359 = x_361;
goto block_360;
}
block_360:
{
return x_359;
}
}
}
default: 
{
lean_object* x_362; lean_object* x_363; 
lean_del_object(x_10);
lean_dec(x_5);
x_362 = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(x_1, x_2, x_3, x_9);
x_363 = l_Std_DTreeMap_Internal_Impl_balance_x21___redArg(x_6, x_7, x_8, x_362);
return x_363;
}
}
}
}
else
{
lean_object* x_366; lean_object* x_367; 
lean_dec_ref(x_1);
x_366 = lean_box(0);
x_367 = lean_apply_1(x_3, x_366);
if (lean_obj_tag(x_367) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
lean_dec_ref(x_367);
x_369 = lean_unsigned_to_nat(1u);
x_370 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_2);
lean_ctor_set(x_370, 2, x_368);
lean_ctor_set(x_370, 3, x_4);
lean_ctor_set(x_370, 4, x_4);
return x_370;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_alter_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_modify___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_27; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
x_10 = x_4;
x_11 = x_27;
goto block_26;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_12; uint8_t x_13; 
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_6);
x_13 = lean_unbox(x_12);
switch (x_13) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DTreeMap_Internal_Impl_modify___redArg(x_1, x_2, x_3, x_8);
if (x_11 == 0)
{
lean_ctor_set(x_10, 3, x_14);
x_15 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_9);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
case 1:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_18 = lean_apply_1(x_3, x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 2, x_18);
lean_ctor_set(x_10, 1, x_2);
x_19 = x_10;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_8);
lean_ctor_set(x_21, 4, x_9);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
default: 
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Std_DTreeMap_Internal_Impl_modify___redArg(x_1, x_2, x_3, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_22);
x_23 = x_10;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_6);
lean_ctor_set(x_25, 2, x_7);
lean_ctor_set(x_25, 3, x_8);
lean_ctor_set(x_25, 4, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_modify(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_modify___redArg(x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_5; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_2, lean_box(0));
return x_5;
}
case 1:
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_4, lean_box(0));
return x_6;
}
default: 
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_apply_1(x_3, lean_box(0));
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mergeWith___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_14; 
x_6 = lean_ctor_get(x_4, 0);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
x_7 = x_4;
x_8 = x_14;
goto block_13;
}
else
{
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_3(x_2, x_3, x_6, x_1);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_9);
x_10 = x_7;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mergeWith___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_6 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_4);
x_7 = l_Std_DTreeMap_Internal_Impl_alter___redArg(x_2, x_4, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mergeWith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mergeWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_3);
x_10 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mergeWith_x21___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_6 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_4);
x_7 = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(x_2, x_4, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mergeWith_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_mergeWith_x21___redArg___lam__1), 5, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_mergeWith_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_mergeWith_x21___redArg___lam__1), 5, 2);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_3);
x_9 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(x_1, x_2, x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = l_Option_instBEq_beq___redArg(x_3, x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_5);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_5);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_11; lean_object* x_12; lean_object* x_21; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_21 = x_25;
goto block_24;
}
else
{
lean_object* x_26; 
x_26 = lean_unsigned_to_nat(0u);
x_21 = x_26;
goto block_24;
}
block_10:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
return x_9;
}
}
block_20:
{
uint8_t x_13; 
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_union___redArg___closed__9));
x_15 = lean_box(0);
x_16 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_beq___redArg___closed__0));
x_17 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_beq___redArg___lam__0___boxed), 8, 5);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_4);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_15);
lean_closure_set(x_17, 4, x_16);
x_18 = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(x_14, x_17, x_16, x_3);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_5 = x_19;
goto block_10;
}
}
block_24:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
x_11 = x_21;
x_12 = x_22;
goto block_20;
}
else
{
lean_object* x_23; 
x_23 = lean_unsigned_to_nat(0u);
x_11 = x_21;
x_12 = x_23;
goto block_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_Const_beq(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_instCoeTypeForall(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_336; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_336 = !lean_is_exclusive(x_4);
if (x_336 == 0)
{
x_10 = x_4;
x_11 = x_336;
goto block_335;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = x_336;
goto block_335;
}
block_335:
{
lean_object* x_12; uint8_t x_13; 
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_6);
x_13 = lean_unbox(x_12);
switch (x_13) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_del_object(x_10);
lean_dec(x_5);
x_14 = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(x_1, x_2, x_3, x_8);
x_15 = l_Std_DTreeMap_Internal_Impl_balance___redArg(x_6, x_7, x_14, x_9);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_7);
x_17 = lean_apply_1(x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_del_object(x_10);
lean_dec(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_8) == 0)
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
x_22 = lean_ctor_get(x_8, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
x_25 = lean_ctor_get(x_9, 2);
x_26 = lean_ctor_get(x_9, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_9, 4);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_dec_lt(x_18, x_23);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; uint8_t x_165; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_165 = !lean_is_exclusive(x_8);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_8, 4);
lean_dec(x_166);
x_167 = lean_ctor_get(x_8, 3);
lean_dec(x_167);
x_168 = lean_ctor_get(x_8, 2);
lean_dec(x_168);
x_169 = lean_ctor_get(x_8, 1);
lean_dec(x_169);
x_170 = lean_ctor_get(x_8, 0);
lean_dec(x_170);
x_30 = x_8;
x_31 = x_165;
goto block_164;
}
else
{
lean_dec(x_8);
x_30 = lean_box(0);
x_31 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_19, x_20, x_21, x_22);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_unsigned_to_nat(3u);
x_38 = lean_nat_mul(x_37, x_36);
x_39 = lean_nat_dec_lt(x_38, x_23);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_26);
x_40 = lean_nat_add(x_28, x_36);
x_41 = lean_nat_add(x_40, x_23);
lean_dec(x_40);
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_9);
lean_ctor_set(x_30, 3, x_33);
lean_ctor_set(x_30, 2, x_35);
lean_ctor_set(x_30, 1, x_34);
lean_ctor_set(x_30, 0, x_41);
x_42 = x_30;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 3, x_33);
lean_ctor_set(x_44, 4, x_9);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
else
{
lean_object* x_45; uint8_t x_46; uint8_t x_99; 
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_99 = !lean_is_exclusive(x_9);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_9, 4);
lean_dec(x_100);
x_101 = lean_ctor_get(x_9, 3);
lean_dec(x_101);
x_102 = lean_ctor_get(x_9, 2);
lean_dec(x_102);
x_103 = lean_ctor_get(x_9, 1);
lean_dec(x_103);
x_104 = lean_ctor_get(x_9, 0);
lean_dec(x_104);
x_45 = x_9;
x_46 = x_99;
goto block_98;
}
else
{
lean_dec(x_9);
x_45 = lean_box(0);
x_46 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_47 = lean_ctor_get(x_26, 0);
x_48 = lean_ctor_get(x_26, 1);
x_49 = lean_ctor_get(x_26, 2);
x_50 = lean_ctor_get(x_26, 3);
x_51 = lean_ctor_get(x_26, 4);
x_52 = lean_ctor_get(x_27, 0);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_mul(x_53, x_52);
x_55 = lean_nat_dec_lt(x_47, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; uint8_t x_83; 
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_83 = !lean_is_exclusive(x_26);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_26, 4);
lean_dec(x_84);
x_85 = lean_ctor_get(x_26, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_26, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_26, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_26, 0);
lean_dec(x_88);
x_56 = x_26;
x_57 = x_83;
goto block_82;
}
else
{
lean_dec(x_26);
x_56 = lean_box(0);
x_57 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_71; 
x_58 = lean_nat_add(x_28, x_36);
x_59 = lean_nat_add(x_58, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_50, 0);
lean_inc(x_80);
x_71 = x_80;
goto block_79;
}
else
{
lean_object* x_81; 
x_81 = lean_unsigned_to_nat(0u);
x_71 = x_81;
goto block_79;
}
block_70:
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_nat_add(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_57 == 0)
{
lean_ctor_set(x_56, 4, x_27);
lean_ctor_set(x_56, 3, x_51);
lean_ctor_set(x_56, 2, x_25);
lean_ctor_set(x_56, 1, x_24);
lean_ctor_set(x_56, 0, x_63);
x_64 = x_56;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_24);
lean_ctor_set(x_69, 2, x_25);
lean_ctor_set(x_69, 3, x_51);
lean_ctor_set(x_69, 4, x_27);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_46 == 0)
{
lean_ctor_set(x_45, 4, x_64);
lean_ctor_set(x_45, 3, x_60);
lean_ctor_set(x_45, 2, x_49);
lean_ctor_set(x_45, 1, x_48);
lean_ctor_set(x_45, 0, x_59);
x_65 = x_45;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_48);
lean_ctor_set(x_67, 2, x_49);
lean_ctor_set(x_67, 3, x_60);
lean_ctor_set(x_67, 4, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
block_79:
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_nat_add(x_58, x_71);
lean_dec(x_71);
lean_dec(x_58);
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_50);
lean_ctor_set(x_30, 3, x_33);
lean_ctor_set(x_30, 2, x_35);
lean_ctor_set(x_30, 1, x_34);
lean_ctor_set(x_30, 0, x_72);
x_73 = x_30;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_34);
lean_ctor_set(x_78, 2, x_35);
lean_ctor_set(x_78, 3, x_33);
lean_ctor_set(x_78, 4, x_50);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
x_74 = lean_nat_add(x_28, x_52);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_51, 0);
lean_inc(x_75);
x_60 = x_73;
x_61 = x_74;
x_62 = x_75;
goto block_70;
}
else
{
lean_object* x_76; 
x_76 = lean_unsigned_to_nat(0u);
x_60 = x_73;
x_61 = x_74;
x_62 = x_76;
goto block_70;
}
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_nat_add(x_28, x_36);
x_90 = lean_nat_add(x_89, x_23);
lean_dec(x_23);
x_91 = lean_nat_add(x_89, x_47);
lean_dec(x_89);
if (x_46 == 0)
{
lean_ctor_set(x_45, 4, x_26);
lean_ctor_set(x_45, 3, x_33);
lean_ctor_set(x_45, 2, x_35);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_45, 0, x_91);
x_92 = x_45;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set(x_97, 1, x_34);
lean_ctor_set(x_97, 2, x_35);
lean_ctor_set(x_97, 3, x_33);
lean_ctor_set(x_97, 4, x_26);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_27);
lean_ctor_set(x_30, 3, x_92);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 0, x_90);
x_93 = x_30;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_24);
lean_ctor_set(x_95, 2, x_25);
lean_ctor_set(x_95, 3, x_92);
lean_ctor_set(x_95, 4, x_27);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
}
}
else
{
lean_object* x_105; uint8_t x_106; uint8_t x_158; 
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_158 = !lean_is_exclusive(x_9);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = lean_ctor_get(x_9, 4);
lean_dec(x_159);
x_160 = lean_ctor_get(x_9, 3);
lean_dec(x_160);
x_161 = lean_ctor_get(x_9, 2);
lean_dec(x_161);
x_162 = lean_ctor_get(x_9, 1);
lean_dec(x_162);
x_163 = lean_ctor_get(x_9, 0);
lean_dec(x_163);
x_105 = x_9;
x_106 = x_158;
goto block_157;
}
else
{
lean_dec(x_9);
x_105 = lean_box(0);
x_106 = x_158;
goto block_157;
}
block_157:
{
if (lean_obj_tag(x_26) == 0)
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_32, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_32, 1);
lean_inc(x_108);
lean_dec_ref(x_32);
x_109 = lean_ctor_get(x_26, 0);
x_110 = lean_nat_add(x_28, x_23);
lean_dec(x_23);
x_111 = lean_nat_add(x_28, x_109);
if (x_106 == 0)
{
lean_ctor_set(x_105, 4, x_26);
lean_ctor_set(x_105, 3, x_33);
lean_ctor_set(x_105, 2, x_108);
lean_ctor_set(x_105, 1, x_107);
lean_ctor_set(x_105, 0, x_111);
x_112 = x_105;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_111);
lean_ctor_set(x_117, 1, x_107);
lean_ctor_set(x_117, 2, x_108);
lean_ctor_set(x_117, 3, x_33);
lean_ctor_set(x_117, 4, x_26);
x_112 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_113; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_27);
lean_ctor_set(x_30, 3, x_112);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 0, x_110);
x_113 = x_30;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_24);
lean_ctor_set(x_115, 2, x_25);
lean_ctor_set(x_115, 3, x_112);
lean_ctor_set(x_115, 4, x_27);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_135; 
lean_dec(x_23);
x_118 = lean_ctor_get(x_32, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_32, 1);
lean_inc(x_119);
lean_dec_ref(x_32);
x_120 = lean_ctor_get(x_26, 1);
x_121 = lean_ctor_get(x_26, 2);
x_135 = !lean_is_exclusive(x_26);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_26, 4);
lean_dec(x_136);
x_137 = lean_ctor_get(x_26, 3);
lean_dec(x_137);
x_138 = lean_ctor_get(x_26, 0);
lean_dec(x_138);
x_122 = x_26;
x_123 = x_135;
goto block_134;
}
else
{
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_26);
x_122 = lean_box(0);
x_123 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_unsigned_to_nat(3u);
if (x_123 == 0)
{
lean_ctor_set(x_122, 4, x_27);
lean_ctor_set(x_122, 3, x_27);
lean_ctor_set(x_122, 2, x_119);
lean_ctor_set(x_122, 1, x_118);
lean_ctor_set(x_122, 0, x_28);
x_125 = x_122;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_133, 0, x_28);
lean_ctor_set(x_133, 1, x_118);
lean_ctor_set(x_133, 2, x_119);
lean_ctor_set(x_133, 3, x_27);
lean_ctor_set(x_133, 4, x_27);
x_125 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_126; 
if (x_106 == 0)
{
lean_ctor_set(x_105, 3, x_27);
lean_ctor_set(x_105, 0, x_28);
x_126 = x_105;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_131, 0, x_28);
lean_ctor_set(x_131, 1, x_24);
lean_ctor_set(x_131, 2, x_25);
lean_ctor_set(x_131, 3, x_27);
lean_ctor_set(x_131, 4, x_27);
x_126 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_127; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_126);
lean_ctor_set(x_30, 3, x_125);
lean_ctor_set(x_30, 2, x_121);
lean_ctor_set(x_30, 1, x_120);
lean_ctor_set(x_30, 0, x_124);
x_127 = x_30;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set(x_129, 1, x_120);
lean_ctor_set(x_129, 2, x_121);
lean_ctor_set(x_129, 3, x_125);
lean_ctor_set(x_129, 4, x_126);
x_127 = x_129;
goto block_128;
}
block_128:
{
return x_127;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_23);
x_139 = lean_ctor_get(x_32, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_32, 1);
lean_inc(x_140);
lean_dec_ref(x_32);
x_141 = lean_unsigned_to_nat(3u);
if (x_106 == 0)
{
lean_ctor_set(x_105, 4, x_26);
lean_ctor_set(x_105, 2, x_140);
lean_ctor_set(x_105, 1, x_139);
lean_ctor_set(x_105, 0, x_28);
x_142 = x_105;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_28);
lean_ctor_set(x_147, 1, x_139);
lean_ctor_set(x_147, 2, x_140);
lean_ctor_set(x_147, 3, x_26);
lean_ctor_set(x_147, 4, x_26);
x_142 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_143; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_27);
lean_ctor_set(x_30, 3, x_142);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 0, x_141);
x_143 = x_30;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_145, 0, x_141);
lean_ctor_set(x_145, 1, x_24);
lean_ctor_set(x_145, 2, x_25);
lean_ctor_set(x_145, 3, x_142);
lean_ctor_set(x_145, 4, x_27);
x_143 = x_145;
goto block_144;
}
block_144:
{
return x_143;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_32, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_32, 1);
lean_inc(x_149);
lean_dec_ref(x_32);
if (x_106 == 0)
{
lean_ctor_set(x_105, 3, x_27);
x_150 = x_105;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_156, 0, x_23);
lean_ctor_set(x_156, 1, x_24);
lean_ctor_set(x_156, 2, x_25);
lean_ctor_set(x_156, 3, x_27);
lean_ctor_set(x_156, 4, x_27);
x_150 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_unsigned_to_nat(2u);
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_150);
lean_ctor_set(x_30, 3, x_27);
lean_ctor_set(x_30, 2, x_149);
lean_ctor_set(x_30, 1, x_148);
lean_ctor_set(x_30, 0, x_151);
x_152 = x_30;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_148);
lean_ctor_set(x_154, 2, x_149);
lean_ctor_set(x_154, 3, x_27);
lean_ctor_set(x_154, 4, x_150);
x_152 = x_154;
goto block_153;
}
block_153:
{
return x_152;
}
}
}
}
}
}
}
}
else
{
lean_object* x_171; uint8_t x_172; uint8_t x_323; 
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
x_323 = !lean_is_exclusive(x_9);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_324 = lean_ctor_get(x_9, 4);
lean_dec(x_324);
x_325 = lean_ctor_get(x_9, 3);
lean_dec(x_325);
x_326 = lean_ctor_get(x_9, 2);
lean_dec(x_326);
x_327 = lean_ctor_get(x_9, 1);
lean_dec(x_327);
x_328 = lean_ctor_get(x_9, 0);
lean_dec(x_328);
x_171 = x_9;
x_172 = x_323;
goto block_322;
}
else
{
lean_dec(x_9);
x_171 = lean_box(0);
x_172 = x_323;
goto block_322;
}
block_322:
{
lean_object* x_173; lean_object* x_174; 
x_173 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_24, x_25, x_26, x_27);
x_174 = lean_ctor_get(x_173, 2);
lean_inc(x_174);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec_ref(x_173);
x_177 = lean_ctor_get(x_174, 0);
x_178 = lean_unsigned_to_nat(3u);
x_179 = lean_nat_mul(x_178, x_177);
x_180 = lean_nat_dec_lt(x_179, x_18);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_22);
x_181 = lean_nat_add(x_28, x_18);
x_182 = lean_nat_add(x_181, x_177);
lean_dec(x_181);
if (x_172 == 0)
{
lean_ctor_set(x_171, 4, x_174);
lean_ctor_set(x_171, 3, x_8);
lean_ctor_set(x_171, 2, x_176);
lean_ctor_set(x_171, 1, x_175);
lean_ctor_set(x_171, 0, x_182);
x_183 = x_171;
goto block_184;
}
else
{
lean_object* x_185; 
x_185 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_175);
lean_ctor_set(x_185, 2, x_176);
lean_ctor_set(x_185, 3, x_8);
lean_ctor_set(x_185, 4, x_174);
x_183 = x_185;
goto block_184;
}
block_184:
{
return x_183;
}
}
else
{
lean_object* x_186; uint8_t x_187; uint8_t x_251; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_251 = !lean_is_exclusive(x_8);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_8, 4);
lean_dec(x_252);
x_253 = lean_ctor_get(x_8, 3);
lean_dec(x_253);
x_254 = lean_ctor_get(x_8, 2);
lean_dec(x_254);
x_255 = lean_ctor_get(x_8, 1);
lean_dec(x_255);
x_256 = lean_ctor_get(x_8, 0);
lean_dec(x_256);
x_186 = x_8;
x_187 = x_251;
goto block_250;
}
else
{
lean_dec(x_8);
x_186 = lean_box(0);
x_187 = x_251;
goto block_250;
}
block_250:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_188 = lean_ctor_get(x_21, 0);
x_189 = lean_ctor_get(x_22, 0);
x_190 = lean_ctor_get(x_22, 1);
x_191 = lean_ctor_get(x_22, 2);
x_192 = lean_ctor_get(x_22, 3);
x_193 = lean_ctor_get(x_22, 4);
x_194 = lean_unsigned_to_nat(2u);
x_195 = lean_nat_mul(x_194, x_188);
x_196 = lean_nat_dec_lt(x_189, x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; uint8_t x_198; uint8_t x_234; 
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_del_object(x_186);
x_234 = !lean_is_exclusive(x_22);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_235 = lean_ctor_get(x_22, 4);
lean_dec(x_235);
x_236 = lean_ctor_get(x_22, 3);
lean_dec(x_236);
x_237 = lean_ctor_get(x_22, 2);
lean_dec(x_237);
x_238 = lean_ctor_get(x_22, 1);
lean_dec(x_238);
x_239 = lean_ctor_get(x_22, 0);
lean_dec(x_239);
x_197 = x_22;
x_198 = x_234;
goto block_233;
}
else
{
lean_dec(x_22);
x_197 = lean_box(0);
x_198 = x_234;
goto block_233;
}
block_233:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_221; lean_object* x_222; 
x_199 = lean_nat_add(x_28, x_18);
lean_dec(x_18);
x_200 = lean_nat_add(x_199, x_177);
lean_dec(x_199);
x_221 = lean_nat_add(x_28, x_188);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_192, 0);
lean_inc(x_231);
x_222 = x_231;
goto block_230;
}
else
{
lean_object* x_232; 
x_232 = lean_unsigned_to_nat(0u);
x_222 = x_232;
goto block_230;
}
block_220:
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_nat_add(x_201, x_203);
lean_dec(x_203);
lean_dec(x_201);
lean_inc_ref(x_174);
if (x_198 == 0)
{
lean_ctor_set(x_197, 4, x_174);
lean_ctor_set(x_197, 3, x_193);
lean_ctor_set(x_197, 2, x_176);
lean_ctor_set(x_197, 1, x_175);
lean_ctor_set(x_197, 0, x_204);
x_205 = x_197;
goto block_218;
}
else
{
lean_object* x_219; 
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_204);
lean_ctor_set(x_219, 1, x_175);
lean_ctor_set(x_219, 2, x_176);
lean_ctor_set(x_219, 3, x_193);
lean_ctor_set(x_219, 4, x_174);
x_205 = x_219;
goto block_218;
}
block_218:
{
lean_object* x_206; uint8_t x_207; uint8_t x_212; 
x_212 = !lean_is_exclusive(x_174);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_213 = lean_ctor_get(x_174, 4);
lean_dec(x_213);
x_214 = lean_ctor_get(x_174, 3);
lean_dec(x_214);
x_215 = lean_ctor_get(x_174, 2);
lean_dec(x_215);
x_216 = lean_ctor_get(x_174, 1);
lean_dec(x_216);
x_217 = lean_ctor_get(x_174, 0);
lean_dec(x_217);
x_206 = x_174;
x_207 = x_212;
goto block_211;
}
else
{
lean_dec(x_174);
x_206 = lean_box(0);
x_207 = x_212;
goto block_211;
}
block_211:
{
lean_object* x_208; 
if (x_207 == 0)
{
lean_ctor_set(x_206, 4, x_205);
lean_ctor_set(x_206, 3, x_202);
lean_ctor_set(x_206, 2, x_191);
lean_ctor_set(x_206, 1, x_190);
lean_ctor_set(x_206, 0, x_200);
x_208 = x_206;
goto block_209;
}
else
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_210, 0, x_200);
lean_ctor_set(x_210, 1, x_190);
lean_ctor_set(x_210, 2, x_191);
lean_ctor_set(x_210, 3, x_202);
lean_ctor_set(x_210, 4, x_205);
x_208 = x_210;
goto block_209;
}
block_209:
{
return x_208;
}
}
}
}
block_230:
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_nat_add(x_221, x_222);
lean_dec(x_222);
lean_dec(x_221);
if (x_172 == 0)
{
lean_ctor_set(x_171, 4, x_192);
lean_ctor_set(x_171, 3, x_21);
lean_ctor_set(x_171, 2, x_20);
lean_ctor_set(x_171, 1, x_19);
lean_ctor_set(x_171, 0, x_223);
x_224 = x_171;
goto block_228;
}
else
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_229, 0, x_223);
lean_ctor_set(x_229, 1, x_19);
lean_ctor_set(x_229, 2, x_20);
lean_ctor_set(x_229, 3, x_21);
lean_ctor_set(x_229, 4, x_192);
x_224 = x_229;
goto block_228;
}
block_228:
{
lean_object* x_225; 
x_225 = lean_nat_add(x_28, x_177);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_193, 0);
lean_inc(x_226);
x_201 = x_225;
x_202 = x_224;
x_203 = x_226;
goto block_220;
}
else
{
lean_object* x_227; 
x_227 = lean_unsigned_to_nat(0u);
x_201 = x_225;
x_202 = x_224;
x_203 = x_227;
goto block_220;
}
}
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_240 = lean_nat_add(x_28, x_18);
lean_dec(x_18);
x_241 = lean_nat_add(x_240, x_177);
lean_dec(x_240);
x_242 = lean_nat_add(x_28, x_177);
x_243 = lean_nat_add(x_242, x_189);
lean_dec(x_242);
if (x_172 == 0)
{
lean_ctor_set(x_171, 4, x_174);
lean_ctor_set(x_171, 3, x_22);
lean_ctor_set(x_171, 2, x_176);
lean_ctor_set(x_171, 1, x_175);
lean_ctor_set(x_171, 0, x_243);
x_244 = x_171;
goto block_248;
}
else
{
lean_object* x_249; 
x_249 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_249, 0, x_243);
lean_ctor_set(x_249, 1, x_175);
lean_ctor_set(x_249, 2, x_176);
lean_ctor_set(x_249, 3, x_22);
lean_ctor_set(x_249, 4, x_174);
x_244 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_245; 
if (x_187 == 0)
{
lean_ctor_set(x_186, 4, x_244);
lean_ctor_set(x_186, 0, x_241);
x_245 = x_186;
goto block_246;
}
else
{
lean_object* x_247; 
x_247 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_247, 0, x_241);
lean_ctor_set(x_247, 1, x_19);
lean_ctor_set(x_247, 2, x_20);
lean_ctor_set(x_247, 3, x_21);
lean_ctor_set(x_247, 4, x_244);
x_245 = x_247;
goto block_246;
}
block_246:
{
return x_245;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_257; uint8_t x_258; uint8_t x_280; 
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_280 = !lean_is_exclusive(x_8);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_281 = lean_ctor_get(x_8, 4);
lean_dec(x_281);
x_282 = lean_ctor_get(x_8, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_8, 2);
lean_dec(x_283);
x_284 = lean_ctor_get(x_8, 1);
lean_dec(x_284);
x_285 = lean_ctor_get(x_8, 0);
lean_dec(x_285);
x_257 = x_8;
x_258 = x_280;
goto block_279;
}
else
{
lean_dec(x_8);
x_257 = lean_box(0);
x_258 = x_280;
goto block_279;
}
block_279:
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_259 = lean_ctor_get(x_173, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_173, 1);
lean_inc(x_260);
lean_dec_ref(x_173);
x_261 = lean_ctor_get(x_22, 0);
x_262 = lean_nat_add(x_28, x_18);
lean_dec(x_18);
x_263 = lean_nat_add(x_28, x_261);
if (x_172 == 0)
{
lean_ctor_set(x_171, 4, x_174);
lean_ctor_set(x_171, 3, x_22);
lean_ctor_set(x_171, 2, x_260);
lean_ctor_set(x_171, 1, x_259);
lean_ctor_set(x_171, 0, x_263);
x_264 = x_171;
goto block_268;
}
else
{
lean_object* x_269; 
x_269 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_269, 0, x_263);
lean_ctor_set(x_269, 1, x_259);
lean_ctor_set(x_269, 2, x_260);
lean_ctor_set(x_269, 3, x_22);
lean_ctor_set(x_269, 4, x_174);
x_264 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_265; 
if (x_258 == 0)
{
lean_ctor_set(x_257, 4, x_264);
lean_ctor_set(x_257, 0, x_262);
x_265 = x_257;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_267, 0, x_262);
lean_ctor_set(x_267, 1, x_19);
lean_ctor_set(x_267, 2, x_20);
lean_ctor_set(x_267, 3, x_21);
lean_ctor_set(x_267, 4, x_264);
x_265 = x_267;
goto block_266;
}
block_266:
{
return x_265;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_18);
x_270 = lean_ctor_get(x_173, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_173, 1);
lean_inc(x_271);
lean_dec_ref(x_173);
x_272 = lean_unsigned_to_nat(3u);
if (x_172 == 0)
{
lean_ctor_set(x_171, 4, x_22);
lean_ctor_set(x_171, 3, x_22);
lean_ctor_set(x_171, 2, x_271);
lean_ctor_set(x_171, 1, x_270);
lean_ctor_set(x_171, 0, x_28);
x_273 = x_171;
goto block_277;
}
else
{
lean_object* x_278; 
x_278 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_278, 0, x_28);
lean_ctor_set(x_278, 1, x_270);
lean_ctor_set(x_278, 2, x_271);
lean_ctor_set(x_278, 3, x_22);
lean_ctor_set(x_278, 4, x_22);
x_273 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_274; 
if (x_258 == 0)
{
lean_ctor_set(x_257, 4, x_273);
lean_ctor_set(x_257, 0, x_272);
x_274 = x_257;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_276, 0, x_272);
lean_ctor_set(x_276, 1, x_19);
lean_ctor_set(x_276, 2, x_20);
lean_ctor_set(x_276, 3, x_21);
lean_ctor_set(x_276, 4, x_273);
x_274 = x_276;
goto block_275;
}
block_275:
{
return x_274;
}
}
}
}
}
else
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_286; uint8_t x_287; uint8_t x_310; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_310 = !lean_is_exclusive(x_8);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_311 = lean_ctor_get(x_8, 4);
lean_dec(x_311);
x_312 = lean_ctor_get(x_8, 3);
lean_dec(x_312);
x_313 = lean_ctor_get(x_8, 2);
lean_dec(x_313);
x_314 = lean_ctor_get(x_8, 1);
lean_dec(x_314);
x_315 = lean_ctor_get(x_8, 0);
lean_dec(x_315);
x_286 = x_8;
x_287 = x_310;
goto block_309;
}
else
{
lean_dec(x_8);
x_286 = lean_box(0);
x_287 = x_310;
goto block_309;
}
block_309:
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; uint8_t x_305; 
x_288 = lean_ctor_get(x_173, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_173, 1);
lean_inc(x_289);
lean_dec_ref(x_173);
x_290 = lean_ctor_get(x_22, 1);
x_291 = lean_ctor_get(x_22, 2);
x_305 = !lean_is_exclusive(x_22);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_22, 4);
lean_dec(x_306);
x_307 = lean_ctor_get(x_22, 3);
lean_dec(x_307);
x_308 = lean_ctor_get(x_22, 0);
lean_dec(x_308);
x_292 = x_22;
x_293 = x_305;
goto block_304;
}
else
{
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_22);
x_292 = lean_box(0);
x_293 = x_305;
goto block_304;
}
block_304:
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_unsigned_to_nat(3u);
if (x_293 == 0)
{
lean_ctor_set(x_292, 4, x_21);
lean_ctor_set(x_292, 3, x_21);
lean_ctor_set(x_292, 2, x_20);
lean_ctor_set(x_292, 1, x_19);
lean_ctor_set(x_292, 0, x_28);
x_295 = x_292;
goto block_302;
}
else
{
lean_object* x_303; 
x_303 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_303, 0, x_28);
lean_ctor_set(x_303, 1, x_19);
lean_ctor_set(x_303, 2, x_20);
lean_ctor_set(x_303, 3, x_21);
lean_ctor_set(x_303, 4, x_21);
x_295 = x_303;
goto block_302;
}
block_302:
{
lean_object* x_296; 
if (x_172 == 0)
{
lean_ctor_set(x_171, 4, x_21);
lean_ctor_set(x_171, 3, x_21);
lean_ctor_set(x_171, 2, x_289);
lean_ctor_set(x_171, 1, x_288);
lean_ctor_set(x_171, 0, x_28);
x_296 = x_171;
goto block_300;
}
else
{
lean_object* x_301; 
x_301 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_301, 0, x_28);
lean_ctor_set(x_301, 1, x_288);
lean_ctor_set(x_301, 2, x_289);
lean_ctor_set(x_301, 3, x_21);
lean_ctor_set(x_301, 4, x_21);
x_296 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_297; 
if (x_287 == 0)
{
lean_ctor_set(x_286, 4, x_296);
lean_ctor_set(x_286, 3, x_295);
lean_ctor_set(x_286, 2, x_291);
lean_ctor_set(x_286, 1, x_290);
lean_ctor_set(x_286, 0, x_294);
x_297 = x_286;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_299, 0, x_294);
lean_ctor_set(x_299, 1, x_290);
lean_ctor_set(x_299, 2, x_291);
lean_ctor_set(x_299, 3, x_295);
lean_ctor_set(x_299, 4, x_296);
x_297 = x_299;
goto block_298;
}
block_298:
{
return x_297;
}
}
}
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_316 = lean_ctor_get(x_173, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_173, 1);
lean_inc(x_317);
lean_dec_ref(x_173);
x_318 = lean_unsigned_to_nat(2u);
if (x_172 == 0)
{
lean_ctor_set(x_171, 4, x_22);
lean_ctor_set(x_171, 3, x_8);
lean_ctor_set(x_171, 2, x_317);
lean_ctor_set(x_171, 1, x_316);
lean_ctor_set(x_171, 0, x_318);
x_319 = x_171;
goto block_320;
}
else
{
lean_object* x_321; 
x_321 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_316);
lean_ctor_set(x_321, 2, x_317);
lean_ctor_set(x_321, 3, x_8);
lean_ctor_set(x_321, 4, x_22);
x_319 = x_321;
goto block_320;
}
block_320:
{
return x_319;
}
}
}
}
}
}
}
else
{
return x_8;
}
}
else
{
return x_9;
}
}
else
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_17, 0);
lean_inc(x_329);
lean_dec_ref(x_17);
if (x_11 == 0)
{
lean_ctor_set(x_10, 2, x_329);
lean_ctor_set(x_10, 1, x_2);
x_330 = x_10;
goto block_331;
}
else
{
lean_object* x_332; 
x_332 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_332, 0, x_5);
lean_ctor_set(x_332, 1, x_2);
lean_ctor_set(x_332, 2, x_329);
lean_ctor_set(x_332, 3, x_8);
lean_ctor_set(x_332, 4, x_9);
x_330 = x_332;
goto block_331;
}
block_331:
{
return x_330;
}
}
}
default: 
{
lean_object* x_333; lean_object* x_334; 
lean_del_object(x_10);
lean_dec(x_5);
x_333 = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(x_1, x_2, x_3, x_9);
x_334 = l_Std_DTreeMap_Internal_Impl_balance___redArg(x_6, x_7, x_8, x_333);
return x_334;
}
}
}
}
else
{
lean_object* x_337; lean_object* x_338; 
lean_dec_ref(x_1);
x_337 = lean_box(0);
x_338 = lean_apply_1(x_3, x_337);
if (lean_obj_tag(x_338) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
x_340 = lean_unsigned_to_nat(1u);
x_341 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_2);
lean_ctor_set(x_341, 2, x_339);
lean_ctor_set(x_341, 3, x_4);
lean_ctor_set(x_341, 4, x_4);
return x_341;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_365; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_365 = !lean_is_exclusive(x_4);
if (x_365 == 0)
{
x_10 = x_4;
x_11 = x_365;
goto block_364;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = x_365;
goto block_364;
}
block_364:
{
lean_object* x_12; uint8_t x_13; 
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_6);
x_13 = lean_unbox(x_12);
switch (x_13) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_del_object(x_10);
lean_dec(x_5);
x_14 = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(x_1, x_2, x_3, x_8);
x_15 = l_Std_DTreeMap_Internal_Impl_balance_x21___redArg(x_6, x_7, x_14, x_9);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_7);
x_17 = lean_apply_1(x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_del_object(x_10);
lean_dec(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_8) == 0)
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
x_22 = lean_ctor_get(x_8, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
x_25 = lean_ctor_get(x_9, 2);
x_26 = lean_ctor_get(x_9, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_9, 4);
x_28 = lean_nat_dec_lt(x_18, x_23);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_182; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_182 = !lean_is_exclusive(x_8);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_ctor_get(x_8, 4);
lean_dec(x_183);
x_184 = lean_ctor_get(x_8, 3);
lean_dec(x_184);
x_185 = lean_ctor_get(x_8, 2);
lean_dec(x_185);
x_186 = lean_ctor_get(x_8, 1);
lean_dec(x_186);
x_187 = lean_ctor_get(x_8, 0);
lean_dec(x_187);
x_29 = x_8;
x_30 = x_182;
goto block_181;
}
else
{
lean_dec(x_8);
x_29 = lean_box(0);
x_30 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(x_19, x_20, x_21, x_22);
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec_ref(x_31);
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_mul(x_36, x_35);
x_38 = lean_nat_dec_lt(x_37, x_23);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_26);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_39, x_35);
x_41 = lean_nat_add(x_40, x_23);
lean_dec(x_40);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_9);
lean_ctor_set(x_29, 3, x_32);
lean_ctor_set(x_29, 2, x_34);
lean_ctor_set(x_29, 1, x_33);
lean_ctor_set(x_29, 0, x_41);
x_42 = x_29;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_33);
lean_ctor_set(x_44, 2, x_34);
lean_ctor_set(x_44, 3, x_32);
lean_ctor_set(x_44, 4, x_9);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
else
{
lean_object* x_45; uint8_t x_46; uint8_t x_107; 
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_107 = !lean_is_exclusive(x_9);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_9, 4);
lean_dec(x_108);
x_109 = lean_ctor_get(x_9, 3);
lean_dec(x_109);
x_110 = lean_ctor_get(x_9, 2);
lean_dec(x_110);
x_111 = lean_ctor_get(x_9, 1);
lean_dec(x_111);
x_112 = lean_ctor_get(x_9, 0);
lean_dec(x_112);
x_45 = x_9;
x_46 = x_107;
goto block_106;
}
else
{
lean_dec(x_9);
x_45 = lean_box(0);
x_46 = x_107;
goto block_106;
}
block_106:
{
if (lean_obj_tag(x_26) == 0)
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_47 = lean_ctor_get(x_26, 0);
x_48 = lean_ctor_get(x_26, 1);
x_49 = lean_ctor_get(x_26, 2);
x_50 = lean_ctor_get(x_26, 3);
x_51 = lean_ctor_get(x_26, 4);
x_52 = lean_ctor_get(x_27, 0);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_mul(x_53, x_52);
x_55 = lean_nat_dec_lt(x_47, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; uint8_t x_84; 
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_84 = !lean_is_exclusive(x_26);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_26, 4);
lean_dec(x_85);
x_86 = lean_ctor_get(x_26, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_26, 2);
lean_dec(x_87);
x_88 = lean_ctor_get(x_26, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_26, 0);
lean_dec(x_89);
x_56 = x_26;
x_57 = x_84;
goto block_83;
}
else
{
lean_dec(x_26);
x_56 = lean_box(0);
x_57 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_72; 
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_58, x_35);
x_60 = lean_nat_add(x_59, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_50, 0);
lean_inc(x_81);
x_72 = x_81;
goto block_80;
}
else
{
lean_object* x_82; 
x_82 = lean_unsigned_to_nat(0u);
x_72 = x_82;
goto block_80;
}
block_71:
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_nat_add(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_57 == 0)
{
lean_ctor_set(x_56, 4, x_27);
lean_ctor_set(x_56, 3, x_51);
lean_ctor_set(x_56, 2, x_25);
lean_ctor_set(x_56, 1, x_24);
lean_ctor_set(x_56, 0, x_64);
x_65 = x_56;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_24);
lean_ctor_set(x_70, 2, x_25);
lean_ctor_set(x_70, 3, x_51);
lean_ctor_set(x_70, 4, x_27);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_46 == 0)
{
lean_ctor_set(x_45, 4, x_65);
lean_ctor_set(x_45, 3, x_61);
lean_ctor_set(x_45, 2, x_49);
lean_ctor_set(x_45, 1, x_48);
lean_ctor_set(x_45, 0, x_60);
x_66 = x_45;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_48);
lean_ctor_set(x_68, 2, x_49);
lean_ctor_set(x_68, 3, x_61);
lean_ctor_set(x_68, 4, x_65);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
block_80:
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_nat_add(x_59, x_72);
lean_dec(x_72);
lean_dec(x_59);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_50);
lean_ctor_set(x_29, 3, x_32);
lean_ctor_set(x_29, 2, x_34);
lean_ctor_set(x_29, 1, x_33);
lean_ctor_set(x_29, 0, x_73);
x_74 = x_29;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_33);
lean_ctor_set(x_79, 2, x_34);
lean_ctor_set(x_79, 3, x_32);
lean_ctor_set(x_79, 4, x_50);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
x_75 = lean_nat_add(x_58, x_52);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_51, 0);
lean_inc(x_76);
x_61 = x_74;
x_62 = x_75;
x_63 = x_76;
goto block_71;
}
else
{
lean_object* x_77; 
x_77 = lean_unsigned_to_nat(0u);
x_61 = x_74;
x_62 = x_75;
x_63 = x_77;
goto block_71;
}
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_add(x_90, x_35);
x_92 = lean_nat_add(x_91, x_23);
lean_dec(x_23);
x_93 = lean_nat_add(x_91, x_47);
lean_dec(x_91);
if (x_46 == 0)
{
lean_ctor_set(x_45, 4, x_26);
lean_ctor_set(x_45, 3, x_32);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 0, x_93);
x_94 = x_45;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_93);
lean_ctor_set(x_99, 1, x_33);
lean_ctor_set(x_99, 2, x_34);
lean_ctor_set(x_99, 3, x_32);
lean_ctor_set(x_99, 4, x_26);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set(x_29, 3, x_94);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 0, x_92);
x_95 = x_29;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_24);
lean_ctor_set(x_97, 2, x_25);
lean_ctor_set(x_97, 3, x_94);
lean_ctor_set(x_97, 4, x_27);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_26);
lean_del_object(x_45);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_33);
lean_del_object(x_29);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_100 = lean_box(1);
x_101 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__3);
x_102 = l_panic___redArg(x_100, x_101);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_del_object(x_45);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_33);
lean_del_object(x_29);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_103 = lean_box(1);
x_104 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_minView_x21___redArg___closed__4);
x_105 = l_panic___redArg(x_103, x_104);
return x_105;
}
}
}
}
else
{
lean_inc(x_27);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_113; uint8_t x_114; uint8_t x_150; 
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_150 = !lean_is_exclusive(x_9);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_9, 4);
lean_dec(x_151);
x_152 = lean_ctor_get(x_9, 3);
lean_dec(x_152);
x_153 = lean_ctor_get(x_9, 2);
lean_dec(x_153);
x_154 = lean_ctor_get(x_9, 1);
lean_dec(x_154);
x_155 = lean_ctor_get(x_9, 0);
lean_dec(x_155);
x_113 = x_9;
x_114 = x_150;
goto block_149;
}
else
{
lean_dec(x_9);
x_113 = lean_box(0);
x_114 = x_150;
goto block_149;
}
block_149:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_31, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_31, 1);
lean_inc(x_116);
lean_dec_ref(x_31);
x_117 = lean_ctor_get(x_26, 0);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_118, x_23);
lean_dec(x_23);
x_120 = lean_nat_add(x_118, x_117);
if (x_114 == 0)
{
lean_ctor_set(x_113, 4, x_26);
lean_ctor_set(x_113, 3, x_32);
lean_ctor_set(x_113, 2, x_116);
lean_ctor_set(x_113, 1, x_115);
lean_ctor_set(x_113, 0, x_120);
x_121 = x_113;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_120);
lean_ctor_set(x_126, 1, x_115);
lean_ctor_set(x_126, 2, x_116);
lean_ctor_set(x_126, 3, x_32);
lean_ctor_set(x_126, 4, x_26);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set(x_29, 3, x_121);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 0, x_119);
x_122 = x_29;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_119);
lean_ctor_set(x_124, 1, x_24);
lean_ctor_set(x_124, 2, x_25);
lean_ctor_set(x_124, 3, x_121);
lean_ctor_set(x_124, 4, x_27);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_145; 
lean_dec(x_23);
x_127 = lean_ctor_get(x_31, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_31, 1);
lean_inc(x_128);
lean_dec_ref(x_31);
x_129 = lean_ctor_get(x_26, 1);
x_130 = lean_ctor_get(x_26, 2);
x_145 = !lean_is_exclusive(x_26);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_26, 4);
lean_dec(x_146);
x_147 = lean_ctor_get(x_26, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_26, 0);
lean_dec(x_148);
x_131 = x_26;
x_132 = x_145;
goto block_144;
}
else
{
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_26);
x_131 = lean_box(0);
x_132 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_unsigned_to_nat(3u);
x_134 = lean_unsigned_to_nat(1u);
if (x_132 == 0)
{
lean_ctor_set(x_131, 4, x_27);
lean_ctor_set(x_131, 3, x_27);
lean_ctor_set(x_131, 2, x_128);
lean_ctor_set(x_131, 1, x_127);
lean_ctor_set(x_131, 0, x_134);
x_135 = x_131;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_143, 0, x_134);
lean_ctor_set(x_143, 1, x_127);
lean_ctor_set(x_143, 2, x_128);
lean_ctor_set(x_143, 3, x_27);
lean_ctor_set(x_143, 4, x_27);
x_135 = x_143;
goto block_142;
}
block_142:
{
lean_object* x_136; 
if (x_114 == 0)
{
lean_ctor_set(x_113, 3, x_27);
lean_ctor_set(x_113, 0, x_134);
x_136 = x_113;
goto block_140;
}
else
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_141, 0, x_134);
lean_ctor_set(x_141, 1, x_24);
lean_ctor_set(x_141, 2, x_25);
lean_ctor_set(x_141, 3, x_27);
lean_ctor_set(x_141, 4, x_27);
x_136 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_137; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_136);
lean_ctor_set(x_29, 3, x_135);
lean_ctor_set(x_29, 2, x_130);
lean_ctor_set(x_29, 1, x_129);
lean_ctor_set(x_29, 0, x_133);
x_137 = x_29;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_129);
lean_ctor_set(x_139, 2, x_130);
lean_ctor_set(x_139, 3, x_135);
lean_ctor_set(x_139, 4, x_136);
x_137 = x_139;
goto block_138;
}
block_138:
{
return x_137;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_156; uint8_t x_157; uint8_t x_169; 
lean_inc(x_25);
lean_inc(x_24);
x_169 = !lean_is_exclusive(x_9);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_9, 4);
lean_dec(x_170);
x_171 = lean_ctor_get(x_9, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_9, 2);
lean_dec(x_172);
x_173 = lean_ctor_get(x_9, 1);
lean_dec(x_173);
x_174 = lean_ctor_get(x_9, 0);
lean_dec(x_174);
x_156 = x_9;
x_157 = x_169;
goto block_168;
}
else
{
lean_dec(x_9);
x_156 = lean_box(0);
x_157 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_31, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_31, 1);
lean_inc(x_159);
lean_dec_ref(x_31);
x_160 = lean_unsigned_to_nat(3u);
x_161 = lean_unsigned_to_nat(1u);
if (x_157 == 0)
{
lean_ctor_set(x_156, 4, x_26);
lean_ctor_set(x_156, 2, x_159);
lean_ctor_set(x_156, 1, x_158);
lean_ctor_set(x_156, 0, x_161);
x_162 = x_156;
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_161);
lean_ctor_set(x_167, 1, x_158);
lean_ctor_set(x_167, 2, x_159);
lean_ctor_set(x_167, 3, x_26);
lean_ctor_set(x_167, 4, x_26);
x_162 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_163; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set(x_29, 3, x_162);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 0, x_160);
x_163 = x_29;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_24);
lean_ctor_set(x_165, 2, x_25);
lean_ctor_set(x_165, 3, x_162);
lean_ctor_set(x_165, 4, x_27);
x_163 = x_165;
goto block_164;
}
block_164:
{
return x_163;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_31, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_31, 1);
lean_inc(x_176);
lean_dec_ref(x_31);
x_177 = lean_unsigned_to_nat(2u);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_9);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 2, x_176);
lean_ctor_set(x_29, 1, x_175);
lean_ctor_set(x_29, 0, x_177);
x_178 = x_29;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_175);
lean_ctor_set(x_180, 2, x_176);
lean_ctor_set(x_180, 3, x_27);
lean_ctor_set(x_180, 4, x_9);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
}
}
else
{
lean_object* x_188; uint8_t x_189; uint8_t x_352; 
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
x_352 = !lean_is_exclusive(x_9);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_353 = lean_ctor_get(x_9, 4);
lean_dec(x_353);
x_354 = lean_ctor_get(x_9, 3);
lean_dec(x_354);
x_355 = lean_ctor_get(x_9, 2);
lean_dec(x_355);
x_356 = lean_ctor_get(x_9, 1);
lean_dec(x_356);
x_357 = lean_ctor_get(x_9, 0);
lean_dec(x_357);
x_188 = x_9;
x_189 = x_352;
goto block_351;
}
else
{
lean_dec(x_9);
x_188 = lean_box(0);
x_189 = x_352;
goto block_351;
}
block_351:
{
lean_object* x_190; lean_object* x_191; 
x_190 = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(x_24, x_25, x_26, x_27);
x_191 = lean_ctor_get(x_190, 2);
lean_inc(x_191);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_dec_ref(x_190);
x_194 = lean_ctor_get(x_191, 0);
x_195 = lean_unsigned_to_nat(3u);
x_196 = lean_nat_mul(x_195, x_194);
x_197 = lean_nat_dec_lt(x_196, x_18);
lean_dec(x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_22);
x_198 = lean_unsigned_to_nat(1u);
x_199 = lean_nat_add(x_198, x_18);
x_200 = lean_nat_add(x_199, x_194);
lean_dec(x_199);
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_191);
lean_ctor_set(x_188, 3, x_8);
lean_ctor_set(x_188, 2, x_193);
lean_ctor_set(x_188, 1, x_192);
lean_ctor_set(x_188, 0, x_200);
x_201 = x_188;
goto block_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_192);
lean_ctor_set(x_203, 2, x_193);
lean_ctor_set(x_203, 3, x_8);
lean_ctor_set(x_203, 4, x_191);
x_201 = x_203;
goto block_202;
}
block_202:
{
return x_201;
}
}
else
{
lean_object* x_204; uint8_t x_205; uint8_t x_277; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_277 = !lean_is_exclusive(x_8);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_278 = lean_ctor_get(x_8, 4);
lean_dec(x_278);
x_279 = lean_ctor_get(x_8, 3);
lean_dec(x_279);
x_280 = lean_ctor_get(x_8, 2);
lean_dec(x_280);
x_281 = lean_ctor_get(x_8, 1);
lean_dec(x_281);
x_282 = lean_ctor_get(x_8, 0);
lean_dec(x_282);
x_204 = x_8;
x_205 = x_277;
goto block_276;
}
else
{
lean_dec(x_8);
x_204 = lean_box(0);
x_205 = x_277;
goto block_276;
}
block_276:
{
if (lean_obj_tag(x_21) == 0)
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_206 = lean_ctor_get(x_21, 0);
x_207 = lean_ctor_get(x_22, 0);
x_208 = lean_ctor_get(x_22, 1);
x_209 = lean_ctor_get(x_22, 2);
x_210 = lean_ctor_get(x_22, 3);
x_211 = lean_ctor_get(x_22, 4);
x_212 = lean_unsigned_to_nat(2u);
x_213 = lean_nat_mul(x_212, x_206);
x_214 = lean_nat_dec_lt(x_207, x_213);
lean_dec(x_213);
if (x_214 == 0)
{
lean_object* x_215; uint8_t x_216; uint8_t x_253; 
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_del_object(x_204);
x_253 = !lean_is_exclusive(x_22);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_254 = lean_ctor_get(x_22, 4);
lean_dec(x_254);
x_255 = lean_ctor_get(x_22, 3);
lean_dec(x_255);
x_256 = lean_ctor_get(x_22, 2);
lean_dec(x_256);
x_257 = lean_ctor_get(x_22, 1);
lean_dec(x_257);
x_258 = lean_ctor_get(x_22, 0);
lean_dec(x_258);
x_215 = x_22;
x_216 = x_253;
goto block_252;
}
else
{
lean_dec(x_22);
x_215 = lean_box(0);
x_216 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_240; lean_object* x_241; 
x_217 = lean_unsigned_to_nat(1u);
x_218 = lean_nat_add(x_217, x_18);
lean_dec(x_18);
x_219 = lean_nat_add(x_218, x_194);
lean_dec(x_218);
x_240 = lean_nat_add(x_217, x_206);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_210, 0);
lean_inc(x_250);
x_241 = x_250;
goto block_249;
}
else
{
lean_object* x_251; 
x_251 = lean_unsigned_to_nat(0u);
x_241 = x_251;
goto block_249;
}
block_239:
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_nat_add(x_221, x_222);
lean_dec(x_222);
lean_dec(x_221);
lean_inc_ref(x_191);
if (x_216 == 0)
{
lean_ctor_set(x_215, 4, x_191);
lean_ctor_set(x_215, 3, x_211);
lean_ctor_set(x_215, 2, x_193);
lean_ctor_set(x_215, 1, x_192);
lean_ctor_set(x_215, 0, x_223);
x_224 = x_215;
goto block_237;
}
else
{
lean_object* x_238; 
x_238 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_238, 0, x_223);
lean_ctor_set(x_238, 1, x_192);
lean_ctor_set(x_238, 2, x_193);
lean_ctor_set(x_238, 3, x_211);
lean_ctor_set(x_238, 4, x_191);
x_224 = x_238;
goto block_237;
}
block_237:
{
lean_object* x_225; uint8_t x_226; uint8_t x_231; 
x_231 = !lean_is_exclusive(x_191);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = lean_ctor_get(x_191, 4);
lean_dec(x_232);
x_233 = lean_ctor_get(x_191, 3);
lean_dec(x_233);
x_234 = lean_ctor_get(x_191, 2);
lean_dec(x_234);
x_235 = lean_ctor_get(x_191, 1);
lean_dec(x_235);
x_236 = lean_ctor_get(x_191, 0);
lean_dec(x_236);
x_225 = x_191;
x_226 = x_231;
goto block_230;
}
else
{
lean_dec(x_191);
x_225 = lean_box(0);
x_226 = x_231;
goto block_230;
}
block_230:
{
lean_object* x_227; 
if (x_226 == 0)
{
lean_ctor_set(x_225, 4, x_224);
lean_ctor_set(x_225, 3, x_220);
lean_ctor_set(x_225, 2, x_209);
lean_ctor_set(x_225, 1, x_208);
lean_ctor_set(x_225, 0, x_219);
x_227 = x_225;
goto block_228;
}
else
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_229, 0, x_219);
lean_ctor_set(x_229, 1, x_208);
lean_ctor_set(x_229, 2, x_209);
lean_ctor_set(x_229, 3, x_220);
lean_ctor_set(x_229, 4, x_224);
x_227 = x_229;
goto block_228;
}
block_228:
{
return x_227;
}
}
}
}
block_249:
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_nat_add(x_240, x_241);
lean_dec(x_241);
lean_dec(x_240);
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_210);
lean_ctor_set(x_188, 3, x_21);
lean_ctor_set(x_188, 2, x_20);
lean_ctor_set(x_188, 1, x_19);
lean_ctor_set(x_188, 0, x_242);
x_243 = x_188;
goto block_247;
}
else
{
lean_object* x_248; 
x_248 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_248, 0, x_242);
lean_ctor_set(x_248, 1, x_19);
lean_ctor_set(x_248, 2, x_20);
lean_ctor_set(x_248, 3, x_21);
lean_ctor_set(x_248, 4, x_210);
x_243 = x_248;
goto block_247;
}
block_247:
{
lean_object* x_244; 
x_244 = lean_nat_add(x_217, x_194);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_211, 0);
lean_inc(x_245);
x_220 = x_243;
x_221 = x_244;
x_222 = x_245;
goto block_239;
}
else
{
lean_object* x_246; 
x_246 = lean_unsigned_to_nat(0u);
x_220 = x_243;
x_221 = x_244;
x_222 = x_246;
goto block_239;
}
}
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_259 = lean_unsigned_to_nat(1u);
x_260 = lean_nat_add(x_259, x_18);
lean_dec(x_18);
x_261 = lean_nat_add(x_260, x_194);
lean_dec(x_260);
x_262 = lean_nat_add(x_259, x_194);
x_263 = lean_nat_add(x_262, x_207);
lean_dec(x_262);
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_191);
lean_ctor_set(x_188, 3, x_22);
lean_ctor_set(x_188, 2, x_193);
lean_ctor_set(x_188, 1, x_192);
lean_ctor_set(x_188, 0, x_263);
x_264 = x_188;
goto block_268;
}
else
{
lean_object* x_269; 
x_269 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_269, 0, x_263);
lean_ctor_set(x_269, 1, x_192);
lean_ctor_set(x_269, 2, x_193);
lean_ctor_set(x_269, 3, x_22);
lean_ctor_set(x_269, 4, x_191);
x_264 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_265; 
if (x_205 == 0)
{
lean_ctor_set(x_204, 4, x_264);
lean_ctor_set(x_204, 0, x_261);
x_265 = x_204;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_267, 0, x_261);
lean_ctor_set(x_267, 1, x_19);
lean_ctor_set(x_267, 2, x_20);
lean_ctor_set(x_267, 3, x_21);
lean_ctor_set(x_267, 4, x_264);
x_265 = x_267;
goto block_266;
}
block_266:
{
return x_265;
}
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec_ref(x_21);
lean_del_object(x_204);
lean_dec(x_193);
lean_dec(x_192);
lean_dec_ref(x_191);
lean_del_object(x_188);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_270 = lean_box(1);
x_271 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__2);
x_272 = l_panic___redArg(x_270, x_271);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_del_object(x_204);
lean_dec(x_193);
lean_dec(x_192);
lean_dec_ref(x_191);
lean_del_object(x_188);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_273 = lean_box(1);
x_274 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg___closed__3);
x_275 = l_panic___redArg(x_273, x_274);
return x_275;
}
}
}
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_283; uint8_t x_284; uint8_t x_308; 
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_308 = !lean_is_exclusive(x_8);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_309 = lean_ctor_get(x_8, 4);
lean_dec(x_309);
x_310 = lean_ctor_get(x_8, 3);
lean_dec(x_310);
x_311 = lean_ctor_get(x_8, 2);
lean_dec(x_311);
x_312 = lean_ctor_get(x_8, 1);
lean_dec(x_312);
x_313 = lean_ctor_get(x_8, 0);
lean_dec(x_313);
x_283 = x_8;
x_284 = x_308;
goto block_307;
}
else
{
lean_dec(x_8);
x_283 = lean_box(0);
x_284 = x_308;
goto block_307;
}
block_307:
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_285 = lean_ctor_get(x_190, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_190, 1);
lean_inc(x_286);
lean_dec_ref(x_190);
x_287 = lean_ctor_get(x_22, 0);
x_288 = lean_unsigned_to_nat(1u);
x_289 = lean_nat_add(x_288, x_18);
lean_dec(x_18);
x_290 = lean_nat_add(x_288, x_287);
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_191);
lean_ctor_set(x_188, 3, x_22);
lean_ctor_set(x_188, 2, x_286);
lean_ctor_set(x_188, 1, x_285);
lean_ctor_set(x_188, 0, x_290);
x_291 = x_188;
goto block_295;
}
else
{
lean_object* x_296; 
x_296 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_296, 0, x_290);
lean_ctor_set(x_296, 1, x_285);
lean_ctor_set(x_296, 2, x_286);
lean_ctor_set(x_296, 3, x_22);
lean_ctor_set(x_296, 4, x_191);
x_291 = x_296;
goto block_295;
}
block_295:
{
lean_object* x_292; 
if (x_284 == 0)
{
lean_ctor_set(x_283, 4, x_291);
lean_ctor_set(x_283, 0, x_289);
x_292 = x_283;
goto block_293;
}
else
{
lean_object* x_294; 
x_294 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_294, 0, x_289);
lean_ctor_set(x_294, 1, x_19);
lean_ctor_set(x_294, 2, x_20);
lean_ctor_set(x_294, 3, x_21);
lean_ctor_set(x_294, 4, x_291);
x_292 = x_294;
goto block_293;
}
block_293:
{
return x_292;
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_18);
x_297 = lean_ctor_get(x_190, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_190, 1);
lean_inc(x_298);
lean_dec_ref(x_190);
x_299 = lean_unsigned_to_nat(3u);
x_300 = lean_unsigned_to_nat(1u);
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_22);
lean_ctor_set(x_188, 3, x_22);
lean_ctor_set(x_188, 2, x_298);
lean_ctor_set(x_188, 1, x_297);
lean_ctor_set(x_188, 0, x_300);
x_301 = x_188;
goto block_305;
}
else
{
lean_object* x_306; 
x_306 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_306, 0, x_300);
lean_ctor_set(x_306, 1, x_297);
lean_ctor_set(x_306, 2, x_298);
lean_ctor_set(x_306, 3, x_22);
lean_ctor_set(x_306, 4, x_22);
x_301 = x_306;
goto block_305;
}
block_305:
{
lean_object* x_302; 
if (x_284 == 0)
{
lean_ctor_set(x_283, 4, x_301);
lean_ctor_set(x_283, 0, x_299);
x_302 = x_283;
goto block_303;
}
else
{
lean_object* x_304; 
x_304 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_304, 0, x_299);
lean_ctor_set(x_304, 1, x_19);
lean_ctor_set(x_304, 2, x_20);
lean_ctor_set(x_304, 3, x_21);
lean_ctor_set(x_304, 4, x_301);
x_302 = x_304;
goto block_303;
}
block_303:
{
return x_302;
}
}
}
}
}
else
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_314; uint8_t x_315; uint8_t x_339; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_339 = !lean_is_exclusive(x_8);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_340 = lean_ctor_get(x_8, 4);
lean_dec(x_340);
x_341 = lean_ctor_get(x_8, 3);
lean_dec(x_341);
x_342 = lean_ctor_get(x_8, 2);
lean_dec(x_342);
x_343 = lean_ctor_get(x_8, 1);
lean_dec(x_343);
x_344 = lean_ctor_get(x_8, 0);
lean_dec(x_344);
x_314 = x_8;
x_315 = x_339;
goto block_338;
}
else
{
lean_dec(x_8);
x_314 = lean_box(0);
x_315 = x_339;
goto block_338;
}
block_338:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; uint8_t x_334; 
x_316 = lean_ctor_get(x_190, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_190, 1);
lean_inc(x_317);
lean_dec_ref(x_190);
x_318 = lean_ctor_get(x_22, 1);
x_319 = lean_ctor_get(x_22, 2);
x_334 = !lean_is_exclusive(x_22);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_22, 4);
lean_dec(x_335);
x_336 = lean_ctor_get(x_22, 3);
lean_dec(x_336);
x_337 = lean_ctor_get(x_22, 0);
lean_dec(x_337);
x_320 = x_22;
x_321 = x_334;
goto block_333;
}
else
{
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_22);
x_320 = lean_box(0);
x_321 = x_334;
goto block_333;
}
block_333:
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_unsigned_to_nat(3u);
x_323 = lean_unsigned_to_nat(1u);
if (x_321 == 0)
{
lean_ctor_set(x_320, 4, x_21);
lean_ctor_set(x_320, 3, x_21);
lean_ctor_set(x_320, 2, x_20);
lean_ctor_set(x_320, 1, x_19);
lean_ctor_set(x_320, 0, x_323);
x_324 = x_320;
goto block_331;
}
else
{
lean_object* x_332; 
x_332 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_332, 0, x_323);
lean_ctor_set(x_332, 1, x_19);
lean_ctor_set(x_332, 2, x_20);
lean_ctor_set(x_332, 3, x_21);
lean_ctor_set(x_332, 4, x_21);
x_324 = x_332;
goto block_331;
}
block_331:
{
lean_object* x_325; 
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_21);
lean_ctor_set(x_188, 3, x_21);
lean_ctor_set(x_188, 2, x_317);
lean_ctor_set(x_188, 1, x_316);
lean_ctor_set(x_188, 0, x_323);
x_325 = x_188;
goto block_329;
}
else
{
lean_object* x_330; 
x_330 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_330, 0, x_323);
lean_ctor_set(x_330, 1, x_316);
lean_ctor_set(x_330, 2, x_317);
lean_ctor_set(x_330, 3, x_21);
lean_ctor_set(x_330, 4, x_21);
x_325 = x_330;
goto block_329;
}
block_329:
{
lean_object* x_326; 
if (x_315 == 0)
{
lean_ctor_set(x_314, 4, x_325);
lean_ctor_set(x_314, 3, x_324);
lean_ctor_set(x_314, 2, x_319);
lean_ctor_set(x_314, 1, x_318);
lean_ctor_set(x_314, 0, x_322);
x_326 = x_314;
goto block_327;
}
else
{
lean_object* x_328; 
x_328 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_328, 0, x_322);
lean_ctor_set(x_328, 1, x_318);
lean_ctor_set(x_328, 2, x_319);
lean_ctor_set(x_328, 3, x_324);
lean_ctor_set(x_328, 4, x_325);
x_326 = x_328;
goto block_327;
}
block_327:
{
return x_326;
}
}
}
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_345 = lean_ctor_get(x_190, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_190, 1);
lean_inc(x_346);
lean_dec_ref(x_190);
x_347 = lean_unsigned_to_nat(2u);
if (x_189 == 0)
{
lean_ctor_set(x_188, 4, x_22);
lean_ctor_set(x_188, 3, x_8);
lean_ctor_set(x_188, 2, x_346);
lean_ctor_set(x_188, 1, x_345);
lean_ctor_set(x_188, 0, x_347);
x_348 = x_188;
goto block_349;
}
else
{
lean_object* x_350; 
x_350 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_345);
lean_ctor_set(x_350, 2, x_346);
lean_ctor_set(x_350, 3, x_8);
lean_ctor_set(x_350, 4, x_22);
x_348 = x_350;
goto block_349;
}
block_349:
{
return x_348;
}
}
}
}
}
}
}
else
{
return x_8;
}
}
else
{
return x_9;
}
}
else
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_17, 0);
lean_inc(x_358);
lean_dec_ref(x_17);
if (x_11 == 0)
{
lean_ctor_set(x_10, 2, x_358);
lean_ctor_set(x_10, 1, x_2);
x_359 = x_10;
goto block_360;
}
else
{
lean_object* x_361; 
x_361 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_361, 0, x_5);
lean_ctor_set(x_361, 1, x_2);
lean_ctor_set(x_361, 2, x_358);
lean_ctor_set(x_361, 3, x_8);
lean_ctor_set(x_361, 4, x_9);
x_359 = x_361;
goto block_360;
}
block_360:
{
return x_359;
}
}
}
default: 
{
lean_object* x_362; lean_object* x_363; 
lean_del_object(x_10);
lean_dec(x_5);
x_362 = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(x_1, x_2, x_3, x_9);
x_363 = l_Std_DTreeMap_Internal_Impl_balance_x21___redArg(x_6, x_7, x_8, x_362);
return x_363;
}
}
}
}
else
{
lean_object* x_366; lean_object* x_367; 
lean_dec_ref(x_1);
x_366 = lean_box(0);
x_367 = lean_apply_1(x_3, x_366);
if (lean_obj_tag(x_367) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
lean_dec_ref(x_367);
x_369 = lean_unsigned_to_nat(1u);
x_370 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_2);
lean_ctor_set(x_370, 2, x_368);
lean_ctor_set(x_370, 3, x_4);
lean_ctor_set(x_370, 4, x_4);
return x_370;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_27; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
x_10 = x_4;
x_11 = x_27;
goto block_26;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_12; uint8_t x_13; 
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_6);
x_13 = lean_unbox(x_12);
switch (x_13) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(x_1, x_2, x_3, x_8);
if (x_11 == 0)
{
lean_ctor_set(x_10, 3, x_14);
x_15 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_9);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
case 1:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_18 = lean_apply_1(x_3, x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 2, x_18);
lean_ctor_set(x_10, 1, x_2);
x_19 = x_10;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_8);
lean_ctor_set(x_21, 4, x_9);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
default: 
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(x_1, x_2, x_3, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_22);
x_23 = x_10;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_6);
lean_ctor_set(x_25, 2, x_7);
lean_ctor_set(x_25, 3, x_8);
lean_ctor_set(x_25, 4, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_4, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l___private_Std_Data_DTreeMap_Internal_Operations_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_mergeWith___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_6 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_4);
x_7 = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(x_2, x_4, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_mergeWith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_mergeWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_3);
x_9 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_mergeWith_x21___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_6 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_4);
x_7 = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(x_2, x_4, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_mergeWith_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_mergeWith_x21___redArg___lam__1), 5, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_mergeWith_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_mergeWith_x21___redArg___lam__1), 5, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
x_8 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_7, x_5, x_6);
return x_8;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Balancing(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Queries(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Operations(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DTreeMap_Internal_Balancing(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Queries(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Control(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Internal_Operations(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Internal_Balancing(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Internal_Queries(uint8_t builtin);
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Internal_Operations(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Internal_Balancing(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Internal_Queries(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Operations(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Internal_Operations(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Internal_Operations(builtin);
}
#ifdef __cplusplus
}
#endif
