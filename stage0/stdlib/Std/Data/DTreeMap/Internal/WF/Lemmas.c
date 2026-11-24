// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.WF.Lemmas
// Imports: public import Std.Data.DTreeMap.Internal.Model import all Std.Data.Internal.List.Associative import Init.Data.List.Impl import Init.Data.Nat.Internal.Linear import Init.Data.Option.List import Init.Data.Subtype.Basic
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filterMap_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1(lean_object* v_00_u03b1_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter___redArg(lean_object* v_l_7_, lean_object* v_h__1_8_, lean_object* v_h__2_9_){
_start:
{
if (lean_obj_tag(v_l_7_) == 0)
{
lean_object* v_size_10_; lean_object* v_k_11_; lean_object* v_v_12_; lean_object* v_l_13_; lean_object* v_r_14_; lean_object* v___x_15_; 
lean_dec(v_h__1_8_);
v_size_10_ = lean_ctor_get(v_l_7_, 0);
lean_inc(v_size_10_);
v_k_11_ = lean_ctor_get(v_l_7_, 1);
lean_inc(v_k_11_);
v_v_12_ = lean_ctor_get(v_l_7_, 2);
lean_inc(v_v_12_);
v_l_13_ = lean_ctor_get(v_l_7_, 3);
lean_inc(v_l_13_);
v_r_14_ = lean_ctor_get(v_l_7_, 4);
lean_inc(v_r_14_);
lean_dec_ref_known(v_l_7_, 5);
v___x_15_ = lean_apply_5(v_h__2_9_, v_size_10_, v_k_11_, v_v_12_, v_l_13_, v_r_14_);
return v___x_15_;
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v_h__2_9_);
v___x_16_ = lean_box(0);
v___x_17_ = lean_apply_1(v_h__1_8_, v___x_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter(lean_object* v_00_u03b1_18_, lean_object* v_00_u03b2_19_, lean_object* v_motive_20_, lean_object* v_l_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
if (lean_obj_tag(v_l_21_) == 0)
{
lean_object* v_size_24_; lean_object* v_k_25_; lean_object* v_v_26_; lean_object* v_l_27_; lean_object* v_r_28_; lean_object* v___x_29_; 
lean_dec(v_h__1_22_);
v_size_24_ = lean_ctor_get(v_l_21_, 0);
lean_inc(v_size_24_);
v_k_25_ = lean_ctor_get(v_l_21_, 1);
lean_inc(v_k_25_);
v_v_26_ = lean_ctor_get(v_l_21_, 2);
lean_inc(v_v_26_);
v_l_27_ = lean_ctor_get(v_l_21_, 3);
lean_inc(v_l_27_);
v_r_28_ = lean_ctor_get(v_l_21_, 4);
lean_inc(v_r_28_);
lean_dec_ref_known(v_l_21_, 5);
v___x_29_ = lean_apply_5(v_h__2_23_, v_size_24_, v_k_25_, v_v_26_, v_l_27_, v_r_28_);
return v___x_29_;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; 
lean_dec(v_h__2_23_);
v___x_30_ = lean_box(0);
v___x_31_ = lean_apply_1(v_h__1_22_, v___x_30_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(lean_object* v_r_32_, lean_object* v_h__1_33_, lean_object* v_h__2_34_){
_start:
{
if (lean_obj_tag(v_r_32_) == 0)
{
lean_object* v_size_35_; lean_object* v_k_36_; lean_object* v_v_37_; lean_object* v_l_38_; lean_object* v_r_39_; lean_object* v___x_40_; 
lean_dec(v_h__1_33_);
v_size_35_ = lean_ctor_get(v_r_32_, 0);
lean_inc(v_size_35_);
v_k_36_ = lean_ctor_get(v_r_32_, 1);
lean_inc(v_k_36_);
v_v_37_ = lean_ctor_get(v_r_32_, 2);
lean_inc(v_v_37_);
v_l_38_ = lean_ctor_get(v_r_32_, 3);
lean_inc(v_l_38_);
v_r_39_ = lean_ctor_get(v_r_32_, 4);
lean_inc(v_r_39_);
lean_dec_ref_known(v_r_32_, 5);
v___x_40_ = lean_apply_6(v_h__2_34_, v_size_35_, v_k_36_, v_v_37_, v_l_38_, v_r_39_, lean_box(0));
return v___x_40_;
}
else
{
lean_object* v___x_41_; 
lean_dec(v_h__2_34_);
v___x_41_ = lean_apply_1(v_h__1_33_, lean_box(0));
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(lean_object* v_00_u03b1_42_, lean_object* v_00_u03b2_43_, lean_object* v_l_44_, lean_object* v_motive_45_, lean_object* v_r_46_, lean_object* v_h_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_){
_start:
{
if (lean_obj_tag(v_r_46_) == 0)
{
lean_object* v_size_50_; lean_object* v_k_51_; lean_object* v_v_52_; lean_object* v_l_53_; lean_object* v_r_54_; lean_object* v___x_55_; 
lean_dec(v_h__1_48_);
v_size_50_ = lean_ctor_get(v_r_46_, 0);
lean_inc(v_size_50_);
v_k_51_ = lean_ctor_get(v_r_46_, 1);
lean_inc(v_k_51_);
v_v_52_ = lean_ctor_get(v_r_46_, 2);
lean_inc(v_v_52_);
v_l_53_ = lean_ctor_get(v_r_46_, 3);
lean_inc(v_l_53_);
v_r_54_ = lean_ctor_get(v_r_46_, 4);
lean_inc(v_r_54_);
lean_dec_ref_known(v_r_46_, 5);
v___x_55_ = lean_apply_6(v_h__2_49_, v_size_50_, v_k_51_, v_v_52_, v_l_53_, v_r_54_, lean_box(0));
return v___x_55_;
}
else
{
lean_object* v___x_56_; 
lean_dec(v_h__2_49_);
v___x_56_ = lean_apply_1(v_h__1_48_, lean_box(0));
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___boxed(lean_object* v_00_u03b1_57_, lean_object* v_00_u03b2_58_, lean_object* v_l_59_, lean_object* v_motive_60_, lean_object* v_r_61_, lean_object* v_h_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(v_00_u03b1_57_, v_00_u03b2_58_, v_l_59_, v_motive_60_, v_r_61_, v_h_62_, v_h__1_63_, v_h__2_64_);
lean_dec(v_l_59_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(lean_object* v_l_66_, lean_object* v_h__1_67_, lean_object* v_h__2_68_){
_start:
{
if (lean_obj_tag(v_l_66_) == 0)
{
lean_object* v_size_69_; lean_object* v_k_70_; lean_object* v_v_71_; lean_object* v_l_72_; lean_object* v_r_73_; lean_object* v___x_74_; 
lean_dec(v_h__1_67_);
v_size_69_ = lean_ctor_get(v_l_66_, 0);
lean_inc(v_size_69_);
v_k_70_ = lean_ctor_get(v_l_66_, 1);
lean_inc(v_k_70_);
v_v_71_ = lean_ctor_get(v_l_66_, 2);
lean_inc(v_v_71_);
v_l_72_ = lean_ctor_get(v_l_66_, 3);
lean_inc(v_l_72_);
v_r_73_ = lean_ctor_get(v_l_66_, 4);
lean_inc(v_r_73_);
lean_dec_ref_known(v_l_66_, 5);
v___x_74_ = lean_apply_7(v_h__2_68_, v_size_69_, v_k_70_, v_v_71_, v_l_72_, v_r_73_, lean_box(0), lean_box(0));
return v___x_74_;
}
else
{
lean_object* v___x_75_; 
lean_dec(v_h__2_68_);
v___x_75_ = lean_apply_2(v_h__1_67_, lean_box(0), lean_box(0));
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_r_78_, lean_object* v_motive_79_, lean_object* v_l_80_, lean_object* v_h_81_, lean_object* v_h_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_){
_start:
{
if (lean_obj_tag(v_l_80_) == 0)
{
lean_object* v_size_85_; lean_object* v_k_86_; lean_object* v_v_87_; lean_object* v_l_88_; lean_object* v_r_89_; lean_object* v___x_90_; 
lean_dec(v_h__1_83_);
v_size_85_ = lean_ctor_get(v_l_80_, 0);
lean_inc(v_size_85_);
v_k_86_ = lean_ctor_get(v_l_80_, 1);
lean_inc(v_k_86_);
v_v_87_ = lean_ctor_get(v_l_80_, 2);
lean_inc(v_v_87_);
v_l_88_ = lean_ctor_get(v_l_80_, 3);
lean_inc(v_l_88_);
v_r_89_ = lean_ctor_get(v_l_80_, 4);
lean_inc(v_r_89_);
lean_dec_ref_known(v_l_80_, 5);
v___x_90_ = lean_apply_7(v_h__2_84_, v_size_85_, v_k_86_, v_v_87_, v_l_88_, v_r_89_, lean_box(0), lean_box(0));
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
lean_dec(v_h__2_84_);
v___x_91_ = lean_apply_2(v_h__1_83_, lean_box(0), lean_box(0));
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___boxed(lean_object* v_00_u03b1_92_, lean_object* v_00_u03b2_93_, lean_object* v_r_94_, lean_object* v_motive_95_, lean_object* v_l_96_, lean_object* v_h_97_, lean_object* v_h_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(v_00_u03b1_92_, v_00_u03b2_93_, v_r_94_, v_motive_95_, v_l_96_, v_h_97_, v_h_98_, v_h__1_99_, v_h__2_100_);
lean_dec(v_r_94_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object* v_l_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_){
_start:
{
if (lean_obj_tag(v_l_102_) == 0)
{
lean_object* v_size_105_; lean_object* v_k_106_; lean_object* v_v_107_; lean_object* v_l_108_; lean_object* v_r_109_; lean_object* v___x_110_; 
lean_dec(v_h__1_103_);
v_size_105_ = lean_ctor_get(v_l_102_, 0);
lean_inc(v_size_105_);
v_k_106_ = lean_ctor_get(v_l_102_, 1);
lean_inc(v_k_106_);
v_v_107_ = lean_ctor_get(v_l_102_, 2);
lean_inc(v_v_107_);
v_l_108_ = lean_ctor_get(v_l_102_, 3);
lean_inc(v_l_108_);
v_r_109_ = lean_ctor_get(v_l_102_, 4);
lean_inc(v_r_109_);
lean_dec_ref_known(v_l_102_, 5);
v___x_110_ = lean_apply_7(v_h__2_104_, v_size_105_, v_k_106_, v_v_107_, v_l_108_, v_r_109_, lean_box(0), lean_box(0));
return v___x_110_;
}
else
{
lean_object* v___x_111_; 
lean_dec(v_h__2_104_);
v___x_111_ = lean_apply_2(v_h__1_103_, lean_box(0), lean_box(0));
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object* v_00_u03b1_112_, lean_object* v_00_u03b2_113_, lean_object* v_r_114_, lean_object* v_motive_115_, lean_object* v_l_116_, lean_object* v_hl_117_, lean_object* v_hlr_118_, lean_object* v_h__1_119_, lean_object* v_h__2_120_){
_start:
{
if (lean_obj_tag(v_l_116_) == 0)
{
lean_object* v_size_121_; lean_object* v_k_122_; lean_object* v_v_123_; lean_object* v_l_124_; lean_object* v_r_125_; lean_object* v___x_126_; 
lean_dec(v_h__1_119_);
v_size_121_ = lean_ctor_get(v_l_116_, 0);
lean_inc(v_size_121_);
v_k_122_ = lean_ctor_get(v_l_116_, 1);
lean_inc(v_k_122_);
v_v_123_ = lean_ctor_get(v_l_116_, 2);
lean_inc(v_v_123_);
v_l_124_ = lean_ctor_get(v_l_116_, 3);
lean_inc(v_l_124_);
v_r_125_ = lean_ctor_get(v_l_116_, 4);
lean_inc(v_r_125_);
lean_dec_ref_known(v_l_116_, 5);
v___x_126_ = lean_apply_7(v_h__2_120_, v_size_121_, v_k_122_, v_v_123_, v_l_124_, v_r_125_, lean_box(0), lean_box(0));
return v___x_126_;
}
else
{
lean_object* v___x_127_; 
lean_dec(v_h__2_120_);
v___x_127_ = lean_apply_2(v_h__1_119_, lean_box(0), lean_box(0));
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object* v_00_u03b1_128_, lean_object* v_00_u03b2_129_, lean_object* v_r_130_, lean_object* v_motive_131_, lean_object* v_l_132_, lean_object* v_hl_133_, lean_object* v_hlr_134_, lean_object* v_h__1_135_, lean_object* v_h__2_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(v_00_u03b1_128_, v_00_u03b2_129_, v_r_130_, v_motive_131_, v_l_132_, v_hl_133_, v_hlr_134_, v_h__1_135_, v_h__2_136_);
lean_dec(v_r_130_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(lean_object* v_x_138_, lean_object* v_h__1_139_){
_start:
{
lean_object* v_k_140_; lean_object* v_v_141_; lean_object* v_tree_142_; lean_object* v___x_143_; 
v_k_140_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_k_140_);
v_v_141_ = lean_ctor_get(v_x_138_, 1);
lean_inc(v_v_141_);
v_tree_142_ = lean_ctor_get(v_x_138_, 2);
lean_inc(v_tree_142_);
lean_dec_ref(v_x_138_);
v___x_143_ = lean_apply_5(v_h__1_139_, v_k_140_, v_v_141_, v_tree_142_, lean_box(0), lean_box(0));
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object* v_00_u03b1_144_, lean_object* v_00_u03b2_145_, lean_object* v_l_x27_146_, lean_object* v_r_x27_147_, lean_object* v_motive_148_, lean_object* v_x_149_, lean_object* v_h__1_150_){
_start:
{
lean_object* v_k_151_; lean_object* v_v_152_; lean_object* v_tree_153_; lean_object* v___x_154_; 
v_k_151_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_k_151_);
v_v_152_ = lean_ctor_get(v_x_149_, 1);
lean_inc(v_v_152_);
v_tree_153_ = lean_ctor_get(v_x_149_, 2);
lean_inc(v_tree_153_);
lean_dec_ref(v_x_149_);
v___x_154_ = lean_apply_5(v_h__1_150_, v_k_151_, v_v_152_, v_tree_153_, lean_box(0), lean_box(0));
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object* v_00_u03b1_155_, lean_object* v_00_u03b2_156_, lean_object* v_l_x27_157_, lean_object* v_r_x27_158_, lean_object* v_motive_159_, lean_object* v_x_160_, lean_object* v_h__1_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(v_00_u03b1_155_, v_00_u03b2_156_, v_l_x27_157_, v_r_x27_158_, v_motive_159_, v_x_160_, v_h__1_161_);
lean_dec(v_r_x27_158_);
lean_dec(v_l_x27_157_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(lean_object* v_r_163_, lean_object* v_h__1_164_, lean_object* v_h__2_165_){
_start:
{
if (lean_obj_tag(v_r_163_) == 0)
{
lean_object* v_size_166_; lean_object* v_k_167_; lean_object* v_v_168_; lean_object* v_l_169_; lean_object* v_r_170_; lean_object* v___x_171_; 
lean_dec(v_h__1_164_);
v_size_166_ = lean_ctor_get(v_r_163_, 0);
lean_inc(v_size_166_);
v_k_167_ = lean_ctor_get(v_r_163_, 1);
lean_inc(v_k_167_);
v_v_168_ = lean_ctor_get(v_r_163_, 2);
lean_inc(v_v_168_);
v_l_169_ = lean_ctor_get(v_r_163_, 3);
lean_inc(v_l_169_);
v_r_170_ = lean_ctor_get(v_r_163_, 4);
lean_inc(v_r_170_);
lean_dec_ref_known(v_r_163_, 5);
v___x_171_ = lean_apply_7(v_h__2_165_, v_size_166_, v_k_167_, v_v_168_, v_l_169_, v_r_170_, lean_box(0), lean_box(0));
return v___x_171_;
}
else
{
lean_object* v___x_172_; 
lean_dec(v_h__2_165_);
v___x_172_ = lean_apply_2(v_h__1_164_, lean_box(0), lean_box(0));
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object* v_00_u03b1_173_, lean_object* v_00_u03b2_174_, lean_object* v_l_175_, lean_object* v_motive_176_, lean_object* v_r_177_, lean_object* v_hr_178_, lean_object* v_hlr_179_, lean_object* v_h__1_180_, lean_object* v_h__2_181_){
_start:
{
if (lean_obj_tag(v_r_177_) == 0)
{
lean_object* v_size_182_; lean_object* v_k_183_; lean_object* v_v_184_; lean_object* v_l_185_; lean_object* v_r_186_; lean_object* v___x_187_; 
lean_dec(v_h__1_180_);
v_size_182_ = lean_ctor_get(v_r_177_, 0);
lean_inc(v_size_182_);
v_k_183_ = lean_ctor_get(v_r_177_, 1);
lean_inc(v_k_183_);
v_v_184_ = lean_ctor_get(v_r_177_, 2);
lean_inc(v_v_184_);
v_l_185_ = lean_ctor_get(v_r_177_, 3);
lean_inc(v_l_185_);
v_r_186_ = lean_ctor_get(v_r_177_, 4);
lean_inc(v_r_186_);
lean_dec_ref_known(v_r_177_, 5);
v___x_187_ = lean_apply_7(v_h__2_181_, v_size_182_, v_k_183_, v_v_184_, v_l_185_, v_r_186_, lean_box(0), lean_box(0));
return v___x_187_;
}
else
{
lean_object* v___x_188_; 
lean_dec(v_h__2_181_);
v___x_188_ = lean_apply_2(v_h__1_180_, lean_box(0), lean_box(0));
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object* v_00_u03b1_189_, lean_object* v_00_u03b2_190_, lean_object* v_l_191_, lean_object* v_motive_192_, lean_object* v_r_193_, lean_object* v_hr_194_, lean_object* v_hlr_195_, lean_object* v_h__1_196_, lean_object* v_h__2_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(v_00_u03b1_189_, v_00_u03b2_190_, v_l_191_, v_motive_192_, v_r_193_, v_hr_194_, v_hlr_195_, v_h__1_196_, v_h__2_197_);
lean_dec(v_l_191_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(lean_object* v_r_199_, lean_object* v_h__1_200_, lean_object* v_h__2_201_){
_start:
{
if (lean_obj_tag(v_r_199_) == 0)
{
lean_object* v_size_202_; lean_object* v_k_203_; lean_object* v_v_204_; lean_object* v_l_205_; lean_object* v_r_206_; lean_object* v___x_207_; 
lean_dec(v_h__1_200_);
v_size_202_ = lean_ctor_get(v_r_199_, 0);
lean_inc(v_size_202_);
v_k_203_ = lean_ctor_get(v_r_199_, 1);
lean_inc(v_k_203_);
v_v_204_ = lean_ctor_get(v_r_199_, 2);
lean_inc(v_v_204_);
v_l_205_ = lean_ctor_get(v_r_199_, 3);
lean_inc(v_l_205_);
v_r_206_ = lean_ctor_get(v_r_199_, 4);
lean_inc(v_r_206_);
lean_dec_ref_known(v_r_199_, 5);
v___x_207_ = lean_apply_7(v_h__2_201_, v_size_202_, v_k_203_, v_v_204_, v_l_205_, v_r_206_, lean_box(0), lean_box(0));
return v___x_207_;
}
else
{
lean_object* v___x_208_; 
lean_dec(v_h__2_201_);
v___x_208_ = lean_apply_2(v_h__1_200_, lean_box(0), lean_box(0));
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object* v_00_u03b1_209_, lean_object* v_00_u03b2_210_, lean_object* v_sz_211_, lean_object* v_k_212_, lean_object* v_v_213_, lean_object* v_l_x27_214_, lean_object* v_r_x27_215_, lean_object* v_motive_216_, lean_object* v_r_217_, lean_object* v_hr_218_, lean_object* v_hlr_219_, lean_object* v_h__1_220_, lean_object* v_h__2_221_){
_start:
{
if (lean_obj_tag(v_r_217_) == 0)
{
lean_object* v_size_222_; lean_object* v_k_223_; lean_object* v_v_224_; lean_object* v_l_225_; lean_object* v_r_226_; lean_object* v___x_227_; 
lean_dec(v_h__1_220_);
v_size_222_ = lean_ctor_get(v_r_217_, 0);
lean_inc(v_size_222_);
v_k_223_ = lean_ctor_get(v_r_217_, 1);
lean_inc(v_k_223_);
v_v_224_ = lean_ctor_get(v_r_217_, 2);
lean_inc(v_v_224_);
v_l_225_ = lean_ctor_get(v_r_217_, 3);
lean_inc(v_l_225_);
v_r_226_ = lean_ctor_get(v_r_217_, 4);
lean_inc(v_r_226_);
lean_dec_ref_known(v_r_217_, 5);
v___x_227_ = lean_apply_7(v_h__2_221_, v_size_222_, v_k_223_, v_v_224_, v_l_225_, v_r_226_, lean_box(0), lean_box(0));
return v___x_227_;
}
else
{
lean_object* v___x_228_; 
lean_dec(v_h__2_221_);
v___x_228_ = lean_apply_2(v_h__1_220_, lean_box(0), lean_box(0));
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object* v_00_u03b1_229_, lean_object* v_00_u03b2_230_, lean_object* v_sz_231_, lean_object* v_k_232_, lean_object* v_v_233_, lean_object* v_l_x27_234_, lean_object* v_r_x27_235_, lean_object* v_motive_236_, lean_object* v_r_237_, lean_object* v_hr_238_, lean_object* v_hlr_239_, lean_object* v_h__1_240_, lean_object* v_h__2_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(v_00_u03b1_229_, v_00_u03b2_230_, v_sz_231_, v_k_232_, v_v_233_, v_l_x27_234_, v_r_x27_235_, v_motive_236_, v_r_237_, v_hr_238_, v_hlr_239_, v_h__1_240_, v_h__2_241_);
lean_dec(v_r_x27_235_);
lean_dec(v_l_x27_234_);
lean_dec(v_v_233_);
lean_dec(v_k_232_);
lean_dec(v_sz_231_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object* v_r_243_, lean_object* v_h__1_244_, lean_object* v_h__2_245_){
_start:
{
if (lean_obj_tag(v_r_243_) == 0)
{
lean_object* v_size_246_; lean_object* v_k_247_; lean_object* v_v_248_; lean_object* v_l_249_; lean_object* v_r_250_; lean_object* v___x_251_; 
lean_dec(v_h__1_244_);
v_size_246_ = lean_ctor_get(v_r_243_, 0);
lean_inc(v_size_246_);
v_k_247_ = lean_ctor_get(v_r_243_, 1);
lean_inc(v_k_247_);
v_v_248_ = lean_ctor_get(v_r_243_, 2);
lean_inc(v_v_248_);
v_l_249_ = lean_ctor_get(v_r_243_, 3);
lean_inc(v_l_249_);
v_r_250_ = lean_ctor_get(v_r_243_, 4);
lean_inc(v_r_250_);
lean_dec_ref_known(v_r_243_, 5);
v___x_251_ = lean_apply_7(v_h__2_245_, v_size_246_, v_k_247_, v_v_248_, v_l_249_, v_r_250_, lean_box(0), lean_box(0));
return v___x_251_;
}
else
{
lean_object* v___x_252_; 
lean_dec(v_h__2_245_);
v___x_252_ = lean_apply_2(v_h__1_244_, lean_box(0), lean_box(0));
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_motive_255_, lean_object* v_r_256_, lean_object* v_hr_257_, lean_object* v_h__1_258_, lean_object* v_h__2_259_){
_start:
{
if (lean_obj_tag(v_r_256_) == 0)
{
lean_object* v_size_260_; lean_object* v_k_261_; lean_object* v_v_262_; lean_object* v_l_263_; lean_object* v_r_264_; lean_object* v___x_265_; 
lean_dec(v_h__1_258_);
v_size_260_ = lean_ctor_get(v_r_256_, 0);
lean_inc(v_size_260_);
v_k_261_ = lean_ctor_get(v_r_256_, 1);
lean_inc(v_k_261_);
v_v_262_ = lean_ctor_get(v_r_256_, 2);
lean_inc(v_v_262_);
v_l_263_ = lean_ctor_get(v_r_256_, 3);
lean_inc(v_l_263_);
v_r_264_ = lean_ctor_get(v_r_256_, 4);
lean_inc(v_r_264_);
lean_dec_ref_known(v_r_256_, 5);
v___x_265_ = lean_apply_7(v_h__2_259_, v_size_260_, v_k_261_, v_v_262_, v_l_263_, v_r_264_, lean_box(0), lean_box(0));
return v___x_265_;
}
else
{
lean_object* v___x_266_; 
lean_dec(v_h__2_259_);
v___x_266_ = lean_apply_2(v_h__1_258_, lean_box(0), lean_box(0));
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___redArg(lean_object* v_x_267_, lean_object* v_h__1_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_apply_3(v_h__1_268_, v_x_267_, lean_box(0), lean_box(0));
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(lean_object* v_00_u03b1_270_, lean_object* v_00_u03b2_271_, lean_object* v_l_272_, lean_object* v_l_x27_x27_273_, lean_object* v_motive_274_, lean_object* v_x_275_, lean_object* v_h__1_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_apply_3(v_h__1_276_, v_x_275_, lean_box(0), lean_box(0));
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___boxed(lean_object* v_00_u03b1_278_, lean_object* v_00_u03b2_279_, lean_object* v_l_280_, lean_object* v_l_x27_x27_281_, lean_object* v_motive_282_, lean_object* v_x_283_, lean_object* v_h__1_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(v_00_u03b1_278_, v_00_u03b2_279_, v_l_280_, v_l_x27_x27_281_, v_motive_282_, v_x_283_, v_h__1_284_);
lean_dec(v_l_x27_x27_281_);
lean_dec(v_l_280_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___redArg(lean_object* v_x_286_, lean_object* v_h__1_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_apply_3(v_h__1_287_, v_x_286_, lean_box(0), lean_box(0));
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(lean_object* v_00_u03b1_289_, lean_object* v_00_u03b2_290_, lean_object* v_r_291_, lean_object* v_r_x27_292_, lean_object* v_motive_293_, lean_object* v_x_294_, lean_object* v_h__1_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lean_apply_3(v_h__1_295_, v_x_294_, lean_box(0), lean_box(0));
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___boxed(lean_object* v_00_u03b1_297_, lean_object* v_00_u03b2_298_, lean_object* v_r_299_, lean_object* v_r_x27_300_, lean_object* v_motive_301_, lean_object* v_x_302_, lean_object* v_h__1_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(v_00_u03b1_297_, v_00_u03b2_298_, v_r_299_, v_r_x27_300_, v_motive_301_, v_x_302_, v_h__1_303_);
lean_dec(v_r_x27_300_);
lean_dec(v_r_299_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object* v_t_305_, lean_object* v_h__1_306_, lean_object* v_h__2_307_){
_start:
{
if (lean_obj_tag(v_t_305_) == 0)
{
lean_object* v_size_308_; lean_object* v_k_309_; lean_object* v_v_310_; lean_object* v_l_311_; lean_object* v_r_312_; lean_object* v___x_313_; 
lean_dec(v_h__1_306_);
v_size_308_ = lean_ctor_get(v_t_305_, 0);
lean_inc(v_size_308_);
v_k_309_ = lean_ctor_get(v_t_305_, 1);
lean_inc(v_k_309_);
v_v_310_ = lean_ctor_get(v_t_305_, 2);
lean_inc(v_v_310_);
v_l_311_ = lean_ctor_get(v_t_305_, 3);
lean_inc(v_l_311_);
v_r_312_ = lean_ctor_get(v_t_305_, 4);
lean_inc(v_r_312_);
lean_dec_ref_known(v_t_305_, 5);
v___x_313_ = lean_apply_6(v_h__2_307_, v_size_308_, v_k_309_, v_v_310_, v_l_311_, v_r_312_, lean_box(0));
return v___x_313_;
}
else
{
lean_object* v___x_314_; 
lean_dec(v_h__2_307_);
v___x_314_ = lean_apply_1(v_h__1_306_, lean_box(0));
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object* v_00_u03b1_315_, lean_object* v_00_u03b2_316_, lean_object* v_motive_317_, lean_object* v_t_318_, lean_object* v_hr_319_, lean_object* v_h__1_320_, lean_object* v_h__2_321_){
_start:
{
if (lean_obj_tag(v_t_318_) == 0)
{
lean_object* v_size_322_; lean_object* v_k_323_; lean_object* v_v_324_; lean_object* v_l_325_; lean_object* v_r_326_; lean_object* v___x_327_; 
lean_dec(v_h__1_320_);
v_size_322_ = lean_ctor_get(v_t_318_, 0);
lean_inc(v_size_322_);
v_k_323_ = lean_ctor_get(v_t_318_, 1);
lean_inc(v_k_323_);
v_v_324_ = lean_ctor_get(v_t_318_, 2);
lean_inc(v_v_324_);
v_l_325_ = lean_ctor_get(v_t_318_, 3);
lean_inc(v_l_325_);
v_r_326_ = lean_ctor_get(v_t_318_, 4);
lean_inc(v_r_326_);
lean_dec_ref_known(v_t_318_, 5);
v___x_327_ = lean_apply_6(v_h__2_321_, v_size_322_, v_k_323_, v_v_324_, v_l_325_, v_r_326_, lean_box(0));
return v___x_327_;
}
else
{
lean_object* v___x_328_; 
lean_dec(v_h__2_321_);
v___x_328_ = lean_apply_1(v_h__1_320_, lean_box(0));
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___redArg(lean_object* v_x_329_, lean_object* v_h__1_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = lean_apply_3(v_h__1_330_, v_x_329_, lean_box(0), lean_box(0));
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(lean_object* v_00_u03b1_332_, lean_object* v_00_u03b2_333_, lean_object* v_l_x27_334_, lean_object* v_motive_335_, lean_object* v_x_336_, lean_object* v_h__1_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = lean_apply_3(v_h__1_337_, v_x_336_, lean_box(0), lean_box(0));
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___boxed(lean_object* v_00_u03b1_339_, lean_object* v_00_u03b2_340_, lean_object* v_l_x27_341_, lean_object* v_motive_342_, lean_object* v_x_343_, lean_object* v_h__1_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(v_00_u03b1_339_, v_00_u03b2_340_, v_l_x27_341_, v_motive_342_, v_x_343_, v_h__1_344_);
lean_dec(v_l_x27_341_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___redArg(lean_object* v_x_346_, lean_object* v_h__1_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = lean_apply_3(v_h__1_347_, v_x_346_, lean_box(0), lean_box(0));
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(lean_object* v_00_u03b1_349_, lean_object* v_00_u03b2_350_, lean_object* v_r_x27_351_, lean_object* v_motive_352_, lean_object* v_x_353_, lean_object* v_h__1_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_apply_3(v_h__1_354_, v_x_353_, lean_box(0), lean_box(0));
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___boxed(lean_object* v_00_u03b1_356_, lean_object* v_00_u03b2_357_, lean_object* v_r_x27_358_, lean_object* v_motive_359_, lean_object* v_x_360_, lean_object* v_h__1_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(v_00_u03b1_356_, v_00_u03b2_357_, v_r_x27_358_, v_motive_359_, v_x_360_, v_h__1_361_);
lean_dec(v_r_x27_358_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___redArg(lean_object* v_x_363_, lean_object* v_h__1_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_apply_3(v_h__1_364_, v_x_363_, lean_box(0), lean_box(0));
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(lean_object* v_00_u03b1_366_, lean_object* v_00_u03b2_367_, lean_object* v_szl_368_, lean_object* v_k_x27_369_, lean_object* v_v_x27_370_, lean_object* v_l_x27_371_, lean_object* v_r_x27_372_, lean_object* v_l_x27_x27_373_, lean_object* v_motive_374_, lean_object* v_x_375_, lean_object* v_h__1_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_apply_3(v_h__1_376_, v_x_375_, lean_box(0), lean_box(0));
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___boxed(lean_object* v_00_u03b1_378_, lean_object* v_00_u03b2_379_, lean_object* v_szl_380_, lean_object* v_k_x27_381_, lean_object* v_v_x27_382_, lean_object* v_l_x27_383_, lean_object* v_r_x27_384_, lean_object* v_l_x27_x27_385_, lean_object* v_motive_386_, lean_object* v_x_387_, lean_object* v_h__1_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(v_00_u03b1_378_, v_00_u03b2_379_, v_szl_380_, v_k_x27_381_, v_v_x27_382_, v_l_x27_383_, v_r_x27_384_, v_l_x27_x27_385_, v_motive_386_, v_x_387_, v_h__1_388_);
lean_dec(v_l_x27_x27_385_);
lean_dec(v_r_x27_384_);
lean_dec(v_l_x27_383_);
lean_dec(v_v_x27_382_);
lean_dec(v_k_x27_381_);
lean_dec(v_szl_380_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___redArg(lean_object* v_x_390_, lean_object* v_h__1_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_apply_3(v_h__1_391_, v_x_390_, lean_box(0), lean_box(0));
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(lean_object* v_00_u03b1_393_, lean_object* v_00_u03b2_394_, lean_object* v_r_x27_395_, lean_object* v_szr_396_, lean_object* v_k_x27_x27_397_, lean_object* v_v_x27_x27_398_, lean_object* v_l_x27_x27_399_, lean_object* v_r_x27_x27_400_, lean_object* v_motive_401_, lean_object* v_x_402_, lean_object* v_h__1_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = lean_apply_3(v_h__1_403_, v_x_402_, lean_box(0), lean_box(0));
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___boxed(lean_object* v_00_u03b1_405_, lean_object* v_00_u03b2_406_, lean_object* v_r_x27_407_, lean_object* v_szr_408_, lean_object* v_k_x27_x27_409_, lean_object* v_v_x27_x27_410_, lean_object* v_l_x27_x27_411_, lean_object* v_r_x27_x27_412_, lean_object* v_motive_413_, lean_object* v_x_414_, lean_object* v_h__1_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(v_00_u03b1_405_, v_00_u03b2_406_, v_r_x27_407_, v_szr_408_, v_k_x27_x27_409_, v_v_x27_x27_410_, v_l_x27_x27_411_, v_r_x27_x27_412_, v_motive_413_, v_x_414_, v_h__1_415_);
lean_dec(v_r_x27_x27_412_);
lean_dec(v_l_x27_x27_411_);
lean_dec(v_v_x27_x27_410_);
lean_dec(v_k_x27_x27_409_);
lean_dec(v_szr_408_);
lean_dec(v_r_x27_407_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(lean_object* v_l_417_, lean_object* v_h__1_418_, lean_object* v_h__2_419_){
_start:
{
if (lean_obj_tag(v_l_417_) == 0)
{
lean_object* v_size_420_; lean_object* v_k_421_; lean_object* v_v_422_; lean_object* v_l_423_; lean_object* v_r_424_; lean_object* v___x_425_; 
lean_dec(v_h__1_418_);
v_size_420_ = lean_ctor_get(v_l_417_, 0);
lean_inc(v_size_420_);
v_k_421_ = lean_ctor_get(v_l_417_, 1);
lean_inc(v_k_421_);
v_v_422_ = lean_ctor_get(v_l_417_, 2);
lean_inc(v_v_422_);
v_l_423_ = lean_ctor_get(v_l_417_, 3);
lean_inc(v_l_423_);
v_r_424_ = lean_ctor_get(v_l_417_, 4);
lean_inc(v_r_424_);
lean_dec_ref_known(v_l_417_, 5);
v___x_425_ = lean_apply_6(v_h__2_419_, v_size_420_, v_k_421_, v_v_422_, v_l_423_, v_r_424_, lean_box(0));
return v___x_425_;
}
else
{
lean_object* v___x_426_; 
lean_dec(v_h__2_419_);
v___x_426_ = lean_apply_1(v_h__1_418_, lean_box(0));
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(lean_object* v_00_u03b1_427_, lean_object* v_00_u03b2_428_, lean_object* v_motive_429_, lean_object* v_l_430_, lean_object* v_hl_431_, lean_object* v_h__1_432_, lean_object* v_h__2_433_){
_start:
{
if (lean_obj_tag(v_l_430_) == 0)
{
lean_object* v_size_434_; lean_object* v_k_435_; lean_object* v_v_436_; lean_object* v_l_437_; lean_object* v_r_438_; lean_object* v___x_439_; 
lean_dec(v_h__1_432_);
v_size_434_ = lean_ctor_get(v_l_430_, 0);
lean_inc(v_size_434_);
v_k_435_ = lean_ctor_get(v_l_430_, 1);
lean_inc(v_k_435_);
v_v_436_ = lean_ctor_get(v_l_430_, 2);
lean_inc(v_v_436_);
v_l_437_ = lean_ctor_get(v_l_430_, 3);
lean_inc(v_l_437_);
v_r_438_ = lean_ctor_get(v_l_430_, 4);
lean_inc(v_r_438_);
lean_dec_ref_known(v_l_430_, 5);
v___x_439_ = lean_apply_6(v_h__2_433_, v_size_434_, v_k_435_, v_v_436_, v_l_437_, v_r_438_, lean_box(0));
return v___x_439_;
}
else
{
lean_object* v___x_440_; 
lean_dec(v_h__2_433_);
v___x_440_ = lean_apply_1(v_h__1_432_, lean_box(0));
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object* v_x_441_, lean_object* v_h__1_442_, lean_object* v_h__2_443_){
_start:
{
if (lean_obj_tag(v_x_441_) == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec(v_h__2_443_);
v___x_444_ = lean_box(0);
v___x_445_ = lean_apply_1(v_h__1_442_, v___x_444_);
return v___x_445_;
}
else
{
lean_object* v_val_446_; lean_object* v_fst_447_; lean_object* v_snd_448_; lean_object* v___x_449_; 
lean_dec(v_h__1_442_);
v_val_446_ = lean_ctor_get(v_x_441_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v_x_441_, 1);
v_fst_447_ = lean_ctor_get(v_val_446_, 0);
lean_inc(v_fst_447_);
v_snd_448_ = lean_ctor_get(v_val_446_, 1);
lean_inc(v_snd_448_);
lean_dec(v_val_446_);
v___x_449_ = lean_apply_2(v_h__2_443_, v_fst_447_, v_snd_448_);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* v_00_u03b1_450_, lean_object* v_00_u03b2_451_, lean_object* v_motive_452_, lean_object* v_x_453_, lean_object* v_h__1_454_, lean_object* v_h__2_455_){
_start:
{
if (lean_obj_tag(v_x_453_) == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v_h__2_455_);
v___x_456_ = lean_box(0);
v___x_457_ = lean_apply_1(v_h__1_454_, v___x_456_);
return v___x_457_;
}
else
{
lean_object* v_val_458_; lean_object* v_fst_459_; lean_object* v_snd_460_; lean_object* v___x_461_; 
lean_dec(v_h__1_454_);
v_val_458_ = lean_ctor_get(v_x_453_, 0);
lean_inc(v_val_458_);
lean_dec_ref_known(v_x_453_, 1);
v_fst_459_ = lean_ctor_get(v_val_458_, 0);
lean_inc(v_fst_459_);
v_snd_460_ = lean_ctor_get(v_val_458_, 1);
lean_inc(v_snd_460_);
lean_dec(v_val_458_);
v___x_461_ = lean_apply_2(v_h__2_455_, v_fst_459_, v_snd_460_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(uint8_t v_x_462_, lean_object* v_h__1_463_, lean_object* v_h__2_464_, lean_object* v_h__3_465_){
_start:
{
switch(v_x_462_)
{
case 0:
{
lean_object* v___x_466_; 
lean_dec(v_h__3_465_);
lean_dec(v_h__2_464_);
v___x_466_ = lean_apply_1(v_h__1_463_, lean_box(0));
return v___x_466_;
}
case 1:
{
lean_object* v___x_467_; 
lean_dec(v_h__3_465_);
lean_dec(v_h__1_463_);
v___x_467_ = lean_apply_1(v_h__2_464_, lean_box(0));
return v___x_467_;
}
default: 
{
lean_object* v___x_468_; 
lean_dec(v_h__2_464_);
lean_dec(v_h__1_463_);
v___x_468_ = lean_apply_1(v_h__3_465_, lean_box(0));
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(lean_object* v_x_469_, lean_object* v_h__1_470_, lean_object* v_h__2_471_, lean_object* v_h__3_472_){
_start:
{
uint8_t v_x_33__boxed_473_; lean_object* v_res_474_; 
v_x_33__boxed_473_ = lean_unbox(v_x_469_);
v_res_474_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_33__boxed_473_, v_h__1_470_, v_h__2_471_, v_h__3_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object* v_motive_475_, uint8_t v_x_476_, lean_object* v_h__1_477_, lean_object* v_h__2_478_, lean_object* v_h__3_479_){
_start:
{
switch(v_x_476_)
{
case 0:
{
lean_object* v___x_480_; 
lean_dec(v_h__3_479_);
lean_dec(v_h__2_478_);
v___x_480_ = lean_apply_1(v_h__1_477_, lean_box(0));
return v___x_480_;
}
case 1:
{
lean_object* v___x_481_; 
lean_dec(v_h__3_479_);
lean_dec(v_h__1_477_);
v___x_481_ = lean_apply_1(v_h__2_478_, lean_box(0));
return v___x_481_;
}
default: 
{
lean_object* v___x_482_; 
lean_dec(v_h__2_478_);
lean_dec(v_h__1_477_);
v___x_482_ = lean_apply_1(v_h__3_479_, lean_box(0));
return v___x_482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(lean_object* v_motive_483_, lean_object* v_x_484_, lean_object* v_h__1_485_, lean_object* v_h__2_486_, lean_object* v_h__3_487_){
_start:
{
uint8_t v_x_42__boxed_488_; lean_object* v_res_489_; 
v_x_42__boxed_488_ = lean_unbox(v_x_484_);
v_res_489_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(v_motive_483_, v_x_42__boxed_488_, v_h__1_485_, v_h__2_486_, v_h__3_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(lean_object* v_x_490_, lean_object* v_h__1_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = lean_apply_4(v_h__1_491_, v_x_490_, lean_box(0), lean_box(0), lean_box(0));
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object* v_00_u03b1_493_, lean_object* v_00_u03b2_494_, lean_object* v_l_495_, lean_object* v_motive_496_, lean_object* v_x_497_, lean_object* v_h__1_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = lean_apply_4(v_h__1_498_, v_x_497_, lean_box(0), lean_box(0), lean_box(0));
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(lean_object* v_00_u03b1_500_, lean_object* v_00_u03b2_501_, lean_object* v_l_502_, lean_object* v_motive_503_, lean_object* v_x_504_, lean_object* v_h__1_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_500_, v_00_u03b2_501_, v_l_502_, v_motive_503_, v_x_504_, v_h__1_505_);
lean_dec(v_l_502_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(uint8_t v_x_507_, lean_object* v_h__1_508_, lean_object* v_h__2_509_, lean_object* v_h__3_510_){
_start:
{
switch(v_x_507_)
{
case 0:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_h__3_510_);
lean_dec(v_h__2_509_);
v___x_511_ = lean_box(0);
v___x_512_ = lean_apply_1(v_h__1_508_, v___x_511_);
return v___x_512_;
}
case 1:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v_h__2_509_);
lean_dec(v_h__1_508_);
v___x_513_ = lean_box(0);
v___x_514_ = lean_apply_1(v_h__3_510_, v___x_513_);
return v___x_514_;
}
default: 
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v_h__3_510_);
lean_dec(v_h__1_508_);
v___x_515_ = lean_box(0);
v___x_516_ = lean_apply_1(v_h__2_509_, v___x_515_);
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(lean_object* v_x_517_, lean_object* v_h__1_518_, lean_object* v_h__2_519_, lean_object* v_h__3_520_){
_start:
{
uint8_t v_x_33__boxed_521_; lean_object* v_res_522_; 
v_x_33__boxed_521_ = lean_unbox(v_x_517_);
v_res_522_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_33__boxed_521_, v_h__1_518_, v_h__2_519_, v_h__3_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object* v_motive_523_, uint8_t v_x_524_, lean_object* v_h__1_525_, lean_object* v_h__2_526_, lean_object* v_h__3_527_){
_start:
{
switch(v_x_524_)
{
case 0:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec(v_h__3_527_);
lean_dec(v_h__2_526_);
v___x_528_ = lean_box(0);
v___x_529_ = lean_apply_1(v_h__1_525_, v___x_528_);
return v___x_529_;
}
case 1:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
lean_dec(v_h__2_526_);
lean_dec(v_h__1_525_);
v___x_530_ = lean_box(0);
v___x_531_ = lean_apply_1(v_h__3_527_, v___x_530_);
return v___x_531_;
}
default: 
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec(v_h__3_527_);
lean_dec(v_h__1_525_);
v___x_532_ = lean_box(0);
v___x_533_ = lean_apply_1(v_h__2_526_, v___x_532_);
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(lean_object* v_motive_534_, lean_object* v_x_535_, lean_object* v_h__1_536_, lean_object* v_h__2_537_, lean_object* v_h__3_538_){
_start:
{
uint8_t v_x_48__boxed_539_; lean_object* v_res_540_; 
v_x_48__boxed_539_ = lean_unbox(v_x_535_);
v_res_540_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_534_, v_x_48__boxed_539_, v_h__1_536_, v_h__2_537_, v_h__3_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___redArg(lean_object* v_m_541_, lean_object* v_h__1_542_, lean_object* v_h__2_543_){
_start:
{
if (lean_obj_tag(v_m_541_) == 0)
{
lean_object* v_size_544_; lean_object* v_k_545_; lean_object* v_v_546_; lean_object* v_l_547_; lean_object* v_r_548_; lean_object* v___x_549_; 
lean_dec(v_h__1_542_);
v_size_544_ = lean_ctor_get(v_m_541_, 0);
lean_inc(v_size_544_);
v_k_545_ = lean_ctor_get(v_m_541_, 1);
lean_inc(v_k_545_);
v_v_546_ = lean_ctor_get(v_m_541_, 2);
lean_inc(v_v_546_);
v_l_547_ = lean_ctor_get(v_m_541_, 3);
lean_inc(v_l_547_);
v_r_548_ = lean_ctor_get(v_m_541_, 4);
lean_inc(v_r_548_);
lean_dec_ref_known(v_m_541_, 5);
v___x_549_ = lean_apply_6(v_h__2_543_, v_size_544_, v_k_545_, v_v_546_, v_l_547_, v_r_548_, lean_box(0));
return v___x_549_;
}
else
{
lean_object* v___x_550_; 
lean_dec(v_h__2_543_);
v___x_550_ = lean_apply_1(v_h__1_542_, lean_box(0));
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(lean_object* v_00_u03b1_551_, lean_object* v_00_u03b2_552_, lean_object* v_inst_553_, lean_object* v_k_554_, lean_object* v_l_555_, lean_object* v_motive_556_, lean_object* v_m_557_, lean_object* v_hm_558_, lean_object* v_h__1_559_, lean_object* v_h__2_560_){
_start:
{
if (lean_obj_tag(v_m_557_) == 0)
{
lean_object* v_size_561_; lean_object* v_k_562_; lean_object* v_v_563_; lean_object* v_l_564_; lean_object* v_r_565_; lean_object* v___x_566_; 
lean_dec(v_h__1_559_);
v_size_561_ = lean_ctor_get(v_m_557_, 0);
lean_inc(v_size_561_);
v_k_562_ = lean_ctor_get(v_m_557_, 1);
lean_inc(v_k_562_);
v_v_563_ = lean_ctor_get(v_m_557_, 2);
lean_inc(v_v_563_);
v_l_564_ = lean_ctor_get(v_m_557_, 3);
lean_inc(v_l_564_);
v_r_565_ = lean_ctor_get(v_m_557_, 4);
lean_inc(v_r_565_);
lean_dec_ref_known(v_m_557_, 5);
v___x_566_ = lean_apply_6(v_h__2_560_, v_size_561_, v_k_562_, v_v_563_, v_l_564_, v_r_565_, lean_box(0));
return v___x_566_;
}
else
{
lean_object* v___x_567_; 
lean_dec(v_h__2_560_);
v___x_567_ = lean_apply_1(v_h__1_559_, lean_box(0));
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___boxed(lean_object* v_00_u03b1_568_, lean_object* v_00_u03b2_569_, lean_object* v_inst_570_, lean_object* v_k_571_, lean_object* v_l_572_, lean_object* v_motive_573_, lean_object* v_m_574_, lean_object* v_hm_575_, lean_object* v_h__1_576_, lean_object* v_h__2_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(v_00_u03b1_568_, v_00_u03b2_569_, v_inst_570_, v_k_571_, v_l_572_, v_motive_573_, v_m_574_, v_hm_575_, v_h__1_576_, v_h__2_577_);
lean_dec(v_l_572_);
lean_dec_ref(v_k_571_);
lean_dec_ref(v_inst_570_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(lean_object* v_x_579_, lean_object* v_h__1_580_, lean_object* v_h__2_581_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
lean_object* v_size_582_; lean_object* v_k_583_; lean_object* v_v_584_; lean_object* v_l_585_; lean_object* v_r_586_; lean_object* v___x_587_; 
lean_dec(v_h__2_581_);
v_size_582_ = lean_ctor_get(v_x_579_, 0);
lean_inc(v_size_582_);
v_k_583_ = lean_ctor_get(v_x_579_, 1);
lean_inc(v_k_583_);
v_v_584_ = lean_ctor_get(v_x_579_, 2);
lean_inc(v_v_584_);
v_l_585_ = lean_ctor_get(v_x_579_, 3);
lean_inc(v_l_585_);
v_r_586_ = lean_ctor_get(v_x_579_, 4);
lean_inc(v_r_586_);
lean_dec_ref_known(v_x_579_, 5);
v___x_587_ = lean_apply_5(v_h__1_580_, v_size_582_, v_k_583_, v_v_584_, v_l_585_, v_r_586_);
return v___x_587_;
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_dec(v_h__1_580_);
v___x_588_ = lean_box(0);
v___x_589_ = lean_apply_1(v_h__2_581_, v___x_588_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(lean_object* v_00_u03b1_590_, lean_object* v_00_u03b2_591_, lean_object* v_motive_592_, lean_object* v_x_593_, lean_object* v_h__1_594_, lean_object* v_h__2_595_){
_start:
{
if (lean_obj_tag(v_x_593_) == 0)
{
lean_object* v_size_596_; lean_object* v_k_597_; lean_object* v_v_598_; lean_object* v_l_599_; lean_object* v_r_600_; lean_object* v___x_601_; 
lean_dec(v_h__2_595_);
v_size_596_ = lean_ctor_get(v_x_593_, 0);
lean_inc(v_size_596_);
v_k_597_ = lean_ctor_get(v_x_593_, 1);
lean_inc(v_k_597_);
v_v_598_ = lean_ctor_get(v_x_593_, 2);
lean_inc(v_v_598_);
v_l_599_ = lean_ctor_get(v_x_593_, 3);
lean_inc(v_l_599_);
v_r_600_ = lean_ctor_get(v_x_593_, 4);
lean_inc(v_r_600_);
lean_dec_ref_known(v_x_593_, 5);
v___x_601_ = lean_apply_5(v_h__1_594_, v_size_596_, v_k_597_, v_v_598_, v_l_599_, v_r_600_);
return v___x_601_;
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v_h__1_594_);
v___x_602_ = lean_box(0);
v___x_603_ = lean_apply_1(v_h__2_595_, v___x_602_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object* v_x_604_, lean_object* v_h__1_605_, lean_object* v_h__2_606_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
lean_object* v___x_607_; 
lean_dec(v_h__2_606_);
v___x_607_ = lean_apply_1(v_h__1_605_, lean_box(0));
return v___x_607_;
}
else
{
lean_object* v_val_608_; lean_object* v___x_609_; 
lean_dec(v_h__1_605_);
v_val_608_ = lean_ctor_get(v_x_604_, 0);
lean_inc(v_val_608_);
lean_dec_ref_known(v_x_604_, 1);
v___x_609_ = lean_apply_2(v_h__2_606_, v_val_608_, lean_box(0));
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object* v_00_u03b1_610_, lean_object* v_00_u03b2_611_, lean_object* v_motive_612_, lean_object* v_x_613_, lean_object* v_h__1_614_, lean_object* v_h__2_615_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
lean_object* v___x_616_; 
lean_dec(v_h__2_615_);
v___x_616_ = lean_apply_1(v_h__1_614_, lean_box(0));
return v___x_616_;
}
else
{
lean_object* v_val_617_; lean_object* v___x_618_; 
lean_dec(v_h__1_614_);
v_val_617_ = lean_ctor_get(v_x_613_, 0);
lean_inc(v_val_617_);
lean_dec_ref_known(v_x_613_, 1);
v___x_618_ = lean_apply_2(v_h__2_615_, v_val_617_, lean_box(0));
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_619_, lean_object* v_h__1_620_, lean_object* v_h__2_621_){
_start:
{
if (lean_obj_tag(v_x_619_) == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec(v_h__2_621_);
v___x_622_ = lean_box(0);
v___x_623_ = lean_apply_1(v_h__1_620_, v___x_622_);
return v___x_623_;
}
else
{
lean_object* v_val_624_; lean_object* v___x_625_; 
lean_dec(v_h__1_620_);
v_val_624_ = lean_ctor_get(v_x_619_, 0);
lean_inc(v_val_624_);
lean_dec_ref_known(v_x_619_, 1);
v___x_625_ = lean_apply_1(v_h__2_621_, v_val_624_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_626_, lean_object* v_00_u03b2_627_, lean_object* v_motive_628_, lean_object* v_x_629_, lean_object* v_h__1_630_, lean_object* v_h__2_631_){
_start:
{
if (lean_obj_tag(v_x_629_) == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v_h__2_631_);
v___x_632_ = lean_box(0);
v___x_633_ = lean_apply_1(v_h__1_630_, v___x_632_);
return v___x_633_;
}
else
{
lean_object* v_val_634_; lean_object* v___x_635_; 
lean_dec(v_h__1_630_);
v_val_634_ = lean_ctor_get(v_x_629_, 0);
lean_inc(v_val_634_);
lean_dec_ref_known(v_x_629_, 1);
v___x_635_ = lean_apply_1(v_h__2_631_, v_val_634_);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_636_, lean_object* v_h__1_637_, lean_object* v_h__2_638_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec(v_h__2_638_);
v___x_639_ = lean_box(0);
v___x_640_ = lean_apply_1(v_h__1_637_, v___x_639_);
return v___x_640_;
}
else
{
lean_object* v_head_641_; lean_object* v_tail_642_; lean_object* v_fst_643_; lean_object* v_snd_644_; lean_object* v___x_645_; 
lean_dec(v_h__1_637_);
v_head_641_ = lean_ctor_get(v_x_636_, 0);
lean_inc(v_head_641_);
v_tail_642_ = lean_ctor_get(v_x_636_, 1);
lean_inc(v_tail_642_);
lean_dec_ref_known(v_x_636_, 2);
v_fst_643_ = lean_ctor_get(v_head_641_, 0);
lean_inc(v_fst_643_);
v_snd_644_ = lean_ctor_get(v_head_641_, 1);
lean_inc(v_snd_644_);
lean_dec(v_head_641_);
v___x_645_ = lean_apply_3(v_h__2_638_, v_fst_643_, v_snd_644_, v_tail_642_);
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_646_, lean_object* v_00_u03b2_647_, lean_object* v_motive_648_, lean_object* v_x_649_, lean_object* v_h__1_650_, lean_object* v_h__2_651_){
_start:
{
if (lean_obj_tag(v_x_649_) == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v_h__2_651_);
v___x_652_ = lean_box(0);
v___x_653_ = lean_apply_1(v_h__1_650_, v___x_652_);
return v___x_653_;
}
else
{
lean_object* v_head_654_; lean_object* v_tail_655_; lean_object* v_fst_656_; lean_object* v_snd_657_; lean_object* v___x_658_; 
lean_dec(v_h__1_650_);
v_head_654_ = lean_ctor_get(v_x_649_, 0);
lean_inc(v_head_654_);
v_tail_655_ = lean_ctor_get(v_x_649_, 1);
lean_inc(v_tail_655_);
lean_dec_ref_known(v_x_649_, 2);
v_fst_656_ = lean_ctor_get(v_head_654_, 0);
lean_inc(v_fst_656_);
v_snd_657_ = lean_ctor_get(v_head_654_, 1);
lean_inc(v_snd_657_);
lean_dec(v_head_654_);
v___x_658_ = lean_apply_3(v_h__2_651_, v_fst_656_, v_snd_657_, v_tail_655_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object* v_x_659_, lean_object* v_h__1_660_, lean_object* v_h__2_661_){
_start:
{
if (lean_obj_tag(v_x_659_) == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec(v_h__2_661_);
v___x_662_ = lean_box(0);
v___x_663_ = lean_apply_1(v_h__1_660_, v___x_662_);
return v___x_663_;
}
else
{
lean_object* v_val_664_; lean_object* v___x_665_; 
lean_dec(v_h__1_660_);
v_val_664_ = lean_ctor_get(v_x_659_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v_x_659_, 1);
v___x_665_ = lean_apply_1(v_h__2_661_, v_val_664_);
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_666_, lean_object* v_00_u03b2_667_, lean_object* v_motive_668_, lean_object* v_x_669_, lean_object* v_h__1_670_, lean_object* v_h__2_671_){
_start:
{
if (lean_obj_tag(v_x_669_) == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
lean_dec(v_h__2_671_);
v___x_672_ = lean_box(0);
v___x_673_ = lean_apply_1(v_h__1_670_, v___x_672_);
return v___x_673_;
}
else
{
lean_object* v_val_674_; lean_object* v___x_675_; 
lean_dec(v_h__1_670_);
v_val_674_ = lean_ctor_get(v_x_669_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v_x_669_, 1);
v___x_675_ = lean_apply_1(v_h__2_671_, v_val_674_);
return v___x_675_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___redArg(lean_object* v_x_676_, lean_object* v_h__1_677_, lean_object* v_h__2_678_){
_start:
{
if (lean_obj_tag(v_x_676_) == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec(v_h__2_678_);
v___x_679_ = lean_box(0);
v___x_680_ = lean_apply_1(v_h__1_677_, v___x_679_);
return v___x_680_;
}
else
{
lean_object* v_val_681_; lean_object* v___x_682_; 
lean_dec(v_h__1_677_);
v_val_681_ = lean_ctor_get(v_x_676_, 0);
lean_inc(v_val_681_);
lean_dec_ref_known(v_x_676_, 1);
v___x_682_ = lean_apply_1(v_h__2_678_, v_val_681_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(lean_object* v_00_u03b1_683_, lean_object* v_00_u03b2_684_, lean_object* v_k_685_, lean_object* v_motive_686_, lean_object* v_x_687_, lean_object* v_h__1_688_, lean_object* v_h__2_689_){
_start:
{
if (lean_obj_tag(v_x_687_) == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec(v_h__2_689_);
v___x_690_ = lean_box(0);
v___x_691_ = lean_apply_1(v_h__1_688_, v___x_690_);
return v___x_691_;
}
else
{
lean_object* v_val_692_; lean_object* v___x_693_; 
lean_dec(v_h__1_688_);
v_val_692_ = lean_ctor_get(v_x_687_, 0);
lean_inc(v_val_692_);
lean_dec_ref_known(v_x_687_, 1);
v___x_693_ = lean_apply_1(v_h__2_689_, v_val_692_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___boxed(lean_object* v_00_u03b1_694_, lean_object* v_00_u03b2_695_, lean_object* v_k_696_, lean_object* v_motive_697_, lean_object* v_x_698_, lean_object* v_h__1_699_, lean_object* v_h__2_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(v_00_u03b1_694_, v_00_u03b2_695_, v_k_696_, v_motive_697_, v_x_698_, v_h__1_699_, v_h__2_700_);
lean_dec(v_k_696_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filterMap_match__1_splitter___redArg(lean_object* v_x_702_, lean_object* v_h__1_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = lean_apply_2(v_h__1_703_, v_x_702_, lean_box(0));
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filterMap_match__1_splitter(lean_object* v_00_u03b1_705_, lean_object* v_00_u03b3_706_, lean_object* v_motive_707_, lean_object* v_x_708_, lean_object* v_h__1_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = lean_apply_2(v_h__1_709_, v_x_708_, lean_box(0));
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(uint8_t v_x_711_, lean_object* v_h__1_712_, lean_object* v_h__2_713_){
_start:
{
if (v_x_711_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec(v_h__2_713_);
v___x_714_ = lean_box(0);
v___x_715_ = lean_apply_1(v_h__1_712_, v___x_714_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v_h__1_712_);
v___x_716_ = lean_box(0);
v___x_717_ = lean_apply_1(v_h__2_713_, v___x_716_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg___boxed(lean_object* v_x_718_, lean_object* v_h__1_719_, lean_object* v_h__2_720_){
_start:
{
uint8_t v_x_24__boxed_721_; lean_object* v_res_722_; 
v_x_24__boxed_721_ = lean_unbox(v_x_718_);
v_res_722_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(v_x_24__boxed_721_, v_h__1_719_, v_h__2_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(lean_object* v_motive_723_, uint8_t v_x_724_, lean_object* v_h__1_725_, lean_object* v_h__2_726_){
_start:
{
if (v_x_724_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec(v_h__2_726_);
v___x_727_ = lean_box(0);
v___x_728_ = lean_apply_1(v_h__1_725_, v___x_727_);
return v___x_728_;
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec(v_h__1_725_);
v___x_729_ = lean_box(0);
v___x_730_ = lean_apply_1(v_h__2_726_, v___x_729_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___boxed(lean_object* v_motive_731_, lean_object* v_x_732_, lean_object* v_h__1_733_, lean_object* v_h__2_734_){
_start:
{
uint8_t v_x_35__boxed_735_; lean_object* v_res_736_; 
v_x_35__boxed_735_ = lean_unbox(v_x_732_);
v_res_736_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(v_motive_731_, v_x_35__boxed_735_, v_h__1_733_, v_h__2_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___redArg(lean_object* v_v_x3f_737_, lean_object* v_h__1_738_, lean_object* v_h__2_739_){
_start:
{
if (lean_obj_tag(v_v_x3f_737_) == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec(v_h__2_739_);
v___x_740_ = lean_box(0);
v___x_741_ = lean_apply_1(v_h__1_738_, v___x_740_);
return v___x_741_;
}
else
{
lean_object* v_val_742_; lean_object* v___x_743_; 
lean_dec(v_h__1_738_);
v_val_742_ = lean_ctor_get(v_v_x3f_737_, 0);
lean_inc(v_val_742_);
lean_dec_ref_known(v_v_x3f_737_, 1);
v___x_743_ = lean_apply_1(v_h__2_739_, v_val_742_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(lean_object* v_00_u03b1_744_, lean_object* v_00_u03b2_745_, lean_object* v_k_746_, lean_object* v_motive_747_, lean_object* v_v_x3f_748_, lean_object* v_h__1_749_, lean_object* v_h__2_750_){
_start:
{
if (lean_obj_tag(v_v_x3f_748_) == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec(v_h__2_750_);
v___x_751_ = lean_box(0);
v___x_752_ = lean_apply_1(v_h__1_749_, v___x_751_);
return v___x_752_;
}
else
{
lean_object* v_val_753_; lean_object* v___x_754_; 
lean_dec(v_h__1_749_);
v_val_753_ = lean_ctor_get(v_v_x3f_748_, 0);
lean_inc(v_val_753_);
lean_dec_ref_known(v_v_x3f_748_, 1);
v___x_754_ = lean_apply_1(v_h__2_750_, v_val_753_);
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___boxed(lean_object* v_00_u03b1_755_, lean_object* v_00_u03b2_756_, lean_object* v_k_757_, lean_object* v_motive_758_, lean_object* v_v_x3f_759_, lean_object* v_h__1_760_, lean_object* v_h__2_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(v_00_u03b1_755_, v_00_u03b2_756_, v_k_757_, v_motive_758_, v_v_x3f_759_, v_h__1_760_, v_h__2_761_);
lean_dec(v_k_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_763_, lean_object* v_h__1_764_, lean_object* v_h__2_765_){
_start:
{
if (lean_obj_tag(v_x_763_) == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec(v_h__2_765_);
v___x_766_ = lean_box(0);
v___x_767_ = lean_apply_1(v_h__1_764_, v___x_766_);
return v___x_767_;
}
else
{
lean_object* v_val_768_; lean_object* v___x_769_; 
lean_dec(v_h__1_764_);
v_val_768_ = lean_ctor_get(v_x_763_, 0);
lean_inc(v_val_768_);
lean_dec_ref_known(v_x_763_, 1);
v___x_769_ = lean_apply_1(v_h__2_765_, v_val_768_);
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b1_770_, lean_object* v_00_u03b2_771_, lean_object* v_k_772_, lean_object* v_motive_773_, lean_object* v_x_774_, lean_object* v_h__1_775_, lean_object* v_h__2_776_){
_start:
{
if (lean_obj_tag(v_x_774_) == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec(v_h__2_776_);
v___x_777_ = lean_box(0);
v___x_778_ = lean_apply_1(v_h__1_775_, v___x_777_);
return v___x_778_;
}
else
{
lean_object* v_val_779_; lean_object* v___x_780_; 
lean_dec(v_h__1_775_);
v_val_779_ = lean_ctor_get(v_x_774_, 0);
lean_inc(v_val_779_);
lean_dec_ref_known(v_x_774_, 1);
v___x_780_ = lean_apply_1(v_h__2_776_, v_val_779_);
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object* v_00_u03b1_781_, lean_object* v_00_u03b2_782_, lean_object* v_k_783_, lean_object* v_motive_784_, lean_object* v_x_785_, lean_object* v_h__1_786_, lean_object* v_h__2_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_781_, v_00_u03b2_782_, v_k_783_, v_motive_784_, v_x_785_, v_h__1_786_, v_h__2_787_);
lean_dec(v_k_783_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter___redArg(lean_object* v_x_789_, lean_object* v_h__1_790_, lean_object* v_h__2_791_){
_start:
{
if (lean_obj_tag(v_x_789_) == 0)
{
lean_object* v___x_792_; 
lean_dec(v_h__2_791_);
v___x_792_ = lean_apply_1(v_h__1_790_, lean_box(0));
return v___x_792_;
}
else
{
lean_object* v_val_793_; lean_object* v_fst_794_; lean_object* v_snd_795_; lean_object* v___x_796_; 
lean_dec(v_h__1_790_);
v_val_793_ = lean_ctor_get(v_x_789_, 0);
lean_inc(v_val_793_);
lean_dec_ref_known(v_x_789_, 1);
v_fst_794_ = lean_ctor_get(v_val_793_, 0);
lean_inc(v_fst_794_);
v_snd_795_ = lean_ctor_get(v_val_793_, 1);
lean_inc(v_snd_795_);
lean_dec(v_val_793_);
v___x_796_ = lean_apply_3(v_h__2_791_, v_fst_794_, v_snd_795_, lean_box(0));
return v___x_796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter(lean_object* v_00_u03b1_797_, lean_object* v_00_u03b2_798_, lean_object* v_motive_799_, lean_object* v_x_800_, lean_object* v_h__1_801_, lean_object* v_h__2_802_){
_start:
{
if (lean_obj_tag(v_x_800_) == 0)
{
lean_object* v___x_803_; 
lean_dec(v_h__2_802_);
v___x_803_ = lean_apply_1(v_h__1_801_, lean_box(0));
return v___x_803_;
}
else
{
lean_object* v_val_804_; lean_object* v_fst_805_; lean_object* v_snd_806_; lean_object* v___x_807_; 
lean_dec(v_h__1_801_);
v_val_804_ = lean_ctor_get(v_x_800_, 0);
lean_inc(v_val_804_);
lean_dec_ref_known(v_x_800_, 1);
v_fst_805_ = lean_ctor_get(v_val_804_, 0);
lean_inc(v_fst_805_);
v_snd_806_ = lean_ctor_get(v_val_804_, 1);
lean_inc(v_snd_806_);
lean_dec(v_val_804_);
v___x_807_ = lean_apply_3(v_h__2_802_, v_fst_805_, v_snd_806_, lean_box(0));
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___redArg(lean_object* v_x_808_, lean_object* v_h__1_809_, lean_object* v_h__2_810_){
_start:
{
if (lean_obj_tag(v_x_808_) == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec(v_h__2_810_);
v___x_811_ = lean_box(0);
v___x_812_ = lean_apply_1(v_h__1_809_, v___x_811_);
return v___x_812_;
}
else
{
lean_object* v_val_813_; lean_object* v___x_814_; 
lean_dec(v_h__1_809_);
v_val_813_ = lean_ctor_get(v_x_808_, 0);
lean_inc(v_val_813_);
lean_dec_ref_known(v_x_808_, 1);
v___x_814_ = lean_apply_1(v_h__2_810_, v_val_813_);
return v___x_814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(lean_object* v_00_u03b1_815_, lean_object* v_00_u03b2_816_, lean_object* v_k_817_, lean_object* v_motive_818_, lean_object* v_x_819_, lean_object* v_h__1_820_, lean_object* v_h__2_821_){
_start:
{
if (lean_obj_tag(v_x_819_) == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; 
lean_dec(v_h__2_821_);
v___x_822_ = lean_box(0);
v___x_823_ = lean_apply_1(v_h__1_820_, v___x_822_);
return v___x_823_;
}
else
{
lean_object* v_val_824_; lean_object* v___x_825_; 
lean_dec(v_h__1_820_);
v_val_824_ = lean_ctor_get(v_x_819_, 0);
lean_inc(v_val_824_);
lean_dec_ref_known(v_x_819_, 1);
v___x_825_ = lean_apply_1(v_h__2_821_, v_val_824_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object* v_00_u03b1_826_, lean_object* v_00_u03b2_827_, lean_object* v_k_828_, lean_object* v_motive_829_, lean_object* v_x_830_, lean_object* v_h__1_831_, lean_object* v_h__2_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_826_, v_00_u03b2_827_, v_k_828_, v_motive_829_, v_x_830_, v_h__1_831_, v_h__2_832_);
lean_dec(v_k_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(uint8_t v_x_834_, lean_object* v_h__1_835_, lean_object* v_h__2_836_, lean_object* v_h__3_837_){
_start:
{
switch(v_x_834_)
{
case 0:
{
lean_object* v___x_838_; 
lean_dec(v_h__3_837_);
lean_dec(v_h__2_836_);
v___x_838_ = lean_apply_1(v_h__1_835_, lean_box(0));
return v___x_838_;
}
case 1:
{
lean_object* v___x_839_; 
lean_dec(v_h__2_836_);
lean_dec(v_h__1_835_);
v___x_839_ = lean_apply_1(v_h__3_837_, lean_box(0));
return v___x_839_;
}
default: 
{
lean_object* v___x_840_; 
lean_dec(v_h__3_837_);
lean_dec(v_h__1_835_);
v___x_840_ = lean_apply_1(v_h__2_836_, lean_box(0));
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg___boxed(lean_object* v_x_841_, lean_object* v_h__1_842_, lean_object* v_h__2_843_, lean_object* v_h__3_844_){
_start:
{
uint8_t v_x_33__boxed_845_; lean_object* v_res_846_; 
v_x_33__boxed_845_ = lean_unbox(v_x_841_);
v_res_846_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(v_x_33__boxed_845_, v_h__1_842_, v_h__2_843_, v_h__3_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(lean_object* v_motive_847_, uint8_t v_x_848_, lean_object* v_h__1_849_, lean_object* v_h__2_850_, lean_object* v_h__3_851_){
_start:
{
switch(v_x_848_)
{
case 0:
{
lean_object* v___x_852_; 
lean_dec(v_h__3_851_);
lean_dec(v_h__2_850_);
v___x_852_ = lean_apply_1(v_h__1_849_, lean_box(0));
return v___x_852_;
}
case 1:
{
lean_object* v___x_853_; 
lean_dec(v_h__2_850_);
lean_dec(v_h__1_849_);
v___x_853_ = lean_apply_1(v_h__3_851_, lean_box(0));
return v___x_853_;
}
default: 
{
lean_object* v___x_854_; 
lean_dec(v_h__3_851_);
lean_dec(v_h__1_849_);
v___x_854_ = lean_apply_1(v_h__2_850_, lean_box(0));
return v___x_854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___boxed(lean_object* v_motive_855_, lean_object* v_x_856_, lean_object* v_h__1_857_, lean_object* v_h__2_858_, lean_object* v_h__3_859_){
_start:
{
uint8_t v_x_42__boxed_860_; lean_object* v_res_861_; 
v_x_42__boxed_860_ = lean_unbox(v_x_856_);
v_res_861_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(v_motive_855_, v_x_42__boxed_860_, v_h__1_857_, v_h__2_858_, v_h__3_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter___redArg(lean_object* v_x_862_, lean_object* v_h__1_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = lean_apply_4(v_h__1_863_, v_x_862_, lean_box(0), lean_box(0), lean_box(0));
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter(lean_object* v_00_u03b1_865_, lean_object* v_00_u03b2_866_, lean_object* v_l_x27_867_, lean_object* v_motive_868_, lean_object* v_x_869_, lean_object* v_h__1_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = lean_apply_4(v_h__1_870_, v_x_869_, lean_box(0), lean_box(0), lean_box(0));
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter___boxed(lean_object* v_00_u03b1_872_, lean_object* v_00_u03b2_873_, lean_object* v_l_x27_874_, lean_object* v_motive_875_, lean_object* v_x_876_, lean_object* v_h__1_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter(v_00_u03b1_872_, v_00_u03b2_873_, v_l_x27_874_, v_motive_875_, v_x_876_, v_h__1_877_);
lean_dec(v_l_x27_874_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object* v_l_879_, lean_object* v_h__1_880_, lean_object* v_h__2_881_){
_start:
{
if (lean_obj_tag(v_l_879_) == 0)
{
lean_object* v_size_882_; lean_object* v_k_883_; lean_object* v_v_884_; lean_object* v_l_885_; lean_object* v_r_886_; lean_object* v___x_887_; 
lean_dec(v_h__1_880_);
v_size_882_ = lean_ctor_get(v_l_879_, 0);
lean_inc(v_size_882_);
v_k_883_ = lean_ctor_get(v_l_879_, 1);
lean_inc(v_k_883_);
v_v_884_ = lean_ctor_get(v_l_879_, 2);
lean_inc(v_v_884_);
v_l_885_ = lean_ctor_get(v_l_879_, 3);
lean_inc(v_l_885_);
v_r_886_ = lean_ctor_get(v_l_879_, 4);
lean_inc(v_r_886_);
lean_dec_ref_known(v_l_879_, 5);
v___x_887_ = lean_apply_5(v_h__2_881_, v_size_882_, v_k_883_, v_v_884_, v_l_885_, v_r_886_);
return v___x_887_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec(v_h__2_881_);
v___x_888_ = lean_box(0);
v___x_889_ = lean_apply_1(v_h__1_880_, v___x_888_);
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object* v_00_u03b1_890_, lean_object* v_00_u03b2_891_, lean_object* v_motive_892_, lean_object* v_l_893_, lean_object* v_h__1_894_, lean_object* v_h__2_895_){
_start:
{
if (lean_obj_tag(v_l_893_) == 0)
{
lean_object* v_size_896_; lean_object* v_k_897_; lean_object* v_v_898_; lean_object* v_l_899_; lean_object* v_r_900_; lean_object* v___x_901_; 
lean_dec(v_h__1_894_);
v_size_896_ = lean_ctor_get(v_l_893_, 0);
lean_inc(v_size_896_);
v_k_897_ = lean_ctor_get(v_l_893_, 1);
lean_inc(v_k_897_);
v_v_898_ = lean_ctor_get(v_l_893_, 2);
lean_inc(v_v_898_);
v_l_899_ = lean_ctor_get(v_l_893_, 3);
lean_inc(v_l_899_);
v_r_900_ = lean_ctor_get(v_l_893_, 4);
lean_inc(v_r_900_);
lean_dec_ref_known(v_l_893_, 5);
v___x_901_ = lean_apply_5(v_h__2_895_, v_size_896_, v_k_897_, v_v_898_, v_l_899_, v_r_900_);
return v___x_901_;
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; 
lean_dec(v_h__2_895_);
v___x_902_ = lean_box(0);
v___x_903_ = lean_apply_1(v_h__1_894_, v___x_902_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object* v_t_904_, lean_object* v_h__1_905_, lean_object* v_h__2_906_){
_start:
{
if (lean_obj_tag(v_t_904_) == 0)
{
lean_object* v_size_907_; lean_object* v_k_908_; lean_object* v_v_909_; lean_object* v_l_910_; lean_object* v_r_911_; lean_object* v___x_912_; 
lean_dec(v_h__1_905_);
v_size_907_ = lean_ctor_get(v_t_904_, 0);
lean_inc(v_size_907_);
v_k_908_ = lean_ctor_get(v_t_904_, 1);
lean_inc(v_k_908_);
v_v_909_ = lean_ctor_get(v_t_904_, 2);
lean_inc(v_v_909_);
v_l_910_ = lean_ctor_get(v_t_904_, 3);
lean_inc(v_l_910_);
v_r_911_ = lean_ctor_get(v_t_904_, 4);
lean_inc(v_r_911_);
lean_dec_ref_known(v_t_904_, 5);
v___x_912_ = lean_apply_5(v_h__2_906_, v_size_907_, v_k_908_, v_v_909_, v_l_910_, v_r_911_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v_h__2_906_);
v___x_913_ = lean_box(0);
v___x_914_ = lean_apply_1(v_h__1_905_, v___x_913_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object* v_00_u03b1_915_, lean_object* v_00_u03b2_916_, lean_object* v_motive_917_, lean_object* v_t_918_, lean_object* v_h__1_919_, lean_object* v_h__2_920_){
_start:
{
if (lean_obj_tag(v_t_918_) == 0)
{
lean_object* v_size_921_; lean_object* v_k_922_; lean_object* v_v_923_; lean_object* v_l_924_; lean_object* v_r_925_; lean_object* v___x_926_; 
lean_dec(v_h__1_919_);
v_size_921_ = lean_ctor_get(v_t_918_, 0);
lean_inc(v_size_921_);
v_k_922_ = lean_ctor_get(v_t_918_, 1);
lean_inc(v_k_922_);
v_v_923_ = lean_ctor_get(v_t_918_, 2);
lean_inc(v_v_923_);
v_l_924_ = lean_ctor_get(v_t_918_, 3);
lean_inc(v_l_924_);
v_r_925_ = lean_ctor_get(v_t_918_, 4);
lean_inc(v_r_925_);
lean_dec_ref_known(v_t_918_, 5);
v___x_926_ = lean_apply_5(v_h__2_920_, v_size_921_, v_k_922_, v_v_923_, v_l_924_, v_r_925_);
return v___x_926_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec(v_h__2_920_);
v___x_927_ = lean_box(0);
v___x_928_ = lean_apply_1(v_h__1_919_, v___x_927_);
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter___redArg(lean_object* v_____do__lift_929_, lean_object* v_h__1_930_, lean_object* v_h__2_931_){
_start:
{
if (lean_obj_tag(v_____do__lift_929_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; 
lean_dec(v_h__2_931_);
v_a_932_ = lean_ctor_get(v_____do__lift_929_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v_____do__lift_929_, 1);
v___x_933_ = lean_apply_1(v_h__1_930_, v_a_932_);
return v___x_933_;
}
else
{
lean_object* v_a_934_; lean_object* v___x_935_; 
lean_dec(v_h__1_930_);
v_a_934_ = lean_ctor_get(v_____do__lift_929_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v_____do__lift_929_, 1);
v___x_935_ = lean_apply_1(v_h__2_931_, v_a_934_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter(lean_object* v_00_u03b4_936_, lean_object* v_motive_937_, lean_object* v_____do__lift_938_, lean_object* v_h__1_939_, lean_object* v_h__2_940_){
_start:
{
if (lean_obj_tag(v_____do__lift_938_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_942_; 
lean_dec(v_h__2_940_);
v_a_941_ = lean_ctor_get(v_____do__lift_938_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v_____do__lift_938_, 1);
v___x_942_ = lean_apply_1(v_h__1_939_, v_a_941_);
return v___x_942_;
}
else
{
lean_object* v_a_943_; lean_object* v___x_944_; 
lean_dec(v_h__1_939_);
v_a_943_ = lean_ctor_get(v_____do__lift_938_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v_____do__lift_938_, 1);
v___x_944_ = lean_apply_1(v_h__2_940_, v_a_943_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter___redArg(lean_object* v_x_945_, lean_object* v_h__1_946_, lean_object* v_h__2_947_){
_start:
{
if (lean_obj_tag(v_x_945_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_949_; 
lean_dec(v_h__1_946_);
v_a_948_ = lean_ctor_get(v_x_945_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v_x_945_, 1);
v___x_949_ = lean_apply_1(v_h__2_947_, v_a_948_);
return v___x_949_;
}
else
{
lean_object* v_a_950_; lean_object* v___x_951_; 
lean_dec(v_h__2_947_);
v_a_950_ = lean_ctor_get(v_x_945_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v_x_945_, 1);
v___x_951_ = lean_apply_1(v_h__1_946_, v_a_950_);
return v___x_951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter(lean_object* v_00_u03b4_952_, lean_object* v_motive_953_, lean_object* v_x_954_, lean_object* v_h__1_955_, lean_object* v_h__2_956_){
_start:
{
if (lean_obj_tag(v_x_954_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_958_; 
lean_dec(v_h__1_955_);
v_a_957_ = lean_ctor_get(v_x_954_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v_x_954_, 1);
v___x_958_ = lean_apply_1(v_h__2_956_, v_a_957_);
return v___x_958_;
}
else
{
lean_object* v_a_959_; lean_object* v___x_960_; 
lean_dec(v_h__2_956_);
v_a_959_ = lean_ctor_get(v_x_954_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v_x_954_, 1);
v___x_960_ = lean_apply_1(v_h__1_955_, v_a_959_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_961_, lean_object* v_h__1_962_, lean_object* v_h__2_963_){
_start:
{
if (lean_obj_tag(v_b_961_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_965_; 
lean_dec(v_h__1_962_);
v_a_964_ = lean_ctor_get(v_b_961_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v_b_961_, 1);
v___x_965_ = lean_apply_1(v_h__2_963_, v_a_964_);
return v___x_965_;
}
else
{
lean_object* v_a_966_; lean_object* v___x_967_; 
lean_dec(v_h__2_963_);
v_a_966_ = lean_ctor_get(v_b_961_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v_b_961_, 1);
v___x_967_ = lean_apply_1(v_h__1_962_, v_a_966_);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_968_, lean_object* v_motive_969_, lean_object* v_b_970_, lean_object* v_h__1_971_, lean_object* v_h__2_972_){
_start:
{
if (lean_obj_tag(v_b_970_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_974_; 
lean_dec(v_h__1_971_);
v_a_973_ = lean_ctor_get(v_b_970_, 0);
lean_inc(v_a_973_);
lean_dec_ref_known(v_b_970_, 1);
v___x_974_ = lean_apply_1(v_h__2_972_, v_a_973_);
return v___x_974_;
}
else
{
lean_object* v_a_975_; lean_object* v___x_976_; 
lean_dec(v_h__2_972_);
v_a_975_ = lean_ctor_get(v_b_970_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v_b_970_, 1);
v___x_976_ = lean_apply_1(v_h__1_971_, v_a_975_);
return v___x_976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_977_, lean_object* v_h__1_978_, lean_object* v_h__2_979_){
_start:
{
if (lean_obj_tag(v_x_977_) == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; 
lean_dec(v_h__2_979_);
v___x_980_ = lean_box(0);
v___x_981_ = lean_apply_1(v_h__1_978_, v___x_980_);
return v___x_981_;
}
else
{
lean_object* v_val_982_; lean_object* v___x_983_; 
lean_dec(v_h__1_978_);
v_val_982_ = lean_ctor_get(v_x_977_, 0);
lean_inc(v_val_982_);
lean_dec_ref_known(v_x_977_, 1);
v___x_983_ = lean_apply_1(v_h__2_979_, v_val_982_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b2_984_, lean_object* v_motive_985_, lean_object* v_x_986_, lean_object* v_h__1_987_, lean_object* v_h__2_988_){
_start:
{
if (lean_obj_tag(v_x_986_) == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec(v_h__2_988_);
v___x_989_ = lean_box(0);
v___x_990_ = lean_apply_1(v_h__1_987_, v___x_989_);
return v___x_990_;
}
else
{
lean_object* v_val_991_; lean_object* v___x_992_; 
lean_dec(v_h__1_987_);
v_val_991_ = lean_ctor_get(v_x_986_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v_x_986_, 1);
v___x_992_ = lean_apply_1(v_h__2_988_, v_val_991_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter___redArg(lean_object* v_x_993_, lean_object* v_h__1_994_, lean_object* v_h__2_995_){
_start:
{
if (lean_obj_tag(v_x_993_) == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec(v_h__2_995_);
v___x_996_ = lean_box(0);
v___x_997_ = lean_apply_1(v_h__1_994_, v___x_996_);
return v___x_997_;
}
else
{
lean_object* v_val_998_; lean_object* v_fst_999_; lean_object* v_snd_1000_; lean_object* v___x_1001_; 
lean_dec(v_h__1_994_);
v_val_998_ = lean_ctor_get(v_x_993_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v_x_993_, 1);
v_fst_999_ = lean_ctor_get(v_val_998_, 0);
lean_inc(v_fst_999_);
v_snd_1000_ = lean_ctor_get(v_val_998_, 1);
lean_inc(v_snd_1000_);
lean_dec(v_val_998_);
v___x_1001_ = lean_apply_2(v_h__2_995_, v_fst_999_, v_snd_1000_);
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter(lean_object* v_00_u03b1_1002_, lean_object* v_00_u03b2_1003_, lean_object* v_motive_1004_, lean_object* v_x_1005_, lean_object* v_h__1_1006_, lean_object* v_h__2_1007_){
_start:
{
if (lean_obj_tag(v_x_1005_) == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec(v_h__2_1007_);
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_apply_1(v_h__1_1006_, v___x_1008_);
return v___x_1009_;
}
else
{
lean_object* v_val_1010_; lean_object* v_fst_1011_; lean_object* v_snd_1012_; lean_object* v___x_1013_; 
lean_dec(v_h__1_1006_);
v_val_1010_ = lean_ctor_get(v_x_1005_, 0);
lean_inc(v_val_1010_);
lean_dec_ref_known(v_x_1005_, 1);
v_fst_1011_ = lean_ctor_get(v_val_1010_, 0);
lean_inc(v_fst_1011_);
v_snd_1012_ = lean_ctor_get(v_val_1010_, 1);
lean_inc(v_snd_1012_);
lean_dec(v_val_1010_);
v___x_1013_ = lean_apply_2(v_h__2_1007_, v_fst_1011_, v_snd_1012_);
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(lean_object* v_x_1014_, lean_object* v_h__1_1015_, lean_object* v_h__2_1016_){
_start:
{
if (lean_obj_tag(v_x_1014_) == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_dec(v_h__2_1016_);
v___x_1017_ = lean_box(0);
v___x_1018_ = lean_apply_1(v_h__1_1015_, v___x_1017_);
return v___x_1018_;
}
else
{
lean_object* v_val_1019_; lean_object* v___x_1020_; 
lean_dec(v_h__1_1015_);
v_val_1019_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_val_1019_);
lean_dec_ref_known(v_x_1014_, 1);
v___x_1020_ = lean_apply_1(v_h__2_1016_, v_val_1019_);
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object* v_00_u03b2_1021_, lean_object* v_motive_1022_, lean_object* v_x_1023_, lean_object* v_h__1_1024_, lean_object* v_h__2_1025_){
_start:
{
if (lean_obj_tag(v_x_1023_) == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_dec(v_h__2_1025_);
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_apply_1(v_h__1_1024_, v___x_1026_);
return v___x_1027_;
}
else
{
lean_object* v_val_1028_; lean_object* v___x_1029_; 
lean_dec(v_h__1_1024_);
v_val_1028_ = lean_ctor_get(v_x_1023_, 0);
lean_inc(v_val_1028_);
lean_dec_ref_known(v_x_1023_, 1);
v___x_1029_ = lean_apply_1(v_h__2_1025_, v_val_1028_);
return v___x_1029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter___redArg(lean_object* v_t_1030_, lean_object* v_h__1_1031_, lean_object* v_h__2_1032_){
_start:
{
if (lean_obj_tag(v_t_1030_) == 0)
{
lean_object* v_size_1033_; lean_object* v_k_1034_; lean_object* v_v_1035_; lean_object* v_l_1036_; lean_object* v_r_1037_; lean_object* v___x_1038_; 
lean_dec(v_h__1_1031_);
v_size_1033_ = lean_ctor_get(v_t_1030_, 0);
lean_inc(v_size_1033_);
v_k_1034_ = lean_ctor_get(v_t_1030_, 1);
lean_inc(v_k_1034_);
v_v_1035_ = lean_ctor_get(v_t_1030_, 2);
lean_inc(v_v_1035_);
v_l_1036_ = lean_ctor_get(v_t_1030_, 3);
lean_inc(v_l_1036_);
v_r_1037_ = lean_ctor_get(v_t_1030_, 4);
lean_inc(v_r_1037_);
lean_dec_ref_known(v_t_1030_, 5);
v___x_1038_ = lean_apply_6(v_h__2_1032_, v_size_1033_, v_k_1034_, v_v_1035_, v_l_1036_, v_r_1037_, lean_box(0));
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; 
lean_dec(v_h__2_1032_);
v___x_1039_ = lean_apply_1(v_h__1_1031_, lean_box(0));
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter(lean_object* v_00_u03b1_1040_, lean_object* v_00_u03b2_1041_, lean_object* v_motive_1042_, lean_object* v_t_1043_, lean_object* v_hl_1044_, lean_object* v_h__1_1045_, lean_object* v_h__2_1046_){
_start:
{
if (lean_obj_tag(v_t_1043_) == 0)
{
lean_object* v_size_1047_; lean_object* v_k_1048_; lean_object* v_v_1049_; lean_object* v_l_1050_; lean_object* v_r_1051_; lean_object* v___x_1052_; 
lean_dec(v_h__1_1045_);
v_size_1047_ = lean_ctor_get(v_t_1043_, 0);
lean_inc(v_size_1047_);
v_k_1048_ = lean_ctor_get(v_t_1043_, 1);
lean_inc(v_k_1048_);
v_v_1049_ = lean_ctor_get(v_t_1043_, 2);
lean_inc(v_v_1049_);
v_l_1050_ = lean_ctor_get(v_t_1043_, 3);
lean_inc(v_l_1050_);
v_r_1051_ = lean_ctor_get(v_t_1043_, 4);
lean_inc(v_r_1051_);
lean_dec_ref_known(v_t_1043_, 5);
v___x_1052_ = lean_apply_6(v_h__2_1046_, v_size_1047_, v_k_1048_, v_v_1049_, v_l_1050_, v_r_1051_, lean_box(0));
return v___x_1052_;
}
else
{
lean_object* v___x_1053_; 
lean_dec(v_h__2_1046_);
v___x_1053_ = lean_apply_1(v_h__1_1045_, lean_box(0));
return v___x_1053_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___redArg(lean_object* v_x_1054_, lean_object* v_h__1_1055_, lean_object* v_h__2_1056_){
_start:
{
if (lean_obj_tag(v_x_1054_) == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec(v_h__2_1056_);
v___x_1057_ = lean_box(0);
v___x_1058_ = lean_apply_1(v_h__1_1055_, v___x_1057_);
return v___x_1058_;
}
else
{
lean_object* v_val_1059_; lean_object* v___x_1060_; 
lean_dec(v_h__1_1055_);
v_val_1059_ = lean_ctor_get(v_x_1054_, 0);
lean_inc(v_val_1059_);
lean_dec_ref_known(v_x_1054_, 1);
v___x_1060_ = lean_apply_1(v_h__2_1056_, v_val_1059_);
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter(lean_object* v_00_u03b2_1061_, lean_object* v_motive_1062_, lean_object* v_x_1063_, lean_object* v_h__1_1064_, lean_object* v_h__2_1065_){
_start:
{
if (lean_obj_tag(v_x_1063_) == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_dec(v_h__2_1065_);
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_apply_1(v_h__1_1064_, v___x_1066_);
return v___x_1067_;
}
else
{
lean_object* v_val_1068_; lean_object* v___x_1069_; 
lean_dec(v_h__1_1064_);
v_val_1068_ = lean_ctor_get(v_x_1063_, 0);
lean_inc(v_val_1068_);
lean_dec_ref_known(v_x_1063_, 1);
v___x_1069_ = lean_apply_1(v_h__2_1065_, v_val_1068_);
return v___x_1069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t v_x_1070_, lean_object* v_h__1_1071_, lean_object* v_h__2_1072_, lean_object* v_h__3_1073_){
_start:
{
switch(v_x_1070_)
{
case 0:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec(v_h__3_1073_);
lean_dec(v_h__2_1072_);
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_apply_1(v_h__1_1071_, v___x_1074_);
return v___x_1075_;
}
case 1:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec(v_h__2_1072_);
lean_dec(v_h__1_1071_);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_apply_1(v_h__3_1073_, v___x_1076_);
return v___x_1077_;
}
default: 
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_dec(v_h__3_1073_);
lean_dec(v_h__1_1071_);
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_apply_1(v_h__2_1072_, v___x_1078_);
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object* v_x_1080_, lean_object* v_h__1_1081_, lean_object* v_h__2_1082_, lean_object* v_h__3_1083_){
_start:
{
uint8_t v_x_33__boxed_1084_; lean_object* v_res_1085_; 
v_x_33__boxed_1084_ = lean_unbox(v_x_1080_);
v_res_1085_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_33__boxed_1084_, v_h__1_1081_, v_h__2_1082_, v_h__3_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object* v_motive_1086_, uint8_t v_x_1087_, lean_object* v_h__1_1088_, lean_object* v_h__2_1089_, lean_object* v_h__3_1090_){
_start:
{
switch(v_x_1087_)
{
case 0:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec(v_h__3_1090_);
lean_dec(v_h__2_1089_);
v___x_1091_ = lean_box(0);
v___x_1092_ = lean_apply_1(v_h__1_1088_, v___x_1091_);
return v___x_1092_;
}
case 1:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_dec(v_h__2_1089_);
lean_dec(v_h__1_1088_);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_apply_1(v_h__3_1090_, v___x_1093_);
return v___x_1094_;
}
default: 
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v_h__3_1090_);
lean_dec(v_h__1_1088_);
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_apply_1(v_h__2_1089_, v___x_1095_);
return v___x_1096_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object* v_motive_1097_, lean_object* v_x_1098_, lean_object* v_h__1_1099_, lean_object* v_h__2_1100_, lean_object* v_h__3_1101_){
_start:
{
uint8_t v_x_48__boxed_1102_; lean_object* v_res_1103_; 
v_x_48__boxed_1102_ = lean_unbox(v_x_1098_);
v_res_1103_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_1097_, v_x_48__boxed_1102_, v_h__1_1099_, v_h__2_1100_, v_h__3_1101_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter___redArg(lean_object* v_x_1104_, lean_object* v_h__1_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_apply_4(v_h__1_1105_, v_x_1104_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter(lean_object* v_00_u03b1_1107_, lean_object* v_00_u03b2_1108_, lean_object* v_l_x27_1109_, lean_object* v_motive_1110_, lean_object* v_x_1111_, lean_object* v_h__1_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_apply_4(v_h__1_1112_, v_x_1111_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter___boxed(lean_object* v_00_u03b1_1114_, lean_object* v_00_u03b2_1115_, lean_object* v_l_x27_1116_, lean_object* v_motive_1117_, lean_object* v_x_1118_, lean_object* v_h__1_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter(v_00_u03b1_1114_, v_00_u03b2_1115_, v_l_x27_1116_, v_motive_1117_, v_x_1118_, v_h__1_1119_);
lean_dec(v_l_x27_1116_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___redArg(lean_object* v_t_1121_, lean_object* v_h__1_1122_, lean_object* v_h__2_1123_){
_start:
{
if (lean_obj_tag(v_t_1121_) == 0)
{
lean_object* v_size_1124_; lean_object* v_k_1125_; lean_object* v_v_1126_; lean_object* v_l_1127_; lean_object* v_r_1128_; lean_object* v___x_1129_; 
lean_dec(v_h__1_1122_);
v_size_1124_ = lean_ctor_get(v_t_1121_, 0);
lean_inc(v_size_1124_);
v_k_1125_ = lean_ctor_get(v_t_1121_, 1);
lean_inc(v_k_1125_);
v_v_1126_ = lean_ctor_get(v_t_1121_, 2);
lean_inc(v_v_1126_);
v_l_1127_ = lean_ctor_get(v_t_1121_, 3);
lean_inc(v_l_1127_);
v_r_1128_ = lean_ctor_get(v_t_1121_, 4);
lean_inc(v_r_1128_);
lean_dec_ref_known(v_t_1121_, 5);
v___x_1129_ = lean_apply_5(v_h__2_1123_, v_size_1124_, v_k_1125_, v_v_1126_, v_l_1127_, v_r_1128_);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v_h__2_1123_);
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_apply_1(v_h__1_1122_, v___x_1130_);
return v___x_1131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter(lean_object* v_00_u03b1_1132_, lean_object* v_00_u03b2_1133_, lean_object* v_motive_1134_, lean_object* v_t_1135_, lean_object* v_h__1_1136_, lean_object* v_h__2_1137_){
_start:
{
if (lean_obj_tag(v_t_1135_) == 0)
{
lean_object* v_size_1138_; lean_object* v_k_1139_; lean_object* v_v_1140_; lean_object* v_l_1141_; lean_object* v_r_1142_; lean_object* v___x_1143_; 
lean_dec(v_h__1_1136_);
v_size_1138_ = lean_ctor_get(v_t_1135_, 0);
lean_inc(v_size_1138_);
v_k_1139_ = lean_ctor_get(v_t_1135_, 1);
lean_inc(v_k_1139_);
v_v_1140_ = lean_ctor_get(v_t_1135_, 2);
lean_inc(v_v_1140_);
v_l_1141_ = lean_ctor_get(v_t_1135_, 3);
lean_inc(v_l_1141_);
v_r_1142_ = lean_ctor_get(v_t_1135_, 4);
lean_inc(v_r_1142_);
lean_dec_ref_known(v_t_1135_, 5);
v___x_1143_ = lean_apply_5(v_h__2_1137_, v_size_1138_, v_k_1139_, v_v_1140_, v_l_1141_, v_r_1142_);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec(v_h__2_1137_);
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_apply_1(v_h__1_1136_, v___x_1144_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter___redArg(lean_object* v_x_1146_, lean_object* v_h__1_1147_, lean_object* v_h__2_1148_){
_start:
{
if (lean_obj_tag(v_x_1146_) == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec(v_h__1_1147_);
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_apply_1(v_h__2_1148_, v___x_1149_);
return v___x_1150_;
}
else
{
lean_object* v_val_1151_; lean_object* v___x_1152_; 
lean_dec(v_h__2_1148_);
v_val_1151_ = lean_ctor_get(v_x_1146_, 0);
lean_inc(v_val_1151_);
lean_dec_ref_known(v_x_1146_, 1);
v___x_1152_ = lean_apply_1(v_h__1_1147_, v_val_1151_);
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter(lean_object* v_00_u03b1_1153_, lean_object* v_00_u03b2_1154_, lean_object* v_motive_1155_, lean_object* v_x_1156_, lean_object* v_h__1_1157_, lean_object* v_h__2_1158_){
_start:
{
if (lean_obj_tag(v_x_1156_) == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec(v_h__1_1157_);
v___x_1159_ = lean_box(0);
v___x_1160_ = lean_apply_1(v_h__2_1158_, v___x_1159_);
return v___x_1160_;
}
else
{
lean_object* v_val_1161_; lean_object* v___x_1162_; 
lean_dec(v_h__2_1158_);
v_val_1161_ = lean_ctor_get(v_x_1156_, 0);
lean_inc(v_val_1161_);
lean_dec_ref_known(v_x_1156_, 1);
v___x_1162_ = lean_apply_1(v_h__1_1157_, v_val_1161_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_1163_, lean_object* v_h__1_1164_, lean_object* v_h__2_1165_){
_start:
{
if (lean_obj_tag(v_x_1163_) == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_dec(v_h__1_1164_);
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_apply_1(v_h__2_1165_, v___x_1166_);
return v___x_1167_;
}
else
{
lean_object* v_val_1168_; lean_object* v___x_1169_; 
lean_dec(v_h__2_1165_);
v_val_1168_ = lean_ctor_get(v_x_1163_, 0);
lean_inc(v_val_1168_);
lean_dec_ref_known(v_x_1163_, 1);
v___x_1169_ = lean_apply_1(v_h__1_1164_, v_val_1168_);
return v___x_1169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_1170_, lean_object* v_motive_1171_, lean_object* v_x_1172_, lean_object* v_h__1_1173_, lean_object* v_h__2_1174_){
_start:
{
if (lean_obj_tag(v_x_1172_) == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec(v_h__1_1173_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_apply_1(v_h__2_1174_, v___x_1175_);
return v___x_1176_;
}
else
{
lean_object* v_val_1177_; lean_object* v___x_1178_; 
lean_dec(v_h__2_1174_);
v_val_1177_ = lean_ctor_get(v_x_1172_, 0);
lean_inc(v_val_1177_);
lean_dec_ref_known(v_x_1172_, 1);
v___x_1178_ = lean_apply_1(v_h__1_1173_, v_val_1177_);
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_1179_, lean_object* v_h__1_1180_, lean_object* v_h__2_1181_){
_start:
{
if (lean_obj_tag(v_x_1179_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; 
lean_dec(v_h__2_1181_);
v_a_1182_ = lean_ctor_get(v_x_1179_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v_x_1179_, 1);
v___x_1183_ = lean_apply_1(v_h__1_1180_, v_a_1182_);
return v___x_1183_;
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1185_; 
lean_dec(v_h__1_1180_);
v_a_1184_ = lean_ctor_get(v_x_1179_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v_x_1179_, 1);
v___x_1185_ = lean_apply_1(v_h__2_1181_, v_a_1184_);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_1186_, lean_object* v_motive_1187_, lean_object* v_x_1188_, lean_object* v_h__1_1189_, lean_object* v_h__2_1190_){
_start:
{
if (lean_obj_tag(v_x_1188_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1192_; 
lean_dec(v_h__2_1190_);
v_a_1191_ = lean_ctor_get(v_x_1188_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v_x_1188_, 1);
v___x_1192_ = lean_apply_1(v_h__1_1189_, v_a_1191_);
return v___x_1192_;
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1194_; 
lean_dec(v_h__1_1189_);
v_a_1193_ = lean_ctor_get(v_x_1188_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v_x_1188_, 1);
v___x_1194_ = lean_apply_1(v_h__2_1190_, v_a_1193_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_1195_, lean_object* v_h__1_1196_, lean_object* v_h__2_1197_){
_start:
{
if (lean_obj_tag(v_x_1195_) == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_dec(v_h__1_1196_);
v___x_1198_ = lean_box(0);
v___x_1199_ = lean_apply_1(v_h__2_1197_, v___x_1198_);
return v___x_1199_;
}
else
{
lean_object* v_val_1200_; lean_object* v___x_1201_; 
lean_dec(v_h__2_1197_);
v_val_1200_ = lean_ctor_get(v_x_1195_, 0);
lean_inc(v_val_1200_);
lean_dec_ref_known(v_x_1195_, 1);
v___x_1201_ = lean_apply_1(v_h__1_1196_, v_val_1200_);
return v___x_1201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_1202_, lean_object* v_00_u03b2_1203_, lean_object* v_motive_1204_, lean_object* v_x_1205_, lean_object* v_h__1_1206_, lean_object* v_h__2_1207_){
_start:
{
if (lean_obj_tag(v_x_1205_) == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_h__1_1206_);
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_apply_1(v_h__2_1207_, v___x_1208_);
return v___x_1209_;
}
else
{
lean_object* v_val_1210_; lean_object* v___x_1211_; 
lean_dec(v_h__2_1207_);
v_val_1210_ = lean_ctor_get(v_x_1205_, 0);
lean_inc(v_val_1210_);
lean_dec_ref_known(v_x_1205_, 1);
v___x_1211_ = lean_apply_1(v_h__1_1206_, v_val_1210_);
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___redArg(lean_object* v_l_1212_, lean_object* v_h__1_1213_, lean_object* v_h__2_1214_){
_start:
{
if (lean_obj_tag(v_l_1212_) == 0)
{
lean_object* v_size_1215_; lean_object* v_k_1216_; lean_object* v_v_1217_; lean_object* v_l_1218_; lean_object* v_r_1219_; lean_object* v___x_1220_; 
lean_dec(v_h__1_1213_);
v_size_1215_ = lean_ctor_get(v_l_1212_, 0);
lean_inc(v_size_1215_);
v_k_1216_ = lean_ctor_get(v_l_1212_, 1);
lean_inc(v_k_1216_);
v_v_1217_ = lean_ctor_get(v_l_1212_, 2);
lean_inc(v_v_1217_);
v_l_1218_ = lean_ctor_get(v_l_1212_, 3);
lean_inc(v_l_1218_);
v_r_1219_ = lean_ctor_get(v_l_1212_, 4);
lean_inc(v_r_1219_);
lean_dec_ref_known(v_l_1212_, 5);
v___x_1220_ = lean_apply_5(v_h__2_1214_, v_size_1215_, v_k_1216_, v_v_1217_, v_l_1218_, v_r_1219_);
return v___x_1220_;
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec(v_h__2_1214_);
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_apply_1(v_h__1_1213_, v___x_1221_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter(lean_object* v_00_u03b1_1223_, lean_object* v_00_u03b2_1224_, lean_object* v_motive_1225_, lean_object* v_l_1226_, lean_object* v_h__1_1227_, lean_object* v_h__2_1228_){
_start:
{
if (lean_obj_tag(v_l_1226_) == 0)
{
lean_object* v_size_1229_; lean_object* v_k_1230_; lean_object* v_v_1231_; lean_object* v_l_1232_; lean_object* v_r_1233_; lean_object* v___x_1234_; 
lean_dec(v_h__1_1227_);
v_size_1229_ = lean_ctor_get(v_l_1226_, 0);
lean_inc(v_size_1229_);
v_k_1230_ = lean_ctor_get(v_l_1226_, 1);
lean_inc(v_k_1230_);
v_v_1231_ = lean_ctor_get(v_l_1226_, 2);
lean_inc(v_v_1231_);
v_l_1232_ = lean_ctor_get(v_l_1226_, 3);
lean_inc(v_l_1232_);
v_r_1233_ = lean_ctor_get(v_l_1226_, 4);
lean_inc(v_r_1233_);
lean_dec_ref_known(v_l_1226_, 5);
v___x_1234_ = lean_apply_5(v_h__2_1228_, v_size_1229_, v_k_1230_, v_v_1231_, v_l_1232_, v_r_1233_);
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec(v_h__2_1228_);
v___x_1235_ = lean_box(0);
v___x_1236_ = lean_apply_1(v_h__1_1227_, v___x_1235_);
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object* v_x_1237_, lean_object* v_x_1238_, lean_object* v_h__1_1239_, lean_object* v_h__2_1240_){
_start:
{
if (lean_obj_tag(v_x_1237_) == 0)
{
lean_object* v_size_1241_; lean_object* v_k_1242_; lean_object* v_v_1243_; lean_object* v_l_1244_; lean_object* v_r_1245_; lean_object* v___x_1246_; 
lean_dec(v_h__1_1239_);
v_size_1241_ = lean_ctor_get(v_x_1237_, 0);
lean_inc(v_size_1241_);
v_k_1242_ = lean_ctor_get(v_x_1237_, 1);
lean_inc(v_k_1242_);
v_v_1243_ = lean_ctor_get(v_x_1237_, 2);
lean_inc(v_v_1243_);
v_l_1244_ = lean_ctor_get(v_x_1237_, 3);
lean_inc(v_l_1244_);
v_r_1245_ = lean_ctor_get(v_x_1237_, 4);
lean_inc(v_r_1245_);
lean_dec_ref_known(v_x_1237_, 5);
v___x_1246_ = lean_apply_6(v_h__2_1240_, v_size_1241_, v_k_1242_, v_v_1243_, v_l_1244_, v_r_1245_, v_x_1238_);
return v___x_1246_;
}
else
{
lean_object* v___x_1247_; 
lean_dec(v_h__2_1240_);
v___x_1247_ = lean_apply_1(v_h__1_1239_, v_x_1238_);
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object* v_00_u03b1_1248_, lean_object* v_00_u03b2_1249_, lean_object* v_motive_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_, lean_object* v_h__1_1253_, lean_object* v_h__2_1254_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 0)
{
lean_object* v_size_1255_; lean_object* v_k_1256_; lean_object* v_v_1257_; lean_object* v_l_1258_; lean_object* v_r_1259_; lean_object* v___x_1260_; 
lean_dec(v_h__1_1253_);
v_size_1255_ = lean_ctor_get(v_x_1251_, 0);
lean_inc(v_size_1255_);
v_k_1256_ = lean_ctor_get(v_x_1251_, 1);
lean_inc(v_k_1256_);
v_v_1257_ = lean_ctor_get(v_x_1251_, 2);
lean_inc(v_v_1257_);
v_l_1258_ = lean_ctor_get(v_x_1251_, 3);
lean_inc(v_l_1258_);
v_r_1259_ = lean_ctor_get(v_x_1251_, 4);
lean_inc(v_r_1259_);
lean_dec_ref_known(v_x_1251_, 5);
v___x_1260_ = lean_apply_6(v_h__2_1254_, v_size_1255_, v_k_1256_, v_v_1257_, v_l_1258_, v_r_1259_, v_x_1252_);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; 
lean_dec(v_h__2_1254_);
v___x_1261_ = lean_apply_1(v_h__1_1253_, v_x_1252_);
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t v_x_1262_, lean_object* v_h__1_1263_, lean_object* v_h__2_1264_, lean_object* v_h__3_1265_){
_start:
{
switch(v_x_1262_)
{
case 0:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec(v_h__3_1265_);
lean_dec(v_h__2_1264_);
v___x_1266_ = lean_box(0);
v___x_1267_ = lean_apply_1(v_h__1_1263_, v___x_1266_);
return v___x_1267_;
}
case 1:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec(v_h__3_1265_);
lean_dec(v_h__1_1263_);
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_apply_1(v_h__2_1264_, v___x_1268_);
return v___x_1269_;
}
default: 
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec(v_h__2_1264_);
lean_dec(v_h__1_1263_);
v___x_1270_ = lean_box(0);
v___x_1271_ = lean_apply_1(v_h__3_1265_, v___x_1270_);
return v___x_1271_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_1272_, lean_object* v_h__1_1273_, lean_object* v_h__2_1274_, lean_object* v_h__3_1275_){
_start:
{
uint8_t v_x_33__boxed_1276_; lean_object* v_res_1277_; 
v_x_33__boxed_1276_ = lean_unbox(v_x_1272_);
v_res_1277_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_33__boxed_1276_, v_h__1_1273_, v_h__2_1274_, v_h__3_1275_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object* v_motive_1278_, uint8_t v_x_1279_, lean_object* v_h__1_1280_, lean_object* v_h__2_1281_, lean_object* v_h__3_1282_){
_start:
{
switch(v_x_1279_)
{
case 0:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
lean_dec(v_h__3_1282_);
lean_dec(v_h__2_1281_);
v___x_1283_ = lean_box(0);
v___x_1284_ = lean_apply_1(v_h__1_1280_, v___x_1283_);
return v___x_1284_;
}
case 1:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_dec(v_h__3_1282_);
lean_dec(v_h__1_1280_);
v___x_1285_ = lean_box(0);
v___x_1286_ = lean_apply_1(v_h__2_1281_, v___x_1285_);
return v___x_1286_;
}
default: 
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_dec(v_h__2_1281_);
lean_dec(v_h__1_1280_);
v___x_1287_ = lean_box(0);
v___x_1288_ = lean_apply_1(v_h__3_1282_, v___x_1287_);
return v___x_1288_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object* v_motive_1289_, lean_object* v_x_1290_, lean_object* v_h__1_1291_, lean_object* v_h__2_1292_, lean_object* v_h__3_1293_){
_start:
{
uint8_t v_x_48__boxed_1294_; lean_object* v_res_1295_; 
v_x_48__boxed_1294_ = lean_unbox(v_x_1290_);
v_res_1295_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(v_motive_1289_, v_x_48__boxed_1294_, v_h__1_1291_, v_h__2_1292_, v_h__3_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(uint8_t v_x_1296_, lean_object* v_h__1_1297_, lean_object* v_h__2_1298_){
_start:
{
if (v_x_1296_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec(v_h__1_1297_);
v___x_1299_ = lean_box(0);
v___x_1300_ = lean_apply_1(v_h__2_1298_, v___x_1299_);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_dec(v_h__2_1298_);
v___x_1301_ = lean_box(0);
v___x_1302_ = lean_apply_1(v_h__1_1297_, v___x_1301_);
return v___x_1302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_1303_, lean_object* v_h__1_1304_, lean_object* v_h__2_1305_){
_start:
{
uint8_t v_x_24__boxed_1306_; lean_object* v_res_1307_; 
v_x_24__boxed_1306_ = lean_unbox(v_x_1303_);
v_res_1307_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_1306_, v_h__1_1304_, v_h__2_1305_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(lean_object* v_motive_1308_, uint8_t v_x_1309_, lean_object* v_h__1_1310_, lean_object* v_h__2_1311_){
_start:
{
if (v_x_1309_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec(v_h__1_1310_);
v___x_1312_ = lean_box(0);
v___x_1313_ = lean_apply_1(v_h__2_1311_, v___x_1312_);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec(v_h__2_1311_);
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_apply_1(v_h__1_1310_, v___x_1314_);
return v___x_1315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_1316_, lean_object* v_x_1317_, lean_object* v_h__1_1318_, lean_object* v_h__2_1319_){
_start:
{
uint8_t v_x_35__boxed_1320_; lean_object* v_res_1321_; 
v_x_35__boxed_1320_ = lean_unbox(v_x_1317_);
v_res_1321_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(v_motive_1316_, v_x_35__boxed_1320_, v_h__1_1318_, v_h__2_1319_);
return v_res_1321_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Model(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Internal_List_Associative(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_List(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Subtype_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_DTreeMap_Internal_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Internal_Model(uint8_t builtin);
lean_object* initialize_Std_Data_Internal_List_Associative(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Option_List(uint8_t builtin);
lean_object* initialize_Init_Data_Subtype_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Internal_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Internal_List_Associative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
