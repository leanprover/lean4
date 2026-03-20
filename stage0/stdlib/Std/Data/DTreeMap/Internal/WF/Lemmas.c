// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.WF.Lemmas
// Imports: public import Std.Data.DTreeMap.Internal.Model import all Std.Data.Internal.List.Associative import Init.Data.List.Impl import Init.Data.Nat.Linear import Init.Data.Option.List import Init.Data.Subtype.Basic
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1(lean_object* v_00_u03b1_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter___redArg(lean_object* v_l_3_, lean_object* v_h__1_4_, lean_object* v_h__2_5_){
_start:
{
if (lean_obj_tag(v_l_3_) == 0)
{
lean_object* v_size_6_; lean_object* v_k_7_; lean_object* v_v_8_; lean_object* v_l_9_; lean_object* v_r_10_; lean_object* v___x_11_; 
lean_dec(v_h__1_4_);
v_size_6_ = lean_ctor_get(v_l_3_, 0);
lean_inc(v_size_6_);
v_k_7_ = lean_ctor_get(v_l_3_, 1);
lean_inc(v_k_7_);
v_v_8_ = lean_ctor_get(v_l_3_, 2);
lean_inc(v_v_8_);
v_l_9_ = lean_ctor_get(v_l_3_, 3);
lean_inc(v_l_9_);
v_r_10_ = lean_ctor_get(v_l_3_, 4);
lean_inc(v_r_10_);
lean_dec_ref(v_l_3_);
v___x_11_ = lean_apply_5(v_h__2_5_, v_size_6_, v_k_7_, v_v_8_, v_l_9_, v_r_10_);
return v___x_11_;
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec(v_h__2_5_);
v___x_12_ = lean_box(0);
v___x_13_ = lean_apply_1(v_h__1_4_, v___x_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter(lean_object* v_00_u03b1_14_, lean_object* v_00_u03b2_15_, lean_object* v_motive_16_, lean_object* v_l_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter___redArg(v_l_17_, v_h__1_18_, v_h__2_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(lean_object* v_r_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
if (lean_obj_tag(v_r_21_) == 0)
{
lean_object* v_size_24_; lean_object* v_k_25_; lean_object* v_v_26_; lean_object* v_l_27_; lean_object* v_r_28_; lean_object* v___x_29_; 
lean_dec(v_h__1_22_);
v_size_24_ = lean_ctor_get(v_r_21_, 0);
lean_inc(v_size_24_);
v_k_25_ = lean_ctor_get(v_r_21_, 1);
lean_inc(v_k_25_);
v_v_26_ = lean_ctor_get(v_r_21_, 2);
lean_inc(v_v_26_);
v_l_27_ = lean_ctor_get(v_r_21_, 3);
lean_inc(v_l_27_);
v_r_28_ = lean_ctor_get(v_r_21_, 4);
lean_inc(v_r_28_);
lean_dec_ref(v_r_21_);
v___x_29_ = lean_apply_6(v_h__2_23_, v_size_24_, v_k_25_, v_v_26_, v_l_27_, v_r_28_, lean_box(0));
return v___x_29_;
}
else
{
lean_object* v___x_30_; 
lean_dec(v_h__2_23_);
v___x_30_ = lean_apply_1(v_h__1_22_, lean_box(0));
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_l_33_, lean_object* v_motive_34_, lean_object* v_r_35_, lean_object* v_h_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(v_r_35_, v_h__1_37_, v_h__2_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___boxed(lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_, lean_object* v_l_42_, lean_object* v_motive_43_, lean_object* v_r_44_, lean_object* v_h_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(v_00_u03b1_40_, v_00_u03b2_41_, v_l_42_, v_motive_43_, v_r_44_, v_h_45_, v_h__1_46_, v_h__2_47_);
lean_dec(v_l_42_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(lean_object* v_l_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
if (lean_obj_tag(v_l_49_) == 0)
{
lean_object* v_size_52_; lean_object* v_k_53_; lean_object* v_v_54_; lean_object* v_l_55_; lean_object* v_r_56_; lean_object* v___x_57_; 
lean_dec(v_h__1_50_);
v_size_52_ = lean_ctor_get(v_l_49_, 0);
lean_inc(v_size_52_);
v_k_53_ = lean_ctor_get(v_l_49_, 1);
lean_inc(v_k_53_);
v_v_54_ = lean_ctor_get(v_l_49_, 2);
lean_inc(v_v_54_);
v_l_55_ = lean_ctor_get(v_l_49_, 3);
lean_inc(v_l_55_);
v_r_56_ = lean_ctor_get(v_l_49_, 4);
lean_inc(v_r_56_);
lean_dec_ref(v_l_49_);
v___x_57_ = lean_apply_7(v_h__2_51_, v_size_52_, v_k_53_, v_v_54_, v_l_55_, v_r_56_, lean_box(0), lean_box(0));
return v___x_57_;
}
else
{
lean_object* v___x_58_; 
lean_dec(v_h__2_51_);
v___x_58_ = lean_apply_2(v_h__1_50_, lean_box(0), lean_box(0));
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(lean_object* v_00_u03b1_59_, lean_object* v_00_u03b2_60_, lean_object* v_r_61_, lean_object* v_motive_62_, lean_object* v_l_63_, lean_object* v_h_64_, lean_object* v_h_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(v_l_63_, v_h__1_66_, v_h__2_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___boxed(lean_object* v_00_u03b1_69_, lean_object* v_00_u03b2_70_, lean_object* v_r_71_, lean_object* v_motive_72_, lean_object* v_l_73_, lean_object* v_h_74_, lean_object* v_h_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(v_00_u03b1_69_, v_00_u03b2_70_, v_r_71_, v_motive_72_, v_l_73_, v_h_74_, v_h_75_, v_h__1_76_, v_h__2_77_);
lean_dec(v_r_71_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object* v_r_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
if (lean_obj_tag(v_r_79_) == 0)
{
lean_object* v_size_82_; lean_object* v_k_83_; lean_object* v_v_84_; lean_object* v_l_85_; lean_object* v_r_86_; lean_object* v___x_87_; 
lean_dec(v_h__1_80_);
v_size_82_ = lean_ctor_get(v_r_79_, 0);
lean_inc(v_size_82_);
v_k_83_ = lean_ctor_get(v_r_79_, 1);
lean_inc(v_k_83_);
v_v_84_ = lean_ctor_get(v_r_79_, 2);
lean_inc(v_v_84_);
v_l_85_ = lean_ctor_get(v_r_79_, 3);
lean_inc(v_l_85_);
v_r_86_ = lean_ctor_get(v_r_79_, 4);
lean_inc(v_r_86_);
lean_dec_ref(v_r_79_);
v___x_87_ = lean_apply_7(v_h__2_81_, v_size_82_, v_k_83_, v_v_84_, v_l_85_, v_r_86_, lean_box(0), lean_box(0));
return v___x_87_;
}
else
{
lean_object* v___x_88_; 
lean_dec(v_h__2_81_);
v___x_88_ = lean_apply_2(v_h__1_80_, lean_box(0), lean_box(0));
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object* v_00_u03b1_89_, lean_object* v_00_u03b2_90_, lean_object* v_motive_91_, lean_object* v_r_92_, lean_object* v_hr_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(v_r_92_, v_h__1_94_, v_h__2_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___redArg(lean_object* v_x_97_, lean_object* v_h__1_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_apply_3(v_h__1_98_, v_x_97_, lean_box(0), lean_box(0));
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(lean_object* v_00_u03b1_100_, lean_object* v_00_u03b2_101_, lean_object* v_l_102_, lean_object* v_l_x27_x27_103_, lean_object* v_motive_104_, lean_object* v_x_105_, lean_object* v_h__1_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_apply_3(v_h__1_106_, v_x_105_, lean_box(0), lean_box(0));
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___boxed(lean_object* v_00_u03b1_108_, lean_object* v_00_u03b2_109_, lean_object* v_l_110_, lean_object* v_l_x27_x27_111_, lean_object* v_motive_112_, lean_object* v_x_113_, lean_object* v_h__1_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(v_00_u03b1_108_, v_00_u03b2_109_, v_l_110_, v_l_x27_x27_111_, v_motive_112_, v_x_113_, v_h__1_114_);
lean_dec(v_l_x27_x27_111_);
lean_dec(v_l_110_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___redArg(lean_object* v_x_116_, lean_object* v_h__1_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_apply_3(v_h__1_117_, v_x_116_, lean_box(0), lean_box(0));
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(lean_object* v_00_u03b1_119_, lean_object* v_00_u03b2_120_, lean_object* v_r_121_, lean_object* v_r_x27_122_, lean_object* v_motive_123_, lean_object* v_x_124_, lean_object* v_h__1_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_apply_3(v_h__1_125_, v_x_124_, lean_box(0), lean_box(0));
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___boxed(lean_object* v_00_u03b1_127_, lean_object* v_00_u03b2_128_, lean_object* v_r_129_, lean_object* v_r_x27_130_, lean_object* v_motive_131_, lean_object* v_x_132_, lean_object* v_h__1_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(v_00_u03b1_127_, v_00_u03b2_128_, v_r_129_, v_r_x27_130_, v_motive_131_, v_x_132_, v_h__1_133_);
lean_dec(v_r_x27_130_);
lean_dec(v_r_129_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object* v_t_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_){
_start:
{
if (lean_obj_tag(v_t_135_) == 0)
{
lean_object* v_size_138_; lean_object* v_k_139_; lean_object* v_v_140_; lean_object* v_l_141_; lean_object* v_r_142_; lean_object* v___x_143_; 
lean_dec(v_h__1_136_);
v_size_138_ = lean_ctor_get(v_t_135_, 0);
lean_inc(v_size_138_);
v_k_139_ = lean_ctor_get(v_t_135_, 1);
lean_inc(v_k_139_);
v_v_140_ = lean_ctor_get(v_t_135_, 2);
lean_inc(v_v_140_);
v_l_141_ = lean_ctor_get(v_t_135_, 3);
lean_inc(v_l_141_);
v_r_142_ = lean_ctor_get(v_t_135_, 4);
lean_inc(v_r_142_);
lean_dec_ref(v_t_135_);
v___x_143_ = lean_apply_6(v_h__2_137_, v_size_138_, v_k_139_, v_v_140_, v_l_141_, v_r_142_, lean_box(0));
return v___x_143_;
}
else
{
lean_object* v___x_144_; 
lean_dec(v_h__2_137_);
v___x_144_ = lean_apply_1(v_h__1_136_, lean_box(0));
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object* v_00_u03b1_145_, lean_object* v_00_u03b2_146_, lean_object* v_motive_147_, lean_object* v_t_148_, lean_object* v_hr_149_, lean_object* v_h__1_150_, lean_object* v_h__2_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(v_t_148_, v_h__1_150_, v_h__2_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___redArg(lean_object* v_x_153_, lean_object* v_h__1_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_apply_3(v_h__1_154_, v_x_153_, lean_box(0), lean_box(0));
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(lean_object* v_00_u03b1_156_, lean_object* v_00_u03b2_157_, lean_object* v_szl_158_, lean_object* v_k_x27_159_, lean_object* v_v_x27_160_, lean_object* v_l_x27_161_, lean_object* v_r_x27_162_, lean_object* v_l_x27_x27_163_, lean_object* v_motive_164_, lean_object* v_x_165_, lean_object* v_h__1_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_apply_3(v_h__1_166_, v_x_165_, lean_box(0), lean_box(0));
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___boxed(lean_object* v_00_u03b1_168_, lean_object* v_00_u03b2_169_, lean_object* v_szl_170_, lean_object* v_k_x27_171_, lean_object* v_v_x27_172_, lean_object* v_l_x27_173_, lean_object* v_r_x27_174_, lean_object* v_l_x27_x27_175_, lean_object* v_motive_176_, lean_object* v_x_177_, lean_object* v_h__1_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(v_00_u03b1_168_, v_00_u03b2_169_, v_szl_170_, v_k_x27_171_, v_v_x27_172_, v_l_x27_173_, v_r_x27_174_, v_l_x27_x27_175_, v_motive_176_, v_x_177_, v_h__1_178_);
lean_dec(v_l_x27_x27_175_);
lean_dec(v_r_x27_174_);
lean_dec(v_l_x27_173_);
lean_dec(v_v_x27_172_);
lean_dec(v_k_x27_171_);
lean_dec(v_szl_170_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___redArg(lean_object* v_x_180_, lean_object* v_h__1_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_apply_3(v_h__1_181_, v_x_180_, lean_box(0), lean_box(0));
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(lean_object* v_00_u03b1_183_, lean_object* v_00_u03b2_184_, lean_object* v_r_x27_185_, lean_object* v_szr_186_, lean_object* v_k_x27_x27_187_, lean_object* v_v_x27_x27_188_, lean_object* v_l_x27_x27_189_, lean_object* v_r_x27_x27_190_, lean_object* v_motive_191_, lean_object* v_x_192_, lean_object* v_h__1_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_apply_3(v_h__1_193_, v_x_192_, lean_box(0), lean_box(0));
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___boxed(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_r_x27_197_, lean_object* v_szr_198_, lean_object* v_k_x27_x27_199_, lean_object* v_v_x27_x27_200_, lean_object* v_l_x27_x27_201_, lean_object* v_r_x27_x27_202_, lean_object* v_motive_203_, lean_object* v_x_204_, lean_object* v_h__1_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(v_00_u03b1_195_, v_00_u03b2_196_, v_r_x27_197_, v_szr_198_, v_k_x27_x27_199_, v_v_x27_x27_200_, v_l_x27_x27_201_, v_r_x27_x27_202_, v_motive_203_, v_x_204_, v_h__1_205_);
lean_dec(v_r_x27_x27_202_);
lean_dec(v_l_x27_x27_201_);
lean_dec(v_v_x27_x27_200_);
lean_dec(v_k_x27_x27_199_);
lean_dec(v_szr_198_);
lean_dec(v_r_x27_197_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(lean_object* v_l_207_, lean_object* v_h__1_208_, lean_object* v_h__2_209_){
_start:
{
if (lean_obj_tag(v_l_207_) == 0)
{
lean_object* v_size_210_; lean_object* v_k_211_; lean_object* v_v_212_; lean_object* v_l_213_; lean_object* v_r_214_; lean_object* v___x_215_; 
lean_dec(v_h__1_208_);
v_size_210_ = lean_ctor_get(v_l_207_, 0);
lean_inc(v_size_210_);
v_k_211_ = lean_ctor_get(v_l_207_, 1);
lean_inc(v_k_211_);
v_v_212_ = lean_ctor_get(v_l_207_, 2);
lean_inc(v_v_212_);
v_l_213_ = lean_ctor_get(v_l_207_, 3);
lean_inc(v_l_213_);
v_r_214_ = lean_ctor_get(v_l_207_, 4);
lean_inc(v_r_214_);
lean_dec_ref(v_l_207_);
v___x_215_ = lean_apply_6(v_h__2_209_, v_size_210_, v_k_211_, v_v_212_, v_l_213_, v_r_214_, lean_box(0));
return v___x_215_;
}
else
{
lean_object* v___x_216_; 
lean_dec(v_h__2_209_);
v___x_216_ = lean_apply_1(v_h__1_208_, lean_box(0));
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(lean_object* v_00_u03b1_217_, lean_object* v_00_u03b2_218_, lean_object* v_motive_219_, lean_object* v_l_220_, lean_object* v_hl_221_, lean_object* v_h__1_222_, lean_object* v_h__2_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(v_l_220_, v_h__1_222_, v_h__2_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object* v_x_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec(v_h__2_227_);
v___x_228_ = lean_box(0);
v___x_229_ = lean_apply_1(v_h__1_226_, v___x_228_);
return v___x_229_;
}
else
{
lean_object* v_val_230_; lean_object* v_fst_231_; lean_object* v_snd_232_; lean_object* v___x_233_; 
lean_dec(v_h__1_226_);
v_val_230_ = lean_ctor_get(v_x_225_, 0);
lean_inc(v_val_230_);
lean_dec_ref(v_x_225_);
v_fst_231_ = lean_ctor_get(v_val_230_, 0);
lean_inc(v_fst_231_);
v_snd_232_ = lean_ctor_get(v_val_230_, 1);
lean_inc(v_snd_232_);
lean_dec(v_val_230_);
v___x_233_ = lean_apply_2(v_h__2_227_, v_fst_231_, v_snd_232_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_motive_236_, lean_object* v_x_237_, lean_object* v_h__1_238_, lean_object* v_h__2_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(v_x_237_, v_h__1_238_, v_h__2_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(uint8_t v_x_241_, lean_object* v_h__1_242_, lean_object* v_h__2_243_, lean_object* v_h__3_244_){
_start:
{
switch(v_x_241_)
{
case 0:
{
lean_object* v___x_245_; 
lean_dec(v_h__3_244_);
lean_dec(v_h__2_243_);
v___x_245_ = lean_apply_1(v_h__1_242_, lean_box(0));
return v___x_245_;
}
case 1:
{
lean_object* v___x_246_; 
lean_dec(v_h__3_244_);
lean_dec(v_h__1_242_);
v___x_246_ = lean_apply_1(v_h__2_243_, lean_box(0));
return v___x_246_;
}
default: 
{
lean_object* v___x_247_; 
lean_dec(v_h__2_243_);
lean_dec(v_h__1_242_);
v___x_247_ = lean_apply_1(v_h__3_244_, lean_box(0));
return v___x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(lean_object* v_x_248_, lean_object* v_h__1_249_, lean_object* v_h__2_250_, lean_object* v_h__3_251_){
_start:
{
uint8_t v_x_30__boxed_252_; lean_object* v_res_253_; 
v_x_30__boxed_252_ = lean_unbox(v_x_248_);
v_res_253_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_30__boxed_252_, v_h__1_249_, v_h__2_250_, v_h__3_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object* v_motive_254_, uint8_t v_x_255_, lean_object* v_h__1_256_, lean_object* v_h__2_257_, lean_object* v_h__3_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_255_, v_h__1_256_, v_h__2_257_, v_h__3_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(lean_object* v_motive_260_, lean_object* v_x_261_, lean_object* v_h__1_262_, lean_object* v_h__2_263_, lean_object* v_h__3_264_){
_start:
{
uint8_t v_x_39__boxed_265_; lean_object* v_res_266_; 
v_x_39__boxed_265_ = lean_unbox(v_x_261_);
v_res_266_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(v_motive_260_, v_x_39__boxed_265_, v_h__1_262_, v_h__2_263_, v_h__3_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(lean_object* v_x_267_, lean_object* v_h__1_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_apply_4(v_h__1_268_, v_x_267_, lean_box(0), lean_box(0), lean_box(0));
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object* v_00_u03b1_270_, lean_object* v_00_u03b2_271_, lean_object* v_l_272_, lean_object* v_motive_273_, lean_object* v_x_274_, lean_object* v_h__1_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lean_apply_4(v_h__1_275_, v_x_274_, lean_box(0), lean_box(0), lean_box(0));
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(lean_object* v_00_u03b1_277_, lean_object* v_00_u03b2_278_, lean_object* v_l_279_, lean_object* v_motive_280_, lean_object* v_x_281_, lean_object* v_h__1_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_277_, v_00_u03b2_278_, v_l_279_, v_motive_280_, v_x_281_, v_h__1_282_);
lean_dec(v_l_279_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(uint8_t v_x_284_, lean_object* v_h__1_285_, lean_object* v_h__2_286_, lean_object* v_h__3_287_){
_start:
{
switch(v_x_284_)
{
case 0:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec(v_h__3_287_);
lean_dec(v_h__2_286_);
v___x_288_ = lean_box(0);
v___x_289_ = lean_apply_1(v_h__1_285_, v___x_288_);
return v___x_289_;
}
case 1:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec(v_h__2_286_);
lean_dec(v_h__1_285_);
v___x_290_ = lean_box(0);
v___x_291_ = lean_apply_1(v_h__3_287_, v___x_290_);
return v___x_291_;
}
default: 
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec(v_h__3_287_);
lean_dec(v_h__1_285_);
v___x_292_ = lean_box(0);
v___x_293_ = lean_apply_1(v_h__2_286_, v___x_292_);
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(lean_object* v_x_294_, lean_object* v_h__1_295_, lean_object* v_h__2_296_, lean_object* v_h__3_297_){
_start:
{
uint8_t v_x_30__boxed_298_; lean_object* v_res_299_; 
v_x_30__boxed_298_ = lean_unbox(v_x_294_);
v_res_299_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_30__boxed_298_, v_h__1_295_, v_h__2_296_, v_h__3_297_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object* v_motive_300_, uint8_t v_x_301_, lean_object* v_h__1_302_, lean_object* v_h__2_303_, lean_object* v_h__3_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_301_, v_h__1_302_, v_h__2_303_, v_h__3_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(lean_object* v_motive_306_, lean_object* v_x_307_, lean_object* v_h__1_308_, lean_object* v_h__2_309_, lean_object* v_h__3_310_){
_start:
{
uint8_t v_x_45__boxed_311_; lean_object* v_res_312_; 
v_x_45__boxed_311_ = lean_unbox(v_x_307_);
v_res_312_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_306_, v_x_45__boxed_311_, v_h__1_308_, v_h__2_309_, v_h__3_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object* v_x_313_, lean_object* v_h__1_314_, lean_object* v_h__2_315_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_object* v___x_316_; 
lean_dec(v_h__2_315_);
v___x_316_ = lean_apply_1(v_h__1_314_, lean_box(0));
return v___x_316_;
}
else
{
lean_object* v_val_317_; lean_object* v___x_318_; 
lean_dec(v_h__1_314_);
v_val_317_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_val_317_);
lean_dec_ref(v_x_313_);
v___x_318_ = lean_apply_2(v_h__2_315_, v_val_317_, lean_box(0));
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object* v_00_u03b1_319_, lean_object* v_00_u03b2_320_, lean_object* v_motive_321_, lean_object* v_x_322_, lean_object* v_h__1_323_, lean_object* v_h__2_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(v_x_322_, v_h__1_323_, v_h__2_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_326_, lean_object* v_h__1_327_, lean_object* v_h__2_328_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec(v_h__2_328_);
v___x_329_ = lean_box(0);
v___x_330_ = lean_apply_1(v_h__1_327_, v___x_329_);
return v___x_330_;
}
else
{
lean_object* v_val_331_; lean_object* v___x_332_; 
lean_dec(v_h__1_327_);
v_val_331_ = lean_ctor_get(v_x_326_, 0);
lean_inc(v_val_331_);
lean_dec_ref(v_x_326_);
v___x_332_ = lean_apply_1(v_h__2_328_, v_val_331_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_333_, lean_object* v_00_u03b2_334_, lean_object* v_motive_335_, lean_object* v_x_336_, lean_object* v_h__1_337_, lean_object* v_h__2_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(v_x_336_, v_h__1_337_, v_h__2_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_340_, lean_object* v_h__1_341_, lean_object* v_h__2_342_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v_h__2_342_);
v___x_343_ = lean_box(0);
v___x_344_ = lean_apply_1(v_h__1_341_, v___x_343_);
return v___x_344_;
}
else
{
lean_object* v_head_345_; lean_object* v_tail_346_; lean_object* v_fst_347_; lean_object* v_snd_348_; lean_object* v___x_349_; 
lean_dec(v_h__1_341_);
v_head_345_ = lean_ctor_get(v_x_340_, 0);
lean_inc(v_head_345_);
v_tail_346_ = lean_ctor_get(v_x_340_, 1);
lean_inc(v_tail_346_);
lean_dec_ref(v_x_340_);
v_fst_347_ = lean_ctor_get(v_head_345_, 0);
lean_inc(v_fst_347_);
v_snd_348_ = lean_ctor_get(v_head_345_, 1);
lean_inc(v_snd_348_);
lean_dec(v_head_345_);
v___x_349_ = lean_apply_3(v_h__2_342_, v_fst_347_, v_snd_348_, v_tail_346_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_motive_352_, lean_object* v_x_353_, lean_object* v_h__1_354_, lean_object* v_h__2_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(v_x_353_, v_h__1_354_, v_h__2_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object* v_x_357_, lean_object* v_h__1_358_, lean_object* v_h__2_359_){
_start:
{
if (lean_obj_tag(v_x_357_) == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v_h__2_359_);
v___x_360_ = lean_box(0);
v___x_361_ = lean_apply_1(v_h__1_358_, v___x_360_);
return v___x_361_;
}
else
{
lean_object* v_val_362_; lean_object* v___x_363_; 
lean_dec(v_h__1_358_);
v_val_362_ = lean_ctor_get(v_x_357_, 0);
lean_inc(v_val_362_);
lean_dec_ref(v_x_357_);
v___x_363_ = lean_apply_1(v_h__2_359_, v_val_362_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_364_, lean_object* v_00_u03b2_365_, lean_object* v_motive_366_, lean_object* v_x_367_, lean_object* v_h__1_368_, lean_object* v_h__2_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(v_x_367_, v_h__1_368_, v_h__2_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___redArg(lean_object* v_x_371_, lean_object* v_h__1_372_, lean_object* v_h__2_373_){
_start:
{
if (lean_obj_tag(v_x_371_) == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; 
lean_dec(v_h__2_373_);
v___x_374_ = lean_box(0);
v___x_375_ = lean_apply_1(v_h__1_372_, v___x_374_);
return v___x_375_;
}
else
{
lean_object* v_val_376_; lean_object* v___x_377_; 
lean_dec(v_h__1_372_);
v_val_376_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_val_376_);
lean_dec_ref(v_x_371_);
v___x_377_ = lean_apply_1(v_h__2_373_, v_val_376_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(lean_object* v_00_u03b1_378_, lean_object* v_00_u03b2_379_, lean_object* v_k_380_, lean_object* v_motive_381_, lean_object* v_x_382_, lean_object* v_h__1_383_, lean_object* v_h__2_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___redArg(v_x_382_, v_h__1_383_, v_h__2_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___boxed(lean_object* v_00_u03b1_386_, lean_object* v_00_u03b2_387_, lean_object* v_k_388_, lean_object* v_motive_389_, lean_object* v_x_390_, lean_object* v_h__1_391_, lean_object* v_h__2_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(v_00_u03b1_386_, v_00_u03b2_387_, v_k_388_, v_motive_389_, v_x_390_, v_h__1_391_, v_h__2_392_);
lean_dec(v_k_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filterMap_match__1_splitter___redArg(lean_object* v_x_394_, lean_object* v_h__1_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = lean_apply_2(v_h__1_395_, v_x_394_, lean_box(0));
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filterMap_match__1_splitter(lean_object* v_00_u03b1_397_, lean_object* v_00_u03b3_398_, lean_object* v_motive_399_, lean_object* v_x_400_, lean_object* v_h__1_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = lean_apply_2(v_h__1_401_, v_x_400_, lean_box(0));
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(uint8_t v_x_403_, lean_object* v_h__1_404_, lean_object* v_h__2_405_){
_start:
{
if (v_x_403_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec(v_h__2_405_);
v___x_406_ = lean_box(0);
v___x_407_ = lean_apply_1(v_h__1_404_, v___x_406_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v_h__1_404_);
v___x_408_ = lean_box(0);
v___x_409_ = lean_apply_1(v_h__2_405_, v___x_408_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg___boxed(lean_object* v_x_410_, lean_object* v_h__1_411_, lean_object* v_h__2_412_){
_start:
{
uint8_t v_x_22__boxed_413_; lean_object* v_res_414_; 
v_x_22__boxed_413_ = lean_unbox(v_x_410_);
v_res_414_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(v_x_22__boxed_413_, v_h__1_411_, v_h__2_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(lean_object* v_motive_415_, uint8_t v_x_416_, lean_object* v_h__1_417_, lean_object* v_h__2_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(v_x_416_, v_h__1_417_, v_h__2_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___boxed(lean_object* v_motive_420_, lean_object* v_x_421_, lean_object* v_h__1_422_, lean_object* v_h__2_423_){
_start:
{
uint8_t v_x_33__boxed_424_; lean_object* v_res_425_; 
v_x_33__boxed_424_ = lean_unbox(v_x_421_);
v_res_425_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(v_motive_420_, v_x_33__boxed_424_, v_h__1_422_, v_h__2_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___redArg(lean_object* v_v_x3f_426_, lean_object* v_h__1_427_, lean_object* v_h__2_428_){
_start:
{
if (lean_obj_tag(v_v_x3f_426_) == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v_h__2_428_);
v___x_429_ = lean_box(0);
v___x_430_ = lean_apply_1(v_h__1_427_, v___x_429_);
return v___x_430_;
}
else
{
lean_object* v_val_431_; lean_object* v___x_432_; 
lean_dec(v_h__1_427_);
v_val_431_ = lean_ctor_get(v_v_x3f_426_, 0);
lean_inc(v_val_431_);
lean_dec_ref(v_v_x3f_426_);
v___x_432_ = lean_apply_1(v_h__2_428_, v_val_431_);
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(lean_object* v_00_u03b1_433_, lean_object* v_00_u03b2_434_, lean_object* v_k_435_, lean_object* v_motive_436_, lean_object* v_v_x3f_437_, lean_object* v_h__1_438_, lean_object* v_h__2_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___redArg(v_v_x3f_437_, v_h__1_438_, v_h__2_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___boxed(lean_object* v_00_u03b1_441_, lean_object* v_00_u03b2_442_, lean_object* v_k_443_, lean_object* v_motive_444_, lean_object* v_v_x3f_445_, lean_object* v_h__1_446_, lean_object* v_h__2_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(v_00_u03b1_441_, v_00_u03b2_442_, v_k_443_, v_motive_444_, v_v_x3f_445_, v_h__1_446_, v_h__2_447_);
lean_dec(v_k_443_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_449_, lean_object* v_h__1_450_, lean_object* v_h__2_451_){
_start:
{
if (lean_obj_tag(v_x_449_) == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec(v_h__2_451_);
v___x_452_ = lean_box(0);
v___x_453_ = lean_apply_1(v_h__1_450_, v___x_452_);
return v___x_453_;
}
else
{
lean_object* v_val_454_; lean_object* v___x_455_; 
lean_dec(v_h__1_450_);
v_val_454_ = lean_ctor_get(v_x_449_, 0);
lean_inc(v_val_454_);
lean_dec_ref(v_x_449_);
v___x_455_ = lean_apply_1(v_h__2_451_, v_val_454_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b1_456_, lean_object* v_00_u03b2_457_, lean_object* v_k_458_, lean_object* v_motive_459_, lean_object* v_x_460_, lean_object* v_h__1_461_, lean_object* v_h__2_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(v_x_460_, v_h__1_461_, v_h__2_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object* v_00_u03b1_464_, lean_object* v_00_u03b2_465_, lean_object* v_k_466_, lean_object* v_motive_467_, lean_object* v_x_468_, lean_object* v_h__1_469_, lean_object* v_h__2_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_464_, v_00_u03b2_465_, v_k_466_, v_motive_467_, v_x_468_, v_h__1_469_, v_h__2_470_);
lean_dec(v_k_466_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter___redArg(lean_object* v_x_472_, lean_object* v_h__1_473_, lean_object* v_h__2_474_){
_start:
{
if (lean_obj_tag(v_x_472_) == 0)
{
lean_object* v___x_475_; 
lean_dec(v_h__2_474_);
v___x_475_ = lean_apply_1(v_h__1_473_, lean_box(0));
return v___x_475_;
}
else
{
lean_object* v_val_476_; lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v___x_479_; 
lean_dec(v_h__1_473_);
v_val_476_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_val_476_);
lean_dec_ref(v_x_472_);
v_fst_477_ = lean_ctor_get(v_val_476_, 0);
lean_inc(v_fst_477_);
v_snd_478_ = lean_ctor_get(v_val_476_, 1);
lean_inc(v_snd_478_);
lean_dec(v_val_476_);
v___x_479_ = lean_apply_3(v_h__2_474_, v_fst_477_, v_snd_478_, lean_box(0));
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter(lean_object* v_00_u03b1_480_, lean_object* v_00_u03b2_481_, lean_object* v_motive_482_, lean_object* v_x_483_, lean_object* v_h__1_484_, lean_object* v_h__2_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter___redArg(v_x_483_, v_h__1_484_, v_h__2_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___redArg(lean_object* v_x_487_, lean_object* v_h__1_488_, lean_object* v_h__2_489_){
_start:
{
if (lean_obj_tag(v_x_487_) == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec(v_h__2_489_);
v___x_490_ = lean_box(0);
v___x_491_ = lean_apply_1(v_h__1_488_, v___x_490_);
return v___x_491_;
}
else
{
lean_object* v_val_492_; lean_object* v___x_493_; 
lean_dec(v_h__1_488_);
v_val_492_ = lean_ctor_get(v_x_487_, 0);
lean_inc(v_val_492_);
lean_dec_ref(v_x_487_);
v___x_493_ = lean_apply_1(v_h__2_489_, v_val_492_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_k_496_, lean_object* v_motive_497_, lean_object* v_x_498_, lean_object* v_h__1_499_, lean_object* v_h__2_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___redArg(v_x_498_, v_h__1_499_, v_h__2_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object* v_00_u03b1_502_, lean_object* v_00_u03b2_503_, lean_object* v_k_504_, lean_object* v_motive_505_, lean_object* v_x_506_, lean_object* v_h__1_507_, lean_object* v_h__2_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_502_, v_00_u03b2_503_, v_k_504_, v_motive_505_, v_x_506_, v_h__1_507_, v_h__2_508_);
lean_dec(v_k_504_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(uint8_t v_x_510_, lean_object* v_h__1_511_, lean_object* v_h__2_512_, lean_object* v_h__3_513_){
_start:
{
switch(v_x_510_)
{
case 0:
{
lean_object* v___x_514_; 
lean_dec(v_h__3_513_);
lean_dec(v_h__2_512_);
v___x_514_ = lean_apply_1(v_h__1_511_, lean_box(0));
return v___x_514_;
}
case 1:
{
lean_object* v___x_515_; 
lean_dec(v_h__2_512_);
lean_dec(v_h__1_511_);
v___x_515_ = lean_apply_1(v_h__3_513_, lean_box(0));
return v___x_515_;
}
default: 
{
lean_object* v___x_516_; 
lean_dec(v_h__3_513_);
lean_dec(v_h__1_511_);
v___x_516_ = lean_apply_1(v_h__2_512_, lean_box(0));
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg___boxed(lean_object* v_x_517_, lean_object* v_h__1_518_, lean_object* v_h__2_519_, lean_object* v_h__3_520_){
_start:
{
uint8_t v_x_30__boxed_521_; lean_object* v_res_522_; 
v_x_30__boxed_521_ = lean_unbox(v_x_517_);
v_res_522_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(v_x_30__boxed_521_, v_h__1_518_, v_h__2_519_, v_h__3_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(lean_object* v_motive_523_, uint8_t v_x_524_, lean_object* v_h__1_525_, lean_object* v_h__2_526_, lean_object* v_h__3_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(v_x_524_, v_h__1_525_, v_h__2_526_, v_h__3_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___boxed(lean_object* v_motive_529_, lean_object* v_x_530_, lean_object* v_h__1_531_, lean_object* v_h__2_532_, lean_object* v_h__3_533_){
_start:
{
uint8_t v_x_39__boxed_534_; lean_object* v_res_535_; 
v_x_39__boxed_534_ = lean_unbox(v_x_530_);
v_res_535_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(v_motive_529_, v_x_39__boxed_534_, v_h__1_531_, v_h__2_532_, v_h__3_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter___redArg(lean_object* v_x_536_, lean_object* v_h__1_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_apply_4(v_h__1_537_, v_x_536_, lean_box(0), lean_box(0), lean_box(0));
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter(lean_object* v_00_u03b1_539_, lean_object* v_00_u03b2_540_, lean_object* v_l_x27_541_, lean_object* v_motive_542_, lean_object* v_x_543_, lean_object* v_h__1_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = lean_apply_4(v_h__1_544_, v_x_543_, lean_box(0), lean_box(0), lean_box(0));
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter___boxed(lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_, lean_object* v_l_x27_548_, lean_object* v_motive_549_, lean_object* v_x_550_, lean_object* v_h__1_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter(v_00_u03b1_546_, v_00_u03b2_547_, v_l_x27_548_, v_motive_549_, v_x_550_, v_h__1_551_);
lean_dec(v_l_x27_548_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object* v_l_553_, lean_object* v_h__1_554_, lean_object* v_h__2_555_){
_start:
{
if (lean_obj_tag(v_l_553_) == 0)
{
lean_object* v_size_556_; lean_object* v_k_557_; lean_object* v_v_558_; lean_object* v_l_559_; lean_object* v_r_560_; lean_object* v___x_561_; 
lean_dec(v_h__1_554_);
v_size_556_ = lean_ctor_get(v_l_553_, 0);
lean_inc(v_size_556_);
v_k_557_ = lean_ctor_get(v_l_553_, 1);
lean_inc(v_k_557_);
v_v_558_ = lean_ctor_get(v_l_553_, 2);
lean_inc(v_v_558_);
v_l_559_ = lean_ctor_get(v_l_553_, 3);
lean_inc(v_l_559_);
v_r_560_ = lean_ctor_get(v_l_553_, 4);
lean_inc(v_r_560_);
lean_dec_ref(v_l_553_);
v___x_561_ = lean_apply_5(v_h__2_555_, v_size_556_, v_k_557_, v_v_558_, v_l_559_, v_r_560_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec(v_h__2_555_);
v___x_562_ = lean_box(0);
v___x_563_ = lean_apply_1(v_h__1_554_, v___x_562_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object* v_00_u03b1_564_, lean_object* v_00_u03b2_565_, lean_object* v_motive_566_, lean_object* v_l_567_, lean_object* v_h__1_568_, lean_object* v_h__2_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(v_l_567_, v_h__1_568_, v_h__2_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object* v_t_571_, lean_object* v_h__1_572_, lean_object* v_h__2_573_){
_start:
{
if (lean_obj_tag(v_t_571_) == 0)
{
lean_object* v_size_574_; lean_object* v_k_575_; lean_object* v_v_576_; lean_object* v_l_577_; lean_object* v_r_578_; lean_object* v___x_579_; 
lean_dec(v_h__1_572_);
v_size_574_ = lean_ctor_get(v_t_571_, 0);
lean_inc(v_size_574_);
v_k_575_ = lean_ctor_get(v_t_571_, 1);
lean_inc(v_k_575_);
v_v_576_ = lean_ctor_get(v_t_571_, 2);
lean_inc(v_v_576_);
v_l_577_ = lean_ctor_get(v_t_571_, 3);
lean_inc(v_l_577_);
v_r_578_ = lean_ctor_get(v_t_571_, 4);
lean_inc(v_r_578_);
lean_dec_ref(v_t_571_);
v___x_579_ = lean_apply_5(v_h__2_573_, v_size_574_, v_k_575_, v_v_576_, v_l_577_, v_r_578_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_h__2_573_);
v___x_580_ = lean_box(0);
v___x_581_ = lean_apply_1(v_h__1_572_, v___x_580_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object* v_00_u03b1_582_, lean_object* v_00_u03b2_583_, lean_object* v_motive_584_, lean_object* v_t_585_, lean_object* v_h__1_586_, lean_object* v_h__2_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(v_t_585_, v_h__1_586_, v_h__2_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter___redArg(lean_object* v_____do__lift_589_, lean_object* v_h__1_590_, lean_object* v_h__2_591_){
_start:
{
if (lean_obj_tag(v_____do__lift_589_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_593_; 
lean_dec(v_h__2_591_);
v_a_592_ = lean_ctor_get(v_____do__lift_589_, 0);
lean_inc(v_a_592_);
lean_dec_ref(v_____do__lift_589_);
v___x_593_ = lean_apply_1(v_h__1_590_, v_a_592_);
return v___x_593_;
}
else
{
lean_object* v_a_594_; lean_object* v___x_595_; 
lean_dec(v_h__1_590_);
v_a_594_ = lean_ctor_get(v_____do__lift_589_, 0);
lean_inc(v_a_594_);
lean_dec_ref(v_____do__lift_589_);
v___x_595_ = lean_apply_1(v_h__2_591_, v_a_594_);
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter(lean_object* v_00_u03b4_596_, lean_object* v_motive_597_, lean_object* v_____do__lift_598_, lean_object* v_h__1_599_, lean_object* v_h__2_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter___redArg(v_____do__lift_598_, v_h__1_599_, v_h__2_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter___redArg(lean_object* v_x_602_, lean_object* v_h__1_603_, lean_object* v_h__2_604_){
_start:
{
if (lean_obj_tag(v_x_602_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_606_; 
lean_dec(v_h__1_603_);
v_a_605_ = lean_ctor_get(v_x_602_, 0);
lean_inc(v_a_605_);
lean_dec_ref(v_x_602_);
v___x_606_ = lean_apply_1(v_h__2_604_, v_a_605_);
return v___x_606_;
}
else
{
lean_object* v_a_607_; lean_object* v___x_608_; 
lean_dec(v_h__2_604_);
v_a_607_ = lean_ctor_get(v_x_602_, 0);
lean_inc(v_a_607_);
lean_dec_ref(v_x_602_);
v___x_608_ = lean_apply_1(v_h__1_603_, v_a_607_);
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter(lean_object* v_00_u03b4_609_, lean_object* v_motive_610_, lean_object* v_x_611_, lean_object* v_h__1_612_, lean_object* v_h__2_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter___redArg(v_x_611_, v_h__1_612_, v_h__2_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_615_, lean_object* v_h__1_616_, lean_object* v_h__2_617_){
_start:
{
if (lean_obj_tag(v_b_615_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_619_; 
lean_dec(v_h__1_616_);
v_a_618_ = lean_ctor_get(v_b_615_, 0);
lean_inc(v_a_618_);
lean_dec_ref(v_b_615_);
v___x_619_ = lean_apply_1(v_h__2_617_, v_a_618_);
return v___x_619_;
}
else
{
lean_object* v_a_620_; lean_object* v___x_621_; 
lean_dec(v_h__2_617_);
v_a_620_ = lean_ctor_get(v_b_615_, 0);
lean_inc(v_a_620_);
lean_dec_ref(v_b_615_);
v___x_621_ = lean_apply_1(v_h__1_616_, v_a_620_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_622_, lean_object* v_motive_623_, lean_object* v_b_624_, lean_object* v_h__1_625_, lean_object* v_h__2_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(v_b_624_, v_h__1_625_, v_h__2_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_628_, lean_object* v_h__1_629_, lean_object* v_h__2_630_){
_start:
{
if (lean_obj_tag(v_x_628_) == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v_h__2_630_);
v___x_631_ = lean_box(0);
v___x_632_ = lean_apply_1(v_h__1_629_, v___x_631_);
return v___x_632_;
}
else
{
lean_object* v_val_633_; lean_object* v___x_634_; 
lean_dec(v_h__1_629_);
v_val_633_ = lean_ctor_get(v_x_628_, 0);
lean_inc(v_val_633_);
lean_dec_ref(v_x_628_);
v___x_634_ = lean_apply_1(v_h__2_630_, v_val_633_);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b2_635_, lean_object* v_motive_636_, lean_object* v_x_637_, lean_object* v_h__1_638_, lean_object* v_h__2_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(v_x_637_, v_h__1_638_, v_h__2_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter___redArg(lean_object* v_x_641_, lean_object* v_h__1_642_, lean_object* v_h__2_643_){
_start:
{
if (lean_obj_tag(v_x_641_) == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec(v_h__2_643_);
v___x_644_ = lean_box(0);
v___x_645_ = lean_apply_1(v_h__1_642_, v___x_644_);
return v___x_645_;
}
else
{
lean_object* v_val_646_; lean_object* v_fst_647_; lean_object* v_snd_648_; lean_object* v___x_649_; 
lean_dec(v_h__1_642_);
v_val_646_ = lean_ctor_get(v_x_641_, 0);
lean_inc(v_val_646_);
lean_dec_ref(v_x_641_);
v_fst_647_ = lean_ctor_get(v_val_646_, 0);
lean_inc(v_fst_647_);
v_snd_648_ = lean_ctor_get(v_val_646_, 1);
lean_inc(v_snd_648_);
lean_dec(v_val_646_);
v___x_649_ = lean_apply_2(v_h__2_643_, v_fst_647_, v_snd_648_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter(lean_object* v_00_u03b1_650_, lean_object* v_00_u03b2_651_, lean_object* v_motive_652_, lean_object* v_x_653_, lean_object* v_h__1_654_, lean_object* v_h__2_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter___redArg(v_x_653_, v_h__1_654_, v_h__2_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(lean_object* v_x_657_, lean_object* v_h__1_658_, lean_object* v_h__2_659_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec(v_h__2_659_);
v___x_660_ = lean_box(0);
v___x_661_ = lean_apply_1(v_h__1_658_, v___x_660_);
return v___x_661_;
}
else
{
lean_object* v_val_662_; lean_object* v___x_663_; 
lean_dec(v_h__1_658_);
v_val_662_ = lean_ctor_get(v_x_657_, 0);
lean_inc(v_val_662_);
lean_dec_ref(v_x_657_);
v___x_663_ = lean_apply_1(v_h__2_659_, v_val_662_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object* v_00_u03b2_664_, lean_object* v_motive_665_, lean_object* v_x_666_, lean_object* v_h__1_667_, lean_object* v_h__2_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(v_x_666_, v_h__1_667_, v_h__2_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter___redArg(lean_object* v_t_670_, lean_object* v_h__1_671_, lean_object* v_h__2_672_){
_start:
{
if (lean_obj_tag(v_t_670_) == 0)
{
lean_object* v_size_673_; lean_object* v_k_674_; lean_object* v_v_675_; lean_object* v_l_676_; lean_object* v_r_677_; lean_object* v___x_678_; 
lean_dec(v_h__1_671_);
v_size_673_ = lean_ctor_get(v_t_670_, 0);
lean_inc(v_size_673_);
v_k_674_ = lean_ctor_get(v_t_670_, 1);
lean_inc(v_k_674_);
v_v_675_ = lean_ctor_get(v_t_670_, 2);
lean_inc(v_v_675_);
v_l_676_ = lean_ctor_get(v_t_670_, 3);
lean_inc(v_l_676_);
v_r_677_ = lean_ctor_get(v_t_670_, 4);
lean_inc(v_r_677_);
lean_dec_ref(v_t_670_);
v___x_678_ = lean_apply_6(v_h__2_672_, v_size_673_, v_k_674_, v_v_675_, v_l_676_, v_r_677_, lean_box(0));
return v___x_678_;
}
else
{
lean_object* v___x_679_; 
lean_dec(v_h__2_672_);
v___x_679_ = lean_apply_1(v_h__1_671_, lean_box(0));
return v___x_679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter(lean_object* v_00_u03b1_680_, lean_object* v_00_u03b2_681_, lean_object* v_motive_682_, lean_object* v_t_683_, lean_object* v_hl_684_, lean_object* v_h__1_685_, lean_object* v_h__2_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter___redArg(v_t_683_, v_h__1_685_, v_h__2_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___redArg(lean_object* v_x_688_, lean_object* v_h__1_689_, lean_object* v_h__2_690_){
_start:
{
if (lean_obj_tag(v_x_688_) == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v_h__2_690_);
v___x_691_ = lean_box(0);
v___x_692_ = lean_apply_1(v_h__1_689_, v___x_691_);
return v___x_692_;
}
else
{
lean_object* v_val_693_; lean_object* v___x_694_; 
lean_dec(v_h__1_689_);
v_val_693_ = lean_ctor_get(v_x_688_, 0);
lean_inc(v_val_693_);
lean_dec_ref(v_x_688_);
v___x_694_ = lean_apply_1(v_h__2_690_, v_val_693_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter(lean_object* v_00_u03b2_695_, lean_object* v_motive_696_, lean_object* v_x_697_, lean_object* v_h__1_698_, lean_object* v_h__2_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___redArg(v_x_697_, v_h__1_698_, v_h__2_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t v_x_701_, lean_object* v_h__1_702_, lean_object* v_h__2_703_, lean_object* v_h__3_704_){
_start:
{
switch(v_x_701_)
{
case 0:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec(v_h__3_704_);
lean_dec(v_h__2_703_);
v___x_705_ = lean_box(0);
v___x_706_ = lean_apply_1(v_h__1_702_, v___x_705_);
return v___x_706_;
}
case 1:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec(v_h__2_703_);
lean_dec(v_h__1_702_);
v___x_707_ = lean_box(0);
v___x_708_ = lean_apply_1(v_h__3_704_, v___x_707_);
return v___x_708_;
}
default: 
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec(v_h__3_704_);
lean_dec(v_h__1_702_);
v___x_709_ = lean_box(0);
v___x_710_ = lean_apply_1(v_h__2_703_, v___x_709_);
return v___x_710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object* v_x_711_, lean_object* v_h__1_712_, lean_object* v_h__2_713_, lean_object* v_h__3_714_){
_start:
{
uint8_t v_x_30__boxed_715_; lean_object* v_res_716_; 
v_x_30__boxed_715_ = lean_unbox(v_x_711_);
v_res_716_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_30__boxed_715_, v_h__1_712_, v_h__2_713_, v_h__3_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object* v_motive_717_, uint8_t v_x_718_, lean_object* v_h__1_719_, lean_object* v_h__2_720_, lean_object* v_h__3_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_718_, v_h__1_719_, v_h__2_720_, v_h__3_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object* v_motive_723_, lean_object* v_x_724_, lean_object* v_h__1_725_, lean_object* v_h__2_726_, lean_object* v_h__3_727_){
_start:
{
uint8_t v_x_45__boxed_728_; lean_object* v_res_729_; 
v_x_45__boxed_728_ = lean_unbox(v_x_724_);
v_res_729_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_723_, v_x_45__boxed_728_, v_h__1_725_, v_h__2_726_, v_h__3_727_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter___redArg(lean_object* v_x_730_, lean_object* v_h__1_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = lean_apply_4(v_h__1_731_, v_x_730_, lean_box(0), lean_box(0), lean_box(0));
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter(lean_object* v_00_u03b1_733_, lean_object* v_00_u03b2_734_, lean_object* v_l_x27_735_, lean_object* v_motive_736_, lean_object* v_x_737_, lean_object* v_h__1_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = lean_apply_4(v_h__1_738_, v_x_737_, lean_box(0), lean_box(0), lean_box(0));
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter___boxed(lean_object* v_00_u03b1_740_, lean_object* v_00_u03b2_741_, lean_object* v_l_x27_742_, lean_object* v_motive_743_, lean_object* v_x_744_, lean_object* v_h__1_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter(v_00_u03b1_740_, v_00_u03b2_741_, v_l_x27_742_, v_motive_743_, v_x_744_, v_h__1_745_);
lean_dec(v_l_x27_742_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___redArg(lean_object* v_t_747_, lean_object* v_h__1_748_, lean_object* v_h__2_749_){
_start:
{
if (lean_obj_tag(v_t_747_) == 0)
{
lean_object* v_size_750_; lean_object* v_k_751_; lean_object* v_v_752_; lean_object* v_l_753_; lean_object* v_r_754_; lean_object* v___x_755_; 
lean_dec(v_h__1_748_);
v_size_750_ = lean_ctor_get(v_t_747_, 0);
lean_inc(v_size_750_);
v_k_751_ = lean_ctor_get(v_t_747_, 1);
lean_inc(v_k_751_);
v_v_752_ = lean_ctor_get(v_t_747_, 2);
lean_inc(v_v_752_);
v_l_753_ = lean_ctor_get(v_t_747_, 3);
lean_inc(v_l_753_);
v_r_754_ = lean_ctor_get(v_t_747_, 4);
lean_inc(v_r_754_);
lean_dec_ref(v_t_747_);
v___x_755_ = lean_apply_5(v_h__2_749_, v_size_750_, v_k_751_, v_v_752_, v_l_753_, v_r_754_);
return v___x_755_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec(v_h__2_749_);
v___x_756_ = lean_box(0);
v___x_757_ = lean_apply_1(v_h__1_748_, v___x_756_);
return v___x_757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter(lean_object* v_00_u03b1_758_, lean_object* v_00_u03b2_759_, lean_object* v_motive_760_, lean_object* v_t_761_, lean_object* v_h__1_762_, lean_object* v_h__2_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___redArg(v_t_761_, v_h__1_762_, v_h__2_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter___redArg(lean_object* v_x_765_, lean_object* v_h__1_766_, lean_object* v_h__2_767_){
_start:
{
if (lean_obj_tag(v_x_765_) == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec(v_h__1_766_);
v___x_768_ = lean_box(0);
v___x_769_ = lean_apply_1(v_h__2_767_, v___x_768_);
return v___x_769_;
}
else
{
lean_object* v_val_770_; lean_object* v___x_771_; 
lean_dec(v_h__2_767_);
v_val_770_ = lean_ctor_get(v_x_765_, 0);
lean_inc(v_val_770_);
lean_dec_ref(v_x_765_);
v___x_771_ = lean_apply_1(v_h__1_766_, v_val_770_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter(lean_object* v_00_u03b1_772_, lean_object* v_00_u03b2_773_, lean_object* v_motive_774_, lean_object* v_x_775_, lean_object* v_h__1_776_, lean_object* v_h__2_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter___redArg(v_x_775_, v_h__1_776_, v_h__2_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_779_, lean_object* v_h__1_780_, lean_object* v_h__2_781_){
_start:
{
if (lean_obj_tag(v_x_779_) == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec(v_h__1_780_);
v___x_782_ = lean_box(0);
v___x_783_ = lean_apply_1(v_h__2_781_, v___x_782_);
return v___x_783_;
}
else
{
lean_object* v_val_784_; lean_object* v___x_785_; 
lean_dec(v_h__2_781_);
v_val_784_ = lean_ctor_get(v_x_779_, 0);
lean_inc(v_val_784_);
lean_dec_ref(v_x_779_);
v___x_785_ = lean_apply_1(v_h__1_780_, v_val_784_);
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_786_, lean_object* v_motive_787_, lean_object* v_x_788_, lean_object* v_h__1_789_, lean_object* v_h__2_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter___redArg(v_x_788_, v_h__1_789_, v_h__2_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_792_, lean_object* v_h__1_793_, lean_object* v_h__2_794_){
_start:
{
if (lean_obj_tag(v_x_792_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_796_; 
lean_dec(v_h__2_794_);
v_a_795_ = lean_ctor_get(v_x_792_, 0);
lean_inc(v_a_795_);
lean_dec_ref(v_x_792_);
v___x_796_ = lean_apply_1(v_h__1_793_, v_a_795_);
return v___x_796_;
}
else
{
lean_object* v_a_797_; lean_object* v___x_798_; 
lean_dec(v_h__1_793_);
v_a_797_ = lean_ctor_get(v_x_792_, 0);
lean_inc(v_a_797_);
lean_dec_ref(v_x_792_);
v___x_798_ = lean_apply_1(v_h__2_794_, v_a_797_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_799_, lean_object* v_motive_800_, lean_object* v_x_801_, lean_object* v_h__1_802_, lean_object* v_h__2_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(v_x_801_, v_h__1_802_, v_h__2_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_805_, lean_object* v_h__1_806_, lean_object* v_h__2_807_){
_start:
{
if (lean_obj_tag(v_x_805_) == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v_h__1_806_);
v___x_808_ = lean_box(0);
v___x_809_ = lean_apply_1(v_h__2_807_, v___x_808_);
return v___x_809_;
}
else
{
lean_object* v_val_810_; lean_object* v___x_811_; 
lean_dec(v_h__2_807_);
v_val_810_ = lean_ctor_get(v_x_805_, 0);
lean_inc(v_val_810_);
lean_dec_ref(v_x_805_);
v___x_811_ = lean_apply_1(v_h__1_806_, v_val_810_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_812_, lean_object* v_00_u03b2_813_, lean_object* v_motive_814_, lean_object* v_x_815_, lean_object* v_h__1_816_, lean_object* v_h__2_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(v_x_815_, v_h__1_816_, v_h__2_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(uint8_t v_x_819_, lean_object* v_h__1_820_, lean_object* v_h__2_821_){
_start:
{
if (v_x_819_ == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; 
lean_dec(v_h__1_820_);
v___x_822_ = lean_box(0);
v___x_823_ = lean_apply_1(v_h__2_821_, v___x_822_);
return v___x_823_;
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec(v_h__2_821_);
v___x_824_ = lean_box(0);
v___x_825_ = lean_apply_1(v_h__1_820_, v___x_824_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_826_, lean_object* v_h__1_827_, lean_object* v_h__2_828_){
_start:
{
uint8_t v_x_22__boxed_829_; lean_object* v_res_830_; 
v_x_22__boxed_829_ = lean_unbox(v_x_826_);
v_res_830_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(v_x_22__boxed_829_, v_h__1_827_, v_h__2_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(lean_object* v_motive_831_, uint8_t v_x_832_, lean_object* v_h__1_833_, lean_object* v_h__2_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(v_x_832_, v_h__1_833_, v_h__2_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_836_, lean_object* v_x_837_, lean_object* v_h__1_838_, lean_object* v_h__2_839_){
_start:
{
uint8_t v_x_33__boxed_840_; lean_object* v_res_841_; 
v_x_33__boxed_840_ = lean_unbox(v_x_837_);
v_res_841_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(v_motive_836_, v_x_33__boxed_840_, v_h__1_838_, v_h__2_839_);
return v_res_841_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Model(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Internal_List_Associative(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_List(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Subtype_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DTreeMap_Internal_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Linear(builtin);
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
