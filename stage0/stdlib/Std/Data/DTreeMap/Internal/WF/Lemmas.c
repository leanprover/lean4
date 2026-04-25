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
if (lean_obj_tag(v_l_17_) == 0)
{
lean_object* v_size_20_; lean_object* v_k_21_; lean_object* v_v_22_; lean_object* v_l_23_; lean_object* v_r_24_; lean_object* v___x_25_; 
lean_dec(v_h__1_18_);
v_size_20_ = lean_ctor_get(v_l_17_, 0);
lean_inc(v_size_20_);
v_k_21_ = lean_ctor_get(v_l_17_, 1);
lean_inc(v_k_21_);
v_v_22_ = lean_ctor_get(v_l_17_, 2);
lean_inc(v_v_22_);
v_l_23_ = lean_ctor_get(v_l_17_, 3);
lean_inc(v_l_23_);
v_r_24_ = lean_ctor_get(v_l_17_, 4);
lean_inc(v_r_24_);
lean_dec_ref(v_l_17_);
v___x_25_ = lean_apply_5(v_h__2_19_, v_size_20_, v_k_21_, v_v_22_, v_l_23_, v_r_24_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v_h__2_19_);
v___x_26_ = lean_box(0);
v___x_27_ = lean_apply_1(v_h__1_18_, v___x_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(lean_object* v_r_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_){
_start:
{
if (lean_obj_tag(v_r_28_) == 0)
{
lean_object* v_size_31_; lean_object* v_k_32_; lean_object* v_v_33_; lean_object* v_l_34_; lean_object* v_r_35_; lean_object* v___x_36_; 
lean_dec(v_h__1_29_);
v_size_31_ = lean_ctor_get(v_r_28_, 0);
lean_inc(v_size_31_);
v_k_32_ = lean_ctor_get(v_r_28_, 1);
lean_inc(v_k_32_);
v_v_33_ = lean_ctor_get(v_r_28_, 2);
lean_inc(v_v_33_);
v_l_34_ = lean_ctor_get(v_r_28_, 3);
lean_inc(v_l_34_);
v_r_35_ = lean_ctor_get(v_r_28_, 4);
lean_inc(v_r_35_);
lean_dec_ref(v_r_28_);
v___x_36_ = lean_apply_6(v_h__2_30_, v_size_31_, v_k_32_, v_v_33_, v_l_34_, v_r_35_, lean_box(0));
return v___x_36_;
}
else
{
lean_object* v___x_37_; 
lean_dec(v_h__2_30_);
v___x_37_ = lean_apply_1(v_h__1_29_, lean_box(0));
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(lean_object* v_00_u03b1_38_, lean_object* v_00_u03b2_39_, lean_object* v_l_40_, lean_object* v_motive_41_, lean_object* v_r_42_, lean_object* v_h_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_){
_start:
{
if (lean_obj_tag(v_r_42_) == 0)
{
lean_object* v_size_46_; lean_object* v_k_47_; lean_object* v_v_48_; lean_object* v_l_49_; lean_object* v_r_50_; lean_object* v___x_51_; 
lean_dec(v_h__1_44_);
v_size_46_ = lean_ctor_get(v_r_42_, 0);
lean_inc(v_size_46_);
v_k_47_ = lean_ctor_get(v_r_42_, 1);
lean_inc(v_k_47_);
v_v_48_ = lean_ctor_get(v_r_42_, 2);
lean_inc(v_v_48_);
v_l_49_ = lean_ctor_get(v_r_42_, 3);
lean_inc(v_l_49_);
v_r_50_ = lean_ctor_get(v_r_42_, 4);
lean_inc(v_r_50_);
lean_dec_ref(v_r_42_);
v___x_51_ = lean_apply_6(v_h__2_45_, v_size_46_, v_k_47_, v_v_48_, v_l_49_, v_r_50_, lean_box(0));
return v___x_51_;
}
else
{
lean_object* v___x_52_; 
lean_dec(v_h__2_45_);
v___x_52_ = lean_apply_1(v_h__1_44_, lean_box(0));
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___boxed(lean_object* v_00_u03b1_53_, lean_object* v_00_u03b2_54_, lean_object* v_l_55_, lean_object* v_motive_56_, lean_object* v_r_57_, lean_object* v_h_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(v_00_u03b1_53_, v_00_u03b2_54_, v_l_55_, v_motive_56_, v_r_57_, v_h_58_, v_h__1_59_, v_h__2_60_);
lean_dec(v_l_55_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(lean_object* v_l_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_){
_start:
{
if (lean_obj_tag(v_l_62_) == 0)
{
lean_object* v_size_65_; lean_object* v_k_66_; lean_object* v_v_67_; lean_object* v_l_68_; lean_object* v_r_69_; lean_object* v___x_70_; 
lean_dec(v_h__1_63_);
v_size_65_ = lean_ctor_get(v_l_62_, 0);
lean_inc(v_size_65_);
v_k_66_ = lean_ctor_get(v_l_62_, 1);
lean_inc(v_k_66_);
v_v_67_ = lean_ctor_get(v_l_62_, 2);
lean_inc(v_v_67_);
v_l_68_ = lean_ctor_get(v_l_62_, 3);
lean_inc(v_l_68_);
v_r_69_ = lean_ctor_get(v_l_62_, 4);
lean_inc(v_r_69_);
lean_dec_ref(v_l_62_);
v___x_70_ = lean_apply_7(v_h__2_64_, v_size_65_, v_k_66_, v_v_67_, v_l_68_, v_r_69_, lean_box(0), lean_box(0));
return v___x_70_;
}
else
{
lean_object* v___x_71_; 
lean_dec(v_h__2_64_);
v___x_71_ = lean_apply_2(v_h__1_63_, lean_box(0), lean_box(0));
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(lean_object* v_00_u03b1_72_, lean_object* v_00_u03b2_73_, lean_object* v_r_74_, lean_object* v_motive_75_, lean_object* v_l_76_, lean_object* v_h_77_, lean_object* v_h_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
if (lean_obj_tag(v_l_76_) == 0)
{
lean_object* v_size_81_; lean_object* v_k_82_; lean_object* v_v_83_; lean_object* v_l_84_; lean_object* v_r_85_; lean_object* v___x_86_; 
lean_dec(v_h__1_79_);
v_size_81_ = lean_ctor_get(v_l_76_, 0);
lean_inc(v_size_81_);
v_k_82_ = lean_ctor_get(v_l_76_, 1);
lean_inc(v_k_82_);
v_v_83_ = lean_ctor_get(v_l_76_, 2);
lean_inc(v_v_83_);
v_l_84_ = lean_ctor_get(v_l_76_, 3);
lean_inc(v_l_84_);
v_r_85_ = lean_ctor_get(v_l_76_, 4);
lean_inc(v_r_85_);
lean_dec_ref(v_l_76_);
v___x_86_ = lean_apply_7(v_h__2_80_, v_size_81_, v_k_82_, v_v_83_, v_l_84_, v_r_85_, lean_box(0), lean_box(0));
return v___x_86_;
}
else
{
lean_object* v___x_87_; 
lean_dec(v_h__2_80_);
v___x_87_ = lean_apply_2(v_h__1_79_, lean_box(0), lean_box(0));
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___boxed(lean_object* v_00_u03b1_88_, lean_object* v_00_u03b2_89_, lean_object* v_r_90_, lean_object* v_motive_91_, lean_object* v_l_92_, lean_object* v_h_93_, lean_object* v_h_94_, lean_object* v_h__1_95_, lean_object* v_h__2_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(v_00_u03b1_88_, v_00_u03b2_89_, v_r_90_, v_motive_91_, v_l_92_, v_h_93_, v_h_94_, v_h__1_95_, v_h__2_96_);
lean_dec(v_r_90_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object* v_r_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_){
_start:
{
if (lean_obj_tag(v_r_98_) == 0)
{
lean_object* v_size_101_; lean_object* v_k_102_; lean_object* v_v_103_; lean_object* v_l_104_; lean_object* v_r_105_; lean_object* v___x_106_; 
lean_dec(v_h__1_99_);
v_size_101_ = lean_ctor_get(v_r_98_, 0);
lean_inc(v_size_101_);
v_k_102_ = lean_ctor_get(v_r_98_, 1);
lean_inc(v_k_102_);
v_v_103_ = lean_ctor_get(v_r_98_, 2);
lean_inc(v_v_103_);
v_l_104_ = lean_ctor_get(v_r_98_, 3);
lean_inc(v_l_104_);
v_r_105_ = lean_ctor_get(v_r_98_, 4);
lean_inc(v_r_105_);
lean_dec_ref(v_r_98_);
v___x_106_ = lean_apply_7(v_h__2_100_, v_size_101_, v_k_102_, v_v_103_, v_l_104_, v_r_105_, lean_box(0), lean_box(0));
return v___x_106_;
}
else
{
lean_object* v___x_107_; 
lean_dec(v_h__2_100_);
v___x_107_ = lean_apply_2(v_h__1_99_, lean_box(0), lean_box(0));
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object* v_00_u03b1_108_, lean_object* v_00_u03b2_109_, lean_object* v_motive_110_, lean_object* v_r_111_, lean_object* v_hr_112_, lean_object* v_h__1_113_, lean_object* v_h__2_114_){
_start:
{
if (lean_obj_tag(v_r_111_) == 0)
{
lean_object* v_size_115_; lean_object* v_k_116_; lean_object* v_v_117_; lean_object* v_l_118_; lean_object* v_r_119_; lean_object* v___x_120_; 
lean_dec(v_h__1_113_);
v_size_115_ = lean_ctor_get(v_r_111_, 0);
lean_inc(v_size_115_);
v_k_116_ = lean_ctor_get(v_r_111_, 1);
lean_inc(v_k_116_);
v_v_117_ = lean_ctor_get(v_r_111_, 2);
lean_inc(v_v_117_);
v_l_118_ = lean_ctor_get(v_r_111_, 3);
lean_inc(v_l_118_);
v_r_119_ = lean_ctor_get(v_r_111_, 4);
lean_inc(v_r_119_);
lean_dec_ref(v_r_111_);
v___x_120_ = lean_apply_7(v_h__2_114_, v_size_115_, v_k_116_, v_v_117_, v_l_118_, v_r_119_, lean_box(0), lean_box(0));
return v___x_120_;
}
else
{
lean_object* v___x_121_; 
lean_dec(v_h__2_114_);
v___x_121_ = lean_apply_2(v_h__1_113_, lean_box(0), lean_box(0));
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___redArg(lean_object* v_x_122_, lean_object* v_h__1_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_apply_3(v_h__1_123_, v_x_122_, lean_box(0), lean_box(0));
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_l_127_, lean_object* v_l_x27_x27_128_, lean_object* v_motive_129_, lean_object* v_x_130_, lean_object* v_h__1_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_apply_3(v_h__1_131_, v_x_130_, lean_box(0), lean_box(0));
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___boxed(lean_object* v_00_u03b1_133_, lean_object* v_00_u03b2_134_, lean_object* v_l_135_, lean_object* v_l_x27_x27_136_, lean_object* v_motive_137_, lean_object* v_x_138_, lean_object* v_h__1_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(v_00_u03b1_133_, v_00_u03b2_134_, v_l_135_, v_l_x27_x27_136_, v_motive_137_, v_x_138_, v_h__1_139_);
lean_dec(v_l_x27_x27_136_);
lean_dec(v_l_135_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___redArg(lean_object* v_x_141_, lean_object* v_h__1_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_apply_3(v_h__1_142_, v_x_141_, lean_box(0), lean_box(0));
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(lean_object* v_00_u03b1_144_, lean_object* v_00_u03b2_145_, lean_object* v_r_146_, lean_object* v_r_x27_147_, lean_object* v_motive_148_, lean_object* v_x_149_, lean_object* v_h__1_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_apply_3(v_h__1_150_, v_x_149_, lean_box(0), lean_box(0));
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___boxed(lean_object* v_00_u03b1_152_, lean_object* v_00_u03b2_153_, lean_object* v_r_154_, lean_object* v_r_x27_155_, lean_object* v_motive_156_, lean_object* v_x_157_, lean_object* v_h__1_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(v_00_u03b1_152_, v_00_u03b2_153_, v_r_154_, v_r_x27_155_, v_motive_156_, v_x_157_, v_h__1_158_);
lean_dec(v_r_x27_155_);
lean_dec(v_r_154_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object* v_t_160_, lean_object* v_h__1_161_, lean_object* v_h__2_162_){
_start:
{
if (lean_obj_tag(v_t_160_) == 0)
{
lean_object* v_size_163_; lean_object* v_k_164_; lean_object* v_v_165_; lean_object* v_l_166_; lean_object* v_r_167_; lean_object* v___x_168_; 
lean_dec(v_h__1_161_);
v_size_163_ = lean_ctor_get(v_t_160_, 0);
lean_inc(v_size_163_);
v_k_164_ = lean_ctor_get(v_t_160_, 1);
lean_inc(v_k_164_);
v_v_165_ = lean_ctor_get(v_t_160_, 2);
lean_inc(v_v_165_);
v_l_166_ = lean_ctor_get(v_t_160_, 3);
lean_inc(v_l_166_);
v_r_167_ = lean_ctor_get(v_t_160_, 4);
lean_inc(v_r_167_);
lean_dec_ref(v_t_160_);
v___x_168_ = lean_apply_6(v_h__2_162_, v_size_163_, v_k_164_, v_v_165_, v_l_166_, v_r_167_, lean_box(0));
return v___x_168_;
}
else
{
lean_object* v___x_169_; 
lean_dec(v_h__2_162_);
v___x_169_ = lean_apply_1(v_h__1_161_, lean_box(0));
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object* v_00_u03b1_170_, lean_object* v_00_u03b2_171_, lean_object* v_motive_172_, lean_object* v_t_173_, lean_object* v_hr_174_, lean_object* v_h__1_175_, lean_object* v_h__2_176_){
_start:
{
if (lean_obj_tag(v_t_173_) == 0)
{
lean_object* v_size_177_; lean_object* v_k_178_; lean_object* v_v_179_; lean_object* v_l_180_; lean_object* v_r_181_; lean_object* v___x_182_; 
lean_dec(v_h__1_175_);
v_size_177_ = lean_ctor_get(v_t_173_, 0);
lean_inc(v_size_177_);
v_k_178_ = lean_ctor_get(v_t_173_, 1);
lean_inc(v_k_178_);
v_v_179_ = lean_ctor_get(v_t_173_, 2);
lean_inc(v_v_179_);
v_l_180_ = lean_ctor_get(v_t_173_, 3);
lean_inc(v_l_180_);
v_r_181_ = lean_ctor_get(v_t_173_, 4);
lean_inc(v_r_181_);
lean_dec_ref(v_t_173_);
v___x_182_ = lean_apply_6(v_h__2_176_, v_size_177_, v_k_178_, v_v_179_, v_l_180_, v_r_181_, lean_box(0));
return v___x_182_;
}
else
{
lean_object* v___x_183_; 
lean_dec(v_h__2_176_);
v___x_183_ = lean_apply_1(v_h__1_175_, lean_box(0));
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___redArg(lean_object* v_x_184_, lean_object* v_h__1_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_apply_3(v_h__1_185_, v_x_184_, lean_box(0), lean_box(0));
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(lean_object* v_00_u03b1_187_, lean_object* v_00_u03b2_188_, lean_object* v_szl_189_, lean_object* v_k_x27_190_, lean_object* v_v_x27_191_, lean_object* v_l_x27_192_, lean_object* v_r_x27_193_, lean_object* v_l_x27_x27_194_, lean_object* v_motive_195_, lean_object* v_x_196_, lean_object* v_h__1_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_apply_3(v_h__1_197_, v_x_196_, lean_box(0), lean_box(0));
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___boxed(lean_object* v_00_u03b1_199_, lean_object* v_00_u03b2_200_, lean_object* v_szl_201_, lean_object* v_k_x27_202_, lean_object* v_v_x27_203_, lean_object* v_l_x27_204_, lean_object* v_r_x27_205_, lean_object* v_l_x27_x27_206_, lean_object* v_motive_207_, lean_object* v_x_208_, lean_object* v_h__1_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(v_00_u03b1_199_, v_00_u03b2_200_, v_szl_201_, v_k_x27_202_, v_v_x27_203_, v_l_x27_204_, v_r_x27_205_, v_l_x27_x27_206_, v_motive_207_, v_x_208_, v_h__1_209_);
lean_dec(v_l_x27_x27_206_);
lean_dec(v_r_x27_205_);
lean_dec(v_l_x27_204_);
lean_dec(v_v_x27_203_);
lean_dec(v_k_x27_202_);
lean_dec(v_szl_201_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___redArg(lean_object* v_x_211_, lean_object* v_h__1_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_apply_3(v_h__1_212_, v_x_211_, lean_box(0), lean_box(0));
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v_r_x27_216_, lean_object* v_szr_217_, lean_object* v_k_x27_x27_218_, lean_object* v_v_x27_x27_219_, lean_object* v_l_x27_x27_220_, lean_object* v_r_x27_x27_221_, lean_object* v_motive_222_, lean_object* v_x_223_, lean_object* v_h__1_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lean_apply_3(v_h__1_224_, v_x_223_, lean_box(0), lean_box(0));
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___boxed(lean_object* v_00_u03b1_226_, lean_object* v_00_u03b2_227_, lean_object* v_r_x27_228_, lean_object* v_szr_229_, lean_object* v_k_x27_x27_230_, lean_object* v_v_x27_x27_231_, lean_object* v_l_x27_x27_232_, lean_object* v_r_x27_x27_233_, lean_object* v_motive_234_, lean_object* v_x_235_, lean_object* v_h__1_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(v_00_u03b1_226_, v_00_u03b2_227_, v_r_x27_228_, v_szr_229_, v_k_x27_x27_230_, v_v_x27_x27_231_, v_l_x27_x27_232_, v_r_x27_x27_233_, v_motive_234_, v_x_235_, v_h__1_236_);
lean_dec(v_r_x27_x27_233_);
lean_dec(v_l_x27_x27_232_);
lean_dec(v_v_x27_x27_231_);
lean_dec(v_k_x27_x27_230_);
lean_dec(v_szr_229_);
lean_dec(v_r_x27_228_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(lean_object* v_l_238_, lean_object* v_h__1_239_, lean_object* v_h__2_240_){
_start:
{
if (lean_obj_tag(v_l_238_) == 0)
{
lean_object* v_size_241_; lean_object* v_k_242_; lean_object* v_v_243_; lean_object* v_l_244_; lean_object* v_r_245_; lean_object* v___x_246_; 
lean_dec(v_h__1_239_);
v_size_241_ = lean_ctor_get(v_l_238_, 0);
lean_inc(v_size_241_);
v_k_242_ = lean_ctor_get(v_l_238_, 1);
lean_inc(v_k_242_);
v_v_243_ = lean_ctor_get(v_l_238_, 2);
lean_inc(v_v_243_);
v_l_244_ = lean_ctor_get(v_l_238_, 3);
lean_inc(v_l_244_);
v_r_245_ = lean_ctor_get(v_l_238_, 4);
lean_inc(v_r_245_);
lean_dec_ref(v_l_238_);
v___x_246_ = lean_apply_6(v_h__2_240_, v_size_241_, v_k_242_, v_v_243_, v_l_244_, v_r_245_, lean_box(0));
return v___x_246_;
}
else
{
lean_object* v___x_247_; 
lean_dec(v_h__2_240_);
v___x_247_ = lean_apply_1(v_h__1_239_, lean_box(0));
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(lean_object* v_00_u03b1_248_, lean_object* v_00_u03b2_249_, lean_object* v_motive_250_, lean_object* v_l_251_, lean_object* v_hl_252_, lean_object* v_h__1_253_, lean_object* v_h__2_254_){
_start:
{
if (lean_obj_tag(v_l_251_) == 0)
{
lean_object* v_size_255_; lean_object* v_k_256_; lean_object* v_v_257_; lean_object* v_l_258_; lean_object* v_r_259_; lean_object* v___x_260_; 
lean_dec(v_h__1_253_);
v_size_255_ = lean_ctor_get(v_l_251_, 0);
lean_inc(v_size_255_);
v_k_256_ = lean_ctor_get(v_l_251_, 1);
lean_inc(v_k_256_);
v_v_257_ = lean_ctor_get(v_l_251_, 2);
lean_inc(v_v_257_);
v_l_258_ = lean_ctor_get(v_l_251_, 3);
lean_inc(v_l_258_);
v_r_259_ = lean_ctor_get(v_l_251_, 4);
lean_inc(v_r_259_);
lean_dec_ref(v_l_251_);
v___x_260_ = lean_apply_6(v_h__2_254_, v_size_255_, v_k_256_, v_v_257_, v_l_258_, v_r_259_, lean_box(0));
return v___x_260_;
}
else
{
lean_object* v___x_261_; 
lean_dec(v_h__2_254_);
v___x_261_ = lean_apply_1(v_h__1_253_, lean_box(0));
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object* v_x_262_, lean_object* v_h__1_263_, lean_object* v_h__2_264_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v_h__2_264_);
v___x_265_ = lean_box(0);
v___x_266_ = lean_apply_1(v_h__1_263_, v___x_265_);
return v___x_266_;
}
else
{
lean_object* v_val_267_; lean_object* v_fst_268_; lean_object* v_snd_269_; lean_object* v___x_270_; 
lean_dec(v_h__1_263_);
v_val_267_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_val_267_);
lean_dec_ref(v_x_262_);
v_fst_268_ = lean_ctor_get(v_val_267_, 0);
lean_inc(v_fst_268_);
v_snd_269_ = lean_ctor_get(v_val_267_, 1);
lean_inc(v_snd_269_);
lean_dec(v_val_267_);
v___x_270_ = lean_apply_2(v_h__2_264_, v_fst_268_, v_snd_269_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* v_00_u03b1_271_, lean_object* v_00_u03b2_272_, lean_object* v_motive_273_, lean_object* v_x_274_, lean_object* v_h__1_275_, lean_object* v_h__2_276_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec(v_h__2_276_);
v___x_277_ = lean_box(0);
v___x_278_ = lean_apply_1(v_h__1_275_, v___x_277_);
return v___x_278_;
}
else
{
lean_object* v_val_279_; lean_object* v_fst_280_; lean_object* v_snd_281_; lean_object* v___x_282_; 
lean_dec(v_h__1_275_);
v_val_279_ = lean_ctor_get(v_x_274_, 0);
lean_inc(v_val_279_);
lean_dec_ref(v_x_274_);
v_fst_280_ = lean_ctor_get(v_val_279_, 0);
lean_inc(v_fst_280_);
v_snd_281_ = lean_ctor_get(v_val_279_, 1);
lean_inc(v_snd_281_);
lean_dec(v_val_279_);
v___x_282_ = lean_apply_2(v_h__2_276_, v_fst_280_, v_snd_281_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(uint8_t v_x_283_, lean_object* v_h__1_284_, lean_object* v_h__2_285_, lean_object* v_h__3_286_){
_start:
{
switch(v_x_283_)
{
case 0:
{
lean_object* v___x_287_; 
lean_dec(v_h__3_286_);
lean_dec(v_h__2_285_);
v___x_287_ = lean_apply_1(v_h__1_284_, lean_box(0));
return v___x_287_;
}
case 1:
{
lean_object* v___x_288_; 
lean_dec(v_h__3_286_);
lean_dec(v_h__1_284_);
v___x_288_ = lean_apply_1(v_h__2_285_, lean_box(0));
return v___x_288_;
}
default: 
{
lean_object* v___x_289_; 
lean_dec(v_h__2_285_);
lean_dec(v_h__1_284_);
v___x_289_ = lean_apply_1(v_h__3_286_, lean_box(0));
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(lean_object* v_x_290_, lean_object* v_h__1_291_, lean_object* v_h__2_292_, lean_object* v_h__3_293_){
_start:
{
uint8_t v_x_33__boxed_294_; lean_object* v_res_295_; 
v_x_33__boxed_294_ = lean_unbox(v_x_290_);
v_res_295_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_33__boxed_294_, v_h__1_291_, v_h__2_292_, v_h__3_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object* v_motive_296_, uint8_t v_x_297_, lean_object* v_h__1_298_, lean_object* v_h__2_299_, lean_object* v_h__3_300_){
_start:
{
switch(v_x_297_)
{
case 0:
{
lean_object* v___x_301_; 
lean_dec(v_h__3_300_);
lean_dec(v_h__2_299_);
v___x_301_ = lean_apply_1(v_h__1_298_, lean_box(0));
return v___x_301_;
}
case 1:
{
lean_object* v___x_302_; 
lean_dec(v_h__3_300_);
lean_dec(v_h__1_298_);
v___x_302_ = lean_apply_1(v_h__2_299_, lean_box(0));
return v___x_302_;
}
default: 
{
lean_object* v___x_303_; 
lean_dec(v_h__2_299_);
lean_dec(v_h__1_298_);
v___x_303_ = lean_apply_1(v_h__3_300_, lean_box(0));
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(lean_object* v_motive_304_, lean_object* v_x_305_, lean_object* v_h__1_306_, lean_object* v_h__2_307_, lean_object* v_h__3_308_){
_start:
{
uint8_t v_x_42__boxed_309_; lean_object* v_res_310_; 
v_x_42__boxed_309_ = lean_unbox(v_x_305_);
v_res_310_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(v_motive_304_, v_x_42__boxed_309_, v_h__1_306_, v_h__2_307_, v_h__3_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(lean_object* v_x_311_, lean_object* v_h__1_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = lean_apply_4(v_h__1_312_, v_x_311_, lean_box(0), lean_box(0), lean_box(0));
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object* v_00_u03b1_314_, lean_object* v_00_u03b2_315_, lean_object* v_l_316_, lean_object* v_motive_317_, lean_object* v_x_318_, lean_object* v_h__1_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_apply_4(v_h__1_319_, v_x_318_, lean_box(0), lean_box(0), lean_box(0));
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(lean_object* v_00_u03b1_321_, lean_object* v_00_u03b2_322_, lean_object* v_l_323_, lean_object* v_motive_324_, lean_object* v_x_325_, lean_object* v_h__1_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_321_, v_00_u03b2_322_, v_l_323_, v_motive_324_, v_x_325_, v_h__1_326_);
lean_dec(v_l_323_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(uint8_t v_x_328_, lean_object* v_h__1_329_, lean_object* v_h__2_330_, lean_object* v_h__3_331_){
_start:
{
switch(v_x_328_)
{
case 0:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v_h__3_331_);
lean_dec(v_h__2_330_);
v___x_332_ = lean_box(0);
v___x_333_ = lean_apply_1(v_h__1_329_, v___x_332_);
return v___x_333_;
}
case 1:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec(v_h__2_330_);
lean_dec(v_h__1_329_);
v___x_334_ = lean_box(0);
v___x_335_ = lean_apply_1(v_h__3_331_, v___x_334_);
return v___x_335_;
}
default: 
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec(v_h__3_331_);
lean_dec(v_h__1_329_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_apply_1(v_h__2_330_, v___x_336_);
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(lean_object* v_x_338_, lean_object* v_h__1_339_, lean_object* v_h__2_340_, lean_object* v_h__3_341_){
_start:
{
uint8_t v_x_36__boxed_342_; lean_object* v_res_343_; 
v_x_36__boxed_342_ = lean_unbox(v_x_338_);
v_res_343_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_36__boxed_342_, v_h__1_339_, v_h__2_340_, v_h__3_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object* v_motive_344_, uint8_t v_x_345_, lean_object* v_h__1_346_, lean_object* v_h__2_347_, lean_object* v_h__3_348_){
_start:
{
switch(v_x_345_)
{
case 0:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec(v_h__3_348_);
lean_dec(v_h__2_347_);
v___x_349_ = lean_box(0);
v___x_350_ = lean_apply_1(v_h__1_346_, v___x_349_);
return v___x_350_;
}
case 1:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v_h__2_347_);
lean_dec(v_h__1_346_);
v___x_351_ = lean_box(0);
v___x_352_ = lean_apply_1(v_h__3_348_, v___x_351_);
return v___x_352_;
}
default: 
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v_h__3_348_);
lean_dec(v_h__1_346_);
v___x_353_ = lean_box(0);
v___x_354_ = lean_apply_1(v_h__2_347_, v___x_353_);
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(lean_object* v_motive_355_, lean_object* v_x_356_, lean_object* v_h__1_357_, lean_object* v_h__2_358_, lean_object* v_h__3_359_){
_start:
{
uint8_t v_x_51__boxed_360_; lean_object* v_res_361_; 
v_x_51__boxed_360_ = lean_unbox(v_x_356_);
v_res_361_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_355_, v_x_51__boxed_360_, v_h__1_357_, v_h__2_358_, v_h__3_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object* v_x_362_, lean_object* v_h__1_363_, lean_object* v_h__2_364_){
_start:
{
if (lean_obj_tag(v_x_362_) == 0)
{
lean_object* v___x_365_; 
lean_dec(v_h__2_364_);
v___x_365_ = lean_apply_1(v_h__1_363_, lean_box(0));
return v___x_365_;
}
else
{
lean_object* v_val_366_; lean_object* v___x_367_; 
lean_dec(v_h__1_363_);
v_val_366_ = lean_ctor_get(v_x_362_, 0);
lean_inc(v_val_366_);
lean_dec_ref(v_x_362_);
v___x_367_ = lean_apply_2(v_h__2_364_, v_val_366_, lean_box(0));
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_motive_370_, lean_object* v_x_371_, lean_object* v_h__1_372_, lean_object* v_h__2_373_){
_start:
{
if (lean_obj_tag(v_x_371_) == 0)
{
lean_object* v___x_374_; 
lean_dec(v_h__2_373_);
v___x_374_ = lean_apply_1(v_h__1_372_, lean_box(0));
return v___x_374_;
}
else
{
lean_object* v_val_375_; lean_object* v___x_376_; 
lean_dec(v_h__1_372_);
v_val_375_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_val_375_);
lean_dec_ref(v_x_371_);
v___x_376_ = lean_apply_2(v_h__2_373_, v_val_375_, lean_box(0));
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_377_, lean_object* v_h__1_378_, lean_object* v_h__2_379_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_h__2_379_);
v___x_380_ = lean_box(0);
v___x_381_ = lean_apply_1(v_h__1_378_, v___x_380_);
return v___x_381_;
}
else
{
lean_object* v_val_382_; lean_object* v___x_383_; 
lean_dec(v_h__1_378_);
v_val_382_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_val_382_);
lean_dec_ref(v_x_377_);
v___x_383_ = lean_apply_1(v_h__2_379_, v_val_382_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_384_, lean_object* v_00_u03b2_385_, lean_object* v_motive_386_, lean_object* v_x_387_, lean_object* v_h__1_388_, lean_object* v_h__2_389_){
_start:
{
if (lean_obj_tag(v_x_387_) == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v_h__2_389_);
v___x_390_ = lean_box(0);
v___x_391_ = lean_apply_1(v_h__1_388_, v___x_390_);
return v___x_391_;
}
else
{
lean_object* v_val_392_; lean_object* v___x_393_; 
lean_dec(v_h__1_388_);
v_val_392_ = lean_ctor_get(v_x_387_, 0);
lean_inc(v_val_392_);
lean_dec_ref(v_x_387_);
v___x_393_ = lean_apply_1(v_h__2_389_, v_val_392_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_394_, lean_object* v_h__1_395_, lean_object* v_h__2_396_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v_h__2_396_);
v___x_397_ = lean_box(0);
v___x_398_ = lean_apply_1(v_h__1_395_, v___x_397_);
return v___x_398_;
}
else
{
lean_object* v_head_399_; lean_object* v_tail_400_; lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v___x_403_; 
lean_dec(v_h__1_395_);
v_head_399_ = lean_ctor_get(v_x_394_, 0);
lean_inc(v_head_399_);
v_tail_400_ = lean_ctor_get(v_x_394_, 1);
lean_inc(v_tail_400_);
lean_dec_ref(v_x_394_);
v_fst_401_ = lean_ctor_get(v_head_399_, 0);
lean_inc(v_fst_401_);
v_snd_402_ = lean_ctor_get(v_head_399_, 1);
lean_inc(v_snd_402_);
lean_dec(v_head_399_);
v___x_403_ = lean_apply_3(v_h__2_396_, v_fst_401_, v_snd_402_, v_tail_400_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_404_, lean_object* v_00_u03b2_405_, lean_object* v_motive_406_, lean_object* v_x_407_, lean_object* v_h__1_408_, lean_object* v_h__2_409_){
_start:
{
if (lean_obj_tag(v_x_407_) == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec(v_h__2_409_);
v___x_410_ = lean_box(0);
v___x_411_ = lean_apply_1(v_h__1_408_, v___x_410_);
return v___x_411_;
}
else
{
lean_object* v_head_412_; lean_object* v_tail_413_; lean_object* v_fst_414_; lean_object* v_snd_415_; lean_object* v___x_416_; 
lean_dec(v_h__1_408_);
v_head_412_ = lean_ctor_get(v_x_407_, 0);
lean_inc(v_head_412_);
v_tail_413_ = lean_ctor_get(v_x_407_, 1);
lean_inc(v_tail_413_);
lean_dec_ref(v_x_407_);
v_fst_414_ = lean_ctor_get(v_head_412_, 0);
lean_inc(v_fst_414_);
v_snd_415_ = lean_ctor_get(v_head_412_, 1);
lean_inc(v_snd_415_);
lean_dec(v_head_412_);
v___x_416_ = lean_apply_3(v_h__2_409_, v_fst_414_, v_snd_415_, v_tail_413_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object* v_x_417_, lean_object* v_h__1_418_, lean_object* v_h__2_419_){
_start:
{
if (lean_obj_tag(v_x_417_) == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v_h__2_419_);
v___x_420_ = lean_box(0);
v___x_421_ = lean_apply_1(v_h__1_418_, v___x_420_);
return v___x_421_;
}
else
{
lean_object* v_val_422_; lean_object* v___x_423_; 
lean_dec(v_h__1_418_);
v_val_422_ = lean_ctor_get(v_x_417_, 0);
lean_inc(v_val_422_);
lean_dec_ref(v_x_417_);
v___x_423_ = lean_apply_1(v_h__2_419_, v_val_422_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_424_, lean_object* v_00_u03b2_425_, lean_object* v_motive_426_, lean_object* v_x_427_, lean_object* v_h__1_428_, lean_object* v_h__2_429_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec(v_h__2_429_);
v___x_430_ = lean_box(0);
v___x_431_ = lean_apply_1(v_h__1_428_, v___x_430_);
return v___x_431_;
}
else
{
lean_object* v_val_432_; lean_object* v___x_433_; 
lean_dec(v_h__1_428_);
v_val_432_ = lean_ctor_get(v_x_427_, 0);
lean_inc(v_val_432_);
lean_dec_ref(v_x_427_);
v___x_433_ = lean_apply_1(v_h__2_429_, v_val_432_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___redArg(lean_object* v_x_434_, lean_object* v_h__1_435_, lean_object* v_h__2_436_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec(v_h__2_436_);
v___x_437_ = lean_box(0);
v___x_438_ = lean_apply_1(v_h__1_435_, v___x_437_);
return v___x_438_;
}
else
{
lean_object* v_val_439_; lean_object* v___x_440_; 
lean_dec(v_h__1_435_);
v_val_439_ = lean_ctor_get(v_x_434_, 0);
lean_inc(v_val_439_);
lean_dec_ref(v_x_434_);
v___x_440_ = lean_apply_1(v_h__2_436_, v_val_439_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(lean_object* v_00_u03b1_441_, lean_object* v_00_u03b2_442_, lean_object* v_k_443_, lean_object* v_motive_444_, lean_object* v_x_445_, lean_object* v_h__1_446_, lean_object* v_h__2_447_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec(v_h__2_447_);
v___x_448_ = lean_box(0);
v___x_449_ = lean_apply_1(v_h__1_446_, v___x_448_);
return v___x_449_;
}
else
{
lean_object* v_val_450_; lean_object* v___x_451_; 
lean_dec(v_h__1_446_);
v_val_450_ = lean_ctor_get(v_x_445_, 0);
lean_inc(v_val_450_);
lean_dec_ref(v_x_445_);
v___x_451_ = lean_apply_1(v_h__2_447_, v_val_450_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___boxed(lean_object* v_00_u03b1_452_, lean_object* v_00_u03b2_453_, lean_object* v_k_454_, lean_object* v_motive_455_, lean_object* v_x_456_, lean_object* v_h__1_457_, lean_object* v_h__2_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(v_00_u03b1_452_, v_00_u03b2_453_, v_k_454_, v_motive_455_, v_x_456_, v_h__1_457_, v_h__2_458_);
lean_dec(v_k_454_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filterMap_match__1_splitter___redArg(lean_object* v_x_460_, lean_object* v_h__1_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = lean_apply_2(v_h__1_461_, v_x_460_, lean_box(0));
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filterMap_match__1_splitter(lean_object* v_00_u03b1_463_, lean_object* v_00_u03b3_464_, lean_object* v_motive_465_, lean_object* v_x_466_, lean_object* v_h__1_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lean_apply_2(v_h__1_467_, v_x_466_, lean_box(0));
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(uint8_t v_x_469_, lean_object* v_h__1_470_, lean_object* v_h__2_471_){
_start:
{
if (v_x_469_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec(v_h__2_471_);
v___x_472_ = lean_box(0);
v___x_473_ = lean_apply_1(v_h__1_470_, v___x_472_);
return v___x_473_;
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec(v_h__1_470_);
v___x_474_ = lean_box(0);
v___x_475_ = lean_apply_1(v_h__2_471_, v___x_474_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg___boxed(lean_object* v_x_476_, lean_object* v_h__1_477_, lean_object* v_h__2_478_){
_start:
{
uint8_t v_x_26__boxed_479_; lean_object* v_res_480_; 
v_x_26__boxed_479_ = lean_unbox(v_x_476_);
v_res_480_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(v_x_26__boxed_479_, v_h__1_477_, v_h__2_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(lean_object* v_motive_481_, uint8_t v_x_482_, lean_object* v_h__1_483_, lean_object* v_h__2_484_){
_start:
{
if (v_x_482_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v_h__2_484_);
v___x_485_ = lean_box(0);
v___x_486_ = lean_apply_1(v_h__1_483_, v___x_485_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v_h__1_483_);
v___x_487_ = lean_box(0);
v___x_488_ = lean_apply_1(v_h__2_484_, v___x_487_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___boxed(lean_object* v_motive_489_, lean_object* v_x_490_, lean_object* v_h__1_491_, lean_object* v_h__2_492_){
_start:
{
uint8_t v_x_37__boxed_493_; lean_object* v_res_494_; 
v_x_37__boxed_493_ = lean_unbox(v_x_490_);
v_res_494_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(v_motive_489_, v_x_37__boxed_493_, v_h__1_491_, v_h__2_492_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___redArg(lean_object* v_v_x3f_495_, lean_object* v_h__1_496_, lean_object* v_h__2_497_){
_start:
{
if (lean_obj_tag(v_v_x3f_495_) == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v_h__2_497_);
v___x_498_ = lean_box(0);
v___x_499_ = lean_apply_1(v_h__1_496_, v___x_498_);
return v___x_499_;
}
else
{
lean_object* v_val_500_; lean_object* v___x_501_; 
lean_dec(v_h__1_496_);
v_val_500_ = lean_ctor_get(v_v_x3f_495_, 0);
lean_inc(v_val_500_);
lean_dec_ref(v_v_x3f_495_);
v___x_501_ = lean_apply_1(v_h__2_497_, v_val_500_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(lean_object* v_00_u03b1_502_, lean_object* v_00_u03b2_503_, lean_object* v_k_504_, lean_object* v_motive_505_, lean_object* v_v_x3f_506_, lean_object* v_h__1_507_, lean_object* v_h__2_508_){
_start:
{
if (lean_obj_tag(v_v_x3f_506_) == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v_h__2_508_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_apply_1(v_h__1_507_, v___x_509_);
return v___x_510_;
}
else
{
lean_object* v_val_511_; lean_object* v___x_512_; 
lean_dec(v_h__1_507_);
v_val_511_ = lean_ctor_get(v_v_x3f_506_, 0);
lean_inc(v_val_511_);
lean_dec_ref(v_v_x3f_506_);
v___x_512_ = lean_apply_1(v_h__2_508_, v_val_511_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___boxed(lean_object* v_00_u03b1_513_, lean_object* v_00_u03b2_514_, lean_object* v_k_515_, lean_object* v_motive_516_, lean_object* v_v_x3f_517_, lean_object* v_h__1_518_, lean_object* v_h__2_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(v_00_u03b1_513_, v_00_u03b2_514_, v_k_515_, v_motive_516_, v_v_x3f_517_, v_h__1_518_, v_h__2_519_);
lean_dec(v_k_515_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_521_, lean_object* v_h__1_522_, lean_object* v_h__2_523_){
_start:
{
if (lean_obj_tag(v_x_521_) == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_dec(v_h__2_523_);
v___x_524_ = lean_box(0);
v___x_525_ = lean_apply_1(v_h__1_522_, v___x_524_);
return v___x_525_;
}
else
{
lean_object* v_val_526_; lean_object* v___x_527_; 
lean_dec(v_h__1_522_);
v_val_526_ = lean_ctor_get(v_x_521_, 0);
lean_inc(v_val_526_);
lean_dec_ref(v_x_521_);
v___x_527_ = lean_apply_1(v_h__2_523_, v_val_526_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b1_528_, lean_object* v_00_u03b2_529_, lean_object* v_k_530_, lean_object* v_motive_531_, lean_object* v_x_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_){
_start:
{
if (lean_obj_tag(v_x_532_) == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v_h__2_534_);
v___x_535_ = lean_box(0);
v___x_536_ = lean_apply_1(v_h__1_533_, v___x_535_);
return v___x_536_;
}
else
{
lean_object* v_val_537_; lean_object* v___x_538_; 
lean_dec(v_h__1_533_);
v_val_537_ = lean_ctor_get(v_x_532_, 0);
lean_inc(v_val_537_);
lean_dec_ref(v_x_532_);
v___x_538_ = lean_apply_1(v_h__2_534_, v_val_537_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object* v_00_u03b1_539_, lean_object* v_00_u03b2_540_, lean_object* v_k_541_, lean_object* v_motive_542_, lean_object* v_x_543_, lean_object* v_h__1_544_, lean_object* v_h__2_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_539_, v_00_u03b2_540_, v_k_541_, v_motive_542_, v_x_543_, v_h__1_544_, v_h__2_545_);
lean_dec(v_k_541_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter___redArg(lean_object* v_x_547_, lean_object* v_h__1_548_, lean_object* v_h__2_549_){
_start:
{
if (lean_obj_tag(v_x_547_) == 0)
{
lean_object* v___x_550_; 
lean_dec(v_h__2_549_);
v___x_550_ = lean_apply_1(v_h__1_548_, lean_box(0));
return v___x_550_;
}
else
{
lean_object* v_val_551_; lean_object* v_fst_552_; lean_object* v_snd_553_; lean_object* v___x_554_; 
lean_dec(v_h__1_548_);
v_val_551_ = lean_ctor_get(v_x_547_, 0);
lean_inc(v_val_551_);
lean_dec_ref(v_x_547_);
v_fst_552_ = lean_ctor_get(v_val_551_, 0);
lean_inc(v_fst_552_);
v_snd_553_ = lean_ctor_get(v_val_551_, 1);
lean_inc(v_snd_553_);
lean_dec(v_val_551_);
v___x_554_ = lean_apply_3(v_h__2_549_, v_fst_552_, v_snd_553_, lean_box(0));
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter(lean_object* v_00_u03b1_555_, lean_object* v_00_u03b2_556_, lean_object* v_motive_557_, lean_object* v_x_558_, lean_object* v_h__1_559_, lean_object* v_h__2_560_){
_start:
{
if (lean_obj_tag(v_x_558_) == 0)
{
lean_object* v___x_561_; 
lean_dec(v_h__2_560_);
v___x_561_ = lean_apply_1(v_h__1_559_, lean_box(0));
return v___x_561_;
}
else
{
lean_object* v_val_562_; lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v___x_565_; 
lean_dec(v_h__1_559_);
v_val_562_ = lean_ctor_get(v_x_558_, 0);
lean_inc(v_val_562_);
lean_dec_ref(v_x_558_);
v_fst_563_ = lean_ctor_get(v_val_562_, 0);
lean_inc(v_fst_563_);
v_snd_564_ = lean_ctor_get(v_val_562_, 1);
lean_inc(v_snd_564_);
lean_dec(v_val_562_);
v___x_565_ = lean_apply_3(v_h__2_560_, v_fst_563_, v_snd_564_, lean_box(0));
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___redArg(lean_object* v_x_566_, lean_object* v_h__1_567_, lean_object* v_h__2_568_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v_h__2_568_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_apply_1(v_h__1_567_, v___x_569_);
return v___x_570_;
}
else
{
lean_object* v_val_571_; lean_object* v___x_572_; 
lean_dec(v_h__1_567_);
v_val_571_ = lean_ctor_get(v_x_566_, 0);
lean_inc(v_val_571_);
lean_dec_ref(v_x_566_);
v___x_572_ = lean_apply_1(v_h__2_568_, v_val_571_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(lean_object* v_00_u03b1_573_, lean_object* v_00_u03b2_574_, lean_object* v_k_575_, lean_object* v_motive_576_, lean_object* v_x_577_, lean_object* v_h__1_578_, lean_object* v_h__2_579_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_h__2_579_);
v___x_580_ = lean_box(0);
v___x_581_ = lean_apply_1(v_h__1_578_, v___x_580_);
return v___x_581_;
}
else
{
lean_object* v_val_582_; lean_object* v___x_583_; 
lean_dec(v_h__1_578_);
v_val_582_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_val_582_);
lean_dec_ref(v_x_577_);
v___x_583_ = lean_apply_1(v_h__2_579_, v_val_582_);
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_k_586_, lean_object* v_motive_587_, lean_object* v_x_588_, lean_object* v_h__1_589_, lean_object* v_h__2_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_584_, v_00_u03b2_585_, v_k_586_, v_motive_587_, v_x_588_, v_h__1_589_, v_h__2_590_);
lean_dec(v_k_586_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(uint8_t v_x_592_, lean_object* v_h__1_593_, lean_object* v_h__2_594_, lean_object* v_h__3_595_){
_start:
{
switch(v_x_592_)
{
case 0:
{
lean_object* v___x_596_; 
lean_dec(v_h__3_595_);
lean_dec(v_h__2_594_);
v___x_596_ = lean_apply_1(v_h__1_593_, lean_box(0));
return v___x_596_;
}
case 1:
{
lean_object* v___x_597_; 
lean_dec(v_h__2_594_);
lean_dec(v_h__1_593_);
v___x_597_ = lean_apply_1(v_h__3_595_, lean_box(0));
return v___x_597_;
}
default: 
{
lean_object* v___x_598_; 
lean_dec(v_h__3_595_);
lean_dec(v_h__1_593_);
v___x_598_ = lean_apply_1(v_h__2_594_, lean_box(0));
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg___boxed(lean_object* v_x_599_, lean_object* v_h__1_600_, lean_object* v_h__2_601_, lean_object* v_h__3_602_){
_start:
{
uint8_t v_x_33__boxed_603_; lean_object* v_res_604_; 
v_x_33__boxed_603_ = lean_unbox(v_x_599_);
v_res_604_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(v_x_33__boxed_603_, v_h__1_600_, v_h__2_601_, v_h__3_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(lean_object* v_motive_605_, uint8_t v_x_606_, lean_object* v_h__1_607_, lean_object* v_h__2_608_, lean_object* v_h__3_609_){
_start:
{
switch(v_x_606_)
{
case 0:
{
lean_object* v___x_610_; 
lean_dec(v_h__3_609_);
lean_dec(v_h__2_608_);
v___x_610_ = lean_apply_1(v_h__1_607_, lean_box(0));
return v___x_610_;
}
case 1:
{
lean_object* v___x_611_; 
lean_dec(v_h__2_608_);
lean_dec(v_h__1_607_);
v___x_611_ = lean_apply_1(v_h__3_609_, lean_box(0));
return v___x_611_;
}
default: 
{
lean_object* v___x_612_; 
lean_dec(v_h__3_609_);
lean_dec(v_h__1_607_);
v___x_612_ = lean_apply_1(v_h__2_608_, lean_box(0));
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___boxed(lean_object* v_motive_613_, lean_object* v_x_614_, lean_object* v_h__1_615_, lean_object* v_h__2_616_, lean_object* v_h__3_617_){
_start:
{
uint8_t v_x_42__boxed_618_; lean_object* v_res_619_; 
v_x_42__boxed_618_ = lean_unbox(v_x_614_);
v_res_619_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(v_motive_613_, v_x_42__boxed_618_, v_h__1_615_, v_h__2_616_, v_h__3_617_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter___redArg(lean_object* v_x_620_, lean_object* v_h__1_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = lean_apply_4(v_h__1_621_, v_x_620_, lean_box(0), lean_box(0), lean_box(0));
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter(lean_object* v_00_u03b1_623_, lean_object* v_00_u03b2_624_, lean_object* v_l_x27_625_, lean_object* v_motive_626_, lean_object* v_x_627_, lean_object* v_h__1_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = lean_apply_4(v_h__1_628_, v_x_627_, lean_box(0), lean_box(0), lean_box(0));
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter___boxed(lean_object* v_00_u03b1_630_, lean_object* v_00_u03b2_631_, lean_object* v_l_x27_632_, lean_object* v_motive_633_, lean_object* v_x_634_, lean_object* v_h__1_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter(v_00_u03b1_630_, v_00_u03b2_631_, v_l_x27_632_, v_motive_633_, v_x_634_, v_h__1_635_);
lean_dec(v_l_x27_632_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object* v_l_637_, lean_object* v_h__1_638_, lean_object* v_h__2_639_){
_start:
{
if (lean_obj_tag(v_l_637_) == 0)
{
lean_object* v_size_640_; lean_object* v_k_641_; lean_object* v_v_642_; lean_object* v_l_643_; lean_object* v_r_644_; lean_object* v___x_645_; 
lean_dec(v_h__1_638_);
v_size_640_ = lean_ctor_get(v_l_637_, 0);
lean_inc(v_size_640_);
v_k_641_ = lean_ctor_get(v_l_637_, 1);
lean_inc(v_k_641_);
v_v_642_ = lean_ctor_get(v_l_637_, 2);
lean_inc(v_v_642_);
v_l_643_ = lean_ctor_get(v_l_637_, 3);
lean_inc(v_l_643_);
v_r_644_ = lean_ctor_get(v_l_637_, 4);
lean_inc(v_r_644_);
lean_dec_ref(v_l_637_);
v___x_645_ = lean_apply_5(v_h__2_639_, v_size_640_, v_k_641_, v_v_642_, v_l_643_, v_r_644_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec(v_h__2_639_);
v___x_646_ = lean_box(0);
v___x_647_ = lean_apply_1(v_h__1_638_, v___x_646_);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object* v_00_u03b1_648_, lean_object* v_00_u03b2_649_, lean_object* v_motive_650_, lean_object* v_l_651_, lean_object* v_h__1_652_, lean_object* v_h__2_653_){
_start:
{
if (lean_obj_tag(v_l_651_) == 0)
{
lean_object* v_size_654_; lean_object* v_k_655_; lean_object* v_v_656_; lean_object* v_l_657_; lean_object* v_r_658_; lean_object* v___x_659_; 
lean_dec(v_h__1_652_);
v_size_654_ = lean_ctor_get(v_l_651_, 0);
lean_inc(v_size_654_);
v_k_655_ = lean_ctor_get(v_l_651_, 1);
lean_inc(v_k_655_);
v_v_656_ = lean_ctor_get(v_l_651_, 2);
lean_inc(v_v_656_);
v_l_657_ = lean_ctor_get(v_l_651_, 3);
lean_inc(v_l_657_);
v_r_658_ = lean_ctor_get(v_l_651_, 4);
lean_inc(v_r_658_);
lean_dec_ref(v_l_651_);
v___x_659_ = lean_apply_5(v_h__2_653_, v_size_654_, v_k_655_, v_v_656_, v_l_657_, v_r_658_);
return v___x_659_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec(v_h__2_653_);
v___x_660_ = lean_box(0);
v___x_661_ = lean_apply_1(v_h__1_652_, v___x_660_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object* v_t_662_, lean_object* v_h__1_663_, lean_object* v_h__2_664_){
_start:
{
if (lean_obj_tag(v_t_662_) == 0)
{
lean_object* v_size_665_; lean_object* v_k_666_; lean_object* v_v_667_; lean_object* v_l_668_; lean_object* v_r_669_; lean_object* v___x_670_; 
lean_dec(v_h__1_663_);
v_size_665_ = lean_ctor_get(v_t_662_, 0);
lean_inc(v_size_665_);
v_k_666_ = lean_ctor_get(v_t_662_, 1);
lean_inc(v_k_666_);
v_v_667_ = lean_ctor_get(v_t_662_, 2);
lean_inc(v_v_667_);
v_l_668_ = lean_ctor_get(v_t_662_, 3);
lean_inc(v_l_668_);
v_r_669_ = lean_ctor_get(v_t_662_, 4);
lean_inc(v_r_669_);
lean_dec_ref(v_t_662_);
v___x_670_ = lean_apply_5(v_h__2_664_, v_size_665_, v_k_666_, v_v_667_, v_l_668_, v_r_669_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v_h__2_664_);
v___x_671_ = lean_box(0);
v___x_672_ = lean_apply_1(v_h__1_663_, v___x_671_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object* v_00_u03b1_673_, lean_object* v_00_u03b2_674_, lean_object* v_motive_675_, lean_object* v_t_676_, lean_object* v_h__1_677_, lean_object* v_h__2_678_){
_start:
{
if (lean_obj_tag(v_t_676_) == 0)
{
lean_object* v_size_679_; lean_object* v_k_680_; lean_object* v_v_681_; lean_object* v_l_682_; lean_object* v_r_683_; lean_object* v___x_684_; 
lean_dec(v_h__1_677_);
v_size_679_ = lean_ctor_get(v_t_676_, 0);
lean_inc(v_size_679_);
v_k_680_ = lean_ctor_get(v_t_676_, 1);
lean_inc(v_k_680_);
v_v_681_ = lean_ctor_get(v_t_676_, 2);
lean_inc(v_v_681_);
v_l_682_ = lean_ctor_get(v_t_676_, 3);
lean_inc(v_l_682_);
v_r_683_ = lean_ctor_get(v_t_676_, 4);
lean_inc(v_r_683_);
lean_dec_ref(v_t_676_);
v___x_684_ = lean_apply_5(v_h__2_678_, v_size_679_, v_k_680_, v_v_681_, v_l_682_, v_r_683_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec(v_h__2_678_);
v___x_685_ = lean_box(0);
v___x_686_ = lean_apply_1(v_h__1_677_, v___x_685_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter___redArg(lean_object* v_____do__lift_687_, lean_object* v_h__1_688_, lean_object* v_h__2_689_){
_start:
{
if (lean_obj_tag(v_____do__lift_687_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_691_; 
lean_dec(v_h__2_689_);
v_a_690_ = lean_ctor_get(v_____do__lift_687_, 0);
lean_inc(v_a_690_);
lean_dec_ref(v_____do__lift_687_);
v___x_691_ = lean_apply_1(v_h__1_688_, v_a_690_);
return v___x_691_;
}
else
{
lean_object* v_a_692_; lean_object* v___x_693_; 
lean_dec(v_h__1_688_);
v_a_692_ = lean_ctor_get(v_____do__lift_687_, 0);
lean_inc(v_a_692_);
lean_dec_ref(v_____do__lift_687_);
v___x_693_ = lean_apply_1(v_h__2_689_, v_a_692_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter(lean_object* v_00_u03b4_694_, lean_object* v_motive_695_, lean_object* v_____do__lift_696_, lean_object* v_h__1_697_, lean_object* v_h__2_698_){
_start:
{
if (lean_obj_tag(v_____do__lift_696_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; 
lean_dec(v_h__2_698_);
v_a_699_ = lean_ctor_get(v_____do__lift_696_, 0);
lean_inc(v_a_699_);
lean_dec_ref(v_____do__lift_696_);
v___x_700_ = lean_apply_1(v_h__1_697_, v_a_699_);
return v___x_700_;
}
else
{
lean_object* v_a_701_; lean_object* v___x_702_; 
lean_dec(v_h__1_697_);
v_a_701_ = lean_ctor_get(v_____do__lift_696_, 0);
lean_inc(v_a_701_);
lean_dec_ref(v_____do__lift_696_);
v___x_702_ = lean_apply_1(v_h__2_698_, v_a_701_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter___redArg(lean_object* v_x_703_, lean_object* v_h__1_704_, lean_object* v_h__2_705_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_707_; 
lean_dec(v_h__1_704_);
v_a_706_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_a_706_);
lean_dec_ref(v_x_703_);
v___x_707_ = lean_apply_1(v_h__2_705_, v_a_706_);
return v___x_707_;
}
else
{
lean_object* v_a_708_; lean_object* v___x_709_; 
lean_dec(v_h__2_705_);
v_a_708_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v_x_703_);
v___x_709_ = lean_apply_1(v_h__1_704_, v_a_708_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter(lean_object* v_00_u03b4_710_, lean_object* v_motive_711_, lean_object* v_x_712_, lean_object* v_h__1_713_, lean_object* v_h__2_714_){
_start:
{
if (lean_obj_tag(v_x_712_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; 
lean_dec(v_h__1_713_);
v_a_715_ = lean_ctor_get(v_x_712_, 0);
lean_inc(v_a_715_);
lean_dec_ref(v_x_712_);
v___x_716_ = lean_apply_1(v_h__2_714_, v_a_715_);
return v___x_716_;
}
else
{
lean_object* v_a_717_; lean_object* v___x_718_; 
lean_dec(v_h__2_714_);
v_a_717_ = lean_ctor_get(v_x_712_, 0);
lean_inc(v_a_717_);
lean_dec_ref(v_x_712_);
v___x_718_ = lean_apply_1(v_h__1_713_, v_a_717_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_719_, lean_object* v_h__1_720_, lean_object* v_h__2_721_){
_start:
{
if (lean_obj_tag(v_b_719_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; 
lean_dec(v_h__1_720_);
v_a_722_ = lean_ctor_get(v_b_719_, 0);
lean_inc(v_a_722_);
lean_dec_ref(v_b_719_);
v___x_723_ = lean_apply_1(v_h__2_721_, v_a_722_);
return v___x_723_;
}
else
{
lean_object* v_a_724_; lean_object* v___x_725_; 
lean_dec(v_h__2_721_);
v_a_724_ = lean_ctor_get(v_b_719_, 0);
lean_inc(v_a_724_);
lean_dec_ref(v_b_719_);
v___x_725_ = lean_apply_1(v_h__1_720_, v_a_724_);
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_726_, lean_object* v_motive_727_, lean_object* v_b_728_, lean_object* v_h__1_729_, lean_object* v_h__2_730_){
_start:
{
if (lean_obj_tag(v_b_728_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; 
lean_dec(v_h__1_729_);
v_a_731_ = lean_ctor_get(v_b_728_, 0);
lean_inc(v_a_731_);
lean_dec_ref(v_b_728_);
v___x_732_ = lean_apply_1(v_h__2_730_, v_a_731_);
return v___x_732_;
}
else
{
lean_object* v_a_733_; lean_object* v___x_734_; 
lean_dec(v_h__2_730_);
v_a_733_ = lean_ctor_get(v_b_728_, 0);
lean_inc(v_a_733_);
lean_dec_ref(v_b_728_);
v___x_734_ = lean_apply_1(v_h__1_729_, v_a_733_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_735_, lean_object* v_h__1_736_, lean_object* v_h__2_737_){
_start:
{
if (lean_obj_tag(v_x_735_) == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec(v_h__2_737_);
v___x_738_ = lean_box(0);
v___x_739_ = lean_apply_1(v_h__1_736_, v___x_738_);
return v___x_739_;
}
else
{
lean_object* v_val_740_; lean_object* v___x_741_; 
lean_dec(v_h__1_736_);
v_val_740_ = lean_ctor_get(v_x_735_, 0);
lean_inc(v_val_740_);
lean_dec_ref(v_x_735_);
v___x_741_ = lean_apply_1(v_h__2_737_, v_val_740_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b2_742_, lean_object* v_motive_743_, lean_object* v_x_744_, lean_object* v_h__1_745_, lean_object* v_h__2_746_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec(v_h__2_746_);
v___x_747_ = lean_box(0);
v___x_748_ = lean_apply_1(v_h__1_745_, v___x_747_);
return v___x_748_;
}
else
{
lean_object* v_val_749_; lean_object* v___x_750_; 
lean_dec(v_h__1_745_);
v_val_749_ = lean_ctor_get(v_x_744_, 0);
lean_inc(v_val_749_);
lean_dec_ref(v_x_744_);
v___x_750_ = lean_apply_1(v_h__2_746_, v_val_749_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter___redArg(lean_object* v_x_751_, lean_object* v_h__1_752_, lean_object* v_h__2_753_){
_start:
{
if (lean_obj_tag(v_x_751_) == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec(v_h__2_753_);
v___x_754_ = lean_box(0);
v___x_755_ = lean_apply_1(v_h__1_752_, v___x_754_);
return v___x_755_;
}
else
{
lean_object* v_val_756_; lean_object* v_fst_757_; lean_object* v_snd_758_; lean_object* v___x_759_; 
lean_dec(v_h__1_752_);
v_val_756_ = lean_ctor_get(v_x_751_, 0);
lean_inc(v_val_756_);
lean_dec_ref(v_x_751_);
v_fst_757_ = lean_ctor_get(v_val_756_, 0);
lean_inc(v_fst_757_);
v_snd_758_ = lean_ctor_get(v_val_756_, 1);
lean_inc(v_snd_758_);
lean_dec(v_val_756_);
v___x_759_ = lean_apply_2(v_h__2_753_, v_fst_757_, v_snd_758_);
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter(lean_object* v_00_u03b1_760_, lean_object* v_00_u03b2_761_, lean_object* v_motive_762_, lean_object* v_x_763_, lean_object* v_h__1_764_, lean_object* v_h__2_765_){
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
lean_object* v_val_768_; lean_object* v_fst_769_; lean_object* v_snd_770_; lean_object* v___x_771_; 
lean_dec(v_h__1_764_);
v_val_768_ = lean_ctor_get(v_x_763_, 0);
lean_inc(v_val_768_);
lean_dec_ref(v_x_763_);
v_fst_769_ = lean_ctor_get(v_val_768_, 0);
lean_inc(v_fst_769_);
v_snd_770_ = lean_ctor_get(v_val_768_, 1);
lean_inc(v_snd_770_);
lean_dec(v_val_768_);
v___x_771_ = lean_apply_2(v_h__2_765_, v_fst_769_, v_snd_770_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(lean_object* v_x_772_, lean_object* v_h__1_773_, lean_object* v_h__2_774_){
_start:
{
if (lean_obj_tag(v_x_772_) == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec(v_h__2_774_);
v___x_775_ = lean_box(0);
v___x_776_ = lean_apply_1(v_h__1_773_, v___x_775_);
return v___x_776_;
}
else
{
lean_object* v_val_777_; lean_object* v___x_778_; 
lean_dec(v_h__1_773_);
v_val_777_ = lean_ctor_get(v_x_772_, 0);
lean_inc(v_val_777_);
lean_dec_ref(v_x_772_);
v___x_778_ = lean_apply_1(v_h__2_774_, v_val_777_);
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object* v_00_u03b2_779_, lean_object* v_motive_780_, lean_object* v_x_781_, lean_object* v_h__1_782_, lean_object* v_h__2_783_){
_start:
{
if (lean_obj_tag(v_x_781_) == 0)
{
lean_object* v___x_784_; lean_object* v___x_785_; 
lean_dec(v_h__2_783_);
v___x_784_ = lean_box(0);
v___x_785_ = lean_apply_1(v_h__1_782_, v___x_784_);
return v___x_785_;
}
else
{
lean_object* v_val_786_; lean_object* v___x_787_; 
lean_dec(v_h__1_782_);
v_val_786_ = lean_ctor_get(v_x_781_, 0);
lean_inc(v_val_786_);
lean_dec_ref(v_x_781_);
v___x_787_ = lean_apply_1(v_h__2_783_, v_val_786_);
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter___redArg(lean_object* v_t_788_, lean_object* v_h__1_789_, lean_object* v_h__2_790_){
_start:
{
if (lean_obj_tag(v_t_788_) == 0)
{
lean_object* v_size_791_; lean_object* v_k_792_; lean_object* v_v_793_; lean_object* v_l_794_; lean_object* v_r_795_; lean_object* v___x_796_; 
lean_dec(v_h__1_789_);
v_size_791_ = lean_ctor_get(v_t_788_, 0);
lean_inc(v_size_791_);
v_k_792_ = lean_ctor_get(v_t_788_, 1);
lean_inc(v_k_792_);
v_v_793_ = lean_ctor_get(v_t_788_, 2);
lean_inc(v_v_793_);
v_l_794_ = lean_ctor_get(v_t_788_, 3);
lean_inc(v_l_794_);
v_r_795_ = lean_ctor_get(v_t_788_, 4);
lean_inc(v_r_795_);
lean_dec_ref(v_t_788_);
v___x_796_ = lean_apply_6(v_h__2_790_, v_size_791_, v_k_792_, v_v_793_, v_l_794_, v_r_795_, lean_box(0));
return v___x_796_;
}
else
{
lean_object* v___x_797_; 
lean_dec(v_h__2_790_);
v___x_797_ = lean_apply_1(v_h__1_789_, lean_box(0));
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter(lean_object* v_00_u03b1_798_, lean_object* v_00_u03b2_799_, lean_object* v_motive_800_, lean_object* v_t_801_, lean_object* v_hl_802_, lean_object* v_h__1_803_, lean_object* v_h__2_804_){
_start:
{
if (lean_obj_tag(v_t_801_) == 0)
{
lean_object* v_size_805_; lean_object* v_k_806_; lean_object* v_v_807_; lean_object* v_l_808_; lean_object* v_r_809_; lean_object* v___x_810_; 
lean_dec(v_h__1_803_);
v_size_805_ = lean_ctor_get(v_t_801_, 0);
lean_inc(v_size_805_);
v_k_806_ = lean_ctor_get(v_t_801_, 1);
lean_inc(v_k_806_);
v_v_807_ = lean_ctor_get(v_t_801_, 2);
lean_inc(v_v_807_);
v_l_808_ = lean_ctor_get(v_t_801_, 3);
lean_inc(v_l_808_);
v_r_809_ = lean_ctor_get(v_t_801_, 4);
lean_inc(v_r_809_);
lean_dec_ref(v_t_801_);
v___x_810_ = lean_apply_6(v_h__2_804_, v_size_805_, v_k_806_, v_v_807_, v_l_808_, v_r_809_, lean_box(0));
return v___x_810_;
}
else
{
lean_object* v___x_811_; 
lean_dec(v_h__2_804_);
v___x_811_ = lean_apply_1(v_h__1_803_, lean_box(0));
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___redArg(lean_object* v_x_812_, lean_object* v_h__1_813_, lean_object* v_h__2_814_){
_start:
{
if (lean_obj_tag(v_x_812_) == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec(v_h__2_814_);
v___x_815_ = lean_box(0);
v___x_816_ = lean_apply_1(v_h__1_813_, v___x_815_);
return v___x_816_;
}
else
{
lean_object* v_val_817_; lean_object* v___x_818_; 
lean_dec(v_h__1_813_);
v_val_817_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_val_817_);
lean_dec_ref(v_x_812_);
v___x_818_ = lean_apply_1(v_h__2_814_, v_val_817_);
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter(lean_object* v_00_u03b2_819_, lean_object* v_motive_820_, lean_object* v_x_821_, lean_object* v_h__1_822_, lean_object* v_h__2_823_){
_start:
{
if (lean_obj_tag(v_x_821_) == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec(v_h__2_823_);
v___x_824_ = lean_box(0);
v___x_825_ = lean_apply_1(v_h__1_822_, v___x_824_);
return v___x_825_;
}
else
{
lean_object* v_val_826_; lean_object* v___x_827_; 
lean_dec(v_h__1_822_);
v_val_826_ = lean_ctor_get(v_x_821_, 0);
lean_inc(v_val_826_);
lean_dec_ref(v_x_821_);
v___x_827_ = lean_apply_1(v_h__2_823_, v_val_826_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t v_x_828_, lean_object* v_h__1_829_, lean_object* v_h__2_830_, lean_object* v_h__3_831_){
_start:
{
switch(v_x_828_)
{
case 0:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec(v_h__3_831_);
lean_dec(v_h__2_830_);
v___x_832_ = lean_box(0);
v___x_833_ = lean_apply_1(v_h__1_829_, v___x_832_);
return v___x_833_;
}
case 1:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec(v_h__2_830_);
lean_dec(v_h__1_829_);
v___x_834_ = lean_box(0);
v___x_835_ = lean_apply_1(v_h__3_831_, v___x_834_);
return v___x_835_;
}
default: 
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v_h__3_831_);
lean_dec(v_h__1_829_);
v___x_836_ = lean_box(0);
v___x_837_ = lean_apply_1(v_h__2_830_, v___x_836_);
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object* v_x_838_, lean_object* v_h__1_839_, lean_object* v_h__2_840_, lean_object* v_h__3_841_){
_start:
{
uint8_t v_x_36__boxed_842_; lean_object* v_res_843_; 
v_x_36__boxed_842_ = lean_unbox(v_x_838_);
v_res_843_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_36__boxed_842_, v_h__1_839_, v_h__2_840_, v_h__3_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object* v_motive_844_, uint8_t v_x_845_, lean_object* v_h__1_846_, lean_object* v_h__2_847_, lean_object* v_h__3_848_){
_start:
{
switch(v_x_845_)
{
case 0:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec(v_h__3_848_);
lean_dec(v_h__2_847_);
v___x_849_ = lean_box(0);
v___x_850_ = lean_apply_1(v_h__1_846_, v___x_849_);
return v___x_850_;
}
case 1:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v_h__2_847_);
lean_dec(v_h__1_846_);
v___x_851_ = lean_box(0);
v___x_852_ = lean_apply_1(v_h__3_848_, v___x_851_);
return v___x_852_;
}
default: 
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec(v_h__3_848_);
lean_dec(v_h__1_846_);
v___x_853_ = lean_box(0);
v___x_854_ = lean_apply_1(v_h__2_847_, v___x_853_);
return v___x_854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object* v_motive_855_, lean_object* v_x_856_, lean_object* v_h__1_857_, lean_object* v_h__2_858_, lean_object* v_h__3_859_){
_start:
{
uint8_t v_x_51__boxed_860_; lean_object* v_res_861_; 
v_x_51__boxed_860_ = lean_unbox(v_x_856_);
v_res_861_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_855_, v_x_51__boxed_860_, v_h__1_857_, v_h__2_858_, v_h__3_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter___redArg(lean_object* v_x_862_, lean_object* v_h__1_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = lean_apply_4(v_h__1_863_, v_x_862_, lean_box(0), lean_box(0), lean_box(0));
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter(lean_object* v_00_u03b1_865_, lean_object* v_00_u03b2_866_, lean_object* v_l_x27_867_, lean_object* v_motive_868_, lean_object* v_x_869_, lean_object* v_h__1_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = lean_apply_4(v_h__1_870_, v_x_869_, lean_box(0), lean_box(0), lean_box(0));
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter___boxed(lean_object* v_00_u03b1_872_, lean_object* v_00_u03b2_873_, lean_object* v_l_x27_874_, lean_object* v_motive_875_, lean_object* v_x_876_, lean_object* v_h__1_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter(v_00_u03b1_872_, v_00_u03b2_873_, v_l_x27_874_, v_motive_875_, v_x_876_, v_h__1_877_);
lean_dec(v_l_x27_874_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___redArg(lean_object* v_t_879_, lean_object* v_h__1_880_, lean_object* v_h__2_881_){
_start:
{
if (lean_obj_tag(v_t_879_) == 0)
{
lean_object* v_size_882_; lean_object* v_k_883_; lean_object* v_v_884_; lean_object* v_l_885_; lean_object* v_r_886_; lean_object* v___x_887_; 
lean_dec(v_h__1_880_);
v_size_882_ = lean_ctor_get(v_t_879_, 0);
lean_inc(v_size_882_);
v_k_883_ = lean_ctor_get(v_t_879_, 1);
lean_inc(v_k_883_);
v_v_884_ = lean_ctor_get(v_t_879_, 2);
lean_inc(v_v_884_);
v_l_885_ = lean_ctor_get(v_t_879_, 3);
lean_inc(v_l_885_);
v_r_886_ = lean_ctor_get(v_t_879_, 4);
lean_inc(v_r_886_);
lean_dec_ref(v_t_879_);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter(lean_object* v_00_u03b1_890_, lean_object* v_00_u03b2_891_, lean_object* v_motive_892_, lean_object* v_t_893_, lean_object* v_h__1_894_, lean_object* v_h__2_895_){
_start:
{
if (lean_obj_tag(v_t_893_) == 0)
{
lean_object* v_size_896_; lean_object* v_k_897_; lean_object* v_v_898_; lean_object* v_l_899_; lean_object* v_r_900_; lean_object* v___x_901_; 
lean_dec(v_h__1_894_);
v_size_896_ = lean_ctor_get(v_t_893_, 0);
lean_inc(v_size_896_);
v_k_897_ = lean_ctor_get(v_t_893_, 1);
lean_inc(v_k_897_);
v_v_898_ = lean_ctor_get(v_t_893_, 2);
lean_inc(v_v_898_);
v_l_899_ = lean_ctor_get(v_t_893_, 3);
lean_inc(v_l_899_);
v_r_900_ = lean_ctor_get(v_t_893_, 4);
lean_inc(v_r_900_);
lean_dec_ref(v_t_893_);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter___redArg(lean_object* v_x_904_, lean_object* v_h__1_905_, lean_object* v_h__2_906_){
_start:
{
if (lean_obj_tag(v_x_904_) == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec(v_h__1_905_);
v___x_907_ = lean_box(0);
v___x_908_ = lean_apply_1(v_h__2_906_, v___x_907_);
return v___x_908_;
}
else
{
lean_object* v_val_909_; lean_object* v___x_910_; 
lean_dec(v_h__2_906_);
v_val_909_ = lean_ctor_get(v_x_904_, 0);
lean_inc(v_val_909_);
lean_dec_ref(v_x_904_);
v___x_910_ = lean_apply_1(v_h__1_905_, v_val_909_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter(lean_object* v_00_u03b1_911_, lean_object* v_00_u03b2_912_, lean_object* v_motive_913_, lean_object* v_x_914_, lean_object* v_h__1_915_, lean_object* v_h__2_916_){
_start:
{
if (lean_obj_tag(v_x_914_) == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec(v_h__1_915_);
v___x_917_ = lean_box(0);
v___x_918_ = lean_apply_1(v_h__2_916_, v___x_917_);
return v___x_918_;
}
else
{
lean_object* v_val_919_; lean_object* v___x_920_; 
lean_dec(v_h__2_916_);
v_val_919_ = lean_ctor_get(v_x_914_, 0);
lean_inc(v_val_919_);
lean_dec_ref(v_x_914_);
v___x_920_ = lean_apply_1(v_h__1_915_, v_val_919_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_921_, lean_object* v_h__1_922_, lean_object* v_h__2_923_){
_start:
{
if (lean_obj_tag(v_x_921_) == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec(v_h__1_922_);
v___x_924_ = lean_box(0);
v___x_925_ = lean_apply_1(v_h__2_923_, v___x_924_);
return v___x_925_;
}
else
{
lean_object* v_val_926_; lean_object* v___x_927_; 
lean_dec(v_h__2_923_);
v_val_926_ = lean_ctor_get(v_x_921_, 0);
lean_inc(v_val_926_);
lean_dec_ref(v_x_921_);
v___x_927_ = lean_apply_1(v_h__1_922_, v_val_926_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_928_, lean_object* v_motive_929_, lean_object* v_x_930_, lean_object* v_h__1_931_, lean_object* v_h__2_932_){
_start:
{
if (lean_obj_tag(v_x_930_) == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec(v_h__1_931_);
v___x_933_ = lean_box(0);
v___x_934_ = lean_apply_1(v_h__2_932_, v___x_933_);
return v___x_934_;
}
else
{
lean_object* v_val_935_; lean_object* v___x_936_; 
lean_dec(v_h__2_932_);
v_val_935_ = lean_ctor_get(v_x_930_, 0);
lean_inc(v_val_935_);
lean_dec_ref(v_x_930_);
v___x_936_ = lean_apply_1(v_h__1_931_, v_val_935_);
return v___x_936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_937_, lean_object* v_h__1_938_, lean_object* v_h__2_939_){
_start:
{
if (lean_obj_tag(v_x_937_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_941_; 
lean_dec(v_h__2_939_);
v_a_940_ = lean_ctor_get(v_x_937_, 0);
lean_inc(v_a_940_);
lean_dec_ref(v_x_937_);
v___x_941_ = lean_apply_1(v_h__1_938_, v_a_940_);
return v___x_941_;
}
else
{
lean_object* v_a_942_; lean_object* v___x_943_; 
lean_dec(v_h__1_938_);
v_a_942_ = lean_ctor_get(v_x_937_, 0);
lean_inc(v_a_942_);
lean_dec_ref(v_x_937_);
v___x_943_ = lean_apply_1(v_h__2_939_, v_a_942_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_944_, lean_object* v_motive_945_, lean_object* v_x_946_, lean_object* v_h__1_947_, lean_object* v_h__2_948_){
_start:
{
if (lean_obj_tag(v_x_946_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_950_; 
lean_dec(v_h__2_948_);
v_a_949_ = lean_ctor_get(v_x_946_, 0);
lean_inc(v_a_949_);
lean_dec_ref(v_x_946_);
v___x_950_ = lean_apply_1(v_h__1_947_, v_a_949_);
return v___x_950_;
}
else
{
lean_object* v_a_951_; lean_object* v___x_952_; 
lean_dec(v_h__1_947_);
v_a_951_ = lean_ctor_get(v_x_946_, 0);
lean_inc(v_a_951_);
lean_dec_ref(v_x_946_);
v___x_952_ = lean_apply_1(v_h__2_948_, v_a_951_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_953_, lean_object* v_h__1_954_, lean_object* v_h__2_955_){
_start:
{
if (lean_obj_tag(v_x_953_) == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec(v_h__1_954_);
v___x_956_ = lean_box(0);
v___x_957_ = lean_apply_1(v_h__2_955_, v___x_956_);
return v___x_957_;
}
else
{
lean_object* v_val_958_; lean_object* v___x_959_; 
lean_dec(v_h__2_955_);
v_val_958_ = lean_ctor_get(v_x_953_, 0);
lean_inc(v_val_958_);
lean_dec_ref(v_x_953_);
v___x_959_ = lean_apply_1(v_h__1_954_, v_val_958_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_960_, lean_object* v_00_u03b2_961_, lean_object* v_motive_962_, lean_object* v_x_963_, lean_object* v_h__1_964_, lean_object* v_h__2_965_){
_start:
{
if (lean_obj_tag(v_x_963_) == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; 
lean_dec(v_h__1_964_);
v___x_966_ = lean_box(0);
v___x_967_ = lean_apply_1(v_h__2_965_, v___x_966_);
return v___x_967_;
}
else
{
lean_object* v_val_968_; lean_object* v___x_969_; 
lean_dec(v_h__2_965_);
v_val_968_ = lean_ctor_get(v_x_963_, 0);
lean_inc(v_val_968_);
lean_dec_ref(v_x_963_);
v___x_969_ = lean_apply_1(v_h__1_964_, v_val_968_);
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(uint8_t v_x_970_, lean_object* v_h__1_971_, lean_object* v_h__2_972_){
_start:
{
if (v_x_970_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec(v_h__1_971_);
v___x_973_ = lean_box(0);
v___x_974_ = lean_apply_1(v_h__2_972_, v___x_973_);
return v___x_974_;
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec(v_h__2_972_);
v___x_975_ = lean_box(0);
v___x_976_ = lean_apply_1(v_h__1_971_, v___x_975_);
return v___x_976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_977_, lean_object* v_h__1_978_, lean_object* v_h__2_979_){
_start:
{
uint8_t v_x_26__boxed_980_; lean_object* v_res_981_; 
v_x_26__boxed_980_ = lean_unbox(v_x_977_);
v_res_981_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(v_x_26__boxed_980_, v_h__1_978_, v_h__2_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(lean_object* v_motive_982_, uint8_t v_x_983_, lean_object* v_h__1_984_, lean_object* v_h__2_985_){
_start:
{
if (v_x_983_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec(v_h__1_984_);
v___x_986_ = lean_box(0);
v___x_987_ = lean_apply_1(v_h__2_985_, v___x_986_);
return v___x_987_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec(v_h__2_985_);
v___x_988_ = lean_box(0);
v___x_989_ = lean_apply_1(v_h__1_984_, v___x_988_);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_990_, lean_object* v_x_991_, lean_object* v_h__1_992_, lean_object* v_h__2_993_){
_start:
{
uint8_t v_x_37__boxed_994_; lean_object* v_res_995_; 
v_x_37__boxed_994_ = lean_unbox(v_x_991_);
v_res_995_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(v_motive_990_, v_x_37__boxed_994_, v_h__1_992_, v_h__2_993_);
return v_res_995_;
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
