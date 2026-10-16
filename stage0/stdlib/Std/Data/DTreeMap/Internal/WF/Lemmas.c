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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object* v_r_199_, lean_object* v_h__1_200_, lean_object* v_h__2_201_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object* v_00_u03b1_209_, lean_object* v_00_u03b2_210_, lean_object* v_motive_211_, lean_object* v_r_212_, lean_object* v_hr_213_, lean_object* v_h__1_214_, lean_object* v_h__2_215_){
_start:
{
if (lean_obj_tag(v_r_212_) == 0)
{
lean_object* v_size_216_; lean_object* v_k_217_; lean_object* v_v_218_; lean_object* v_l_219_; lean_object* v_r_220_; lean_object* v___x_221_; 
lean_dec(v_h__1_214_);
v_size_216_ = lean_ctor_get(v_r_212_, 0);
lean_inc(v_size_216_);
v_k_217_ = lean_ctor_get(v_r_212_, 1);
lean_inc(v_k_217_);
v_v_218_ = lean_ctor_get(v_r_212_, 2);
lean_inc(v_v_218_);
v_l_219_ = lean_ctor_get(v_r_212_, 3);
lean_inc(v_l_219_);
v_r_220_ = lean_ctor_get(v_r_212_, 4);
lean_inc(v_r_220_);
lean_dec_ref_known(v_r_212_, 5);
v___x_221_ = lean_apply_7(v_h__2_215_, v_size_216_, v_k_217_, v_v_218_, v_l_219_, v_r_220_, lean_box(0), lean_box(0));
return v___x_221_;
}
else
{
lean_object* v___x_222_; 
lean_dec(v_h__2_215_);
v___x_222_ = lean_apply_2(v_h__1_214_, lean_box(0), lean_box(0));
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___redArg(lean_object* v_x_223_, lean_object* v_h__1_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lean_apply_3(v_h__1_224_, v_x_223_, lean_box(0), lean_box(0));
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(lean_object* v_00_u03b1_226_, lean_object* v_00_u03b2_227_, lean_object* v_l_228_, lean_object* v_l_x27_x27_229_, lean_object* v_motive_230_, lean_object* v_x_231_, lean_object* v_h__1_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_apply_3(v_h__1_232_, v_x_231_, lean_box(0), lean_box(0));
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___boxed(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_l_236_, lean_object* v_l_x27_x27_237_, lean_object* v_motive_238_, lean_object* v_x_239_, lean_object* v_h__1_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(v_00_u03b1_234_, v_00_u03b2_235_, v_l_236_, v_l_x27_x27_237_, v_motive_238_, v_x_239_, v_h__1_240_);
lean_dec(v_l_x27_x27_237_);
lean_dec(v_l_236_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___redArg(lean_object* v_x_242_, lean_object* v_h__1_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_apply_3(v_h__1_243_, v_x_242_, lean_box(0), lean_box(0));
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(lean_object* v_00_u03b1_245_, lean_object* v_00_u03b2_246_, lean_object* v_r_247_, lean_object* v_r_x27_248_, lean_object* v_motive_249_, lean_object* v_x_250_, lean_object* v_h__1_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_apply_3(v_h__1_251_, v_x_250_, lean_box(0), lean_box(0));
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___boxed(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_r_255_, lean_object* v_r_x27_256_, lean_object* v_motive_257_, lean_object* v_x_258_, lean_object* v_h__1_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(v_00_u03b1_253_, v_00_u03b2_254_, v_r_255_, v_r_x27_256_, v_motive_257_, v_x_258_, v_h__1_259_);
lean_dec(v_r_x27_256_);
lean_dec(v_r_255_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object* v_t_261_, lean_object* v_h__1_262_, lean_object* v_h__2_263_){
_start:
{
if (lean_obj_tag(v_t_261_) == 0)
{
lean_object* v_size_264_; lean_object* v_k_265_; lean_object* v_v_266_; lean_object* v_l_267_; lean_object* v_r_268_; lean_object* v___x_269_; 
lean_dec(v_h__1_262_);
v_size_264_ = lean_ctor_get(v_t_261_, 0);
lean_inc(v_size_264_);
v_k_265_ = lean_ctor_get(v_t_261_, 1);
lean_inc(v_k_265_);
v_v_266_ = lean_ctor_get(v_t_261_, 2);
lean_inc(v_v_266_);
v_l_267_ = lean_ctor_get(v_t_261_, 3);
lean_inc(v_l_267_);
v_r_268_ = lean_ctor_get(v_t_261_, 4);
lean_inc(v_r_268_);
lean_dec_ref_known(v_t_261_, 5);
v___x_269_ = lean_apply_6(v_h__2_263_, v_size_264_, v_k_265_, v_v_266_, v_l_267_, v_r_268_, lean_box(0));
return v___x_269_;
}
else
{
lean_object* v___x_270_; 
lean_dec(v_h__2_263_);
v___x_270_ = lean_apply_1(v_h__1_262_, lean_box(0));
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object* v_00_u03b1_271_, lean_object* v_00_u03b2_272_, lean_object* v_motive_273_, lean_object* v_t_274_, lean_object* v_hr_275_, lean_object* v_h__1_276_, lean_object* v_h__2_277_){
_start:
{
if (lean_obj_tag(v_t_274_) == 0)
{
lean_object* v_size_278_; lean_object* v_k_279_; lean_object* v_v_280_; lean_object* v_l_281_; lean_object* v_r_282_; lean_object* v___x_283_; 
lean_dec(v_h__1_276_);
v_size_278_ = lean_ctor_get(v_t_274_, 0);
lean_inc(v_size_278_);
v_k_279_ = lean_ctor_get(v_t_274_, 1);
lean_inc(v_k_279_);
v_v_280_ = lean_ctor_get(v_t_274_, 2);
lean_inc(v_v_280_);
v_l_281_ = lean_ctor_get(v_t_274_, 3);
lean_inc(v_l_281_);
v_r_282_ = lean_ctor_get(v_t_274_, 4);
lean_inc(v_r_282_);
lean_dec_ref_known(v_t_274_, 5);
v___x_283_ = lean_apply_6(v_h__2_277_, v_size_278_, v_k_279_, v_v_280_, v_l_281_, v_r_282_, lean_box(0));
return v___x_283_;
}
else
{
lean_object* v___x_284_; 
lean_dec(v_h__2_277_);
v___x_284_ = lean_apply_1(v_h__1_276_, lean_box(0));
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___redArg(lean_object* v_x_285_, lean_object* v_h__1_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_apply_3(v_h__1_286_, v_x_285_, lean_box(0), lean_box(0));
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(lean_object* v_00_u03b1_288_, lean_object* v_00_u03b2_289_, lean_object* v_szl_290_, lean_object* v_k_x27_291_, lean_object* v_v_x27_292_, lean_object* v_l_x27_293_, lean_object* v_r_x27_294_, lean_object* v_l_x27_x27_295_, lean_object* v_motive_296_, lean_object* v_x_297_, lean_object* v_h__1_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = lean_apply_3(v_h__1_298_, v_x_297_, lean_box(0), lean_box(0));
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___boxed(lean_object* v_00_u03b1_300_, lean_object* v_00_u03b2_301_, lean_object* v_szl_302_, lean_object* v_k_x27_303_, lean_object* v_v_x27_304_, lean_object* v_l_x27_305_, lean_object* v_r_x27_306_, lean_object* v_l_x27_x27_307_, lean_object* v_motive_308_, lean_object* v_x_309_, lean_object* v_h__1_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(v_00_u03b1_300_, v_00_u03b2_301_, v_szl_302_, v_k_x27_303_, v_v_x27_304_, v_l_x27_305_, v_r_x27_306_, v_l_x27_x27_307_, v_motive_308_, v_x_309_, v_h__1_310_);
lean_dec(v_l_x27_x27_307_);
lean_dec(v_r_x27_306_);
lean_dec(v_l_x27_305_);
lean_dec(v_v_x27_304_);
lean_dec(v_k_x27_303_);
lean_dec(v_szl_302_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___redArg(lean_object* v_x_312_, lean_object* v_h__1_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = lean_apply_3(v_h__1_313_, v_x_312_, lean_box(0), lean_box(0));
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(lean_object* v_00_u03b1_315_, lean_object* v_00_u03b2_316_, lean_object* v_r_x27_317_, lean_object* v_szr_318_, lean_object* v_k_x27_x27_319_, lean_object* v_v_x27_x27_320_, lean_object* v_l_x27_x27_321_, lean_object* v_r_x27_x27_322_, lean_object* v_motive_323_, lean_object* v_x_324_, lean_object* v_h__1_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = lean_apply_3(v_h__1_325_, v_x_324_, lean_box(0), lean_box(0));
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___boxed(lean_object* v_00_u03b1_327_, lean_object* v_00_u03b2_328_, lean_object* v_r_x27_329_, lean_object* v_szr_330_, lean_object* v_k_x27_x27_331_, lean_object* v_v_x27_x27_332_, lean_object* v_l_x27_x27_333_, lean_object* v_r_x27_x27_334_, lean_object* v_motive_335_, lean_object* v_x_336_, lean_object* v_h__1_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(v_00_u03b1_327_, v_00_u03b2_328_, v_r_x27_329_, v_szr_330_, v_k_x27_x27_331_, v_v_x27_x27_332_, v_l_x27_x27_333_, v_r_x27_x27_334_, v_motive_335_, v_x_336_, v_h__1_337_);
lean_dec(v_r_x27_x27_334_);
lean_dec(v_l_x27_x27_333_);
lean_dec(v_v_x27_x27_332_);
lean_dec(v_k_x27_x27_331_);
lean_dec(v_szr_330_);
lean_dec(v_r_x27_329_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(lean_object* v_l_339_, lean_object* v_h__1_340_, lean_object* v_h__2_341_){
_start:
{
if (lean_obj_tag(v_l_339_) == 0)
{
lean_object* v_size_342_; lean_object* v_k_343_; lean_object* v_v_344_; lean_object* v_l_345_; lean_object* v_r_346_; lean_object* v___x_347_; 
lean_dec(v_h__1_340_);
v_size_342_ = lean_ctor_get(v_l_339_, 0);
lean_inc(v_size_342_);
v_k_343_ = lean_ctor_get(v_l_339_, 1);
lean_inc(v_k_343_);
v_v_344_ = lean_ctor_get(v_l_339_, 2);
lean_inc(v_v_344_);
v_l_345_ = lean_ctor_get(v_l_339_, 3);
lean_inc(v_l_345_);
v_r_346_ = lean_ctor_get(v_l_339_, 4);
lean_inc(v_r_346_);
lean_dec_ref_known(v_l_339_, 5);
v___x_347_ = lean_apply_6(v_h__2_341_, v_size_342_, v_k_343_, v_v_344_, v_l_345_, v_r_346_, lean_box(0));
return v___x_347_;
}
else
{
lean_object* v___x_348_; 
lean_dec(v_h__2_341_);
v___x_348_ = lean_apply_1(v_h__1_340_, lean_box(0));
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(lean_object* v_00_u03b1_349_, lean_object* v_00_u03b2_350_, lean_object* v_motive_351_, lean_object* v_l_352_, lean_object* v_hl_353_, lean_object* v_h__1_354_, lean_object* v_h__2_355_){
_start:
{
if (lean_obj_tag(v_l_352_) == 0)
{
lean_object* v_size_356_; lean_object* v_k_357_; lean_object* v_v_358_; lean_object* v_l_359_; lean_object* v_r_360_; lean_object* v___x_361_; 
lean_dec(v_h__1_354_);
v_size_356_ = lean_ctor_get(v_l_352_, 0);
lean_inc(v_size_356_);
v_k_357_ = lean_ctor_get(v_l_352_, 1);
lean_inc(v_k_357_);
v_v_358_ = lean_ctor_get(v_l_352_, 2);
lean_inc(v_v_358_);
v_l_359_ = lean_ctor_get(v_l_352_, 3);
lean_inc(v_l_359_);
v_r_360_ = lean_ctor_get(v_l_352_, 4);
lean_inc(v_r_360_);
lean_dec_ref_known(v_l_352_, 5);
v___x_361_ = lean_apply_6(v_h__2_355_, v_size_356_, v_k_357_, v_v_358_, v_l_359_, v_r_360_, lean_box(0));
return v___x_361_;
}
else
{
lean_object* v___x_362_; 
lean_dec(v_h__2_355_);
v___x_362_ = lean_apply_1(v_h__1_354_, lean_box(0));
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object* v_x_363_, lean_object* v_h__1_364_, lean_object* v_h__2_365_){
_start:
{
if (lean_obj_tag(v_x_363_) == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec(v_h__2_365_);
v___x_366_ = lean_box(0);
v___x_367_ = lean_apply_1(v_h__1_364_, v___x_366_);
return v___x_367_;
}
else
{
lean_object* v_val_368_; lean_object* v_fst_369_; lean_object* v_snd_370_; lean_object* v___x_371_; 
lean_dec(v_h__1_364_);
v_val_368_ = lean_ctor_get(v_x_363_, 0);
lean_inc(v_val_368_);
lean_dec_ref_known(v_x_363_, 1);
v_fst_369_ = lean_ctor_get(v_val_368_, 0);
lean_inc(v_fst_369_);
v_snd_370_ = lean_ctor_get(v_val_368_, 1);
lean_inc(v_snd_370_);
lean_dec(v_val_368_);
v___x_371_ = lean_apply_2(v_h__2_365_, v_fst_369_, v_snd_370_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* v_00_u03b1_372_, lean_object* v_00_u03b2_373_, lean_object* v_motive_374_, lean_object* v_x_375_, lean_object* v_h__1_376_, lean_object* v_h__2_377_){
_start:
{
if (lean_obj_tag(v_x_375_) == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v_h__2_377_);
v___x_378_ = lean_box(0);
v___x_379_ = lean_apply_1(v_h__1_376_, v___x_378_);
return v___x_379_;
}
else
{
lean_object* v_val_380_; lean_object* v_fst_381_; lean_object* v_snd_382_; lean_object* v___x_383_; 
lean_dec(v_h__1_376_);
v_val_380_ = lean_ctor_get(v_x_375_, 0);
lean_inc(v_val_380_);
lean_dec_ref_known(v_x_375_, 1);
v_fst_381_ = lean_ctor_get(v_val_380_, 0);
lean_inc(v_fst_381_);
v_snd_382_ = lean_ctor_get(v_val_380_, 1);
lean_inc(v_snd_382_);
lean_dec(v_val_380_);
v___x_383_ = lean_apply_2(v_h__2_377_, v_fst_381_, v_snd_382_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(uint8_t v_x_384_, lean_object* v_h__1_385_, lean_object* v_h__2_386_, lean_object* v_h__3_387_){
_start:
{
switch(v_x_384_)
{
case 0:
{
lean_object* v___x_388_; 
lean_dec(v_h__3_387_);
lean_dec(v_h__2_386_);
v___x_388_ = lean_apply_1(v_h__1_385_, lean_box(0));
return v___x_388_;
}
case 1:
{
lean_object* v___x_389_; 
lean_dec(v_h__3_387_);
lean_dec(v_h__1_385_);
v___x_389_ = lean_apply_1(v_h__2_386_, lean_box(0));
return v___x_389_;
}
default: 
{
lean_object* v___x_390_; 
lean_dec(v_h__2_386_);
lean_dec(v_h__1_385_);
v___x_390_ = lean_apply_1(v_h__3_387_, lean_box(0));
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(lean_object* v_x_391_, lean_object* v_h__1_392_, lean_object* v_h__2_393_, lean_object* v_h__3_394_){
_start:
{
uint8_t v_x_33__boxed_395_; lean_object* v_res_396_; 
v_x_33__boxed_395_ = lean_unbox(v_x_391_);
v_res_396_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_33__boxed_395_, v_h__1_392_, v_h__2_393_, v_h__3_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object* v_motive_397_, uint8_t v_x_398_, lean_object* v_h__1_399_, lean_object* v_h__2_400_, lean_object* v_h__3_401_){
_start:
{
switch(v_x_398_)
{
case 0:
{
lean_object* v___x_402_; 
lean_dec(v_h__3_401_);
lean_dec(v_h__2_400_);
v___x_402_ = lean_apply_1(v_h__1_399_, lean_box(0));
return v___x_402_;
}
case 1:
{
lean_object* v___x_403_; 
lean_dec(v_h__3_401_);
lean_dec(v_h__1_399_);
v___x_403_ = lean_apply_1(v_h__2_400_, lean_box(0));
return v___x_403_;
}
default: 
{
lean_object* v___x_404_; 
lean_dec(v_h__2_400_);
lean_dec(v_h__1_399_);
v___x_404_ = lean_apply_1(v_h__3_401_, lean_box(0));
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(lean_object* v_motive_405_, lean_object* v_x_406_, lean_object* v_h__1_407_, lean_object* v_h__2_408_, lean_object* v_h__3_409_){
_start:
{
uint8_t v_x_42__boxed_410_; lean_object* v_res_411_; 
v_x_42__boxed_410_ = lean_unbox(v_x_406_);
v_res_411_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(v_motive_405_, v_x_42__boxed_410_, v_h__1_407_, v_h__2_408_, v_h__3_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(lean_object* v_x_412_, lean_object* v_h__1_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_apply_4(v_h__1_413_, v_x_412_, lean_box(0), lean_box(0), lean_box(0));
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object* v_00_u03b1_415_, lean_object* v_00_u03b2_416_, lean_object* v_l_417_, lean_object* v_motive_418_, lean_object* v_x_419_, lean_object* v_h__1_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = lean_apply_4(v_h__1_420_, v_x_419_, lean_box(0), lean_box(0), lean_box(0));
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(lean_object* v_00_u03b1_422_, lean_object* v_00_u03b2_423_, lean_object* v_l_424_, lean_object* v_motive_425_, lean_object* v_x_426_, lean_object* v_h__1_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_422_, v_00_u03b2_423_, v_l_424_, v_motive_425_, v_x_426_, v_h__1_427_);
lean_dec(v_l_424_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(uint8_t v_x_429_, lean_object* v_h__1_430_, lean_object* v_h__2_431_, lean_object* v_h__3_432_){
_start:
{
switch(v_x_429_)
{
case 0:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec(v_h__3_432_);
lean_dec(v_h__2_431_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_apply_1(v_h__1_430_, v___x_433_);
return v___x_434_;
}
case 1:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v_h__2_431_);
lean_dec(v_h__1_430_);
v___x_435_ = lean_box(0);
v___x_436_ = lean_apply_1(v_h__3_432_, v___x_435_);
return v___x_436_;
}
default: 
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec(v_h__3_432_);
lean_dec(v_h__1_430_);
v___x_437_ = lean_box(0);
v___x_438_ = lean_apply_1(v_h__2_431_, v___x_437_);
return v___x_438_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(lean_object* v_x_439_, lean_object* v_h__1_440_, lean_object* v_h__2_441_, lean_object* v_h__3_442_){
_start:
{
uint8_t v_x_33__boxed_443_; lean_object* v_res_444_; 
v_x_33__boxed_443_ = lean_unbox(v_x_439_);
v_res_444_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_33__boxed_443_, v_h__1_440_, v_h__2_441_, v_h__3_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object* v_motive_445_, uint8_t v_x_446_, lean_object* v_h__1_447_, lean_object* v_h__2_448_, lean_object* v_h__3_449_){
_start:
{
switch(v_x_446_)
{
case 0:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec(v_h__3_449_);
lean_dec(v_h__2_448_);
v___x_450_ = lean_box(0);
v___x_451_ = lean_apply_1(v_h__1_447_, v___x_450_);
return v___x_451_;
}
case 1:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec(v_h__2_448_);
lean_dec(v_h__1_447_);
v___x_452_ = lean_box(0);
v___x_453_ = lean_apply_1(v_h__3_449_, v___x_452_);
return v___x_453_;
}
default: 
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v_h__3_449_);
lean_dec(v_h__1_447_);
v___x_454_ = lean_box(0);
v___x_455_ = lean_apply_1(v_h__2_448_, v___x_454_);
return v___x_455_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(lean_object* v_motive_456_, lean_object* v_x_457_, lean_object* v_h__1_458_, lean_object* v_h__2_459_, lean_object* v_h__3_460_){
_start:
{
uint8_t v_x_48__boxed_461_; lean_object* v_res_462_; 
v_x_48__boxed_461_ = lean_unbox(v_x_457_);
v_res_462_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_456_, v_x_48__boxed_461_, v_h__1_458_, v_h__2_459_, v_h__3_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object* v_x_463_, lean_object* v_h__1_464_, lean_object* v_h__2_465_){
_start:
{
if (lean_obj_tag(v_x_463_) == 0)
{
lean_object* v___x_466_; 
lean_dec(v_h__2_465_);
v___x_466_ = lean_apply_1(v_h__1_464_, lean_box(0));
return v___x_466_;
}
else
{
lean_object* v_val_467_; lean_object* v___x_468_; 
lean_dec(v_h__1_464_);
v_val_467_ = lean_ctor_get(v_x_463_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v_x_463_, 1);
v___x_468_ = lean_apply_2(v_h__2_465_, v_val_467_, lean_box(0));
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v_motive_471_, lean_object* v_x_472_, lean_object* v_h__1_473_, lean_object* v_h__2_474_){
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
lean_object* v_val_476_; lean_object* v___x_477_; 
lean_dec(v_h__1_473_);
v_val_476_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_val_476_);
lean_dec_ref_known(v_x_472_, 1);
v___x_477_ = lean_apply_2(v_h__2_474_, v_val_476_, lean_box(0));
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_478_, lean_object* v_h__1_479_, lean_object* v_h__2_480_){
_start:
{
if (lean_obj_tag(v_x_478_) == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v_h__2_480_);
v___x_481_ = lean_box(0);
v___x_482_ = lean_apply_1(v_h__1_479_, v___x_481_);
return v___x_482_;
}
else
{
lean_object* v_val_483_; lean_object* v___x_484_; 
lean_dec(v_h__1_479_);
v_val_483_ = lean_ctor_get(v_x_478_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v_x_478_, 1);
v___x_484_ = lean_apply_1(v_h__2_480_, v_val_483_);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_485_, lean_object* v_00_u03b2_486_, lean_object* v_motive_487_, lean_object* v_x_488_, lean_object* v_h__1_489_, lean_object* v_h__2_490_){
_start:
{
if (lean_obj_tag(v_x_488_) == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v_h__2_490_);
v___x_491_ = lean_box(0);
v___x_492_ = lean_apply_1(v_h__1_489_, v___x_491_);
return v___x_492_;
}
else
{
lean_object* v_val_493_; lean_object* v___x_494_; 
lean_dec(v_h__1_489_);
v_val_493_ = lean_ctor_get(v_x_488_, 0);
lean_inc(v_val_493_);
lean_dec_ref_known(v_x_488_, 1);
v___x_494_ = lean_apply_1(v_h__2_490_, v_val_493_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object* v_x_495_, lean_object* v_h__1_496_, lean_object* v_h__2_497_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
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
v_val_500_ = lean_ctor_get(v_x_495_, 0);
lean_inc(v_val_500_);
lean_dec_ref_known(v_x_495_, 1);
v___x_501_ = lean_apply_1(v_h__2_497_, v_val_500_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_502_, lean_object* v_00_u03b2_503_, lean_object* v_motive_504_, lean_object* v_x_505_, lean_object* v_h__1_506_, lean_object* v_h__2_507_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v_h__2_507_);
v___x_508_ = lean_box(0);
v___x_509_ = lean_apply_1(v_h__1_506_, v___x_508_);
return v___x_509_;
}
else
{
lean_object* v_val_510_; lean_object* v___x_511_; 
lean_dec(v_h__1_506_);
v_val_510_ = lean_ctor_get(v_x_505_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v_x_505_, 1);
v___x_511_ = lean_apply_1(v_h__2_507_, v_val_510_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___redArg(lean_object* v_x_512_, lean_object* v_h__1_513_, lean_object* v_h__2_514_){
_start:
{
if (lean_obj_tag(v_x_512_) == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v_h__2_514_);
v___x_515_ = lean_box(0);
v___x_516_ = lean_apply_1(v_h__1_513_, v___x_515_);
return v___x_516_;
}
else
{
lean_object* v_val_517_; lean_object* v___x_518_; 
lean_dec(v_h__1_513_);
v_val_517_ = lean_ctor_get(v_x_512_, 0);
lean_inc(v_val_517_);
lean_dec_ref_known(v_x_512_, 1);
v___x_518_ = lean_apply_1(v_h__2_514_, v_val_517_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(lean_object* v_00_u03b1_519_, lean_object* v_00_u03b2_520_, lean_object* v_k_521_, lean_object* v_motive_522_, lean_object* v_x_523_, lean_object* v_h__1_524_, lean_object* v_h__2_525_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v_h__2_525_);
v___x_526_ = lean_box(0);
v___x_527_ = lean_apply_1(v_h__1_524_, v___x_526_);
return v___x_527_;
}
else
{
lean_object* v_val_528_; lean_object* v___x_529_; 
lean_dec(v_h__1_524_);
v_val_528_ = lean_ctor_get(v_x_523_, 0);
lean_inc(v_val_528_);
lean_dec_ref_known(v_x_523_, 1);
v___x_529_ = lean_apply_1(v_h__2_525_, v_val_528_);
return v___x_529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___boxed(lean_object* v_00_u03b1_530_, lean_object* v_00_u03b2_531_, lean_object* v_k_532_, lean_object* v_motive_533_, lean_object* v_x_534_, lean_object* v_h__1_535_, lean_object* v_h__2_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(v_00_u03b1_530_, v_00_u03b2_531_, v_k_532_, v_motive_533_, v_x_534_, v_h__1_535_, v_h__2_536_);
lean_dec(v_k_532_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(uint8_t v_x_538_, lean_object* v_h__1_539_, lean_object* v_h__2_540_){
_start:
{
if (v_x_538_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec(v_h__2_540_);
v___x_541_ = lean_box(0);
v___x_542_ = lean_apply_1(v_h__1_539_, v___x_541_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec(v_h__1_539_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_apply_1(v_h__2_540_, v___x_543_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg___boxed(lean_object* v_x_545_, lean_object* v_h__1_546_, lean_object* v_h__2_547_){
_start:
{
uint8_t v_x_24__boxed_548_; lean_object* v_res_549_; 
v_x_24__boxed_548_ = lean_unbox(v_x_545_);
v_res_549_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(v_x_24__boxed_548_, v_h__1_546_, v_h__2_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(lean_object* v_motive_550_, uint8_t v_x_551_, lean_object* v_h__1_552_, lean_object* v_h__2_553_){
_start:
{
if (v_x_551_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec(v_h__2_553_);
v___x_554_ = lean_box(0);
v___x_555_ = lean_apply_1(v_h__1_552_, v___x_554_);
return v___x_555_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec(v_h__1_552_);
v___x_556_ = lean_box(0);
v___x_557_ = lean_apply_1(v_h__2_553_, v___x_556_);
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___boxed(lean_object* v_motive_558_, lean_object* v_x_559_, lean_object* v_h__1_560_, lean_object* v_h__2_561_){
_start:
{
uint8_t v_x_35__boxed_562_; lean_object* v_res_563_; 
v_x_35__boxed_562_ = lean_unbox(v_x_559_);
v_res_563_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(v_motive_558_, v_x_35__boxed_562_, v_h__1_560_, v_h__2_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___redArg(lean_object* v_v_x3f_564_, lean_object* v_h__1_565_, lean_object* v_h__2_566_){
_start:
{
if (lean_obj_tag(v_v_x3f_564_) == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v_h__2_566_);
v___x_567_ = lean_box(0);
v___x_568_ = lean_apply_1(v_h__1_565_, v___x_567_);
return v___x_568_;
}
else
{
lean_object* v_val_569_; lean_object* v___x_570_; 
lean_dec(v_h__1_565_);
v_val_569_ = lean_ctor_get(v_v_x3f_564_, 0);
lean_inc(v_val_569_);
lean_dec_ref_known(v_v_x3f_564_, 1);
v___x_570_ = lean_apply_1(v_h__2_566_, v_val_569_);
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, lean_object* v_k_573_, lean_object* v_motive_574_, lean_object* v_v_x3f_575_, lean_object* v_h__1_576_, lean_object* v_h__2_577_){
_start:
{
if (lean_obj_tag(v_v_x3f_575_) == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_h__2_577_);
v___x_578_ = lean_box(0);
v___x_579_ = lean_apply_1(v_h__1_576_, v___x_578_);
return v___x_579_;
}
else
{
lean_object* v_val_580_; lean_object* v___x_581_; 
lean_dec(v_h__1_576_);
v_val_580_ = lean_ctor_get(v_v_x3f_575_, 0);
lean_inc(v_val_580_);
lean_dec_ref_known(v_v_x3f_575_, 1);
v___x_581_ = lean_apply_1(v_h__2_577_, v_val_580_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___boxed(lean_object* v_00_u03b1_582_, lean_object* v_00_u03b2_583_, lean_object* v_k_584_, lean_object* v_motive_585_, lean_object* v_v_x3f_586_, lean_object* v_h__1_587_, lean_object* v_h__2_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(v_00_u03b1_582_, v_00_u03b2_583_, v_k_584_, v_motive_585_, v_v_x3f_586_, v_h__1_587_, v_h__2_588_);
lean_dec(v_k_584_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_590_, lean_object* v_h__1_591_, lean_object* v_h__2_592_){
_start:
{
if (lean_obj_tag(v_x_590_) == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v_h__2_592_);
v___x_593_ = lean_box(0);
v___x_594_ = lean_apply_1(v_h__1_591_, v___x_593_);
return v___x_594_;
}
else
{
lean_object* v_val_595_; lean_object* v___x_596_; 
lean_dec(v_h__1_591_);
v_val_595_ = lean_ctor_get(v_x_590_, 0);
lean_inc(v_val_595_);
lean_dec_ref_known(v_x_590_, 1);
v___x_596_ = lean_apply_1(v_h__2_592_, v_val_595_);
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b1_597_, lean_object* v_00_u03b2_598_, lean_object* v_k_599_, lean_object* v_motive_600_, lean_object* v_x_601_, lean_object* v_h__1_602_, lean_object* v_h__2_603_){
_start:
{
if (lean_obj_tag(v_x_601_) == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec(v_h__2_603_);
v___x_604_ = lean_box(0);
v___x_605_ = lean_apply_1(v_h__1_602_, v___x_604_);
return v___x_605_;
}
else
{
lean_object* v_val_606_; lean_object* v___x_607_; 
lean_dec(v_h__1_602_);
v_val_606_ = lean_ctor_get(v_x_601_, 0);
lean_inc(v_val_606_);
lean_dec_ref_known(v_x_601_, 1);
v___x_607_ = lean_apply_1(v_h__2_603_, v_val_606_);
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b2_609_, lean_object* v_k_610_, lean_object* v_motive_611_, lean_object* v_x_612_, lean_object* v_h__1_613_, lean_object* v_h__2_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_608_, v_00_u03b2_609_, v_k_610_, v_motive_611_, v_x_612_, v_h__1_613_, v_h__2_614_);
lean_dec(v_k_610_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter___redArg(lean_object* v_x_616_, lean_object* v_h__1_617_, lean_object* v_h__2_618_){
_start:
{
if (lean_obj_tag(v_x_616_) == 0)
{
lean_object* v___x_619_; 
lean_dec(v_h__2_618_);
v___x_619_ = lean_apply_1(v_h__1_617_, lean_box(0));
return v___x_619_;
}
else
{
lean_object* v_val_620_; lean_object* v_fst_621_; lean_object* v_snd_622_; lean_object* v___x_623_; 
lean_dec(v_h__1_617_);
v_val_620_ = lean_ctor_get(v_x_616_, 0);
lean_inc(v_val_620_);
lean_dec_ref_known(v_x_616_, 1);
v_fst_621_ = lean_ctor_get(v_val_620_, 0);
lean_inc(v_fst_621_);
v_snd_622_ = lean_ctor_get(v_val_620_, 1);
lean_inc(v_snd_622_);
lean_dec(v_val_620_);
v___x_623_ = lean_apply_3(v_h__2_618_, v_fst_621_, v_snd_622_, lean_box(0));
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter(lean_object* v_00_u03b1_624_, lean_object* v_00_u03b2_625_, lean_object* v_motive_626_, lean_object* v_x_627_, lean_object* v_h__1_628_, lean_object* v_h__2_629_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
lean_object* v___x_630_; 
lean_dec(v_h__2_629_);
v___x_630_ = lean_apply_1(v_h__1_628_, lean_box(0));
return v___x_630_;
}
else
{
lean_object* v_val_631_; lean_object* v_fst_632_; lean_object* v_snd_633_; lean_object* v___x_634_; 
lean_dec(v_h__1_628_);
v_val_631_ = lean_ctor_get(v_x_627_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v_x_627_, 1);
v_fst_632_ = lean_ctor_get(v_val_631_, 0);
lean_inc(v_fst_632_);
v_snd_633_ = lean_ctor_get(v_val_631_, 1);
lean_inc(v_snd_633_);
lean_dec(v_val_631_);
v___x_634_ = lean_apply_3(v_h__2_629_, v_fst_632_, v_snd_633_, lean_box(0));
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___redArg(lean_object* v_x_635_, lean_object* v_h__1_636_, lean_object* v_h__2_637_){
_start:
{
if (lean_obj_tag(v_x_635_) == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v_h__2_637_);
v___x_638_ = lean_box(0);
v___x_639_ = lean_apply_1(v_h__1_636_, v___x_638_);
return v___x_639_;
}
else
{
lean_object* v_val_640_; lean_object* v___x_641_; 
lean_dec(v_h__1_636_);
v_val_640_ = lean_ctor_get(v_x_635_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v_x_635_, 1);
v___x_641_ = lean_apply_1(v_h__2_637_, v_val_640_);
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_k_644_, lean_object* v_motive_645_, lean_object* v_x_646_, lean_object* v_h__1_647_, lean_object* v_h__2_648_){
_start:
{
if (lean_obj_tag(v_x_646_) == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec(v_h__2_648_);
v___x_649_ = lean_box(0);
v___x_650_ = lean_apply_1(v_h__1_647_, v___x_649_);
return v___x_650_;
}
else
{
lean_object* v_val_651_; lean_object* v___x_652_; 
lean_dec(v_h__1_647_);
v_val_651_ = lean_ctor_get(v_x_646_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v_x_646_, 1);
v___x_652_ = lean_apply_1(v_h__2_648_, v_val_651_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object* v_00_u03b1_653_, lean_object* v_00_u03b2_654_, lean_object* v_k_655_, lean_object* v_motive_656_, lean_object* v_x_657_, lean_object* v_h__1_658_, lean_object* v_h__2_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_653_, v_00_u03b2_654_, v_k_655_, v_motive_656_, v_x_657_, v_h__1_658_, v_h__2_659_);
lean_dec(v_k_655_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(uint8_t v_x_661_, lean_object* v_h__1_662_, lean_object* v_h__2_663_, lean_object* v_h__3_664_){
_start:
{
switch(v_x_661_)
{
case 0:
{
lean_object* v___x_665_; 
lean_dec(v_h__3_664_);
lean_dec(v_h__2_663_);
v___x_665_ = lean_apply_1(v_h__1_662_, lean_box(0));
return v___x_665_;
}
case 1:
{
lean_object* v___x_666_; 
lean_dec(v_h__2_663_);
lean_dec(v_h__1_662_);
v___x_666_ = lean_apply_1(v_h__3_664_, lean_box(0));
return v___x_666_;
}
default: 
{
lean_object* v___x_667_; 
lean_dec(v_h__3_664_);
lean_dec(v_h__1_662_);
v___x_667_ = lean_apply_1(v_h__2_663_, lean_box(0));
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg___boxed(lean_object* v_x_668_, lean_object* v_h__1_669_, lean_object* v_h__2_670_, lean_object* v_h__3_671_){
_start:
{
uint8_t v_x_33__boxed_672_; lean_object* v_res_673_; 
v_x_33__boxed_672_ = lean_unbox(v_x_668_);
v_res_673_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(v_x_33__boxed_672_, v_h__1_669_, v_h__2_670_, v_h__3_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(lean_object* v_motive_674_, uint8_t v_x_675_, lean_object* v_h__1_676_, lean_object* v_h__2_677_, lean_object* v_h__3_678_){
_start:
{
switch(v_x_675_)
{
case 0:
{
lean_object* v___x_679_; 
lean_dec(v_h__3_678_);
lean_dec(v_h__2_677_);
v___x_679_ = lean_apply_1(v_h__1_676_, lean_box(0));
return v___x_679_;
}
case 1:
{
lean_object* v___x_680_; 
lean_dec(v_h__2_677_);
lean_dec(v_h__1_676_);
v___x_680_ = lean_apply_1(v_h__3_678_, lean_box(0));
return v___x_680_;
}
default: 
{
lean_object* v___x_681_; 
lean_dec(v_h__3_678_);
lean_dec(v_h__1_676_);
v___x_681_ = lean_apply_1(v_h__2_677_, lean_box(0));
return v___x_681_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___boxed(lean_object* v_motive_682_, lean_object* v_x_683_, lean_object* v_h__1_684_, lean_object* v_h__2_685_, lean_object* v_h__3_686_){
_start:
{
uint8_t v_x_42__boxed_687_; lean_object* v_res_688_; 
v_x_42__boxed_687_ = lean_unbox(v_x_683_);
v_res_688_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(v_motive_682_, v_x_42__boxed_687_, v_h__1_684_, v_h__2_685_, v_h__3_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter___redArg(lean_object* v_____do__lift_689_, lean_object* v_h__1_690_, lean_object* v_h__2_691_){
_start:
{
if (lean_obj_tag(v_____do__lift_689_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_693_; 
lean_dec(v_h__2_691_);
v_a_692_ = lean_ctor_get(v_____do__lift_689_, 0);
lean_inc(v_a_692_);
lean_dec_ref_known(v_____do__lift_689_, 1);
v___x_693_ = lean_apply_1(v_h__1_690_, v_a_692_);
return v___x_693_;
}
else
{
lean_object* v_a_694_; lean_object* v___x_695_; 
lean_dec(v_h__1_690_);
v_a_694_ = lean_ctor_get(v_____do__lift_689_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v_____do__lift_689_, 1);
v___x_695_ = lean_apply_1(v_h__2_691_, v_a_694_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter(lean_object* v_00_u03b4_696_, lean_object* v_motive_697_, lean_object* v_____do__lift_698_, lean_object* v_h__1_699_, lean_object* v_h__2_700_){
_start:
{
if (lean_obj_tag(v_____do__lift_698_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; 
lean_dec(v_h__2_700_);
v_a_701_ = lean_ctor_get(v_____do__lift_698_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v_____do__lift_698_, 1);
v___x_702_ = lean_apply_1(v_h__1_699_, v_a_701_);
return v___x_702_;
}
else
{
lean_object* v_a_703_; lean_object* v___x_704_; 
lean_dec(v_h__1_699_);
v_a_703_ = lean_ctor_get(v_____do__lift_698_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v_____do__lift_698_, 1);
v___x_704_ = lean_apply_1(v_h__2_700_, v_a_703_);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter___redArg(lean_object* v_x_705_, lean_object* v_h__1_706_, lean_object* v_h__2_707_){
_start:
{
if (lean_obj_tag(v_x_705_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; 
lean_dec(v_h__1_706_);
v_a_708_ = lean_ctor_get(v_x_705_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v_x_705_, 1);
v___x_709_ = lean_apply_1(v_h__2_707_, v_a_708_);
return v___x_709_;
}
else
{
lean_object* v_a_710_; lean_object* v___x_711_; 
lean_dec(v_h__2_707_);
v_a_710_ = lean_ctor_get(v_x_705_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v_x_705_, 1);
v___x_711_ = lean_apply_1(v_h__1_706_, v_a_710_);
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter(lean_object* v_00_u03b4_712_, lean_object* v_motive_713_, lean_object* v_x_714_, lean_object* v_h__1_715_, lean_object* v_h__2_716_){
_start:
{
if (lean_obj_tag(v_x_714_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_718_; 
lean_dec(v_h__1_715_);
v_a_717_ = lean_ctor_get(v_x_714_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v_x_714_, 1);
v___x_718_ = lean_apply_1(v_h__2_716_, v_a_717_);
return v___x_718_;
}
else
{
lean_object* v_a_719_; lean_object* v___x_720_; 
lean_dec(v_h__2_716_);
v_a_719_ = lean_ctor_get(v_x_714_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v_x_714_, 1);
v___x_720_ = lean_apply_1(v_h__1_715_, v_a_719_);
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_721_, lean_object* v_h__1_722_, lean_object* v_h__2_723_){
_start:
{
if (lean_obj_tag(v_b_721_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
lean_dec(v_h__1_722_);
v_a_724_ = lean_ctor_get(v_b_721_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v_b_721_, 1);
v___x_725_ = lean_apply_1(v_h__2_723_, v_a_724_);
return v___x_725_;
}
else
{
lean_object* v_a_726_; lean_object* v___x_727_; 
lean_dec(v_h__2_723_);
v_a_726_ = lean_ctor_get(v_b_721_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v_b_721_, 1);
v___x_727_ = lean_apply_1(v_h__1_722_, v_a_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_728_, lean_object* v_motive_729_, lean_object* v_b_730_, lean_object* v_h__1_731_, lean_object* v_h__2_732_){
_start:
{
if (lean_obj_tag(v_b_730_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; 
lean_dec(v_h__1_731_);
v_a_733_ = lean_ctor_get(v_b_730_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v_b_730_, 1);
v___x_734_ = lean_apply_1(v_h__2_732_, v_a_733_);
return v___x_734_;
}
else
{
lean_object* v_a_735_; lean_object* v___x_736_; 
lean_dec(v_h__2_732_);
v_a_735_ = lean_ctor_get(v_b_730_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v_b_730_, 1);
v___x_736_ = lean_apply_1(v_h__1_731_, v_a_735_);
return v___x_736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_737_, lean_object* v_h__1_738_, lean_object* v_h__2_739_){
_start:
{
if (lean_obj_tag(v_x_737_) == 0)
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
v_val_742_ = lean_ctor_get(v_x_737_, 0);
lean_inc(v_val_742_);
lean_dec_ref_known(v_x_737_, 1);
v___x_743_ = lean_apply_1(v_h__2_739_, v_val_742_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b2_744_, lean_object* v_motive_745_, lean_object* v_x_746_, lean_object* v_h__1_747_, lean_object* v_h__2_748_){
_start:
{
if (lean_obj_tag(v_x_746_) == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; 
lean_dec(v_h__2_748_);
v___x_749_ = lean_box(0);
v___x_750_ = lean_apply_1(v_h__1_747_, v___x_749_);
return v___x_750_;
}
else
{
lean_object* v_val_751_; lean_object* v___x_752_; 
lean_dec(v_h__1_747_);
v_val_751_ = lean_ctor_get(v_x_746_, 0);
lean_inc(v_val_751_);
lean_dec_ref_known(v_x_746_, 1);
v___x_752_ = lean_apply_1(v_h__2_748_, v_val_751_);
return v___x_752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter___redArg(lean_object* v_x_753_, lean_object* v_h__1_754_, lean_object* v_h__2_755_){
_start:
{
if (lean_obj_tag(v_x_753_) == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec(v_h__2_755_);
v___x_756_ = lean_box(0);
v___x_757_ = lean_apply_1(v_h__1_754_, v___x_756_);
return v___x_757_;
}
else
{
lean_object* v_val_758_; lean_object* v_fst_759_; lean_object* v_snd_760_; lean_object* v___x_761_; 
lean_dec(v_h__1_754_);
v_val_758_ = lean_ctor_get(v_x_753_, 0);
lean_inc(v_val_758_);
lean_dec_ref_known(v_x_753_, 1);
v_fst_759_ = lean_ctor_get(v_val_758_, 0);
lean_inc(v_fst_759_);
v_snd_760_ = lean_ctor_get(v_val_758_, 1);
lean_inc(v_snd_760_);
lean_dec(v_val_758_);
v___x_761_ = lean_apply_2(v_h__2_755_, v_fst_759_, v_snd_760_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter(lean_object* v_00_u03b1_762_, lean_object* v_00_u03b2_763_, lean_object* v_motive_764_, lean_object* v_x_765_, lean_object* v_h__1_766_, lean_object* v_h__2_767_){
_start:
{
if (lean_obj_tag(v_x_765_) == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec(v_h__2_767_);
v___x_768_ = lean_box(0);
v___x_769_ = lean_apply_1(v_h__1_766_, v___x_768_);
return v___x_769_;
}
else
{
lean_object* v_val_770_; lean_object* v_fst_771_; lean_object* v_snd_772_; lean_object* v___x_773_; 
lean_dec(v_h__1_766_);
v_val_770_ = lean_ctor_get(v_x_765_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v_x_765_, 1);
v_fst_771_ = lean_ctor_get(v_val_770_, 0);
lean_inc(v_fst_771_);
v_snd_772_ = lean_ctor_get(v_val_770_, 1);
lean_inc(v_snd_772_);
lean_dec(v_val_770_);
v___x_773_ = lean_apply_2(v_h__2_767_, v_fst_771_, v_snd_772_);
return v___x_773_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(lean_object* v_x_774_, lean_object* v_h__1_775_, lean_object* v_h__2_776_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object* v_00_u03b2_781_, lean_object* v_motive_782_, lean_object* v_x_783_, lean_object* v_h__1_784_, lean_object* v_h__2_785_){
_start:
{
if (lean_obj_tag(v_x_783_) == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; 
lean_dec(v_h__2_785_);
v___x_786_ = lean_box(0);
v___x_787_ = lean_apply_1(v_h__1_784_, v___x_786_);
return v___x_787_;
}
else
{
lean_object* v_val_788_; lean_object* v___x_789_; 
lean_dec(v_h__1_784_);
v_val_788_ = lean_ctor_get(v_x_783_, 0);
lean_inc(v_val_788_);
lean_dec_ref_known(v_x_783_, 1);
v___x_789_ = lean_apply_1(v_h__2_785_, v_val_788_);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___redArg(lean_object* v_x_790_, lean_object* v_h__1_791_, lean_object* v_h__2_792_){
_start:
{
if (lean_obj_tag(v_x_790_) == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec(v_h__2_792_);
v___x_793_ = lean_box(0);
v___x_794_ = lean_apply_1(v_h__1_791_, v___x_793_);
return v___x_794_;
}
else
{
lean_object* v_val_795_; lean_object* v___x_796_; 
lean_dec(v_h__1_791_);
v_val_795_ = lean_ctor_get(v_x_790_, 0);
lean_inc(v_val_795_);
lean_dec_ref_known(v_x_790_, 1);
v___x_796_ = lean_apply_1(v_h__2_792_, v_val_795_);
return v___x_796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter(lean_object* v_00_u03b2_797_, lean_object* v_motive_798_, lean_object* v_x_799_, lean_object* v_h__1_800_, lean_object* v_h__2_801_){
_start:
{
if (lean_obj_tag(v_x_799_) == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec(v_h__2_801_);
v___x_802_ = lean_box(0);
v___x_803_ = lean_apply_1(v_h__1_800_, v___x_802_);
return v___x_803_;
}
else
{
lean_object* v_val_804_; lean_object* v___x_805_; 
lean_dec(v_h__1_800_);
v_val_804_ = lean_ctor_get(v_x_799_, 0);
lean_inc(v_val_804_);
lean_dec_ref_known(v_x_799_, 1);
v___x_805_ = lean_apply_1(v_h__2_801_, v_val_804_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t v_x_806_, lean_object* v_h__1_807_, lean_object* v_h__2_808_, lean_object* v_h__3_809_){
_start:
{
switch(v_x_806_)
{
case 0:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v_h__3_809_);
lean_dec(v_h__2_808_);
v___x_810_ = lean_box(0);
v___x_811_ = lean_apply_1(v_h__1_807_, v___x_810_);
return v___x_811_;
}
case 1:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
lean_dec(v_h__2_808_);
lean_dec(v_h__1_807_);
v___x_812_ = lean_box(0);
v___x_813_ = lean_apply_1(v_h__3_809_, v___x_812_);
return v___x_813_;
}
default: 
{
lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec(v_h__3_809_);
lean_dec(v_h__1_807_);
v___x_814_ = lean_box(0);
v___x_815_ = lean_apply_1(v_h__2_808_, v___x_814_);
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object* v_x_816_, lean_object* v_h__1_817_, lean_object* v_h__2_818_, lean_object* v_h__3_819_){
_start:
{
uint8_t v_x_33__boxed_820_; lean_object* v_res_821_; 
v_x_33__boxed_820_ = lean_unbox(v_x_816_);
v_res_821_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_33__boxed_820_, v_h__1_817_, v_h__2_818_, v_h__3_819_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object* v_motive_822_, uint8_t v_x_823_, lean_object* v_h__1_824_, lean_object* v_h__2_825_, lean_object* v_h__3_826_){
_start:
{
switch(v_x_823_)
{
case 0:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec(v_h__3_826_);
lean_dec(v_h__2_825_);
v___x_827_ = lean_box(0);
v___x_828_ = lean_apply_1(v_h__1_824_, v___x_827_);
return v___x_828_;
}
case 1:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec(v_h__2_825_);
lean_dec(v_h__1_824_);
v___x_829_ = lean_box(0);
v___x_830_ = lean_apply_1(v_h__3_826_, v___x_829_);
return v___x_830_;
}
default: 
{
lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec(v_h__3_826_);
lean_dec(v_h__1_824_);
v___x_831_ = lean_box(0);
v___x_832_ = lean_apply_1(v_h__2_825_, v___x_831_);
return v___x_832_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object* v_motive_833_, lean_object* v_x_834_, lean_object* v_h__1_835_, lean_object* v_h__2_836_, lean_object* v_h__3_837_){
_start:
{
uint8_t v_x_48__boxed_838_; lean_object* v_res_839_; 
v_x_48__boxed_838_ = lean_unbox(v_x_834_);
v_res_839_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_833_, v_x_48__boxed_838_, v_h__1_835_, v_h__2_836_, v_h__3_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter___redArg(lean_object* v_x_840_, lean_object* v_h__1_841_, lean_object* v_h__2_842_){
_start:
{
if (lean_obj_tag(v_x_840_) == 0)
{
lean_object* v___x_843_; lean_object* v___x_844_; 
lean_dec(v_h__1_841_);
v___x_843_ = lean_box(0);
v___x_844_ = lean_apply_1(v_h__2_842_, v___x_843_);
return v___x_844_;
}
else
{
lean_object* v_val_845_; lean_object* v___x_846_; 
lean_dec(v_h__2_842_);
v_val_845_ = lean_ctor_get(v_x_840_, 0);
lean_inc(v_val_845_);
lean_dec_ref_known(v_x_840_, 1);
v___x_846_ = lean_apply_1(v_h__1_841_, v_val_845_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter(lean_object* v_00_u03b1_847_, lean_object* v_00_u03b2_848_, lean_object* v_motive_849_, lean_object* v_x_850_, lean_object* v_h__1_851_, lean_object* v_h__2_852_){
_start:
{
if (lean_obj_tag(v_x_850_) == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec(v_h__1_851_);
v___x_853_ = lean_box(0);
v___x_854_ = lean_apply_1(v_h__2_852_, v___x_853_);
return v___x_854_;
}
else
{
lean_object* v_val_855_; lean_object* v___x_856_; 
lean_dec(v_h__2_852_);
v_val_855_ = lean_ctor_get(v_x_850_, 0);
lean_inc(v_val_855_);
lean_dec_ref_known(v_x_850_, 1);
v___x_856_ = lean_apply_1(v_h__1_851_, v_val_855_);
return v___x_856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_857_, lean_object* v_h__1_858_, lean_object* v_h__2_859_){
_start:
{
if (lean_obj_tag(v_x_857_) == 0)
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec(v_h__1_858_);
v___x_860_ = lean_box(0);
v___x_861_ = lean_apply_1(v_h__2_859_, v___x_860_);
return v___x_861_;
}
else
{
lean_object* v_val_862_; lean_object* v___x_863_; 
lean_dec(v_h__2_859_);
v_val_862_ = lean_ctor_get(v_x_857_, 0);
lean_inc(v_val_862_);
lean_dec_ref_known(v_x_857_, 1);
v___x_863_ = lean_apply_1(v_h__1_858_, v_val_862_);
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_864_, lean_object* v_motive_865_, lean_object* v_x_866_, lean_object* v_h__1_867_, lean_object* v_h__2_868_){
_start:
{
if (lean_obj_tag(v_x_866_) == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec(v_h__1_867_);
v___x_869_ = lean_box(0);
v___x_870_ = lean_apply_1(v_h__2_868_, v___x_869_);
return v___x_870_;
}
else
{
lean_object* v_val_871_; lean_object* v___x_872_; 
lean_dec(v_h__2_868_);
v_val_871_ = lean_ctor_get(v_x_866_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v_x_866_, 1);
v___x_872_ = lean_apply_1(v_h__1_867_, v_val_871_);
return v___x_872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_873_, lean_object* v_h__1_874_, lean_object* v_h__2_875_){
_start:
{
if (lean_obj_tag(v_x_873_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_877_; 
lean_dec(v_h__2_875_);
v_a_876_ = lean_ctor_get(v_x_873_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v_x_873_, 1);
v___x_877_ = lean_apply_1(v_h__1_874_, v_a_876_);
return v___x_877_;
}
else
{
lean_object* v_a_878_; lean_object* v___x_879_; 
lean_dec(v_h__1_874_);
v_a_878_ = lean_ctor_get(v_x_873_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v_x_873_, 1);
v___x_879_ = lean_apply_1(v_h__2_875_, v_a_878_);
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_880_, lean_object* v_motive_881_, lean_object* v_x_882_, lean_object* v_h__1_883_, lean_object* v_h__2_884_){
_start:
{
if (lean_obj_tag(v_x_882_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_886_; 
lean_dec(v_h__2_884_);
v_a_885_ = lean_ctor_get(v_x_882_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v_x_882_, 1);
v___x_886_ = lean_apply_1(v_h__1_883_, v_a_885_);
return v___x_886_;
}
else
{
lean_object* v_a_887_; lean_object* v___x_888_; 
lean_dec(v_h__1_883_);
v_a_887_ = lean_ctor_get(v_x_882_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v_x_882_, 1);
v___x_888_ = lean_apply_1(v_h__2_884_, v_a_887_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_889_, lean_object* v_h__1_890_, lean_object* v_h__2_891_){
_start:
{
if (lean_obj_tag(v_x_889_) == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec(v_h__1_890_);
v___x_892_ = lean_box(0);
v___x_893_ = lean_apply_1(v_h__2_891_, v___x_892_);
return v___x_893_;
}
else
{
lean_object* v_val_894_; lean_object* v___x_895_; 
lean_dec(v_h__2_891_);
v_val_894_ = lean_ctor_get(v_x_889_, 0);
lean_inc(v_val_894_);
lean_dec_ref_known(v_x_889_, 1);
v___x_895_ = lean_apply_1(v_h__1_890_, v_val_894_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_896_, lean_object* v_00_u03b2_897_, lean_object* v_motive_898_, lean_object* v_x_899_, lean_object* v_h__1_900_, lean_object* v_h__2_901_){
_start:
{
if (lean_obj_tag(v_x_899_) == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; 
lean_dec(v_h__1_900_);
v___x_902_ = lean_box(0);
v___x_903_ = lean_apply_1(v_h__2_901_, v___x_902_);
return v___x_903_;
}
else
{
lean_object* v_val_904_; lean_object* v___x_905_; 
lean_dec(v_h__2_901_);
v_val_904_ = lean_ctor_get(v_x_899_, 0);
lean_inc(v_val_904_);
lean_dec_ref_known(v_x_899_, 1);
v___x_905_ = lean_apply_1(v_h__1_900_, v_val_904_);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_h__1_908_, lean_object* v_h__2_909_){
_start:
{
if (lean_obj_tag(v_x_906_) == 0)
{
lean_object* v_size_910_; lean_object* v_k_911_; lean_object* v_v_912_; lean_object* v_l_913_; lean_object* v_r_914_; lean_object* v___x_915_; 
lean_dec(v_h__1_908_);
v_size_910_ = lean_ctor_get(v_x_906_, 0);
lean_inc(v_size_910_);
v_k_911_ = lean_ctor_get(v_x_906_, 1);
lean_inc(v_k_911_);
v_v_912_ = lean_ctor_get(v_x_906_, 2);
lean_inc(v_v_912_);
v_l_913_ = lean_ctor_get(v_x_906_, 3);
lean_inc(v_l_913_);
v_r_914_ = lean_ctor_get(v_x_906_, 4);
lean_inc(v_r_914_);
lean_dec_ref_known(v_x_906_, 5);
v___x_915_ = lean_apply_6(v_h__2_909_, v_size_910_, v_k_911_, v_v_912_, v_l_913_, v_r_914_, v_x_907_);
return v___x_915_;
}
else
{
lean_object* v___x_916_; 
lean_dec(v_h__2_909_);
v___x_916_ = lean_apply_1(v_h__1_908_, v_x_907_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object* v_00_u03b1_917_, lean_object* v_00_u03b2_918_, lean_object* v_motive_919_, lean_object* v_x_920_, lean_object* v_x_921_, lean_object* v_h__1_922_, lean_object* v_h__2_923_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
lean_object* v_size_924_; lean_object* v_k_925_; lean_object* v_v_926_; lean_object* v_l_927_; lean_object* v_r_928_; lean_object* v___x_929_; 
lean_dec(v_h__1_922_);
v_size_924_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_size_924_);
v_k_925_ = lean_ctor_get(v_x_920_, 1);
lean_inc(v_k_925_);
v_v_926_ = lean_ctor_get(v_x_920_, 2);
lean_inc(v_v_926_);
v_l_927_ = lean_ctor_get(v_x_920_, 3);
lean_inc(v_l_927_);
v_r_928_ = lean_ctor_get(v_x_920_, 4);
lean_inc(v_r_928_);
lean_dec_ref_known(v_x_920_, 5);
v___x_929_ = lean_apply_6(v_h__2_923_, v_size_924_, v_k_925_, v_v_926_, v_l_927_, v_r_928_, v_x_921_);
return v___x_929_;
}
else
{
lean_object* v___x_930_; 
lean_dec(v_h__2_923_);
v___x_930_ = lean_apply_1(v_h__1_922_, v_x_921_);
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t v_x_931_, lean_object* v_h__1_932_, lean_object* v_h__2_933_, lean_object* v_h__3_934_){
_start:
{
switch(v_x_931_)
{
case 0:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec(v_h__3_934_);
lean_dec(v_h__2_933_);
v___x_935_ = lean_box(0);
v___x_936_ = lean_apply_1(v_h__1_932_, v___x_935_);
return v___x_936_;
}
case 1:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v_h__3_934_);
lean_dec(v_h__1_932_);
v___x_937_ = lean_box(0);
v___x_938_ = lean_apply_1(v_h__2_933_, v___x_937_);
return v___x_938_;
}
default: 
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec(v_h__2_933_);
lean_dec(v_h__1_932_);
v___x_939_ = lean_box(0);
v___x_940_ = lean_apply_1(v_h__3_934_, v___x_939_);
return v___x_940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_941_, lean_object* v_h__1_942_, lean_object* v_h__2_943_, lean_object* v_h__3_944_){
_start:
{
uint8_t v_x_33__boxed_945_; lean_object* v_res_946_; 
v_x_33__boxed_945_ = lean_unbox(v_x_941_);
v_res_946_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_33__boxed_945_, v_h__1_942_, v_h__2_943_, v_h__3_944_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object* v_motive_947_, uint8_t v_x_948_, lean_object* v_h__1_949_, lean_object* v_h__2_950_, lean_object* v_h__3_951_){
_start:
{
switch(v_x_948_)
{
case 0:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
lean_dec(v_h__3_951_);
lean_dec(v_h__2_950_);
v___x_952_ = lean_box(0);
v___x_953_ = lean_apply_1(v_h__1_949_, v___x_952_);
return v___x_953_;
}
case 1:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec(v_h__3_951_);
lean_dec(v_h__1_949_);
v___x_954_ = lean_box(0);
v___x_955_ = lean_apply_1(v_h__2_950_, v___x_954_);
return v___x_955_;
}
default: 
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec(v_h__2_950_);
lean_dec(v_h__1_949_);
v___x_956_ = lean_box(0);
v___x_957_ = lean_apply_1(v_h__3_951_, v___x_956_);
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object* v_motive_958_, lean_object* v_x_959_, lean_object* v_h__1_960_, lean_object* v_h__2_961_, lean_object* v_h__3_962_){
_start:
{
uint8_t v_x_48__boxed_963_; lean_object* v_res_964_; 
v_x_48__boxed_963_ = lean_unbox(v_x_959_);
v_res_964_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(v_motive_958_, v_x_48__boxed_963_, v_h__1_960_, v_h__2_961_, v_h__3_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(uint8_t v_x_965_, lean_object* v_h__1_966_, lean_object* v_h__2_967_){
_start:
{
if (v_x_965_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec(v_h__1_966_);
v___x_968_ = lean_box(0);
v___x_969_ = lean_apply_1(v_h__2_967_, v___x_968_);
return v___x_969_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec(v_h__2_967_);
v___x_970_ = lean_box(0);
v___x_971_ = lean_apply_1(v_h__1_966_, v___x_970_);
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_972_, lean_object* v_h__1_973_, lean_object* v_h__2_974_){
_start:
{
uint8_t v_x_24__boxed_975_; lean_object* v_res_976_; 
v_x_24__boxed_975_ = lean_unbox(v_x_972_);
v_res_976_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_975_, v_h__1_973_, v_h__2_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(lean_object* v_motive_977_, uint8_t v_x_978_, lean_object* v_h__1_979_, lean_object* v_h__2_980_){
_start:
{
if (v_x_978_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec(v_h__1_979_);
v___x_981_ = lean_box(0);
v___x_982_ = lean_apply_1(v_h__2_980_, v___x_981_);
return v___x_982_;
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec(v_h__2_980_);
v___x_983_ = lean_box(0);
v___x_984_ = lean_apply_1(v_h__1_979_, v___x_983_);
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_985_, lean_object* v_x_986_, lean_object* v_h__1_987_, lean_object* v_h__2_988_){
_start:
{
uint8_t v_x_35__boxed_989_; lean_object* v_res_990_; 
v_x_35__boxed_989_ = lean_unbox(v_x_986_);
v_res_990_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(v_motive_985_, v_x_35__boxed_989_, v_h__1_987_, v_h__2_988_);
return v_res_990_;
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
