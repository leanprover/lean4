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
lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1(lean_object* v_00_u03b1_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter___redArg(lean_object* v_l_8_, lean_object* v_h__1_9_, lean_object* v_h__2_10_){
_start:
{
if (lean_obj_tag(v_l_8_) == 0)
{
lean_object* v_size_11_; lean_object* v_k_12_; lean_object* v_v_13_; lean_object* v_l_14_; lean_object* v_r_15_; lean_object* v___x_16_; 
lean_dec(v_h__1_9_);
v_size_11_ = lean_ctor_get(v_l_8_, 0);
lean_inc(v_size_11_);
v_k_12_ = lean_ctor_get(v_l_8_, 1);
lean_inc(v_k_12_);
v_v_13_ = lean_ctor_get(v_l_8_, 2);
lean_inc(v_v_13_);
v_l_14_ = lean_ctor_get(v_l_8_, 3);
lean_inc(v_l_14_);
v_r_15_ = lean_ctor_get(v_l_8_, 4);
lean_inc(v_r_15_);
lean_dec_ref_known(v_l_8_, 5);
v___x_16_ = lean_apply_5(v_h__2_10_, v_size_11_, v_k_12_, v_v_13_, v_l_14_, v_r_15_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_h__2_10_);
v___x_17_ = lean_box(0);
v___x_18_ = lean_apply_1(v_h__1_9_, v___x_17_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter(lean_object* v_00_u03b1_19_, lean_object* v_00_u03b2_20_, lean_object* v_motive_21_, lean_object* v_l_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_){
_start:
{
if (lean_obj_tag(v_l_22_) == 0)
{
lean_object* v_size_25_; lean_object* v_k_26_; lean_object* v_v_27_; lean_object* v_l_28_; lean_object* v_r_29_; lean_object* v___x_30_; 
lean_dec(v_h__1_23_);
v_size_25_ = lean_ctor_get(v_l_22_, 0);
lean_inc(v_size_25_);
v_k_26_ = lean_ctor_get(v_l_22_, 1);
lean_inc(v_k_26_);
v_v_27_ = lean_ctor_get(v_l_22_, 2);
lean_inc(v_v_27_);
v_l_28_ = lean_ctor_get(v_l_22_, 3);
lean_inc(v_l_28_);
v_r_29_ = lean_ctor_get(v_l_22_, 4);
lean_inc(v_r_29_);
lean_dec_ref_known(v_l_22_, 5);
v___x_30_ = lean_apply_5(v_h__2_24_, v_size_25_, v_k_26_, v_v_27_, v_l_28_, v_r_29_);
return v___x_30_;
}
else
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v_h__2_24_);
v___x_31_ = lean_box(0);
v___x_32_ = lean_apply_1(v_h__1_23_, v___x_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(lean_object* v_r_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
if (lean_obj_tag(v_r_33_) == 0)
{
lean_object* v_size_36_; lean_object* v_k_37_; lean_object* v_v_38_; lean_object* v_l_39_; lean_object* v_r_40_; lean_object* v___x_41_; 
lean_dec(v_h__1_34_);
v_size_36_ = lean_ctor_get(v_r_33_, 0);
lean_inc(v_size_36_);
v_k_37_ = lean_ctor_get(v_r_33_, 1);
lean_inc(v_k_37_);
v_v_38_ = lean_ctor_get(v_r_33_, 2);
lean_inc(v_v_38_);
v_l_39_ = lean_ctor_get(v_r_33_, 3);
lean_inc(v_l_39_);
v_r_40_ = lean_ctor_get(v_r_33_, 4);
lean_inc(v_r_40_);
lean_dec_ref_known(v_r_33_, 5);
v___x_41_ = lean_apply_6(v_h__2_35_, v_size_36_, v_k_37_, v_v_38_, v_l_39_, v_r_40_, lean_box(0));
return v___x_41_;
}
else
{
lean_object* v___x_42_; 
lean_dec(v_h__2_35_);
v___x_42_ = lean_apply_1(v_h__1_34_, lean_box(0));
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(lean_object* v_00_u03b1_43_, lean_object* v_00_u03b2_44_, lean_object* v_l_45_, lean_object* v_motive_46_, lean_object* v_r_47_, lean_object* v_h_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_){
_start:
{
if (lean_obj_tag(v_r_47_) == 0)
{
lean_object* v_size_51_; lean_object* v_k_52_; lean_object* v_v_53_; lean_object* v_l_54_; lean_object* v_r_55_; lean_object* v___x_56_; 
lean_dec(v_h__1_49_);
v_size_51_ = lean_ctor_get(v_r_47_, 0);
lean_inc(v_size_51_);
v_k_52_ = lean_ctor_get(v_r_47_, 1);
lean_inc(v_k_52_);
v_v_53_ = lean_ctor_get(v_r_47_, 2);
lean_inc(v_v_53_);
v_l_54_ = lean_ctor_get(v_r_47_, 3);
lean_inc(v_l_54_);
v_r_55_ = lean_ctor_get(v_r_47_, 4);
lean_inc(v_r_55_);
lean_dec_ref_known(v_r_47_, 5);
v___x_56_ = lean_apply_6(v_h__2_50_, v_size_51_, v_k_52_, v_v_53_, v_l_54_, v_r_55_, lean_box(0));
return v___x_56_;
}
else
{
lean_object* v___x_57_; 
lean_dec(v_h__2_50_);
v___x_57_ = lean_apply_1(v_h__1_49_, lean_box(0));
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___boxed(lean_object* v_00_u03b1_58_, lean_object* v_00_u03b2_59_, lean_object* v_l_60_, lean_object* v_motive_61_, lean_object* v_r_62_, lean_object* v_h_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(v_00_u03b1_58_, v_00_u03b2_59_, v_l_60_, v_motive_61_, v_r_62_, v_h_63_, v_h__1_64_, v_h__2_65_);
lean_dec(v_l_60_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(lean_object* v_l_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
if (lean_obj_tag(v_l_67_) == 0)
{
lean_object* v_size_70_; lean_object* v_k_71_; lean_object* v_v_72_; lean_object* v_l_73_; lean_object* v_r_74_; lean_object* v___x_75_; 
lean_dec(v_h__1_68_);
v_size_70_ = lean_ctor_get(v_l_67_, 0);
lean_inc(v_size_70_);
v_k_71_ = lean_ctor_get(v_l_67_, 1);
lean_inc(v_k_71_);
v_v_72_ = lean_ctor_get(v_l_67_, 2);
lean_inc(v_v_72_);
v_l_73_ = lean_ctor_get(v_l_67_, 3);
lean_inc(v_l_73_);
v_r_74_ = lean_ctor_get(v_l_67_, 4);
lean_inc(v_r_74_);
lean_dec_ref_known(v_l_67_, 5);
v___x_75_ = lean_apply_7(v_h__2_69_, v_size_70_, v_k_71_, v_v_72_, v_l_73_, v_r_74_, lean_box(0), lean_box(0));
return v___x_75_;
}
else
{
lean_object* v___x_76_; 
lean_dec(v_h__2_69_);
v___x_76_ = lean_apply_2(v_h__1_68_, lean_box(0), lean_box(0));
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(lean_object* v_00_u03b1_77_, lean_object* v_00_u03b2_78_, lean_object* v_r_79_, lean_object* v_motive_80_, lean_object* v_l_81_, lean_object* v_h_82_, lean_object* v_h_83_, lean_object* v_h__1_84_, lean_object* v_h__2_85_){
_start:
{
if (lean_obj_tag(v_l_81_) == 0)
{
lean_object* v_size_86_; lean_object* v_k_87_; lean_object* v_v_88_; lean_object* v_l_89_; lean_object* v_r_90_; lean_object* v___x_91_; 
lean_dec(v_h__1_84_);
v_size_86_ = lean_ctor_get(v_l_81_, 0);
lean_inc(v_size_86_);
v_k_87_ = lean_ctor_get(v_l_81_, 1);
lean_inc(v_k_87_);
v_v_88_ = lean_ctor_get(v_l_81_, 2);
lean_inc(v_v_88_);
v_l_89_ = lean_ctor_get(v_l_81_, 3);
lean_inc(v_l_89_);
v_r_90_ = lean_ctor_get(v_l_81_, 4);
lean_inc(v_r_90_);
lean_dec_ref_known(v_l_81_, 5);
v___x_91_ = lean_apply_7(v_h__2_85_, v_size_86_, v_k_87_, v_v_88_, v_l_89_, v_r_90_, lean_box(0), lean_box(0));
return v___x_91_;
}
else
{
lean_object* v___x_92_; 
lean_dec(v_h__2_85_);
v___x_92_ = lean_apply_2(v_h__1_84_, lean_box(0), lean_box(0));
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___boxed(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_r_95_, lean_object* v_motive_96_, lean_object* v_l_97_, lean_object* v_h_98_, lean_object* v_h_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(v_00_u03b1_93_, v_00_u03b2_94_, v_r_95_, v_motive_96_, v_l_97_, v_h_98_, v_h_99_, v_h__1_100_, v_h__2_101_);
lean_dec(v_r_95_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object* v_l_103_, lean_object* v_h__1_104_, lean_object* v_h__2_105_){
_start:
{
if (lean_obj_tag(v_l_103_) == 0)
{
lean_object* v_size_106_; lean_object* v_k_107_; lean_object* v_v_108_; lean_object* v_l_109_; lean_object* v_r_110_; lean_object* v___x_111_; 
lean_dec(v_h__1_104_);
v_size_106_ = lean_ctor_get(v_l_103_, 0);
lean_inc(v_size_106_);
v_k_107_ = lean_ctor_get(v_l_103_, 1);
lean_inc(v_k_107_);
v_v_108_ = lean_ctor_get(v_l_103_, 2);
lean_inc(v_v_108_);
v_l_109_ = lean_ctor_get(v_l_103_, 3);
lean_inc(v_l_109_);
v_r_110_ = lean_ctor_get(v_l_103_, 4);
lean_inc(v_r_110_);
lean_dec_ref_known(v_l_103_, 5);
v___x_111_ = lean_apply_7(v_h__2_105_, v_size_106_, v_k_107_, v_v_108_, v_l_109_, v_r_110_, lean_box(0), lean_box(0));
return v___x_111_;
}
else
{
lean_object* v___x_112_; 
lean_dec(v_h__2_105_);
v___x_112_ = lean_apply_2(v_h__1_104_, lean_box(0), lean_box(0));
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object* v_00_u03b1_113_, lean_object* v_00_u03b2_114_, lean_object* v_r_115_, lean_object* v_motive_116_, lean_object* v_l_117_, lean_object* v_hl_118_, lean_object* v_hlr_119_, lean_object* v_h__1_120_, lean_object* v_h__2_121_){
_start:
{
if (lean_obj_tag(v_l_117_) == 0)
{
lean_object* v_size_122_; lean_object* v_k_123_; lean_object* v_v_124_; lean_object* v_l_125_; lean_object* v_r_126_; lean_object* v___x_127_; 
lean_dec(v_h__1_120_);
v_size_122_ = lean_ctor_get(v_l_117_, 0);
lean_inc(v_size_122_);
v_k_123_ = lean_ctor_get(v_l_117_, 1);
lean_inc(v_k_123_);
v_v_124_ = lean_ctor_get(v_l_117_, 2);
lean_inc(v_v_124_);
v_l_125_ = lean_ctor_get(v_l_117_, 3);
lean_inc(v_l_125_);
v_r_126_ = lean_ctor_get(v_l_117_, 4);
lean_inc(v_r_126_);
lean_dec_ref_known(v_l_117_, 5);
v___x_127_ = lean_apply_7(v_h__2_121_, v_size_122_, v_k_123_, v_v_124_, v_l_125_, v_r_126_, lean_box(0), lean_box(0));
return v___x_127_;
}
else
{
lean_object* v___x_128_; 
lean_dec(v_h__2_121_);
v___x_128_ = lean_apply_2(v_h__1_120_, lean_box(0), lean_box(0));
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object* v_00_u03b1_129_, lean_object* v_00_u03b2_130_, lean_object* v_r_131_, lean_object* v_motive_132_, lean_object* v_l_133_, lean_object* v_hl_134_, lean_object* v_hlr_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(v_00_u03b1_129_, v_00_u03b2_130_, v_r_131_, v_motive_132_, v_l_133_, v_hl_134_, v_hlr_135_, v_h__1_136_, v_h__2_137_);
lean_dec(v_r_131_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(lean_object* v_x_139_, lean_object* v_h__1_140_){
_start:
{
lean_object* v_k_141_; lean_object* v_v_142_; lean_object* v_tree_143_; lean_object* v___x_144_; 
v_k_141_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_k_141_);
v_v_142_ = lean_ctor_get(v_x_139_, 1);
lean_inc(v_v_142_);
v_tree_143_ = lean_ctor_get(v_x_139_, 2);
lean_inc(v_tree_143_);
lean_dec_ref(v_x_139_);
v___x_144_ = lean_apply_5(v_h__1_140_, v_k_141_, v_v_142_, v_tree_143_, lean_box(0), lean_box(0));
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object* v_00_u03b1_145_, lean_object* v_00_u03b2_146_, lean_object* v_l_x27_147_, lean_object* v_r_x27_148_, lean_object* v_motive_149_, lean_object* v_x_150_, lean_object* v_h__1_151_){
_start:
{
lean_object* v_k_152_; lean_object* v_v_153_; lean_object* v_tree_154_; lean_object* v___x_155_; 
v_k_152_ = lean_ctor_get(v_x_150_, 0);
lean_inc(v_k_152_);
v_v_153_ = lean_ctor_get(v_x_150_, 1);
lean_inc(v_v_153_);
v_tree_154_ = lean_ctor_get(v_x_150_, 2);
lean_inc(v_tree_154_);
lean_dec_ref(v_x_150_);
v___x_155_ = lean_apply_5(v_h__1_151_, v_k_152_, v_v_153_, v_tree_154_, lean_box(0), lean_box(0));
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object* v_00_u03b1_156_, lean_object* v_00_u03b2_157_, lean_object* v_l_x27_158_, lean_object* v_r_x27_159_, lean_object* v_motive_160_, lean_object* v_x_161_, lean_object* v_h__1_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(v_00_u03b1_156_, v_00_u03b2_157_, v_l_x27_158_, v_r_x27_159_, v_motive_160_, v_x_161_, v_h__1_162_);
lean_dec(v_r_x27_159_);
lean_dec(v_l_x27_158_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(lean_object* v_r_164_, lean_object* v_h__1_165_, lean_object* v_h__2_166_){
_start:
{
if (lean_obj_tag(v_r_164_) == 0)
{
lean_object* v_size_167_; lean_object* v_k_168_; lean_object* v_v_169_; lean_object* v_l_170_; lean_object* v_r_171_; lean_object* v___x_172_; 
lean_dec(v_h__1_165_);
v_size_167_ = lean_ctor_get(v_r_164_, 0);
lean_inc(v_size_167_);
v_k_168_ = lean_ctor_get(v_r_164_, 1);
lean_inc(v_k_168_);
v_v_169_ = lean_ctor_get(v_r_164_, 2);
lean_inc(v_v_169_);
v_l_170_ = lean_ctor_get(v_r_164_, 3);
lean_inc(v_l_170_);
v_r_171_ = lean_ctor_get(v_r_164_, 4);
lean_inc(v_r_171_);
lean_dec_ref_known(v_r_164_, 5);
v___x_172_ = lean_apply_7(v_h__2_166_, v_size_167_, v_k_168_, v_v_169_, v_l_170_, v_r_171_, lean_box(0), lean_box(0));
return v___x_172_;
}
else
{
lean_object* v___x_173_; 
lean_dec(v_h__2_166_);
v___x_173_ = lean_apply_2(v_h__1_165_, lean_box(0), lean_box(0));
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object* v_00_u03b1_174_, lean_object* v_00_u03b2_175_, lean_object* v_l_176_, lean_object* v_motive_177_, lean_object* v_r_178_, lean_object* v_hr_179_, lean_object* v_hlr_180_, lean_object* v_h__1_181_, lean_object* v_h__2_182_){
_start:
{
if (lean_obj_tag(v_r_178_) == 0)
{
lean_object* v_size_183_; lean_object* v_k_184_; lean_object* v_v_185_; lean_object* v_l_186_; lean_object* v_r_187_; lean_object* v___x_188_; 
lean_dec(v_h__1_181_);
v_size_183_ = lean_ctor_get(v_r_178_, 0);
lean_inc(v_size_183_);
v_k_184_ = lean_ctor_get(v_r_178_, 1);
lean_inc(v_k_184_);
v_v_185_ = lean_ctor_get(v_r_178_, 2);
lean_inc(v_v_185_);
v_l_186_ = lean_ctor_get(v_r_178_, 3);
lean_inc(v_l_186_);
v_r_187_ = lean_ctor_get(v_r_178_, 4);
lean_inc(v_r_187_);
lean_dec_ref_known(v_r_178_, 5);
v___x_188_ = lean_apply_7(v_h__2_182_, v_size_183_, v_k_184_, v_v_185_, v_l_186_, v_r_187_, lean_box(0), lean_box(0));
return v___x_188_;
}
else
{
lean_object* v___x_189_; 
lean_dec(v_h__2_182_);
v___x_189_ = lean_apply_2(v_h__1_181_, lean_box(0), lean_box(0));
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object* v_00_u03b1_190_, lean_object* v_00_u03b2_191_, lean_object* v_l_192_, lean_object* v_motive_193_, lean_object* v_r_194_, lean_object* v_hr_195_, lean_object* v_hlr_196_, lean_object* v_h__1_197_, lean_object* v_h__2_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(v_00_u03b1_190_, v_00_u03b2_191_, v_l_192_, v_motive_193_, v_r_194_, v_hr_195_, v_hlr_196_, v_h__1_197_, v_h__2_198_);
lean_dec(v_l_192_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object* v_r_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_){
_start:
{
if (lean_obj_tag(v_r_200_) == 0)
{
lean_object* v_size_203_; lean_object* v_k_204_; lean_object* v_v_205_; lean_object* v_l_206_; lean_object* v_r_207_; lean_object* v___x_208_; 
lean_dec(v_h__1_201_);
v_size_203_ = lean_ctor_get(v_r_200_, 0);
lean_inc(v_size_203_);
v_k_204_ = lean_ctor_get(v_r_200_, 1);
lean_inc(v_k_204_);
v_v_205_ = lean_ctor_get(v_r_200_, 2);
lean_inc(v_v_205_);
v_l_206_ = lean_ctor_get(v_r_200_, 3);
lean_inc(v_l_206_);
v_r_207_ = lean_ctor_get(v_r_200_, 4);
lean_inc(v_r_207_);
lean_dec_ref_known(v_r_200_, 5);
v___x_208_ = lean_apply_7(v_h__2_202_, v_size_203_, v_k_204_, v_v_205_, v_l_206_, v_r_207_, lean_box(0), lean_box(0));
return v___x_208_;
}
else
{
lean_object* v___x_209_; 
lean_dec(v_h__2_202_);
v___x_209_ = lean_apply_2(v_h__1_201_, lean_box(0), lean_box(0));
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object* v_00_u03b1_210_, lean_object* v_00_u03b2_211_, lean_object* v_motive_212_, lean_object* v_r_213_, lean_object* v_hr_214_, lean_object* v_h__1_215_, lean_object* v_h__2_216_){
_start:
{
if (lean_obj_tag(v_r_213_) == 0)
{
lean_object* v_size_217_; lean_object* v_k_218_; lean_object* v_v_219_; lean_object* v_l_220_; lean_object* v_r_221_; lean_object* v___x_222_; 
lean_dec(v_h__1_215_);
v_size_217_ = lean_ctor_get(v_r_213_, 0);
lean_inc(v_size_217_);
v_k_218_ = lean_ctor_get(v_r_213_, 1);
lean_inc(v_k_218_);
v_v_219_ = lean_ctor_get(v_r_213_, 2);
lean_inc(v_v_219_);
v_l_220_ = lean_ctor_get(v_r_213_, 3);
lean_inc(v_l_220_);
v_r_221_ = lean_ctor_get(v_r_213_, 4);
lean_inc(v_r_221_);
lean_dec_ref_known(v_r_213_, 5);
v___x_222_ = lean_apply_7(v_h__2_216_, v_size_217_, v_k_218_, v_v_219_, v_l_220_, v_r_221_, lean_box(0), lean_box(0));
return v___x_222_;
}
else
{
lean_object* v___x_223_; 
lean_dec(v_h__2_216_);
v___x_223_ = lean_apply_2(v_h__1_215_, lean_box(0), lean_box(0));
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___redArg(lean_object* v_x_224_, lean_object* v_h__1_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lean_apply_3(v_h__1_225_, v_x_224_, lean_box(0), lean_box(0));
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(lean_object* v_00_u03b1_227_, lean_object* v_00_u03b2_228_, lean_object* v_l_229_, lean_object* v_l_x27_x27_230_, lean_object* v_motive_231_, lean_object* v_x_232_, lean_object* v_h__1_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_apply_3(v_h__1_233_, v_x_232_, lean_box(0), lean_box(0));
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___boxed(lean_object* v_00_u03b1_235_, lean_object* v_00_u03b2_236_, lean_object* v_l_237_, lean_object* v_l_x27_x27_238_, lean_object* v_motive_239_, lean_object* v_x_240_, lean_object* v_h__1_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(v_00_u03b1_235_, v_00_u03b2_236_, v_l_237_, v_l_x27_x27_238_, v_motive_239_, v_x_240_, v_h__1_241_);
lean_dec(v_l_x27_x27_238_);
lean_dec(v_l_237_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___redArg(lean_object* v_x_243_, lean_object* v_h__1_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_apply_3(v_h__1_244_, v_x_243_, lean_box(0), lean_box(0));
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_r_248_, lean_object* v_r_x27_249_, lean_object* v_motive_250_, lean_object* v_x_251_, lean_object* v_h__1_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_apply_3(v_h__1_252_, v_x_251_, lean_box(0), lean_box(0));
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___boxed(lean_object* v_00_u03b1_254_, lean_object* v_00_u03b2_255_, lean_object* v_r_256_, lean_object* v_r_x27_257_, lean_object* v_motive_258_, lean_object* v_x_259_, lean_object* v_h__1_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(v_00_u03b1_254_, v_00_u03b2_255_, v_r_256_, v_r_x27_257_, v_motive_258_, v_x_259_, v_h__1_260_);
lean_dec(v_r_x27_257_);
lean_dec(v_r_256_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object* v_t_262_, lean_object* v_h__1_263_, lean_object* v_h__2_264_){
_start:
{
if (lean_obj_tag(v_t_262_) == 0)
{
lean_object* v_size_265_; lean_object* v_k_266_; lean_object* v_v_267_; lean_object* v_l_268_; lean_object* v_r_269_; lean_object* v___x_270_; 
lean_dec(v_h__1_263_);
v_size_265_ = lean_ctor_get(v_t_262_, 0);
lean_inc(v_size_265_);
v_k_266_ = lean_ctor_get(v_t_262_, 1);
lean_inc(v_k_266_);
v_v_267_ = lean_ctor_get(v_t_262_, 2);
lean_inc(v_v_267_);
v_l_268_ = lean_ctor_get(v_t_262_, 3);
lean_inc(v_l_268_);
v_r_269_ = lean_ctor_get(v_t_262_, 4);
lean_inc(v_r_269_);
lean_dec_ref_known(v_t_262_, 5);
v___x_270_ = lean_apply_6(v_h__2_264_, v_size_265_, v_k_266_, v_v_267_, v_l_268_, v_r_269_, lean_box(0));
return v___x_270_;
}
else
{
lean_object* v___x_271_; 
lean_dec(v_h__2_264_);
v___x_271_ = lean_apply_1(v_h__1_263_, lean_box(0));
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object* v_00_u03b1_272_, lean_object* v_00_u03b2_273_, lean_object* v_motive_274_, lean_object* v_t_275_, lean_object* v_hr_276_, lean_object* v_h__1_277_, lean_object* v_h__2_278_){
_start:
{
if (lean_obj_tag(v_t_275_) == 0)
{
lean_object* v_size_279_; lean_object* v_k_280_; lean_object* v_v_281_; lean_object* v_l_282_; lean_object* v_r_283_; lean_object* v___x_284_; 
lean_dec(v_h__1_277_);
v_size_279_ = lean_ctor_get(v_t_275_, 0);
lean_inc(v_size_279_);
v_k_280_ = lean_ctor_get(v_t_275_, 1);
lean_inc(v_k_280_);
v_v_281_ = lean_ctor_get(v_t_275_, 2);
lean_inc(v_v_281_);
v_l_282_ = lean_ctor_get(v_t_275_, 3);
lean_inc(v_l_282_);
v_r_283_ = lean_ctor_get(v_t_275_, 4);
lean_inc(v_r_283_);
lean_dec_ref_known(v_t_275_, 5);
v___x_284_ = lean_apply_6(v_h__2_278_, v_size_279_, v_k_280_, v_v_281_, v_l_282_, v_r_283_, lean_box(0));
return v___x_284_;
}
else
{
lean_object* v___x_285_; 
lean_dec(v_h__2_278_);
v___x_285_ = lean_apply_1(v_h__1_277_, lean_box(0));
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___redArg(lean_object* v_x_286_, lean_object* v_h__1_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_apply_3(v_h__1_287_, v_x_286_, lean_box(0), lean_box(0));
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(lean_object* v_00_u03b1_289_, lean_object* v_00_u03b2_290_, lean_object* v_szl_291_, lean_object* v_k_x27_292_, lean_object* v_v_x27_293_, lean_object* v_l_x27_294_, lean_object* v_r_x27_295_, lean_object* v_l_x27_x27_296_, lean_object* v_motive_297_, lean_object* v_x_298_, lean_object* v_h__1_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = lean_apply_3(v_h__1_299_, v_x_298_, lean_box(0), lean_box(0));
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___boxed(lean_object* v_00_u03b1_301_, lean_object* v_00_u03b2_302_, lean_object* v_szl_303_, lean_object* v_k_x27_304_, lean_object* v_v_x27_305_, lean_object* v_l_x27_306_, lean_object* v_r_x27_307_, lean_object* v_l_x27_x27_308_, lean_object* v_motive_309_, lean_object* v_x_310_, lean_object* v_h__1_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(v_00_u03b1_301_, v_00_u03b2_302_, v_szl_303_, v_k_x27_304_, v_v_x27_305_, v_l_x27_306_, v_r_x27_307_, v_l_x27_x27_308_, v_motive_309_, v_x_310_, v_h__1_311_);
lean_dec(v_l_x27_x27_308_);
lean_dec(v_r_x27_307_);
lean_dec(v_l_x27_306_);
lean_dec(v_v_x27_305_);
lean_dec(v_k_x27_304_);
lean_dec(v_szl_303_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___redArg(lean_object* v_x_313_, lean_object* v_h__1_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = lean_apply_3(v_h__1_314_, v_x_313_, lean_box(0), lean_box(0));
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(lean_object* v_00_u03b1_316_, lean_object* v_00_u03b2_317_, lean_object* v_r_x27_318_, lean_object* v_szr_319_, lean_object* v_k_x27_x27_320_, lean_object* v_v_x27_x27_321_, lean_object* v_l_x27_x27_322_, lean_object* v_r_x27_x27_323_, lean_object* v_motive_324_, lean_object* v_x_325_, lean_object* v_h__1_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_apply_3(v_h__1_326_, v_x_325_, lean_box(0), lean_box(0));
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___boxed(lean_object* v_00_u03b1_328_, lean_object* v_00_u03b2_329_, lean_object* v_r_x27_330_, lean_object* v_szr_331_, lean_object* v_k_x27_x27_332_, lean_object* v_v_x27_x27_333_, lean_object* v_l_x27_x27_334_, lean_object* v_r_x27_x27_335_, lean_object* v_motive_336_, lean_object* v_x_337_, lean_object* v_h__1_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(v_00_u03b1_328_, v_00_u03b2_329_, v_r_x27_330_, v_szr_331_, v_k_x27_x27_332_, v_v_x27_x27_333_, v_l_x27_x27_334_, v_r_x27_x27_335_, v_motive_336_, v_x_337_, v_h__1_338_);
lean_dec(v_r_x27_x27_335_);
lean_dec(v_l_x27_x27_334_);
lean_dec(v_v_x27_x27_333_);
lean_dec(v_k_x27_x27_332_);
lean_dec(v_szr_331_);
lean_dec(v_r_x27_330_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(lean_object* v_l_340_, lean_object* v_h__1_341_, lean_object* v_h__2_342_){
_start:
{
if (lean_obj_tag(v_l_340_) == 0)
{
lean_object* v_size_343_; lean_object* v_k_344_; lean_object* v_v_345_; lean_object* v_l_346_; lean_object* v_r_347_; lean_object* v___x_348_; 
lean_dec(v_h__1_341_);
v_size_343_ = lean_ctor_get(v_l_340_, 0);
lean_inc(v_size_343_);
v_k_344_ = lean_ctor_get(v_l_340_, 1);
lean_inc(v_k_344_);
v_v_345_ = lean_ctor_get(v_l_340_, 2);
lean_inc(v_v_345_);
v_l_346_ = lean_ctor_get(v_l_340_, 3);
lean_inc(v_l_346_);
v_r_347_ = lean_ctor_get(v_l_340_, 4);
lean_inc(v_r_347_);
lean_dec_ref_known(v_l_340_, 5);
v___x_348_ = lean_apply_6(v_h__2_342_, v_size_343_, v_k_344_, v_v_345_, v_l_346_, v_r_347_, lean_box(0));
return v___x_348_;
}
else
{
lean_object* v___x_349_; 
lean_dec(v_h__2_342_);
v___x_349_ = lean_apply_1(v_h__1_341_, lean_box(0));
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_motive_352_, lean_object* v_l_353_, lean_object* v_hl_354_, lean_object* v_h__1_355_, lean_object* v_h__2_356_){
_start:
{
if (lean_obj_tag(v_l_353_) == 0)
{
lean_object* v_size_357_; lean_object* v_k_358_; lean_object* v_v_359_; lean_object* v_l_360_; lean_object* v_r_361_; lean_object* v___x_362_; 
lean_dec(v_h__1_355_);
v_size_357_ = lean_ctor_get(v_l_353_, 0);
lean_inc(v_size_357_);
v_k_358_ = lean_ctor_get(v_l_353_, 1);
lean_inc(v_k_358_);
v_v_359_ = lean_ctor_get(v_l_353_, 2);
lean_inc(v_v_359_);
v_l_360_ = lean_ctor_get(v_l_353_, 3);
lean_inc(v_l_360_);
v_r_361_ = lean_ctor_get(v_l_353_, 4);
lean_inc(v_r_361_);
lean_dec_ref_known(v_l_353_, 5);
v___x_362_ = lean_apply_6(v_h__2_356_, v_size_357_, v_k_358_, v_v_359_, v_l_360_, v_r_361_, lean_box(0));
return v___x_362_;
}
else
{
lean_object* v___x_363_; 
lean_dec(v_h__2_356_);
v___x_363_ = lean_apply_1(v_h__1_355_, lean_box(0));
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object* v_x_364_, lean_object* v_h__1_365_, lean_object* v_h__2_366_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; 
lean_dec(v_h__2_366_);
v___x_367_ = lean_box(0);
v___x_368_ = lean_apply_1(v_h__1_365_, v___x_367_);
return v___x_368_;
}
else
{
lean_object* v_val_369_; lean_object* v_fst_370_; lean_object* v_snd_371_; lean_object* v___x_372_; 
lean_dec(v_h__1_365_);
v_val_369_ = lean_ctor_get(v_x_364_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v_x_364_, 1);
v_fst_370_ = lean_ctor_get(v_val_369_, 0);
lean_inc(v_fst_370_);
v_snd_371_ = lean_ctor_get(v_val_369_, 1);
lean_inc(v_snd_371_);
lean_dec(v_val_369_);
v___x_372_ = lean_apply_2(v_h__2_366_, v_fst_370_, v_snd_371_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* v_00_u03b1_373_, lean_object* v_00_u03b2_374_, lean_object* v_motive_375_, lean_object* v_x_376_, lean_object* v_h__1_377_, lean_object* v_h__2_378_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec(v_h__2_378_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_apply_1(v_h__1_377_, v___x_379_);
return v___x_380_;
}
else
{
lean_object* v_val_381_; lean_object* v_fst_382_; lean_object* v_snd_383_; lean_object* v___x_384_; 
lean_dec(v_h__1_377_);
v_val_381_ = lean_ctor_get(v_x_376_, 0);
lean_inc(v_val_381_);
lean_dec_ref_known(v_x_376_, 1);
v_fst_382_ = lean_ctor_get(v_val_381_, 0);
lean_inc(v_fst_382_);
v_snd_383_ = lean_ctor_get(v_val_381_, 1);
lean_inc(v_snd_383_);
lean_dec(v_val_381_);
v___x_384_ = lean_apply_2(v_h__2_378_, v_fst_382_, v_snd_383_);
return v___x_384_;
}
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(uint8_t v_x_385_, lean_object* v_h__1_386_, lean_object* v_h__2_387_, lean_object* v_h__3_388_){
_start:
{
switch(v_x_385_)
{
case 0:
{
lean_object* v___x_389_; 
lean_dec(v_h__3_388_);
lean_dec(v_h__2_387_);
v___x_389_ = lean_apply_1(v_h__1_386_, lean_box(0));
return v___x_389_;
}
case 1:
{
lean_object* v___x_390_; 
lean_dec(v_h__3_388_);
lean_dec(v_h__1_386_);
v___x_390_ = lean_apply_1(v_h__2_387_, lean_box(0));
return v___x_390_;
}
default: 
{
lean_object* v___x_391_; 
lean_dec(v_h__2_387_);
lean_dec(v_h__1_386_);
v___x_391_ = lean_apply_1(v_h__3_388_, lean_box(0));
return v___x_391_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_385_ = stack[0].m_num;
lean_object* v_h__1_386_ = stack[1].m_obj;
lean_object* v_h__2_387_ = stack[2].m_obj;
lean_object* v_h__3_388_ = stack[3].m_obj;
lean_object* v_res_392_;
v_res_392_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_385_, v_h__1_386_, v_h__2_387_, v_h__3_388_);
stack->m_obj
 = v_res_392_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(lean_object* v_x_393_, lean_object* v_h__1_394_, lean_object* v_h__2_395_, lean_object* v_h__3_396_){
_start:
{
uint8_t v_x_33__boxed_397_; lean_object* v_res_398_; 
v_x_33__boxed_397_ = lean_unbox(v_x_393_);
v_res_398_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_33__boxed_397_, v_h__1_394_, v_h__2_395_, v_h__3_396_);
return v_res_398_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object* v_motive_399_, uint8_t v_x_400_, lean_object* v_h__1_401_, lean_object* v_h__2_402_, lean_object* v_h__3_403_){
_start:
{
switch(v_x_400_)
{
case 0:
{
lean_object* v___x_404_; 
lean_dec(v_h__3_403_);
lean_dec(v_h__2_402_);
v___x_404_ = lean_apply_1(v_h__1_401_, lean_box(0));
return v___x_404_;
}
case 1:
{
lean_object* v___x_405_; 
lean_dec(v_h__3_403_);
lean_dec(v_h__1_401_);
v___x_405_ = lean_apply_1(v_h__2_402_, lean_box(0));
return v___x_405_;
}
default: 
{
lean_object* v___x_406_; 
lean_dec(v_h__2_402_);
lean_dec(v_h__1_401_);
v___x_406_ = lean_apply_1(v_h__3_403_, lean_box(0));
return v___x_406_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_400_ = stack[1].m_num;
lean_object* v_h__1_401_ = stack[2].m_obj;
lean_object* v_h__2_402_ = stack[3].m_obj;
lean_object* v_h__3_403_ = stack[4].m_obj;
lean_object* v_res_407_;
v_res_407_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_box(0), v_x_400_, v_h__1_401_, v_h__2_402_, v_h__3_403_);
stack->m_obj
 = v_res_407_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(lean_object* v_motive_408_, lean_object* v_x_409_, lean_object* v_h__1_410_, lean_object* v_h__2_411_, lean_object* v_h__3_412_){
_start:
{
uint8_t v_x_47__boxed_413_; lean_object* v_res_414_; 
v_x_47__boxed_413_ = lean_unbox(v_x_409_);
v_res_414_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(v_motive_408_, v_x_47__boxed_413_, v_h__1_410_, v_h__2_411_, v_h__3_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(lean_object* v_x_415_, lean_object* v_h__1_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = lean_apply_4(v_h__1_416_, v_x_415_, lean_box(0), lean_box(0), lean_box(0));
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object* v_00_u03b1_418_, lean_object* v_00_u03b2_419_, lean_object* v_l_420_, lean_object* v_motive_421_, lean_object* v_x_422_, lean_object* v_h__1_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = lean_apply_4(v_h__1_423_, v_x_422_, lean_box(0), lean_box(0), lean_box(0));
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(lean_object* v_00_u03b1_425_, lean_object* v_00_u03b2_426_, lean_object* v_l_427_, lean_object* v_motive_428_, lean_object* v_x_429_, lean_object* v_h__1_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_425_, v_00_u03b2_426_, v_l_427_, v_motive_428_, v_x_429_, v_h__1_430_);
lean_dec(v_l_427_);
return v_res_431_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(uint8_t v_x_432_, lean_object* v_h__1_433_, lean_object* v_h__2_434_, lean_object* v_h__3_435_){
_start:
{
switch(v_x_432_)
{
case 0:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec(v_h__3_435_);
lean_dec(v_h__2_434_);
v___x_436_ = lean_box(0);
v___x_437_ = lean_apply_1(v_h__1_433_, v___x_436_);
return v___x_437_;
}
case 1:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v_h__2_434_);
lean_dec(v_h__1_433_);
v___x_438_ = lean_box(0);
v___x_439_ = lean_apply_1(v_h__3_435_, v___x_438_);
return v___x_439_;
}
default: 
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec(v_h__3_435_);
lean_dec(v_h__1_433_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_apply_1(v_h__2_434_, v___x_440_);
return v___x_441_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_432_ = stack[0].m_num;
lean_object* v_h__1_433_ = stack[1].m_obj;
lean_object* v_h__2_434_ = stack[2].m_obj;
lean_object* v_h__3_435_ = stack[3].m_obj;
lean_object* v_res_442_;
v_res_442_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_432_, v_h__1_433_, v_h__2_434_, v_h__3_435_);
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(lean_object* v_x_443_, lean_object* v_h__1_444_, lean_object* v_h__2_445_, lean_object* v_h__3_446_){
_start:
{
uint8_t v_x_33__boxed_447_; lean_object* v_res_448_; 
v_x_33__boxed_447_ = lean_unbox(v_x_443_);
v_res_448_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_33__boxed_447_, v_h__1_444_, v_h__2_445_, v_h__3_446_);
return v_res_448_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object* v_motive_449_, uint8_t v_x_450_, lean_object* v_h__1_451_, lean_object* v_h__2_452_, lean_object* v_h__3_453_){
_start:
{
switch(v_x_450_)
{
case 0:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v_h__3_453_);
lean_dec(v_h__2_452_);
v___x_454_ = lean_box(0);
v___x_455_ = lean_apply_1(v_h__1_451_, v___x_454_);
return v___x_455_;
}
case 1:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v_h__2_452_);
lean_dec(v_h__1_451_);
v___x_456_ = lean_box(0);
v___x_457_ = lean_apply_1(v_h__3_453_, v___x_456_);
return v___x_457_;
}
default: 
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v_h__3_453_);
lean_dec(v_h__1_451_);
v___x_458_ = lean_box(0);
v___x_459_ = lean_apply_1(v_h__2_452_, v___x_458_);
return v___x_459_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_450_ = stack[1].m_num;
lean_object* v_h__1_451_ = stack[2].m_obj;
lean_object* v_h__2_452_ = stack[3].m_obj;
lean_object* v_h__3_453_ = stack[4].m_obj;
lean_object* v_res_460_;
v_res_460_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_box(0), v_x_450_, v_h__1_451_, v_h__2_452_, v_h__3_453_);
stack->m_obj
 = v_res_460_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(lean_object* v_motive_461_, lean_object* v_x_462_, lean_object* v_h__1_463_, lean_object* v_h__2_464_, lean_object* v_h__3_465_){
_start:
{
uint8_t v_x_56__boxed_466_; lean_object* v_res_467_; 
v_x_56__boxed_466_ = lean_unbox(v_x_462_);
v_res_467_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_461_, v_x_56__boxed_466_, v_h__1_463_, v_h__2_464_, v_h__3_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object* v_x_468_, lean_object* v_h__1_469_, lean_object* v_h__2_470_){
_start:
{
if (lean_obj_tag(v_x_468_) == 0)
{
lean_object* v___x_471_; 
lean_dec(v_h__2_470_);
v___x_471_ = lean_apply_1(v_h__1_469_, lean_box(0));
return v___x_471_;
}
else
{
lean_object* v_val_472_; lean_object* v___x_473_; 
lean_dec(v_h__1_469_);
v_val_472_ = lean_ctor_get(v_x_468_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v_x_468_, 1);
v___x_473_ = lean_apply_2(v_h__2_470_, v_val_472_, lean_box(0));
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_motive_476_, lean_object* v_x_477_, lean_object* v_h__1_478_, lean_object* v_h__2_479_){
_start:
{
if (lean_obj_tag(v_x_477_) == 0)
{
lean_object* v___x_480_; 
lean_dec(v_h__2_479_);
v___x_480_ = lean_apply_1(v_h__1_478_, lean_box(0));
return v___x_480_;
}
else
{
lean_object* v_val_481_; lean_object* v___x_482_; 
lean_dec(v_h__1_478_);
v_val_481_ = lean_ctor_get(v_x_477_, 0);
lean_inc(v_val_481_);
lean_dec_ref_known(v_x_477_, 1);
v___x_482_ = lean_apply_2(v_h__2_479_, v_val_481_, lean_box(0));
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_483_, lean_object* v_h__1_484_, lean_object* v_h__2_485_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec(v_h__2_485_);
v___x_486_ = lean_box(0);
v___x_487_ = lean_apply_1(v_h__1_484_, v___x_486_);
return v___x_487_;
}
else
{
lean_object* v_val_488_; lean_object* v___x_489_; 
lean_dec(v_h__1_484_);
v_val_488_ = lean_ctor_get(v_x_483_, 0);
lean_inc(v_val_488_);
lean_dec_ref_known(v_x_483_, 1);
v___x_489_ = lean_apply_1(v_h__2_485_, v_val_488_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_490_, lean_object* v_00_u03b2_491_, lean_object* v_motive_492_, lean_object* v_x_493_, lean_object* v_h__1_494_, lean_object* v_h__2_495_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v_h__2_495_);
v___x_496_ = lean_box(0);
v___x_497_ = lean_apply_1(v_h__1_494_, v___x_496_);
return v___x_497_;
}
else
{
lean_object* v_val_498_; lean_object* v___x_499_; 
lean_dec(v_h__1_494_);
v_val_498_ = lean_ctor_get(v_x_493_, 0);
lean_inc(v_val_498_);
lean_dec_ref_known(v_x_493_, 1);
v___x_499_ = lean_apply_1(v_h__2_495_, v_val_498_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object* v_x_500_, lean_object* v_h__1_501_, lean_object* v_h__2_502_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v_h__2_502_);
v___x_503_ = lean_box(0);
v___x_504_ = lean_apply_1(v_h__1_501_, v___x_503_);
return v___x_504_;
}
else
{
lean_object* v_val_505_; lean_object* v___x_506_; 
lean_dec(v_h__1_501_);
v_val_505_ = lean_ctor_get(v_x_500_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v_x_500_, 1);
v___x_506_ = lean_apply_1(v_h__2_502_, v_val_505_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_507_, lean_object* v_00_u03b2_508_, lean_object* v_motive_509_, lean_object* v_x_510_, lean_object* v_h__1_511_, lean_object* v_h__2_512_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v_h__2_512_);
v___x_513_ = lean_box(0);
v___x_514_ = lean_apply_1(v_h__1_511_, v___x_513_);
return v___x_514_;
}
else
{
lean_object* v_val_515_; lean_object* v___x_516_; 
lean_dec(v_h__1_511_);
v_val_515_ = lean_ctor_get(v_x_510_, 0);
lean_inc(v_val_515_);
lean_dec_ref_known(v_x_510_, 1);
v___x_516_ = lean_apply_1(v_h__2_512_, v_val_515_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___redArg(lean_object* v_x_517_, lean_object* v_h__1_518_, lean_object* v_h__2_519_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_h__2_519_);
v___x_520_ = lean_box(0);
v___x_521_ = lean_apply_1(v_h__1_518_, v___x_520_);
return v___x_521_;
}
else
{
lean_object* v_val_522_; lean_object* v___x_523_; 
lean_dec(v_h__1_518_);
v_val_522_ = lean_ctor_get(v_x_517_, 0);
lean_inc(v_val_522_);
lean_dec_ref_known(v_x_517_, 1);
v___x_523_ = lean_apply_1(v_h__2_519_, v_val_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(lean_object* v_00_u03b1_524_, lean_object* v_00_u03b2_525_, lean_object* v_k_526_, lean_object* v_motive_527_, lean_object* v_x_528_, lean_object* v_h__1_529_, lean_object* v_h__2_530_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v_h__2_530_);
v___x_531_ = lean_box(0);
v___x_532_ = lean_apply_1(v_h__1_529_, v___x_531_);
return v___x_532_;
}
else
{
lean_object* v_val_533_; lean_object* v___x_534_; 
lean_dec(v_h__1_529_);
v_val_533_ = lean_ctor_get(v_x_528_, 0);
lean_inc(v_val_533_);
lean_dec_ref_known(v_x_528_, 1);
v___x_534_ = lean_apply_1(v_h__2_530_, v_val_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___boxed(lean_object* v_00_u03b1_535_, lean_object* v_00_u03b2_536_, lean_object* v_k_537_, lean_object* v_motive_538_, lean_object* v_x_539_, lean_object* v_h__1_540_, lean_object* v_h__2_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(v_00_u03b1_535_, v_00_u03b2_536_, v_k_537_, v_motive_538_, v_x_539_, v_h__1_540_, v_h__2_541_);
lean_dec(v_k_537_);
return v_res_542_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(uint8_t v_x_543_, lean_object* v_h__1_544_, lean_object* v_h__2_545_){
_start:
{
if (v_x_543_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec(v_h__2_545_);
v___x_546_ = lean_box(0);
v___x_547_ = lean_apply_1(v_h__1_544_, v___x_546_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v_h__1_544_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_apply_1(v_h__2_545_, v___x_548_);
return v___x_549_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_543_ = stack[0].m_num;
lean_object* v_h__1_544_ = stack[1].m_obj;
lean_object* v_h__2_545_ = stack[2].m_obj;
lean_object* v_res_550_;
v_res_550_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(v_x_543_, v_h__1_544_, v_h__2_545_);
stack->m_obj
 = v_res_550_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg___boxed(lean_object* v_x_551_, lean_object* v_h__1_552_, lean_object* v_h__2_553_){
_start:
{
uint8_t v_x_24__boxed_554_; lean_object* v_res_555_; 
v_x_24__boxed_554_ = lean_unbox(v_x_551_);
v_res_555_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(v_x_24__boxed_554_, v_h__1_552_, v_h__2_553_);
return v_res_555_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(lean_object* v_motive_556_, uint8_t v_x_557_, lean_object* v_h__1_558_, lean_object* v_h__2_559_){
_start:
{
if (v_x_557_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec(v_h__2_559_);
v___x_560_ = lean_box(0);
v___x_561_ = lean_apply_1(v_h__1_558_, v___x_560_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec(v_h__1_558_);
v___x_562_ = lean_box(0);
v___x_563_ = lean_apply_1(v_h__2_559_, v___x_562_);
return v___x_563_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_557_ = stack[1].m_num;
lean_object* v_h__1_558_ = stack[2].m_obj;
lean_object* v_h__2_559_ = stack[3].m_obj;
lean_object* v_res_564_;
v_res_564_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(lean_box(0), v_x_557_, v_h__1_558_, v_h__2_559_);
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___boxed(lean_object* v_motive_565_, lean_object* v_x_566_, lean_object* v_h__1_567_, lean_object* v_h__2_568_){
_start:
{
uint8_t v_x_41__boxed_569_; lean_object* v_res_570_; 
v_x_41__boxed_569_ = lean_unbox(v_x_566_);
v_res_570_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(v_motive_565_, v_x_41__boxed_569_, v_h__1_567_, v_h__2_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___redArg(lean_object* v_v_x3f_571_, lean_object* v_h__1_572_, lean_object* v_h__2_573_){
_start:
{
if (lean_obj_tag(v_v_x3f_571_) == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v_h__2_573_);
v___x_574_ = lean_box(0);
v___x_575_ = lean_apply_1(v_h__1_572_, v___x_574_);
return v___x_575_;
}
else
{
lean_object* v_val_576_; lean_object* v___x_577_; 
lean_dec(v_h__1_572_);
v_val_576_ = lean_ctor_get(v_v_x3f_571_, 0);
lean_inc(v_val_576_);
lean_dec_ref_known(v_v_x3f_571_, 1);
v___x_577_ = lean_apply_1(v_h__2_573_, v_val_576_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_k_580_, lean_object* v_motive_581_, lean_object* v_v_x3f_582_, lean_object* v_h__1_583_, lean_object* v_h__2_584_){
_start:
{
if (lean_obj_tag(v_v_x3f_582_) == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec(v_h__2_584_);
v___x_585_ = lean_box(0);
v___x_586_ = lean_apply_1(v_h__1_583_, v___x_585_);
return v___x_586_;
}
else
{
lean_object* v_val_587_; lean_object* v___x_588_; 
lean_dec(v_h__1_583_);
v_val_587_ = lean_ctor_get(v_v_x3f_582_, 0);
lean_inc(v_val_587_);
lean_dec_ref_known(v_v_x3f_582_, 1);
v___x_588_ = lean_apply_1(v_h__2_584_, v_val_587_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___boxed(lean_object* v_00_u03b1_589_, lean_object* v_00_u03b2_590_, lean_object* v_k_591_, lean_object* v_motive_592_, lean_object* v_v_x3f_593_, lean_object* v_h__1_594_, lean_object* v_h__2_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(v_00_u03b1_589_, v_00_u03b2_590_, v_k_591_, v_motive_592_, v_v_x3f_593_, v_h__1_594_, v_h__2_595_);
lean_dec(v_k_591_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_597_, lean_object* v_h__1_598_, lean_object* v_h__2_599_){
_start:
{
if (lean_obj_tag(v_x_597_) == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v_h__2_599_);
v___x_600_ = lean_box(0);
v___x_601_ = lean_apply_1(v_h__1_598_, v___x_600_);
return v___x_601_;
}
else
{
lean_object* v_val_602_; lean_object* v___x_603_; 
lean_dec(v_h__1_598_);
v_val_602_ = lean_ctor_get(v_x_597_, 0);
lean_inc(v_val_602_);
lean_dec_ref_known(v_x_597_, 1);
v___x_603_ = lean_apply_1(v_h__2_599_, v_val_602_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b1_604_, lean_object* v_00_u03b2_605_, lean_object* v_k_606_, lean_object* v_motive_607_, lean_object* v_x_608_, lean_object* v_h__1_609_, lean_object* v_h__2_610_){
_start:
{
if (lean_obj_tag(v_x_608_) == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec(v_h__2_610_);
v___x_611_ = lean_box(0);
v___x_612_ = lean_apply_1(v_h__1_609_, v___x_611_);
return v___x_612_;
}
else
{
lean_object* v_val_613_; lean_object* v___x_614_; 
lean_dec(v_h__1_609_);
v_val_613_ = lean_ctor_get(v_x_608_, 0);
lean_inc(v_val_613_);
lean_dec_ref_known(v_x_608_, 1);
v___x_614_ = lean_apply_1(v_h__2_610_, v_val_613_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object* v_00_u03b1_615_, lean_object* v_00_u03b2_616_, lean_object* v_k_617_, lean_object* v_motive_618_, lean_object* v_x_619_, lean_object* v_h__1_620_, lean_object* v_h__2_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_615_, v_00_u03b2_616_, v_k_617_, v_motive_618_, v_x_619_, v_h__1_620_, v_h__2_621_);
lean_dec(v_k_617_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter___redArg(lean_object* v_x_623_, lean_object* v_h__1_624_, lean_object* v_h__2_625_){
_start:
{
if (lean_obj_tag(v_x_623_) == 0)
{
lean_object* v___x_626_; 
lean_dec(v_h__2_625_);
v___x_626_ = lean_apply_1(v_h__1_624_, lean_box(0));
return v___x_626_;
}
else
{
lean_object* v_val_627_; lean_object* v_fst_628_; lean_object* v_snd_629_; lean_object* v___x_630_; 
lean_dec(v_h__1_624_);
v_val_627_ = lean_ctor_get(v_x_623_, 0);
lean_inc(v_val_627_);
lean_dec_ref_known(v_x_623_, 1);
v_fst_628_ = lean_ctor_get(v_val_627_, 0);
lean_inc(v_fst_628_);
v_snd_629_ = lean_ctor_get(v_val_627_, 1);
lean_inc(v_snd_629_);
lean_dec(v_val_627_);
v___x_630_ = lean_apply_3(v_h__2_625_, v_fst_628_, v_snd_629_, lean_box(0));
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter(lean_object* v_00_u03b1_631_, lean_object* v_00_u03b2_632_, lean_object* v_motive_633_, lean_object* v_x_634_, lean_object* v_h__1_635_, lean_object* v_h__2_636_){
_start:
{
if (lean_obj_tag(v_x_634_) == 0)
{
lean_object* v___x_637_; 
lean_dec(v_h__2_636_);
v___x_637_ = lean_apply_1(v_h__1_635_, lean_box(0));
return v___x_637_;
}
else
{
lean_object* v_val_638_; lean_object* v_fst_639_; lean_object* v_snd_640_; lean_object* v___x_641_; 
lean_dec(v_h__1_635_);
v_val_638_ = lean_ctor_get(v_x_634_, 0);
lean_inc(v_val_638_);
lean_dec_ref_known(v_x_634_, 1);
v_fst_639_ = lean_ctor_get(v_val_638_, 0);
lean_inc(v_fst_639_);
v_snd_640_ = lean_ctor_get(v_val_638_, 1);
lean_inc(v_snd_640_);
lean_dec(v_val_638_);
v___x_641_ = lean_apply_3(v_h__2_636_, v_fst_639_, v_snd_640_, lean_box(0));
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___redArg(lean_object* v_x_642_, lean_object* v_h__1_643_, lean_object* v_h__2_644_){
_start:
{
if (lean_obj_tag(v_x_642_) == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec(v_h__2_644_);
v___x_645_ = lean_box(0);
v___x_646_ = lean_apply_1(v_h__1_643_, v___x_645_);
return v___x_646_;
}
else
{
lean_object* v_val_647_; lean_object* v___x_648_; 
lean_dec(v_h__1_643_);
v_val_647_ = lean_ctor_get(v_x_642_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v_x_642_, 1);
v___x_648_ = lean_apply_1(v_h__2_644_, v_val_647_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_k_651_, lean_object* v_motive_652_, lean_object* v_x_653_, lean_object* v_h__1_654_, lean_object* v_h__2_655_){
_start:
{
if (lean_obj_tag(v_x_653_) == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec(v_h__2_655_);
v___x_656_ = lean_box(0);
v___x_657_ = lean_apply_1(v_h__1_654_, v___x_656_);
return v___x_657_;
}
else
{
lean_object* v_val_658_; lean_object* v___x_659_; 
lean_dec(v_h__1_654_);
v_val_658_ = lean_ctor_get(v_x_653_, 0);
lean_inc(v_val_658_);
lean_dec_ref_known(v_x_653_, 1);
v___x_659_ = lean_apply_1(v_h__2_655_, v_val_658_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object* v_00_u03b1_660_, lean_object* v_00_u03b2_661_, lean_object* v_k_662_, lean_object* v_motive_663_, lean_object* v_x_664_, lean_object* v_h__1_665_, lean_object* v_h__2_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_660_, v_00_u03b2_661_, v_k_662_, v_motive_663_, v_x_664_, v_h__1_665_, v_h__2_666_);
lean_dec(v_k_662_);
return v_res_667_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(uint8_t v_x_668_, lean_object* v_h__1_669_, lean_object* v_h__2_670_, lean_object* v_h__3_671_){
_start:
{
switch(v_x_668_)
{
case 0:
{
lean_object* v___x_672_; 
lean_dec(v_h__3_671_);
lean_dec(v_h__2_670_);
v___x_672_ = lean_apply_1(v_h__1_669_, lean_box(0));
return v___x_672_;
}
case 1:
{
lean_object* v___x_673_; 
lean_dec(v_h__2_670_);
lean_dec(v_h__1_669_);
v___x_673_ = lean_apply_1(v_h__3_671_, lean_box(0));
return v___x_673_;
}
default: 
{
lean_object* v___x_674_; 
lean_dec(v_h__3_671_);
lean_dec(v_h__1_669_);
v___x_674_ = lean_apply_1(v_h__2_670_, lean_box(0));
return v___x_674_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_668_ = stack[0].m_num;
lean_object* v_h__1_669_ = stack[1].m_obj;
lean_object* v_h__2_670_ = stack[2].m_obj;
lean_object* v_h__3_671_ = stack[3].m_obj;
lean_object* v_res_675_;
v_res_675_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(v_x_668_, v_h__1_669_, v_h__2_670_, v_h__3_671_);
stack->m_obj
 = v_res_675_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg___boxed(lean_object* v_x_676_, lean_object* v_h__1_677_, lean_object* v_h__2_678_, lean_object* v_h__3_679_){
_start:
{
uint8_t v_x_33__boxed_680_; lean_object* v_res_681_; 
v_x_33__boxed_680_ = lean_unbox(v_x_676_);
v_res_681_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(v_x_33__boxed_680_, v_h__1_677_, v_h__2_678_, v_h__3_679_);
return v_res_681_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(lean_object* v_motive_682_, uint8_t v_x_683_, lean_object* v_h__1_684_, lean_object* v_h__2_685_, lean_object* v_h__3_686_){
_start:
{
switch(v_x_683_)
{
case 0:
{
lean_object* v___x_687_; 
lean_dec(v_h__3_686_);
lean_dec(v_h__2_685_);
v___x_687_ = lean_apply_1(v_h__1_684_, lean_box(0));
return v___x_687_;
}
case 1:
{
lean_object* v___x_688_; 
lean_dec(v_h__2_685_);
lean_dec(v_h__1_684_);
v___x_688_ = lean_apply_1(v_h__3_686_, lean_box(0));
return v___x_688_;
}
default: 
{
lean_object* v___x_689_; 
lean_dec(v_h__3_686_);
lean_dec(v_h__1_684_);
v___x_689_ = lean_apply_1(v_h__2_685_, lean_box(0));
return v___x_689_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_683_ = stack[1].m_num;
lean_object* v_h__1_684_ = stack[2].m_obj;
lean_object* v_h__2_685_ = stack[3].m_obj;
lean_object* v_h__3_686_ = stack[4].m_obj;
lean_object* v_res_690_;
v_res_690_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(lean_box(0), v_x_683_, v_h__1_684_, v_h__2_685_, v_h__3_686_);
stack->m_obj
 = v_res_690_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___boxed(lean_object* v_motive_691_, lean_object* v_x_692_, lean_object* v_h__1_693_, lean_object* v_h__2_694_, lean_object* v_h__3_695_){
_start:
{
uint8_t v_x_47__boxed_696_; lean_object* v_res_697_; 
v_x_47__boxed_696_ = lean_unbox(v_x_692_);
v_res_697_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(v_motive_691_, v_x_47__boxed_696_, v_h__1_693_, v_h__2_694_, v_h__3_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter___redArg(lean_object* v_____do__lift_698_, lean_object* v_h__1_699_, lean_object* v_h__2_700_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter(lean_object* v_00_u03b4_705_, lean_object* v_motive_706_, lean_object* v_____do__lift_707_, lean_object* v_h__1_708_, lean_object* v_h__2_709_){
_start:
{
if (lean_obj_tag(v_____do__lift_707_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; 
lean_dec(v_h__2_709_);
v_a_710_ = lean_ctor_get(v_____do__lift_707_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v_____do__lift_707_, 1);
v___x_711_ = lean_apply_1(v_h__1_708_, v_a_710_);
return v___x_711_;
}
else
{
lean_object* v_a_712_; lean_object* v___x_713_; 
lean_dec(v_h__1_708_);
v_a_712_ = lean_ctor_get(v_____do__lift_707_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v_____do__lift_707_, 1);
v___x_713_ = lean_apply_1(v_h__2_709_, v_a_712_);
return v___x_713_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter___redArg(lean_object* v_x_714_, lean_object* v_h__1_715_, lean_object* v_h__2_716_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter(lean_object* v_00_u03b4_721_, lean_object* v_motive_722_, lean_object* v_x_723_, lean_object* v_h__1_724_, lean_object* v_h__2_725_){
_start:
{
if (lean_obj_tag(v_x_723_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; 
lean_dec(v_h__1_724_);
v_a_726_ = lean_ctor_get(v_x_723_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v_x_723_, 1);
v___x_727_ = lean_apply_1(v_h__2_725_, v_a_726_);
return v___x_727_;
}
else
{
lean_object* v_a_728_; lean_object* v___x_729_; 
lean_dec(v_h__2_725_);
v_a_728_ = lean_ctor_get(v_x_723_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v_x_723_, 1);
v___x_729_ = lean_apply_1(v_h__1_724_, v_a_728_);
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_730_, lean_object* v_h__1_731_, lean_object* v_h__2_732_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_737_, lean_object* v_motive_738_, lean_object* v_b_739_, lean_object* v_h__1_740_, lean_object* v_h__2_741_){
_start:
{
if (lean_obj_tag(v_b_739_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; 
lean_dec(v_h__1_740_);
v_a_742_ = lean_ctor_get(v_b_739_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v_b_739_, 1);
v___x_743_ = lean_apply_1(v_h__2_741_, v_a_742_);
return v___x_743_;
}
else
{
lean_object* v_a_744_; lean_object* v___x_745_; 
lean_dec(v_h__2_741_);
v_a_744_ = lean_ctor_get(v_b_739_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v_b_739_, 1);
v___x_745_ = lean_apply_1(v_h__1_740_, v_a_744_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_746_, lean_object* v_h__1_747_, lean_object* v_h__2_748_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b2_753_, lean_object* v_motive_754_, lean_object* v_x_755_, lean_object* v_h__1_756_, lean_object* v_h__2_757_){
_start:
{
if (lean_obj_tag(v_x_755_) == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec(v_h__2_757_);
v___x_758_ = lean_box(0);
v___x_759_ = lean_apply_1(v_h__1_756_, v___x_758_);
return v___x_759_;
}
else
{
lean_object* v_val_760_; lean_object* v___x_761_; 
lean_dec(v_h__1_756_);
v_val_760_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_val_760_);
lean_dec_ref_known(v_x_755_, 1);
v___x_761_ = lean_apply_1(v_h__2_757_, v_val_760_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter___redArg(lean_object* v_x_762_, lean_object* v_h__1_763_, lean_object* v_h__2_764_){
_start:
{
if (lean_obj_tag(v_x_762_) == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec(v_h__2_764_);
v___x_765_ = lean_box(0);
v___x_766_ = lean_apply_1(v_h__1_763_, v___x_765_);
return v___x_766_;
}
else
{
lean_object* v_val_767_; lean_object* v_fst_768_; lean_object* v_snd_769_; lean_object* v___x_770_; 
lean_dec(v_h__1_763_);
v_val_767_ = lean_ctor_get(v_x_762_, 0);
lean_inc(v_val_767_);
lean_dec_ref_known(v_x_762_, 1);
v_fst_768_ = lean_ctor_get(v_val_767_, 0);
lean_inc(v_fst_768_);
v_snd_769_ = lean_ctor_get(v_val_767_, 1);
lean_inc(v_snd_769_);
lean_dec(v_val_767_);
v___x_770_ = lean_apply_2(v_h__2_764_, v_fst_768_, v_snd_769_);
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter(lean_object* v_00_u03b1_771_, lean_object* v_00_u03b2_772_, lean_object* v_motive_773_, lean_object* v_x_774_, lean_object* v_h__1_775_, lean_object* v_h__2_776_){
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
lean_object* v_val_779_; lean_object* v_fst_780_; lean_object* v_snd_781_; lean_object* v___x_782_; 
lean_dec(v_h__1_775_);
v_val_779_ = lean_ctor_get(v_x_774_, 0);
lean_inc(v_val_779_);
lean_dec_ref_known(v_x_774_, 1);
v_fst_780_ = lean_ctor_get(v_val_779_, 0);
lean_inc(v_fst_780_);
v_snd_781_ = lean_ctor_get(v_val_779_, 1);
lean_inc(v_snd_781_);
lean_dec(v_val_779_);
v___x_782_ = lean_apply_2(v_h__2_776_, v_fst_780_, v_snd_781_);
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(lean_object* v_x_783_, lean_object* v_h__1_784_, lean_object* v_h__2_785_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object* v_00_u03b2_790_, lean_object* v_motive_791_, lean_object* v_x_792_, lean_object* v_h__1_793_, lean_object* v_h__2_794_){
_start:
{
if (lean_obj_tag(v_x_792_) == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec(v_h__2_794_);
v___x_795_ = lean_box(0);
v___x_796_ = lean_apply_1(v_h__1_793_, v___x_795_);
return v___x_796_;
}
else
{
lean_object* v_val_797_; lean_object* v___x_798_; 
lean_dec(v_h__1_793_);
v_val_797_ = lean_ctor_get(v_x_792_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v_x_792_, 1);
v___x_798_ = lean_apply_1(v_h__2_794_, v_val_797_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___redArg(lean_object* v_x_799_, lean_object* v_h__1_800_, lean_object* v_h__2_801_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter(lean_object* v_00_u03b2_806_, lean_object* v_motive_807_, lean_object* v_x_808_, lean_object* v_h__1_809_, lean_object* v_h__2_810_){
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
lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t v_x_815_, lean_object* v_h__1_816_, lean_object* v_h__2_817_, lean_object* v_h__3_818_){
_start:
{
switch(v_x_815_)
{
case 0:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec(v_h__3_818_);
lean_dec(v_h__2_817_);
v___x_819_ = lean_box(0);
v___x_820_ = lean_apply_1(v_h__1_816_, v___x_819_);
return v___x_820_;
}
case 1:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec(v_h__2_817_);
lean_dec(v_h__1_816_);
v___x_821_ = lean_box(0);
v___x_822_ = lean_apply_1(v_h__3_818_, v___x_821_);
return v___x_822_;
}
default: 
{
lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec(v_h__3_818_);
lean_dec(v_h__1_816_);
v___x_823_ = lean_box(0);
v___x_824_ = lean_apply_1(v_h__2_817_, v___x_823_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_815_ = stack[0].m_num;
lean_object* v_h__1_816_ = stack[1].m_obj;
lean_object* v_h__2_817_ = stack[2].m_obj;
lean_object* v_h__3_818_ = stack[3].m_obj;
lean_object* v_res_825_;
v_res_825_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_815_, v_h__1_816_, v_h__2_817_, v_h__3_818_);
stack->m_obj
 = v_res_825_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object* v_x_826_, lean_object* v_h__1_827_, lean_object* v_h__2_828_, lean_object* v_h__3_829_){
_start:
{
uint8_t v_x_33__boxed_830_; lean_object* v_res_831_; 
v_x_33__boxed_830_ = lean_unbox(v_x_826_);
v_res_831_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_33__boxed_830_, v_h__1_827_, v_h__2_828_, v_h__3_829_);
return v_res_831_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object* v_motive_832_, uint8_t v_x_833_, lean_object* v_h__1_834_, lean_object* v_h__2_835_, lean_object* v_h__3_836_){
_start:
{
switch(v_x_833_)
{
case 0:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v_h__3_836_);
lean_dec(v_h__2_835_);
v___x_837_ = lean_box(0);
v___x_838_ = lean_apply_1(v_h__1_834_, v___x_837_);
return v___x_838_;
}
case 1:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec(v_h__2_835_);
lean_dec(v_h__1_834_);
v___x_839_ = lean_box(0);
v___x_840_ = lean_apply_1(v_h__3_836_, v___x_839_);
return v___x_840_;
}
default: 
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec(v_h__3_836_);
lean_dec(v_h__1_834_);
v___x_841_ = lean_box(0);
v___x_842_ = lean_apply_1(v_h__2_835_, v___x_841_);
return v___x_842_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_833_ = stack[1].m_num;
lean_object* v_h__1_834_ = stack[2].m_obj;
lean_object* v_h__2_835_ = stack[3].m_obj;
lean_object* v_h__3_836_ = stack[4].m_obj;
lean_object* v_res_843_;
v_res_843_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_box(0), v_x_833_, v_h__1_834_, v_h__2_835_, v_h__3_836_);
stack->m_obj
 = v_res_843_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object* v_motive_844_, lean_object* v_x_845_, lean_object* v_h__1_846_, lean_object* v_h__2_847_, lean_object* v_h__3_848_){
_start:
{
uint8_t v_x_56__boxed_849_; lean_object* v_res_850_; 
v_x_56__boxed_849_ = lean_unbox(v_x_845_);
v_res_850_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_844_, v_x_56__boxed_849_, v_h__1_846_, v_h__2_847_, v_h__3_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter___redArg(lean_object* v_x_851_, lean_object* v_h__1_852_, lean_object* v_h__2_853_){
_start:
{
if (lean_obj_tag(v_x_851_) == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec(v_h__1_852_);
v___x_854_ = lean_box(0);
v___x_855_ = lean_apply_1(v_h__2_853_, v___x_854_);
return v___x_855_;
}
else
{
lean_object* v_val_856_; lean_object* v___x_857_; 
lean_dec(v_h__2_853_);
v_val_856_ = lean_ctor_get(v_x_851_, 0);
lean_inc(v_val_856_);
lean_dec_ref_known(v_x_851_, 1);
v___x_857_ = lean_apply_1(v_h__1_852_, v_val_856_);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter(lean_object* v_00_u03b1_858_, lean_object* v_00_u03b2_859_, lean_object* v_motive_860_, lean_object* v_x_861_, lean_object* v_h__1_862_, lean_object* v_h__2_863_){
_start:
{
if (lean_obj_tag(v_x_861_) == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec(v_h__1_862_);
v___x_864_ = lean_box(0);
v___x_865_ = lean_apply_1(v_h__2_863_, v___x_864_);
return v___x_865_;
}
else
{
lean_object* v_val_866_; lean_object* v___x_867_; 
lean_dec(v_h__2_863_);
v_val_866_ = lean_ctor_get(v_x_861_, 0);
lean_inc(v_val_866_);
lean_dec_ref_known(v_x_861_, 1);
v___x_867_ = lean_apply_1(v_h__1_862_, v_val_866_);
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_868_, lean_object* v_h__1_869_, lean_object* v_h__2_870_){
_start:
{
if (lean_obj_tag(v_x_868_) == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec(v_h__1_869_);
v___x_871_ = lean_box(0);
v___x_872_ = lean_apply_1(v_h__2_870_, v___x_871_);
return v___x_872_;
}
else
{
lean_object* v_val_873_; lean_object* v___x_874_; 
lean_dec(v_h__2_870_);
v_val_873_ = lean_ctor_get(v_x_868_, 0);
lean_inc(v_val_873_);
lean_dec_ref_known(v_x_868_, 1);
v___x_874_ = lean_apply_1(v_h__1_869_, v_val_873_);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_875_, lean_object* v_motive_876_, lean_object* v_x_877_, lean_object* v_h__1_878_, lean_object* v_h__2_879_){
_start:
{
if (lean_obj_tag(v_x_877_) == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec(v_h__1_878_);
v___x_880_ = lean_box(0);
v___x_881_ = lean_apply_1(v_h__2_879_, v___x_880_);
return v___x_881_;
}
else
{
lean_object* v_val_882_; lean_object* v___x_883_; 
lean_dec(v_h__2_879_);
v_val_882_ = lean_ctor_get(v_x_877_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v_x_877_, 1);
v___x_883_ = lean_apply_1(v_h__1_878_, v_val_882_);
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_884_, lean_object* v_h__1_885_, lean_object* v_h__2_886_){
_start:
{
if (lean_obj_tag(v_x_884_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_888_; 
lean_dec(v_h__2_886_);
v_a_887_ = lean_ctor_get(v_x_884_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v_x_884_, 1);
v___x_888_ = lean_apply_1(v_h__1_885_, v_a_887_);
return v___x_888_;
}
else
{
lean_object* v_a_889_; lean_object* v___x_890_; 
lean_dec(v_h__1_885_);
v_a_889_ = lean_ctor_get(v_x_884_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v_x_884_, 1);
v___x_890_ = lean_apply_1(v_h__2_886_, v_a_889_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_891_, lean_object* v_motive_892_, lean_object* v_x_893_, lean_object* v_h__1_894_, lean_object* v_h__2_895_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_897_; 
lean_dec(v_h__2_895_);
v_a_896_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v_x_893_, 1);
v___x_897_ = lean_apply_1(v_h__1_894_, v_a_896_);
return v___x_897_;
}
else
{
lean_object* v_a_898_; lean_object* v___x_899_; 
lean_dec(v_h__1_894_);
v_a_898_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v_x_893_, 1);
v___x_899_ = lean_apply_1(v_h__2_895_, v_a_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_900_, lean_object* v_h__1_901_, lean_object* v_h__2_902_){
_start:
{
if (lean_obj_tag(v_x_900_) == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
lean_dec(v_h__1_901_);
v___x_903_ = lean_box(0);
v___x_904_ = lean_apply_1(v_h__2_902_, v___x_903_);
return v___x_904_;
}
else
{
lean_object* v_val_905_; lean_object* v___x_906_; 
lean_dec(v_h__2_902_);
v_val_905_ = lean_ctor_get(v_x_900_, 0);
lean_inc(v_val_905_);
lean_dec_ref_known(v_x_900_, 1);
v___x_906_ = lean_apply_1(v_h__1_901_, v_val_905_);
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_motive_909_, lean_object* v_x_910_, lean_object* v_h__1_911_, lean_object* v_h__2_912_){
_start:
{
if (lean_obj_tag(v_x_910_) == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v_h__1_911_);
v___x_913_ = lean_box(0);
v___x_914_ = lean_apply_1(v_h__2_912_, v___x_913_);
return v___x_914_;
}
else
{
lean_object* v_val_915_; lean_object* v___x_916_; 
lean_dec(v_h__2_912_);
v_val_915_ = lean_ctor_get(v_x_910_, 0);
lean_inc(v_val_915_);
lean_dec_ref_known(v_x_910_, 1);
v___x_916_ = lean_apply_1(v_h__1_911_, v_val_915_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object* v_x_917_, lean_object* v_x_918_, lean_object* v_h__1_919_, lean_object* v_h__2_920_){
_start:
{
if (lean_obj_tag(v_x_917_) == 0)
{
lean_object* v_size_921_; lean_object* v_k_922_; lean_object* v_v_923_; lean_object* v_l_924_; lean_object* v_r_925_; lean_object* v___x_926_; 
lean_dec(v_h__1_919_);
v_size_921_ = lean_ctor_get(v_x_917_, 0);
lean_inc(v_size_921_);
v_k_922_ = lean_ctor_get(v_x_917_, 1);
lean_inc(v_k_922_);
v_v_923_ = lean_ctor_get(v_x_917_, 2);
lean_inc(v_v_923_);
v_l_924_ = lean_ctor_get(v_x_917_, 3);
lean_inc(v_l_924_);
v_r_925_ = lean_ctor_get(v_x_917_, 4);
lean_inc(v_r_925_);
lean_dec_ref_known(v_x_917_, 5);
v___x_926_ = lean_apply_6(v_h__2_920_, v_size_921_, v_k_922_, v_v_923_, v_l_924_, v_r_925_, v_x_918_);
return v___x_926_;
}
else
{
lean_object* v___x_927_; 
lean_dec(v_h__2_920_);
v___x_927_ = lean_apply_1(v_h__1_919_, v_x_918_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object* v_00_u03b1_928_, lean_object* v_00_u03b2_929_, lean_object* v_motive_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_h__1_933_, lean_object* v_h__2_934_){
_start:
{
if (lean_obj_tag(v_x_931_) == 0)
{
lean_object* v_size_935_; lean_object* v_k_936_; lean_object* v_v_937_; lean_object* v_l_938_; lean_object* v_r_939_; lean_object* v___x_940_; 
lean_dec(v_h__1_933_);
v_size_935_ = lean_ctor_get(v_x_931_, 0);
lean_inc(v_size_935_);
v_k_936_ = lean_ctor_get(v_x_931_, 1);
lean_inc(v_k_936_);
v_v_937_ = lean_ctor_get(v_x_931_, 2);
lean_inc(v_v_937_);
v_l_938_ = lean_ctor_get(v_x_931_, 3);
lean_inc(v_l_938_);
v_r_939_ = lean_ctor_get(v_x_931_, 4);
lean_inc(v_r_939_);
lean_dec_ref_known(v_x_931_, 5);
v___x_940_ = lean_apply_6(v_h__2_934_, v_size_935_, v_k_936_, v_v_937_, v_l_938_, v_r_939_, v_x_932_);
return v___x_940_;
}
else
{
lean_object* v___x_941_; 
lean_dec(v_h__2_934_);
v___x_941_ = lean_apply_1(v_h__1_933_, v_x_932_);
return v___x_941_;
}
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t v_x_942_, lean_object* v_h__1_943_, lean_object* v_h__2_944_, lean_object* v_h__3_945_){
_start:
{
switch(v_x_942_)
{
case 0:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec(v_h__3_945_);
lean_dec(v_h__2_944_);
v___x_946_ = lean_box(0);
v___x_947_ = lean_apply_1(v_h__1_943_, v___x_946_);
return v___x_947_;
}
case 1:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec(v_h__3_945_);
lean_dec(v_h__1_943_);
v___x_948_ = lean_box(0);
v___x_949_ = lean_apply_1(v_h__2_944_, v___x_948_);
return v___x_949_;
}
default: 
{
lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec(v_h__2_944_);
lean_dec(v_h__1_943_);
v___x_950_ = lean_box(0);
v___x_951_ = lean_apply_1(v_h__3_945_, v___x_950_);
return v___x_951_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_942_ = stack[0].m_num;
lean_object* v_h__1_943_ = stack[1].m_obj;
lean_object* v_h__2_944_ = stack[2].m_obj;
lean_object* v_h__3_945_ = stack[3].m_obj;
lean_object* v_res_952_;
v_res_952_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_942_, v_h__1_943_, v_h__2_944_, v_h__3_945_);
stack->m_obj
 = v_res_952_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_953_, lean_object* v_h__1_954_, lean_object* v_h__2_955_, lean_object* v_h__3_956_){
_start:
{
uint8_t v_x_33__boxed_957_; lean_object* v_res_958_; 
v_x_33__boxed_957_ = lean_unbox(v_x_953_);
v_res_958_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_33__boxed_957_, v_h__1_954_, v_h__2_955_, v_h__3_956_);
return v_res_958_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object* v_motive_959_, uint8_t v_x_960_, lean_object* v_h__1_961_, lean_object* v_h__2_962_, lean_object* v_h__3_963_){
_start:
{
switch(v_x_960_)
{
case 0:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
v___x_964_ = lean_box(0);
v___x_965_ = lean_apply_1(v_h__1_961_, v___x_964_);
return v___x_965_;
}
case 1:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
lean_dec(v_h__3_963_);
lean_dec(v_h__1_961_);
v___x_966_ = lean_box(0);
v___x_967_ = lean_apply_1(v_h__2_962_, v___x_966_);
return v___x_967_;
}
default: 
{
lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v___x_968_ = lean_box(0);
v___x_969_ = lean_apply_1(v_h__3_963_, v___x_968_);
return v___x_969_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_960_ = stack[1].m_num;
lean_object* v_h__1_961_ = stack[2].m_obj;
lean_object* v_h__2_962_ = stack[3].m_obj;
lean_object* v_h__3_963_ = stack[4].m_obj;
lean_object* v_res_970_;
v_res_970_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_box(0), v_x_960_, v_h__1_961_, v_h__2_962_, v_h__3_963_);
stack->m_obj
 = v_res_970_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object* v_motive_971_, lean_object* v_x_972_, lean_object* v_h__1_973_, lean_object* v_h__2_974_, lean_object* v_h__3_975_){
_start:
{
uint8_t v_x_56__boxed_976_; lean_object* v_res_977_; 
v_x_56__boxed_976_ = lean_unbox(v_x_972_);
v_res_977_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(v_motive_971_, v_x_56__boxed_976_, v_h__1_973_, v_h__2_974_, v_h__3_975_);
return v_res_977_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(uint8_t v_x_978_, lean_object* v_h__1_979_, lean_object* v_h__2_980_){
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
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_978_ = stack[0].m_num;
lean_object* v_h__1_979_ = stack[1].m_obj;
lean_object* v_h__2_980_ = stack[2].m_obj;
lean_object* v_res_985_;
v_res_985_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(v_x_978_, v_h__1_979_, v_h__2_980_);
stack->m_obj
 = v_res_985_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_986_, lean_object* v_h__1_987_, lean_object* v_h__2_988_){
_start:
{
uint8_t v_x_24__boxed_989_; lean_object* v_res_990_; 
v_x_24__boxed_989_ = lean_unbox(v_x_986_);
v_res_990_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_989_, v_h__1_987_, v_h__2_988_);
return v_res_990_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(lean_object* v_motive_991_, uint8_t v_x_992_, lean_object* v_h__1_993_, lean_object* v_h__2_994_){
_start:
{
if (v_x_992_ == 0)
{
lean_object* v___x_995_; lean_object* v___x_996_; 
lean_dec(v_h__1_993_);
v___x_995_ = lean_box(0);
v___x_996_ = lean_apply_1(v_h__2_994_, v___x_995_);
return v___x_996_;
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec(v_h__2_994_);
v___x_997_ = lean_box(0);
v___x_998_ = lean_apply_1(v_h__1_993_, v___x_997_);
return v___x_998_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_992_ = stack[1].m_num;
lean_object* v_h__1_993_ = stack[2].m_obj;
lean_object* v_h__2_994_ = stack[3].m_obj;
lean_object* v_res_999_;
v_res_999_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(lean_box(0), v_x_992_, v_h__1_993_, v_h__2_994_);
stack->m_obj
 = v_res_999_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_1000_, lean_object* v_x_1001_, lean_object* v_h__1_1002_, lean_object* v_h__2_1003_){
_start:
{
uint8_t v_x_41__boxed_1004_; lean_object* v_res_1005_; 
v_x_41__boxed_1004_ = lean_unbox(v_x_1001_);
v_res_1005_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(v_motive_1000_, v_x_41__boxed_1004_, v_h__1_1002_, v_h__2_1003_);
return v_res_1005_;
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
