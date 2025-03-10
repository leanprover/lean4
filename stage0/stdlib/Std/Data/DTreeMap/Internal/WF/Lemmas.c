// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.WF.Lemmas
// Imports: Init.Data.Option.List Init.Data.Array.Bootstrap Std.Classes.Ord Std.Data.DTreeMap.Internal.Model Std.Data.Internal.Cut Std.Data.Internal.List.Associative
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__2_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__5_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__2_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__5_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__2_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__2_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__2_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__2_splitter___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___rarg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__2_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__2_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__4_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__2_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__6_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__instCoeTypeForall__std(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__3_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__6_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_keys_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_keys_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__2_splitter___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__2_splitter___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__2_splitter___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_keys_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__6_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__4_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__instCoeTypeForall__std(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__6_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_7(x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0), lean_box(0));
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_5);
x_12 = lean_apply_2(x_4, lean_box(0), lean_box(0));
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__6_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__6_splitter___rarg), 5, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__6_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__6_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 4);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_10, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 4);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_apply_15(x_8, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, lean_box(0), lean_box(0));
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_9, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_9, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_9, 4);
lean_inc(x_32);
lean_dec(x_9);
x_33 = lean_apply_10(x_7, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, lean_box(0), lean_box(0));
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_7);
x_34 = lean_ctor_get(x_1, 4);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_5);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 2);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_34, 4);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_apply_10(x_6, x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42, lean_box(0), lean_box(0));
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_6);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
lean_dec(x_1);
x_47 = lean_apply_5(x_5, x_44, x_45, x_46, lean_box(0), lean_box(0));
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_48 = lean_apply_2(x_4, lean_box(0), lean_box(0));
return x_48;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__1_splitter___rarg), 8, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__5_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_7(x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0), lean_box(0));
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_5);
x_12 = lean_apply_2(x_4, lean_box(0), lean_box(0));
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__5_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__5_splitter___rarg), 5, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__5_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__5_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 4);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 4);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_apply_12(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, lean_box(0), lean_box(0));
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 4);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_apply_7(x_7, x_20, x_21, x_22, x_23, x_24, lean_box(0), lean_box(0));
return x_25;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_5);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 4);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_apply_7(x_6, x_26, x_27, x_28, x_29, x_30, lean_box(0), lean_box(0));
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_6);
x_32 = lean_apply_2(x_5, lean_box(0), lean_box(0));
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__2_splitter___rarg), 8, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__2_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__2_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__3_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_7);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 4);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_apply_12(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, lean_box(0), lean_box(0));
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 4);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_apply_7(x_6, x_19, x_20, x_21, x_22, x_23, lean_box(0), lean_box(0));
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_apply_3(x_7, x_2, lean_box(0), lean_box(0));
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__3_splitter___rarg), 7, 0);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__4_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_7);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 4);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_apply_12(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, lean_box(0), lean_box(0));
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 4);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_apply_7(x_6, x_19, x_20, x_21, x_22, x_23, lean_box(0), lean_box(0));
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_apply_3(x_7, x_2, lean_box(0), lean_box(0));
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__4_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__4_splitter___rarg), 7, 0);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__4_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_match__4_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_7(x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0), lean_box(0));
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_2(x_3, lean_box(0), lean_box(0));
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_3(x_2, x_1, lean_box(0), lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___rarg), 2, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_3(x_2, x_1, lean_box(0), lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__2_splitter___rarg), 2, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__2_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__2_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_6(x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_1(x_3, lean_box(0));
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__2_splitter___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_3(x_2, x_1, lean_box(0), lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___rarg), 2, 0);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_3(x_2, x_1, lean_box(0), lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__2_splitter___rarg), 2, 0);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__2_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__2_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_6(x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_1(x_3, lean_box(0));
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_3, x_5, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_apply_1(x_3, lean_box(0));
return x_6;
}
default: 
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_apply_1(x_4, lean_box(0));
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_4(x_2, x_1, lean_box(0), lean_box(0), lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__2_splitter___rarg), 2, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__2_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__2_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_inc(x_2);
return x_2;
}
case 1:
{
lean_inc(x_4);
return x_4;
}
default: 
{
lean_inc(x_3);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___rarg(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
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
lean_dec(x_1);
x_9 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___rarg___boxed), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___rarg(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___rarg___boxed), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___rarg___boxed), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__2_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__2_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__2_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__2_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__2_splitter___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
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
lean_dec(x_1);
x_9 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
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
lean_dec(x_1);
x_9 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_keys_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_apply_3(x_3, x_6, x_7, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_keys_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_keys_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_keys_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_keys_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_6(x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_1(x_3, lean_box(0));
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__2_splitter___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_inc(x_2);
return x_2;
}
case 1:
{
lean_inc(x_4);
return x_4;
}
default: 
{
lean_inc(x_3);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter___rarg(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
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
lean_dec(x_1);
x_9 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Data_Option_List(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Classes_Ord(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_DTreeMap_Internal_Model(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Internal_Cut(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Internal_List_Associative(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_List(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Classes_Ord(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Internal_Model(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Internal_Cut(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Internal_List_Associative(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
