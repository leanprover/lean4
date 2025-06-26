// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Model
// Imports: Std.Data.DTreeMap.Internal.WF.Defs Std.Data.DTreeMap.Internal.Cell Std.Data.Internal.Cut
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_ofEq___redArg(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___closed__0;
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_toListModel___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Cell_contains___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 4);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_3);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
switch (x_7) {
case 0:
{
lean_dec(x_5);
x_2 = x_4;
goto _start;
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
return x_10;
}
default: 
{
lean_dec(x_4);
x_2 = x_5;
goto _start;
}
}
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_x27___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_DTreeMap_Internal_Impl_contains_x27(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (x_2) {
case 0:
{
lean_inc(x_3);
return x_3;
}
case 1:
{
lean_inc(x_5);
return x_5;
}
default: 
{
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (x_2) {
case 0:
{
lean_inc(x_3);
return x_3;
}
case 1:
{
lean_inc(x_5);
return x_5;
}
default: 
{
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 4);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_6);
x_10 = lean_apply_1(x_1, x_6);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
switch (x_11) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
x_13 = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(x_9);
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_List_appendTR___redArg(x_14, x_5);
x_4 = x_8;
x_5 = x_15;
goto _start;
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_17 = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(x_8);
lean_dec(x_8);
x_18 = l_List_appendTR___redArg(x_3, x_17);
x_19 = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(x_6, x_7);
x_20 = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(x_9);
lean_dec(x_9);
x_21 = l_List_appendTR___redArg(x_20, x_5);
x_22 = lean_apply_4(x_2, x_18, x_19, lean_box(0), x_21);
return x_22;
}
default: 
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(x_8);
lean_dec(x_8);
x_24 = l_List_appendTR___redArg(x_3, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_7);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_List_appendTR___redArg(x_24, x_27);
x_3 = x_28;
x_4 = x_9;
goto _start;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_apply_4(x_2, x_3, x_30, lean_box(0), x_5);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(x_5, x_7, x_8, x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_DTreeMap_Internal_Impl_applyPartition_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(x_1, x_3, x_4, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_applyPartition(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
switch (x_10) {
case 0:
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0), 3, 1);
lean_closure_set(x_11, 0, x_4);
x_3 = x_7;
x_4 = x_11;
goto _start;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(x_5, x_6);
x_14 = lean_apply_2(x_4, x_13, lean_box(0));
return x_14;
}
default: 
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0), 3, 1);
lean_closure_set(x_15, 0, x_4);
x_3 = x_8;
x_4 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_4, x_17, lean_box(0));
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = lean_apply_6(x_4, x_5, x_6, x_7, x_8, x_9, x_2);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_1(x_3, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___redArg(x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___redArg(x_7, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
x_9 = lean_apply_1(x_1, x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
switch (x_10) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(x_8);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_11);
lean_inc(x_3);
x_13 = lean_apply_2(x_3, x_2, x_12);
x_2 = x_13;
x_4 = x_7;
goto _start;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_15 = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(x_7);
lean_dec(x_7);
x_16 = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(x_5, x_6);
x_17 = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(x_8);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_apply_2(x_3, x_2, x_18);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(x_7);
lean_dec(x_7);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
lean_ctor_set(x_21, 2, x_6);
lean_inc(x_3);
x_22 = lean_apply_2(x_3, x_2, x_21);
x_2 = x_22;
x_4 = x_8;
goto _start;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0;
x_25 = lean_apply_2(x_3, x_2, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DTreeMap_Internal_Impl_explore___redArg(x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DTreeMap_Internal_Impl_explore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_DTreeMap_Internal_Cell_contains___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0___boxed), 2, 0);
x_5 = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(x_1, x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(x_3, x_4, x_5);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_DTreeMap_Internal_Impl_contains_u2098(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0), 2, 0);
x_5 = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(x_1, x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(x_3, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(21u);
x_4 = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1;
x_5 = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3;
x_7 = l_panic___redArg(x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(x_3, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(x_1, x_3, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(x_3, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DTreeMap_Internal_Impl_getD_u2098(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0), 2, 0);
x_5 = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(x_1, x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3;
x_7 = l_panic___redArg(x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(x_1, x_3, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 2);
x_8 = l_List_head_x3f___redArg(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed), 2, 0);
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_explore___redArg(x_2, x_4, x_3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_head_x3f___redArg(x_4);
return x_5;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0;
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed), 4, 0);
x_4 = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_ctor_get(x_1, 4);
x_5 = l_Std_DTreeMap_Internal_Impl_reverse___redArg(x_4);
x_6 = l_Std_DTreeMap_Internal_Impl_reverse___redArg(x_3);
lean_ctor_set(x_1, 4, x_6);
lean_ctor_set(x_1, 3, x_5);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_12 = l_Std_DTreeMap_Internal_Impl_reverse___redArg(x_11);
x_13 = l_Std_DTreeMap_Internal_Impl_reverse___redArg(x_10);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_12);
lean_ctor_set(x_14, 4, x_13);
return x_14;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_reverse___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0), 2, 0);
x_5 = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(x_1, x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3;
x_7 = l_panic___redArg(x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_apply_1(x_2, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_5, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___redArg(x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___redArg(x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_apply_9(x_4, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_4(x_3, x_16, x_17, x_18, x_19);
return x_20;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_4, lean_box(0), x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_3(x_3, x_8, x_9, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_apply_10(x_5, x_7, x_8, x_9, x_11, x_12, x_13, x_14, x_15, x_10, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_5(x_4, x_17, x_18, x_19, x_20, x_2);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_3, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 4);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_apply_10(x_3, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_8, lean_box(0));
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_5(x_2, x_15, x_16, x_17, x_18, lean_box(0));
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_apply_9(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_4(x_3, x_16, x_17, x_18, x_19);
return x_20;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_apply_10(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_5(x_4, x_17, x_18, x_19, x_20, x_2);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_3, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 4);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_apply_10(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_5(x_2, x_15, x_16, x_17, x_18, lean_box(0));
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_apply_10(x_5, x_7, x_8, x_9, x_11, x_12, x_13, x_14, x_15, x_10, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_5(x_4, x_17, x_18, x_19, x_20, x_2);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_3, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_apply_10(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_5(x_4, x_17, x_18, x_19, x_20, x_2);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_3, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_apply_9(x_4, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_4(x_3, x_16, x_17, x_18, x_19);
return x_20;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_apply_10(x_5, x_7, x_8, x_9, x_11, x_12, x_13, x_14, x_15, x_10, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_5(x_4, x_17, x_18, x_19, x_20, x_2);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_3, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 4);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_apply_10(x_3, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_8, lean_box(0));
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_5(x_2, x_15, x_16, x_17, x_18, lean_box(0));
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_apply_9(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_4(x_3, x_16, x_17, x_18, x_19);
return x_20;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_apply_10(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_5(x_4, x_17, x_18, x_19, x_20, x_2);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_3, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 4);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_apply_10(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_5(x_2, x_15, x_16, x_17, x_18, lean_box(0));
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_5(x_2, x_3, x_4, x_5, lean_box(0), lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(x_9, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (x_2) {
case 0:
{
lean_inc(x_3);
return x_3;
}
case 1:
{
lean_inc(x_5);
return x_5;
}
default: 
{
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_4(x_2, x_1, lean_box(0), lean_box(0), lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_4(x_6, x_5, lean_box(0), lean_box(0), lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_4(x_2, x_1, lean_box(0), lean_box(0), lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_4(x_6, x_5, lean_box(0), lean_box(0), lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___redArg(x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
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
x_9 = lean_apply_8(x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0), x_2, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(x_4, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = lean_apply_6(x_4, x_5, x_6, x_7, x_8, x_9, x_2);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_1(x_3, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_3);
return x_3;
}
default: 
{
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (x_2) {
case 0:
{
lean_inc(x_3);
return x_3;
}
case 1:
{
lean_inc(x_4);
return x_4;
}
default: 
{
lean_inc(x_5);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = lean_apply_7(x_5, x_6, x_7, x_8, x_9, x_10, x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_5);
x_12 = lean_apply_2(x_4, x_2, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = lean_apply_7(x_5, x_6, x_7, x_8, x_9, x_10, x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_5);
x_12 = lean_apply_2(x_4, x_2, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = l_List_head_x3f___redArg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed), 4, 0);
x_5 = lean_apply_1(x_1, x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_List_head_x3f___redArg(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
default: 
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed), 2, 0);
x_5 = lean_apply_1(x_1, x_2);
x_6 = lean_box(0);
x_7 = l_Std_DTreeMap_Internal_Impl_explore___redArg(x_5, x_6, x_4, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_5(x_3, x_1, x_6, lean_box(0), x_7, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_4(x_4, x_1, x_10, x_11, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_apply_5(x_5, x_1, x_14, x_15, lean_box(0), x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___redArg(x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = lean_box(x_5);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(2);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_dec(x_6);
return x_5;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___closed__0;
x_6 = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 2);
x_8 = l_List_head_x3f___redArg(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
return x_8;
}
}
default: 
{
lean_inc(x_1);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed), 2, 0);
x_6 = lean_box(0);
x_7 = l_Std_DTreeMap_Internal_Impl_explore___redArg(x_4, x_6, x_5, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_5(x_3, x_1, x_6, lean_box(0), x_7, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_4(x_4, x_1, x_10, x_11, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_apply_5(x_5, x_1, x_14, x_15, lean_box(0), x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___redArg(x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_3);
return x_3;
}
default: 
{
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (x_2) {
case 0:
{
lean_inc(x_3);
return x_3;
}
case 1:
{
lean_inc(x_4);
return x_4;
}
default: 
{
lean_inc(x_5);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___redArg(x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___redArg(x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___redArg(x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, lean_box(0));
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
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_apply_1(x_2, lean_box(0));
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___redArg(x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = lean_apply_6(x_4, x_5, x_6, x_7, x_8, x_9, x_2);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_1(x_3, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
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
x_9 = lean_apply_8(x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0), x_2, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(x_4, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = lean_apply_7(x_5, x_6, x_7, x_8, x_9, x_10, x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_5);
x_12 = lean_apply_2(x_4, x_2, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___redArg(x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___redArg(x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___redArg(x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___redArg(x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* initialize_Std_Data_DTreeMap_Internal_WF_Defs(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_DTreeMap_Internal_Cell(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Internal_Cut(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Internal_Model(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Internal_Cell(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Internal_Cut(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0 = _init_l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0);
l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0 = _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0);
l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1);
l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2);
l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3 = _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0 = _init_l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0);
l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___closed__0 = _init_l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
