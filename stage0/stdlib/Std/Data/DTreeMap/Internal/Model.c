// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Model
// Imports: Std.Data.DTreeMap.Internal.WF.Defs Std.Data.DTreeMap.Internal.Cell
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_alter_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_x27___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_u2098___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_Const_alter_u2098___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Cell_contains___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_alter_u2098___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_erase_u2098___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insert_u2098___spec__1(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__3;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_alter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_panic___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__2_splitter(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__2_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_x27___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_alter_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_u2098___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_ofEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_alter_u2098___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__4;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_erase_u2098___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__2_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__2_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_Const_alter___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_toListModel___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__2_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_Const_alter_u2098___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insert_u2098___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_u2098(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 4);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_2);
x_7 = lean_apply_1(x_2, x_4);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
switch (x_8) {
case 0:
{
lean_dec(x_6);
x_3 = x_5;
goto _start;
}
case 1:
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_10 = 1;
return x_10;
}
default: 
{
lean_dec(x_5);
x_3 = x_6;
goto _start;
}
}
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_contains_x27___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains_x27___rarg(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__2_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__2_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__2_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___rarg(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___rarg(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 4);
lean_inc(x_12);
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_9);
x_13 = lean_apply_1(x_2, x_9);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
switch (x_14) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
x_16 = l_Std_DTreeMap_Internal_Impl_toListModel___rarg(x_12);
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_List_appendTR___rarg(x_17, x_8);
x_6 = x_11;
x_7 = lean_box(0);
x_8 = x_18;
goto _start;
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_20 = l_Std_DTreeMap_Internal_Impl_toListModel___rarg(x_11);
lean_dec(x_11);
x_21 = l_List_appendTR___rarg(x_5, x_20);
x_22 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_9, x_10, lean_box(0));
x_23 = l_Std_DTreeMap_Internal_Impl_toListModel___rarg(x_12);
lean_dec(x_12);
x_24 = l_List_appendTR___rarg(x_23, x_8);
x_25 = lean_apply_4(x_4, x_21, x_22, lean_box(0), x_24);
return x_25;
}
default: 
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = l_Std_DTreeMap_Internal_Impl_toListModel___rarg(x_11);
lean_dec(x_11);
x_27 = l_List_appendTR___rarg(x_5, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_10);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_List_appendTR___rarg(x_27, x_30);
x_5 = x_31;
x_6 = x_12;
x_7 = lean_box(0);
goto _start;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = lean_apply_4(x_4, x_5, x_33, lean_box(0), x_8);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyPartition_go___rarg___boxed), 8, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DTreeMap_Internal_Impl_applyPartition_go___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
lean_inc(x_3);
x_6 = l_Std_DTreeMap_Internal_Impl_applyPartition_go___rarg(x_1, x_2, x_3, x_4, x_5, x_3, lean_box(0), x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyPartition___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_applyPartition___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_11 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyCell___rarg___lambda__1), 3, 1);
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
x_13 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_5, x_6, lean_box(0));
x_14 = lean_apply_2(x_4, x_13, lean_box(0));
return x_14;
}
default: 
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyCell___rarg___lambda__1), 3, 1);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyCell___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___rarg), 4, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__2_splitter___rarg), 4, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__2_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__2_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 4);
lean_inc(x_9);
lean_dec(x_5);
lean_inc(x_2);
lean_inc(x_6);
x_10 = lean_apply_1(x_2, x_6);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
switch (x_11) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Std_DTreeMap_Internal_Impl_toListModel___rarg(x_9);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_12);
lean_inc(x_4);
x_14 = lean_apply_2(x_4, x_3, x_13);
x_3 = x_14;
x_5 = x_8;
goto _start;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_16 = l_Std_DTreeMap_Internal_Impl_toListModel___rarg(x_8);
lean_dec(x_8);
x_17 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_6, x_7, lean_box(0));
x_18 = l_Std_DTreeMap_Internal_Impl_toListModel___rarg(x_9);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_apply_2(x_4, x_3, x_19);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Std_DTreeMap_Internal_Impl_toListModel___rarg(x_8);
lean_dec(x_8);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
lean_ctor_set(x_22, 2, x_7);
lean_inc(x_4);
x_23 = lean_apply_2(x_4, x_3, x_22);
x_3 = x_23;
x_5 = x_9;
goto _start;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_25);
x_28 = lean_apply_2(x_4, x_3, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_explore___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_explore___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_4, 3);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_8);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
switch (x_13) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_4);
lean_dec(x_7);
x_14 = l_Std_DTreeMap_Internal_Impl_updateCell___rarg(x_1, x_2, x_3, x_10, lean_box(0));
x_15 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_8, x_9, x_14, x_11, lean_box(0), lean_box(0), lean_box(0));
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_8, x_9, lean_box(0));
x_17 = lean_apply_1(x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_7);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_10, 2);
x_23 = lean_ctor_get(x_10, 3);
x_24 = lean_ctor_get(x_10, 4);
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
x_27 = lean_ctor_get(x_11, 2);
x_28 = lean_ctor_get(x_11, 3);
x_29 = lean_ctor_get(x_11, 4);
x_30 = lean_nat_dec_lt(x_20, x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_20);
x_31 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_21, x_22, x_23, x_24, lean_box(0), lean_box(0), lean_box(0));
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_mul(x_36, x_35);
x_38 = lean_nat_dec_lt(x_37, x_25);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_4);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_39, x_35);
lean_dec(x_35);
x_41 = lean_nat_add(x_40, x_25);
lean_dec(x_25);
lean_dec(x_40);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_32);
lean_ctor_set(x_10, 2, x_34);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_41);
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_11);
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_28, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_28, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_28, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_29, 0);
lean_inc(x_47);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_mul(x_48, x_47);
x_50 = lean_nat_dec_lt(x_42, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
uint8_t x_51; 
lean_dec(x_42);
lean_free_object(x_4);
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_28, 4);
lean_dec(x_52);
x_53 = lean_ctor_get(x_28, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_28, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_28, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_28, 0);
lean_dec(x_56);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_57, x_35);
lean_dec(x_35);
x_59 = lean_nat_add(x_58, x_25);
lean_dec(x_25);
x_60 = lean_nat_add(x_57, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
x_62 = lean_nat_add(x_58, x_61);
lean_dec(x_61);
lean_dec(x_58);
lean_inc(x_32);
lean_ctor_set(x_28, 4, x_45);
lean_ctor_set(x_28, 3, x_32);
lean_ctor_set(x_28, 2, x_34);
lean_ctor_set(x_28, 1, x_33);
lean_ctor_set(x_28, 0, x_62);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_32, 4);
lean_dec(x_64);
x_65 = lean_ctor_get(x_32, 3);
lean_dec(x_65);
x_66 = lean_ctor_get(x_32, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_32, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_32, 0);
lean_dec(x_68);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_46, 0);
lean_inc(x_69);
x_70 = lean_nat_add(x_60, x_69);
lean_dec(x_69);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_70);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_add(x_60, x_71);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_72);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
else
{
lean_dec(x_32);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_46, 0);
lean_inc(x_73);
x_74 = lean_nat_add(x_60, x_73);
lean_dec(x_73);
lean_dec(x_60);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_26);
lean_ctor_set(x_75, 2, x_27);
lean_ctor_set(x_75, 3, x_46);
lean_ctor_set(x_75, 4, x_29);
lean_ctor_set(x_10, 4, x_75);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_add(x_60, x_76);
lean_dec(x_60);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_26);
lean_ctor_set(x_78, 2, x_27);
lean_ctor_set(x_78, 3, x_46);
lean_ctor_set(x_78, 4, x_29);
lean_ctor_set(x_10, 4, x_78);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_add(x_58, x_79);
lean_dec(x_58);
lean_inc(x_32);
lean_ctor_set(x_28, 4, x_45);
lean_ctor_set(x_28, 3, x_32);
lean_ctor_set(x_28, 2, x_34);
lean_ctor_set(x_28, 1, x_33);
lean_ctor_set(x_28, 0, x_80);
x_81 = !lean_is_exclusive(x_32);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_32, 4);
lean_dec(x_82);
x_83 = lean_ctor_get(x_32, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_32, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_32, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_32, 0);
lean_dec(x_86);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_46, 0);
lean_inc(x_87);
x_88 = lean_nat_add(x_60, x_87);
lean_dec(x_87);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_88);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_89; 
x_89 = lean_nat_add(x_60, x_79);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_89);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
else
{
lean_dec(x_32);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_46, 0);
lean_inc(x_90);
x_91 = lean_nat_add(x_60, x_90);
lean_dec(x_90);
lean_dec(x_60);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_26);
lean_ctor_set(x_92, 2, x_27);
lean_ctor_set(x_92, 3, x_46);
lean_ctor_set(x_92, 4, x_29);
lean_ctor_set(x_10, 4, x_92);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_nat_add(x_60, x_79);
lean_dec(x_60);
x_94 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_26);
lean_ctor_set(x_94, 2, x_27);
lean_ctor_set(x_94, 3, x_46);
lean_ctor_set(x_94, 4, x_29);
lean_ctor_set(x_10, 4, x_94);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_28);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_95, x_35);
lean_dec(x_35);
x_97 = lean_nat_add(x_96, x_25);
lean_dec(x_25);
x_98 = lean_nat_add(x_95, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_45, 0);
lean_inc(x_99);
x_100 = lean_nat_add(x_96, x_99);
lean_dec(x_99);
lean_dec(x_96);
lean_inc(x_32);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_33);
lean_ctor_set(x_101, 2, x_34);
lean_ctor_set(x_101, 3, x_32);
lean_ctor_set(x_101, 4, x_45);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_102 = x_32;
} else {
 lean_dec_ref(x_32);
 x_102 = lean_box(0);
}
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_46, 0);
lean_inc(x_103);
x_104 = lean_nat_add(x_98, x_103);
lean_dec(x_103);
lean_dec(x_98);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 5, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_26);
lean_ctor_set(x_105, 2, x_27);
lean_ctor_set(x_105, 3, x_46);
lean_ctor_set(x_105, 4, x_29);
lean_ctor_set(x_10, 4, x_105);
lean_ctor_set(x_10, 3, x_101);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_nat_add(x_98, x_106);
lean_dec(x_98);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(0, 5, 0);
} else {
 x_108 = x_102;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_26);
lean_ctor_set(x_108, 2, x_27);
lean_ctor_set(x_108, 3, x_46);
lean_ctor_set(x_108, 4, x_29);
lean_ctor_set(x_10, 4, x_108);
lean_ctor_set(x_10, 3, x_101);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_nat_add(x_96, x_109);
lean_dec(x_96);
lean_inc(x_32);
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_33);
lean_ctor_set(x_111, 2, x_34);
lean_ctor_set(x_111, 3, x_32);
lean_ctor_set(x_111, 4, x_45);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_112 = x_32;
} else {
 lean_dec_ref(x_32);
 x_112 = lean_box(0);
}
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_46, 0);
lean_inc(x_113);
x_114 = lean_nat_add(x_98, x_113);
lean_dec(x_113);
lean_dec(x_98);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 5, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_26);
lean_ctor_set(x_115, 2, x_27);
lean_ctor_set(x_115, 3, x_46);
lean_ctor_set(x_115, 4, x_29);
lean_ctor_set(x_10, 4, x_115);
lean_ctor_set(x_10, 3, x_111);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_nat_add(x_98, x_109);
lean_dec(x_98);
if (lean_is_scalar(x_112)) {
 x_117 = lean_alloc_ctor(0, 5, 0);
} else {
 x_117 = x_112;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_26);
lean_ctor_set(x_117, 2, x_27);
lean_ctor_set(x_117, 3, x_46);
lean_ctor_set(x_117, 4, x_29);
lean_ctor_set(x_10, 4, x_117);
lean_ctor_set(x_10, 3, x_111);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_118, x_35);
lean_dec(x_35);
x_120 = lean_nat_add(x_119, x_25);
lean_dec(x_25);
x_121 = lean_nat_add(x_119, x_42);
lean_dec(x_42);
lean_dec(x_119);
lean_ctor_set(x_10, 4, x_28);
lean_ctor_set(x_10, 3, x_32);
lean_ctor_set(x_10, 2, x_34);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_121);
lean_ctor_set(x_4, 4, x_29);
lean_ctor_set(x_4, 2, x_27);
lean_ctor_set(x_4, 1, x_26);
lean_ctor_set(x_4, 0, x_120);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_28) == 0)
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_31, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_31, 1);
lean_inc(x_123);
lean_dec(x_31);
x_124 = lean_ctor_get(x_28, 0);
lean_inc(x_124);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_add(x_125, x_25);
lean_dec(x_25);
x_127 = lean_nat_add(x_125, x_124);
lean_dec(x_124);
x_128 = lean_box(1);
lean_ctor_set(x_11, 4, x_28);
lean_ctor_set(x_11, 3, x_128);
lean_ctor_set(x_11, 2, x_123);
lean_ctor_set(x_11, 1, x_122);
lean_ctor_set(x_11, 0, x_127);
lean_ctor_set(x_10, 4, x_29);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_27);
lean_ctor_set(x_10, 1, x_26);
lean_ctor_set(x_10, 0, x_126);
return x_10;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_25);
x_129 = lean_ctor_get(x_31, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_31, 1);
lean_inc(x_130);
lean_dec(x_31);
x_131 = !lean_is_exclusive(x_28);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_28, 1);
x_133 = lean_ctor_get(x_28, 2);
x_134 = lean_ctor_get(x_28, 4);
lean_dec(x_134);
x_135 = lean_ctor_get(x_28, 3);
lean_dec(x_135);
x_136 = lean_ctor_get(x_28, 0);
lean_dec(x_136);
x_137 = lean_box(1);
x_138 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_28, 4, x_137);
lean_ctor_set(x_28, 3, x_137);
lean_ctor_set(x_28, 2, x_130);
lean_ctor_set(x_28, 1, x_129);
lean_ctor_set(x_28, 0, x_138);
lean_ctor_set(x_11, 4, x_137);
lean_ctor_set(x_11, 3, x_137);
lean_ctor_set(x_11, 0, x_138);
x_139 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_133);
lean_ctor_set(x_10, 1, x_132);
lean_ctor_set(x_10, 0, x_139);
return x_10;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_ctor_get(x_28, 1);
x_141 = lean_ctor_get(x_28, 2);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_28);
x_142 = lean_box(1);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_129);
lean_ctor_set(x_144, 2, x_130);
lean_ctor_set(x_144, 3, x_142);
lean_ctor_set(x_144, 4, x_142);
lean_ctor_set(x_11, 4, x_142);
lean_ctor_set(x_11, 3, x_142);
lean_ctor_set(x_11, 0, x_143);
x_145 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_144);
lean_ctor_set(x_10, 2, x_141);
lean_ctor_set(x_10, 1, x_140);
lean_ctor_set(x_10, 0, x_145);
return x_10;
}
}
}
else
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_25);
x_146 = lean_ctor_get(x_31, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_31, 1);
lean_inc(x_147);
lean_dec(x_31);
x_148 = lean_box(1);
x_149 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_11, 4, x_148);
lean_ctor_set(x_11, 3, x_148);
lean_ctor_set(x_11, 2, x_147);
lean_ctor_set(x_11, 1, x_146);
lean_ctor_set(x_11, 0, x_149);
x_150 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_29);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_27);
lean_ctor_set(x_10, 1, x_26);
lean_ctor_set(x_10, 0, x_150);
return x_10;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_31, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_31, 1);
lean_inc(x_152);
lean_dec(x_31);
lean_ctor_set(x_11, 3, x_29);
x_153 = lean_box(1);
x_154 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_153);
lean_ctor_set(x_10, 2, x_152);
lean_ctor_set(x_10, 1, x_151);
lean_ctor_set(x_10, 0, x_154);
return x_10;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_25);
x_155 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_26, x_27, x_28, x_29, lean_box(0), lean_box(0), lean_box(0));
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 2);
lean_inc(x_158);
lean_dec(x_155);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_ctor_set(x_11, 4, x_24);
lean_ctor_set(x_11, 3, x_23);
lean_ctor_set(x_11, 2, x_22);
lean_ctor_set(x_11, 1, x_21);
lean_ctor_set(x_11, 0, x_20);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_unsigned_to_nat(3u);
x_161 = lean_nat_mul(x_160, x_159);
x_162 = lean_nat_dec_lt(x_161, x_20);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_4);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_nat_add(x_163, x_20);
lean_dec(x_20);
x_165 = lean_nat_add(x_164, x_159);
lean_dec(x_159);
lean_dec(x_164);
lean_ctor_set(x_10, 4, x_158);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_165);
return x_10;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_dec(x_11);
x_166 = lean_ctor_get(x_23, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_24, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_24, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_24, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_24, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_24, 4);
lean_inc(x_171);
x_172 = lean_unsigned_to_nat(2u);
x_173 = lean_nat_mul(x_172, x_166);
x_174 = lean_nat_dec_lt(x_167, x_173);
lean_dec(x_173);
if (x_174 == 0)
{
uint8_t x_175; 
lean_dec(x_167);
lean_free_object(x_10);
lean_free_object(x_4);
x_175 = !lean_is_exclusive(x_24);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_176 = lean_ctor_get(x_24, 4);
lean_dec(x_176);
x_177 = lean_ctor_get(x_24, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_24, 2);
lean_dec(x_178);
x_179 = lean_ctor_get(x_24, 1);
lean_dec(x_179);
x_180 = lean_ctor_get(x_24, 0);
lean_dec(x_180);
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_nat_add(x_181, x_20);
lean_dec(x_20);
x_183 = lean_nat_add(x_182, x_159);
lean_dec(x_182);
x_184 = lean_nat_add(x_181, x_166);
lean_dec(x_166);
x_185 = lean_nat_add(x_181, x_159);
lean_dec(x_159);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_170, 0);
lean_inc(x_186);
x_187 = lean_nat_add(x_184, x_186);
lean_dec(x_186);
lean_dec(x_184);
lean_inc(x_23);
lean_ctor_set(x_24, 4, x_170);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_187);
x_188 = !lean_is_exclusive(x_23);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_23, 4);
lean_dec(x_189);
x_190 = lean_ctor_get(x_23, 3);
lean_dec(x_190);
x_191 = lean_ctor_get(x_23, 2);
lean_dec(x_191);
x_192 = lean_ctor_get(x_23, 1);
lean_dec(x_192);
x_193 = lean_ctor_get(x_23, 0);
lean_dec(x_193);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_171, 0);
lean_inc(x_194);
x_195 = lean_nat_add(x_185, x_194);
lean_dec(x_194);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_195);
x_196 = !lean_is_exclusive(x_158);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_158, 4);
lean_dec(x_197);
x_198 = lean_ctor_get(x_158, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_158, 2);
lean_dec(x_199);
x_200 = lean_ctor_get(x_158, 1);
lean_dec(x_200);
x_201 = lean_ctor_get(x_158, 0);
lean_dec(x_201);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_202; 
lean_dec(x_158);
x_202 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_202, 0, x_183);
lean_ctor_set(x_202, 1, x_168);
lean_ctor_set(x_202, 2, x_169);
lean_ctor_set(x_202, 3, x_24);
lean_ctor_set(x_202, 4, x_23);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_203 = lean_unsigned_to_nat(0u);
x_204 = lean_nat_add(x_185, x_203);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_204);
x_205 = !lean_is_exclusive(x_158);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_158, 4);
lean_dec(x_206);
x_207 = lean_ctor_get(x_158, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_158, 2);
lean_dec(x_208);
x_209 = lean_ctor_get(x_158, 1);
lean_dec(x_209);
x_210 = lean_ctor_get(x_158, 0);
lean_dec(x_210);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_211; 
lean_dec(x_158);
x_211 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_211, 0, x_183);
lean_ctor_set(x_211, 1, x_168);
lean_ctor_set(x_211, 2, x_169);
lean_ctor_set(x_211, 3, x_24);
lean_ctor_set(x_211, 4, x_23);
return x_211;
}
}
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_ctor_get(x_171, 0);
lean_inc(x_212);
x_213 = lean_nat_add(x_185, x_212);
lean_dec(x_212);
lean_dec(x_185);
lean_inc(x_158);
x_214 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_156);
lean_ctor_set(x_214, 2, x_157);
lean_ctor_set(x_214, 3, x_171);
lean_ctor_set(x_214, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_215 = x_158;
} else {
 lean_dec_ref(x_158);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(0, 5, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_183);
lean_ctor_set(x_216, 1, x_168);
lean_ctor_set(x_216, 2, x_169);
lean_ctor_set(x_216, 3, x_24);
lean_ctor_set(x_216, 4, x_214);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_unsigned_to_nat(0u);
x_218 = lean_nat_add(x_185, x_217);
lean_dec(x_185);
lean_inc(x_158);
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_156);
lean_ctor_set(x_219, 2, x_157);
lean_ctor_set(x_219, 3, x_171);
lean_ctor_set(x_219, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_220 = x_158;
} else {
 lean_dec_ref(x_158);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 5, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_183);
lean_ctor_set(x_221, 1, x_168);
lean_ctor_set(x_221, 2, x_169);
lean_ctor_set(x_221, 3, x_24);
lean_ctor_set(x_221, 4, x_219);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_unsigned_to_nat(0u);
x_223 = lean_nat_add(x_184, x_222);
lean_dec(x_184);
lean_inc(x_23);
lean_ctor_set(x_24, 4, x_170);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_223);
x_224 = !lean_is_exclusive(x_23);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_23, 4);
lean_dec(x_225);
x_226 = lean_ctor_get(x_23, 3);
lean_dec(x_226);
x_227 = lean_ctor_get(x_23, 2);
lean_dec(x_227);
x_228 = lean_ctor_get(x_23, 1);
lean_dec(x_228);
x_229 = lean_ctor_get(x_23, 0);
lean_dec(x_229);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_230 = lean_ctor_get(x_171, 0);
lean_inc(x_230);
x_231 = lean_nat_add(x_185, x_230);
lean_dec(x_230);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_231);
x_232 = !lean_is_exclusive(x_158);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_158, 4);
lean_dec(x_233);
x_234 = lean_ctor_get(x_158, 3);
lean_dec(x_234);
x_235 = lean_ctor_get(x_158, 2);
lean_dec(x_235);
x_236 = lean_ctor_get(x_158, 1);
lean_dec(x_236);
x_237 = lean_ctor_get(x_158, 0);
lean_dec(x_237);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_238; 
lean_dec(x_158);
x_238 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_238, 0, x_183);
lean_ctor_set(x_238, 1, x_168);
lean_ctor_set(x_238, 2, x_169);
lean_ctor_set(x_238, 3, x_24);
lean_ctor_set(x_238, 4, x_23);
return x_238;
}
}
else
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_nat_add(x_185, x_222);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_239);
x_240 = !lean_is_exclusive(x_158);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = lean_ctor_get(x_158, 4);
lean_dec(x_241);
x_242 = lean_ctor_get(x_158, 3);
lean_dec(x_242);
x_243 = lean_ctor_get(x_158, 2);
lean_dec(x_243);
x_244 = lean_ctor_get(x_158, 1);
lean_dec(x_244);
x_245 = lean_ctor_get(x_158, 0);
lean_dec(x_245);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_246; 
lean_dec(x_158);
x_246 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_246, 0, x_183);
lean_ctor_set(x_246, 1, x_168);
lean_ctor_set(x_246, 2, x_169);
lean_ctor_set(x_246, 3, x_24);
lean_ctor_set(x_246, 4, x_23);
return x_246;
}
}
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = lean_ctor_get(x_171, 0);
lean_inc(x_247);
x_248 = lean_nat_add(x_185, x_247);
lean_dec(x_247);
lean_dec(x_185);
lean_inc(x_158);
x_249 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_156);
lean_ctor_set(x_249, 2, x_157);
lean_ctor_set(x_249, 3, x_171);
lean_ctor_set(x_249, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_250 = x_158;
} else {
 lean_dec_ref(x_158);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 5, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_183);
lean_ctor_set(x_251, 1, x_168);
lean_ctor_set(x_251, 2, x_169);
lean_ctor_set(x_251, 3, x_24);
lean_ctor_set(x_251, 4, x_249);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_nat_add(x_185, x_222);
lean_dec(x_185);
lean_inc(x_158);
x_253 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_156);
lean_ctor_set(x_253, 2, x_157);
lean_ctor_set(x_253, 3, x_171);
lean_ctor_set(x_253, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_254 = x_158;
} else {
 lean_dec_ref(x_158);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(0, 5, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_183);
lean_ctor_set(x_255, 1, x_168);
lean_ctor_set(x_255, 2, x_169);
lean_ctor_set(x_255, 3, x_24);
lean_ctor_set(x_255, 4, x_253);
return x_255;
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_24);
x_256 = lean_unsigned_to_nat(1u);
x_257 = lean_nat_add(x_256, x_20);
lean_dec(x_20);
x_258 = lean_nat_add(x_257, x_159);
lean_dec(x_257);
x_259 = lean_nat_add(x_256, x_166);
lean_dec(x_166);
x_260 = lean_nat_add(x_256, x_159);
lean_dec(x_159);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_170, 0);
lean_inc(x_261);
x_262 = lean_nat_add(x_259, x_261);
lean_dec(x_261);
lean_dec(x_259);
lean_inc(x_23);
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_21);
lean_ctor_set(x_263, 2, x_22);
lean_ctor_set(x_263, 3, x_23);
lean_ctor_set(x_263, 4, x_170);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 x_264 = x_23;
} else {
 lean_dec_ref(x_23);
 x_264 = lean_box(0);
}
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_265 = lean_ctor_get(x_171, 0);
lean_inc(x_265);
x_266 = lean_nat_add(x_260, x_265);
lean_dec(x_265);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_264)) {
 x_267 = lean_alloc_ctor(0, 5, 0);
} else {
 x_267 = x_264;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_156);
lean_ctor_set(x_267, 2, x_157);
lean_ctor_set(x_267, 3, x_171);
lean_ctor_set(x_267, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_268 = x_158;
} else {
 lean_dec_ref(x_158);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(0, 5, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_258);
lean_ctor_set(x_269, 1, x_168);
lean_ctor_set(x_269, 2, x_169);
lean_ctor_set(x_269, 3, x_263);
lean_ctor_set(x_269, 4, x_267);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_unsigned_to_nat(0u);
x_271 = lean_nat_add(x_260, x_270);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_264)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_264;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_156);
lean_ctor_set(x_272, 2, x_157);
lean_ctor_set(x_272, 3, x_171);
lean_ctor_set(x_272, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_273 = x_158;
} else {
 lean_dec_ref(x_158);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 5, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_258);
lean_ctor_set(x_274, 1, x_168);
lean_ctor_set(x_274, 2, x_169);
lean_ctor_set(x_274, 3, x_263);
lean_ctor_set(x_274, 4, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_unsigned_to_nat(0u);
x_276 = lean_nat_add(x_259, x_275);
lean_dec(x_259);
lean_inc(x_23);
x_277 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_21);
lean_ctor_set(x_277, 2, x_22);
lean_ctor_set(x_277, 3, x_23);
lean_ctor_set(x_277, 4, x_170);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 x_278 = x_23;
} else {
 lean_dec_ref(x_23);
 x_278 = lean_box(0);
}
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_ctor_get(x_171, 0);
lean_inc(x_279);
x_280 = lean_nat_add(x_260, x_279);
lean_dec(x_279);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_278)) {
 x_281 = lean_alloc_ctor(0, 5, 0);
} else {
 x_281 = x_278;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_156);
lean_ctor_set(x_281, 2, x_157);
lean_ctor_set(x_281, 3, x_171);
lean_ctor_set(x_281, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_282 = x_158;
} else {
 lean_dec_ref(x_158);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(0, 5, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_258);
lean_ctor_set(x_283, 1, x_168);
lean_ctor_set(x_283, 2, x_169);
lean_ctor_set(x_283, 3, x_277);
lean_ctor_set(x_283, 4, x_281);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_284 = lean_nat_add(x_260, x_275);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_278)) {
 x_285 = lean_alloc_ctor(0, 5, 0);
} else {
 x_285 = x_278;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_156);
lean_ctor_set(x_285, 2, x_157);
lean_ctor_set(x_285, 3, x_171);
lean_ctor_set(x_285, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_286 = x_158;
} else {
 lean_dec_ref(x_158);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(0, 5, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_258);
lean_ctor_set(x_287, 1, x_168);
lean_ctor_set(x_287, 2, x_169);
lean_ctor_set(x_287, 3, x_277);
lean_ctor_set(x_287, 4, x_285);
return x_287;
}
}
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_166);
x_288 = lean_unsigned_to_nat(1u);
x_289 = lean_nat_add(x_288, x_20);
lean_dec(x_20);
x_290 = lean_nat_add(x_289, x_159);
lean_dec(x_289);
x_291 = lean_nat_add(x_288, x_159);
lean_dec(x_159);
x_292 = lean_nat_add(x_291, x_167);
lean_dec(x_167);
lean_dec(x_291);
lean_ctor_set(x_10, 4, x_158);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_292);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_290);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_24, 0);
lean_inc(x_293);
x_294 = lean_unsigned_to_nat(1u);
x_295 = lean_nat_add(x_294, x_20);
lean_dec(x_20);
x_296 = lean_nat_add(x_294, x_293);
lean_dec(x_293);
x_297 = lean_box(1);
lean_ctor_set(x_10, 4, x_297);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_296);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_295);
return x_4;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_20);
x_298 = lean_box(1);
x_299 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_10, 4, x_298);
lean_ctor_set(x_10, 3, x_298);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_299);
x_300 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_300);
return x_4;
}
}
else
{
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_301; 
lean_dec(x_11);
x_301 = !lean_is_exclusive(x_24);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_302 = lean_ctor_get(x_24, 1);
x_303 = lean_ctor_get(x_24, 2);
x_304 = lean_ctor_get(x_24, 4);
lean_dec(x_304);
x_305 = lean_ctor_get(x_24, 3);
lean_dec(x_305);
x_306 = lean_ctor_get(x_24, 0);
lean_dec(x_306);
x_307 = lean_box(1);
x_308 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_24, 4, x_307);
lean_ctor_set(x_24, 3, x_307);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_308);
lean_ctor_set(x_10, 4, x_307);
lean_ctor_set(x_10, 3, x_307);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_308);
x_309 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_24);
lean_ctor_set(x_4, 2, x_303);
lean_ctor_set(x_4, 1, x_302);
lean_ctor_set(x_4, 0, x_309);
return x_4;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_310 = lean_ctor_get(x_24, 1);
x_311 = lean_ctor_get(x_24, 2);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_24);
x_312 = lean_box(1);
x_313 = lean_unsigned_to_nat(1u);
x_314 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_21);
lean_ctor_set(x_314, 2, x_22);
lean_ctor_set(x_314, 3, x_312);
lean_ctor_set(x_314, 4, x_312);
lean_ctor_set(x_10, 4, x_312);
lean_ctor_set(x_10, 3, x_312);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_313);
x_315 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_314);
lean_ctor_set(x_4, 2, x_311);
lean_ctor_set(x_4, 1, x_310);
lean_ctor_set(x_4, 0, x_315);
return x_4;
}
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_4);
x_316 = lean_box(1);
x_317 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_316);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_317);
return x_10;
}
}
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_318 = lean_ctor_get(x_10, 0);
x_319 = lean_ctor_get(x_10, 1);
x_320 = lean_ctor_get(x_10, 2);
x_321 = lean_ctor_get(x_10, 3);
x_322 = lean_ctor_get(x_10, 4);
x_323 = lean_ctor_get(x_11, 0);
x_324 = lean_ctor_get(x_11, 1);
x_325 = lean_ctor_get(x_11, 2);
x_326 = lean_ctor_get(x_11, 3);
x_327 = lean_ctor_get(x_11, 4);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_11);
x_328 = lean_nat_dec_lt(x_318, x_323);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_318);
x_329 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_319, x_320, x_321, x_322, lean_box(0), lean_box(0), lean_box(0));
x_330 = lean_ctor_get(x_329, 2);
lean_inc(x_330);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_331 = lean_ctor_get(x_329, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_dec(x_329);
x_333 = lean_ctor_get(x_330, 0);
lean_inc(x_333);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
x_334 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_334, 0, x_323);
lean_ctor_set(x_334, 1, x_324);
lean_ctor_set(x_334, 2, x_325);
lean_ctor_set(x_334, 3, x_326);
lean_ctor_set(x_334, 4, x_327);
x_335 = lean_unsigned_to_nat(3u);
x_336 = lean_nat_mul(x_335, x_333);
x_337 = lean_nat_dec_lt(x_336, x_323);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_free_object(x_4);
x_338 = lean_unsigned_to_nat(1u);
x_339 = lean_nat_add(x_338, x_333);
lean_dec(x_333);
x_340 = lean_nat_add(x_339, x_323);
lean_dec(x_323);
lean_dec(x_339);
lean_ctor_set(x_10, 4, x_334);
lean_ctor_set(x_10, 3, x_330);
lean_ctor_set(x_10, 2, x_332);
lean_ctor_set(x_10, 1, x_331);
lean_ctor_set(x_10, 0, x_340);
return x_10;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
lean_dec(x_334);
x_341 = lean_ctor_get(x_326, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_326, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_326, 2);
lean_inc(x_343);
x_344 = lean_ctor_get(x_326, 3);
lean_inc(x_344);
x_345 = lean_ctor_get(x_326, 4);
lean_inc(x_345);
x_346 = lean_ctor_get(x_327, 0);
lean_inc(x_346);
x_347 = lean_unsigned_to_nat(2u);
x_348 = lean_nat_mul(x_347, x_346);
x_349 = lean_nat_dec_lt(x_341, x_348);
lean_dec(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_341);
lean_free_object(x_4);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 x_350 = x_326;
} else {
 lean_dec_ref(x_326);
 x_350 = lean_box(0);
}
x_351 = lean_unsigned_to_nat(1u);
x_352 = lean_nat_add(x_351, x_333);
lean_dec(x_333);
x_353 = lean_nat_add(x_352, x_323);
lean_dec(x_323);
x_354 = lean_nat_add(x_351, x_346);
lean_dec(x_346);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_355 = lean_ctor_get(x_344, 0);
lean_inc(x_355);
x_356 = lean_nat_add(x_352, x_355);
lean_dec(x_355);
lean_dec(x_352);
lean_inc(x_330);
if (lean_is_scalar(x_350)) {
 x_357 = lean_alloc_ctor(0, 5, 0);
} else {
 x_357 = x_350;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_331);
lean_ctor_set(x_357, 2, x_332);
lean_ctor_set(x_357, 3, x_330);
lean_ctor_set(x_357, 4, x_344);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 x_358 = x_330;
} else {
 lean_dec_ref(x_330);
 x_358 = lean_box(0);
}
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_345, 0);
lean_inc(x_359);
x_360 = lean_nat_add(x_354, x_359);
lean_dec(x_359);
lean_dec(x_354);
if (lean_is_scalar(x_358)) {
 x_361 = lean_alloc_ctor(0, 5, 0);
} else {
 x_361 = x_358;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_324);
lean_ctor_set(x_361, 2, x_325);
lean_ctor_set(x_361, 3, x_345);
lean_ctor_set(x_361, 4, x_327);
lean_ctor_set(x_10, 4, x_361);
lean_ctor_set(x_10, 3, x_357);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_unsigned_to_nat(0u);
x_363 = lean_nat_add(x_354, x_362);
lean_dec(x_354);
if (lean_is_scalar(x_358)) {
 x_364 = lean_alloc_ctor(0, 5, 0);
} else {
 x_364 = x_358;
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_324);
lean_ctor_set(x_364, 2, x_325);
lean_ctor_set(x_364, 3, x_345);
lean_ctor_set(x_364, 4, x_327);
lean_ctor_set(x_10, 4, x_364);
lean_ctor_set(x_10, 3, x_357);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = lean_unsigned_to_nat(0u);
x_366 = lean_nat_add(x_352, x_365);
lean_dec(x_352);
lean_inc(x_330);
if (lean_is_scalar(x_350)) {
 x_367 = lean_alloc_ctor(0, 5, 0);
} else {
 x_367 = x_350;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_331);
lean_ctor_set(x_367, 2, x_332);
lean_ctor_set(x_367, 3, x_330);
lean_ctor_set(x_367, 4, x_344);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 x_368 = x_330;
} else {
 lean_dec_ref(x_330);
 x_368 = lean_box(0);
}
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_345, 0);
lean_inc(x_369);
x_370 = lean_nat_add(x_354, x_369);
lean_dec(x_369);
lean_dec(x_354);
if (lean_is_scalar(x_368)) {
 x_371 = lean_alloc_ctor(0, 5, 0);
} else {
 x_371 = x_368;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_324);
lean_ctor_set(x_371, 2, x_325);
lean_ctor_set(x_371, 3, x_345);
lean_ctor_set(x_371, 4, x_327);
lean_ctor_set(x_10, 4, x_371);
lean_ctor_set(x_10, 3, x_367);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_nat_add(x_354, x_365);
lean_dec(x_354);
if (lean_is_scalar(x_368)) {
 x_373 = lean_alloc_ctor(0, 5, 0);
} else {
 x_373 = x_368;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_324);
lean_ctor_set(x_373, 2, x_325);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set(x_373, 4, x_327);
lean_ctor_set(x_10, 4, x_373);
lean_ctor_set(x_10, 3, x_367);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
x_374 = lean_unsigned_to_nat(1u);
x_375 = lean_nat_add(x_374, x_333);
lean_dec(x_333);
x_376 = lean_nat_add(x_375, x_323);
lean_dec(x_323);
x_377 = lean_nat_add(x_375, x_341);
lean_dec(x_341);
lean_dec(x_375);
lean_ctor_set(x_10, 4, x_326);
lean_ctor_set(x_10, 3, x_330);
lean_ctor_set(x_10, 2, x_332);
lean_ctor_set(x_10, 1, x_331);
lean_ctor_set(x_10, 0, x_377);
lean_ctor_set(x_4, 4, x_327);
lean_ctor_set(x_4, 2, x_325);
lean_ctor_set(x_4, 1, x_324);
lean_ctor_set(x_4, 0, x_376);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_326) == 0)
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_378 = lean_ctor_get(x_329, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_329, 1);
lean_inc(x_379);
lean_dec(x_329);
x_380 = lean_ctor_get(x_326, 0);
lean_inc(x_380);
x_381 = lean_unsigned_to_nat(1u);
x_382 = lean_nat_add(x_381, x_323);
lean_dec(x_323);
x_383 = lean_nat_add(x_381, x_380);
lean_dec(x_380);
x_384 = lean_box(1);
x_385 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_378);
lean_ctor_set(x_385, 2, x_379);
lean_ctor_set(x_385, 3, x_384);
lean_ctor_set(x_385, 4, x_326);
lean_ctor_set(x_10, 4, x_327);
lean_ctor_set(x_10, 3, x_385);
lean_ctor_set(x_10, 2, x_325);
lean_ctor_set(x_10, 1, x_324);
lean_ctor_set(x_10, 0, x_382);
return x_10;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_323);
x_386 = lean_ctor_get(x_329, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_329, 1);
lean_inc(x_387);
lean_dec(x_329);
x_388 = lean_ctor_get(x_326, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_326, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 x_390 = x_326;
} else {
 lean_dec_ref(x_326);
 x_390 = lean_box(0);
}
x_391 = lean_box(1);
x_392 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_390)) {
 x_393 = lean_alloc_ctor(0, 5, 0);
} else {
 x_393 = x_390;
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_386);
lean_ctor_set(x_393, 2, x_387);
lean_ctor_set(x_393, 3, x_391);
lean_ctor_set(x_393, 4, x_391);
x_394 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_324);
lean_ctor_set(x_394, 2, x_325);
lean_ctor_set(x_394, 3, x_391);
lean_ctor_set(x_394, 4, x_391);
x_395 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_394);
lean_ctor_set(x_10, 3, x_393);
lean_ctor_set(x_10, 2, x_389);
lean_ctor_set(x_10, 1, x_388);
lean_ctor_set(x_10, 0, x_395);
return x_10;
}
}
else
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_323);
x_396 = lean_ctor_get(x_329, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_329, 1);
lean_inc(x_397);
lean_dec(x_329);
x_398 = lean_box(1);
x_399 = lean_unsigned_to_nat(1u);
x_400 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_396);
lean_ctor_set(x_400, 2, x_397);
lean_ctor_set(x_400, 3, x_398);
lean_ctor_set(x_400, 4, x_398);
x_401 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_327);
lean_ctor_set(x_10, 3, x_400);
lean_ctor_set(x_10, 2, x_325);
lean_ctor_set(x_10, 1, x_324);
lean_ctor_set(x_10, 0, x_401);
return x_10;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_402 = lean_ctor_get(x_329, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_329, 1);
lean_inc(x_403);
lean_dec(x_329);
x_404 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_404, 0, x_323);
lean_ctor_set(x_404, 1, x_324);
lean_ctor_set(x_404, 2, x_325);
lean_ctor_set(x_404, 3, x_327);
lean_ctor_set(x_404, 4, x_327);
x_405 = lean_box(1);
x_406 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_404);
lean_ctor_set(x_10, 3, x_405);
lean_ctor_set(x_10, 2, x_403);
lean_ctor_set(x_10, 1, x_402);
lean_ctor_set(x_10, 0, x_406);
return x_10;
}
}
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_323);
x_407 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_324, x_325, x_326, x_327, lean_box(0), lean_box(0), lean_box(0));
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_407, 2);
lean_inc(x_410);
lean_dec(x_407);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
x_411 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_411, 0, x_318);
lean_ctor_set(x_411, 1, x_319);
lean_ctor_set(x_411, 2, x_320);
lean_ctor_set(x_411, 3, x_321);
lean_ctor_set(x_411, 4, x_322);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_412 = lean_ctor_get(x_410, 0);
lean_inc(x_412);
x_413 = lean_unsigned_to_nat(3u);
x_414 = lean_nat_mul(x_413, x_412);
x_415 = lean_nat_dec_lt(x_414, x_318);
lean_dec(x_414);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_free_object(x_4);
x_416 = lean_unsigned_to_nat(1u);
x_417 = lean_nat_add(x_416, x_318);
lean_dec(x_318);
x_418 = lean_nat_add(x_417, x_412);
lean_dec(x_412);
lean_dec(x_417);
lean_ctor_set(x_10, 4, x_410);
lean_ctor_set(x_10, 3, x_411);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_418);
return x_10;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_dec(x_411);
x_419 = lean_ctor_get(x_321, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_322, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_322, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_322, 2);
lean_inc(x_422);
x_423 = lean_ctor_get(x_322, 3);
lean_inc(x_423);
x_424 = lean_ctor_get(x_322, 4);
lean_inc(x_424);
x_425 = lean_unsigned_to_nat(2u);
x_426 = lean_nat_mul(x_425, x_419);
x_427 = lean_nat_dec_lt(x_420, x_426);
lean_dec(x_426);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_420);
lean_free_object(x_10);
lean_free_object(x_4);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 lean_ctor_release(x_322, 4);
 x_428 = x_322;
} else {
 lean_dec_ref(x_322);
 x_428 = lean_box(0);
}
x_429 = lean_unsigned_to_nat(1u);
x_430 = lean_nat_add(x_429, x_318);
lean_dec(x_318);
x_431 = lean_nat_add(x_430, x_412);
lean_dec(x_430);
x_432 = lean_nat_add(x_429, x_419);
lean_dec(x_419);
x_433 = lean_nat_add(x_429, x_412);
lean_dec(x_412);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = lean_ctor_get(x_423, 0);
lean_inc(x_434);
x_435 = lean_nat_add(x_432, x_434);
lean_dec(x_434);
lean_dec(x_432);
lean_inc(x_321);
if (lean_is_scalar(x_428)) {
 x_436 = lean_alloc_ctor(0, 5, 0);
} else {
 x_436 = x_428;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_319);
lean_ctor_set(x_436, 2, x_320);
lean_ctor_set(x_436, 3, x_321);
lean_ctor_set(x_436, 4, x_423);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 x_437 = x_321;
} else {
 lean_dec_ref(x_321);
 x_437 = lean_box(0);
}
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_438 = lean_ctor_get(x_424, 0);
lean_inc(x_438);
x_439 = lean_nat_add(x_433, x_438);
lean_dec(x_438);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_437)) {
 x_440 = lean_alloc_ctor(0, 5, 0);
} else {
 x_440 = x_437;
}
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_408);
lean_ctor_set(x_440, 2, x_409);
lean_ctor_set(x_440, 3, x_424);
lean_ctor_set(x_440, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_441 = x_410;
} else {
 lean_dec_ref(x_410);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(0, 5, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_431);
lean_ctor_set(x_442, 1, x_421);
lean_ctor_set(x_442, 2, x_422);
lean_ctor_set(x_442, 3, x_436);
lean_ctor_set(x_442, 4, x_440);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_443 = lean_unsigned_to_nat(0u);
x_444 = lean_nat_add(x_433, x_443);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(0, 5, 0);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_408);
lean_ctor_set(x_445, 2, x_409);
lean_ctor_set(x_445, 3, x_424);
lean_ctor_set(x_445, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_446 = x_410;
} else {
 lean_dec_ref(x_410);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(0, 5, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_431);
lean_ctor_set(x_447, 1, x_421);
lean_ctor_set(x_447, 2, x_422);
lean_ctor_set(x_447, 3, x_436);
lean_ctor_set(x_447, 4, x_445);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_448 = lean_unsigned_to_nat(0u);
x_449 = lean_nat_add(x_432, x_448);
lean_dec(x_432);
lean_inc(x_321);
if (lean_is_scalar(x_428)) {
 x_450 = lean_alloc_ctor(0, 5, 0);
} else {
 x_450 = x_428;
}
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_319);
lean_ctor_set(x_450, 2, x_320);
lean_ctor_set(x_450, 3, x_321);
lean_ctor_set(x_450, 4, x_423);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 x_451 = x_321;
} else {
 lean_dec_ref(x_321);
 x_451 = lean_box(0);
}
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_452 = lean_ctor_get(x_424, 0);
lean_inc(x_452);
x_453 = lean_nat_add(x_433, x_452);
lean_dec(x_452);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_451)) {
 x_454 = lean_alloc_ctor(0, 5, 0);
} else {
 x_454 = x_451;
}
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_408);
lean_ctor_set(x_454, 2, x_409);
lean_ctor_set(x_454, 3, x_424);
lean_ctor_set(x_454, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_455 = x_410;
} else {
 lean_dec_ref(x_410);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(0, 5, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_431);
lean_ctor_set(x_456, 1, x_421);
lean_ctor_set(x_456, 2, x_422);
lean_ctor_set(x_456, 3, x_450);
lean_ctor_set(x_456, 4, x_454);
return x_456;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_457 = lean_nat_add(x_433, x_448);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_451)) {
 x_458 = lean_alloc_ctor(0, 5, 0);
} else {
 x_458 = x_451;
}
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_408);
lean_ctor_set(x_458, 2, x_409);
lean_ctor_set(x_458, 3, x_424);
lean_ctor_set(x_458, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_459 = x_410;
} else {
 lean_dec_ref(x_410);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(0, 5, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_431);
lean_ctor_set(x_460, 1, x_421);
lean_ctor_set(x_460, 2, x_422);
lean_ctor_set(x_460, 3, x_450);
lean_ctor_set(x_460, 4, x_458);
return x_460;
}
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_419);
x_461 = lean_unsigned_to_nat(1u);
x_462 = lean_nat_add(x_461, x_318);
lean_dec(x_318);
x_463 = lean_nat_add(x_462, x_412);
lean_dec(x_462);
x_464 = lean_nat_add(x_461, x_412);
lean_dec(x_412);
x_465 = lean_nat_add(x_464, x_420);
lean_dec(x_420);
lean_dec(x_464);
lean_ctor_set(x_10, 4, x_410);
lean_ctor_set(x_10, 3, x_322);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_465);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_463);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_321) == 0)
{
lean_dec(x_411);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_466 = lean_ctor_get(x_322, 0);
lean_inc(x_466);
x_467 = lean_unsigned_to_nat(1u);
x_468 = lean_nat_add(x_467, x_318);
lean_dec(x_318);
x_469 = lean_nat_add(x_467, x_466);
lean_dec(x_466);
x_470 = lean_box(1);
lean_ctor_set(x_10, 4, x_470);
lean_ctor_set(x_10, 3, x_322);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_469);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_468);
return x_4;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_318);
x_471 = lean_box(1);
x_472 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_10, 4, x_471);
lean_ctor_set(x_10, 3, x_471);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_472);
x_473 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_473);
return x_4;
}
}
else
{
lean_dec(x_318);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec(x_411);
x_474 = lean_ctor_get(x_322, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_322, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 lean_ctor_release(x_322, 4);
 x_476 = x_322;
} else {
 lean_dec_ref(x_322);
 x_476 = lean_box(0);
}
x_477 = lean_box(1);
x_478 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_476)) {
 x_479 = lean_alloc_ctor(0, 5, 0);
} else {
 x_479 = x_476;
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_319);
lean_ctor_set(x_479, 2, x_320);
lean_ctor_set(x_479, 3, x_477);
lean_ctor_set(x_479, 4, x_477);
lean_ctor_set(x_10, 4, x_477);
lean_ctor_set(x_10, 3, x_477);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_478);
x_480 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_479);
lean_ctor_set(x_4, 2, x_475);
lean_ctor_set(x_4, 1, x_474);
lean_ctor_set(x_4, 0, x_480);
return x_4;
}
else
{
lean_object* x_481; lean_object* x_482; 
lean_dec(x_320);
lean_dec(x_319);
lean_free_object(x_4);
x_481 = lean_box(1);
x_482 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_481);
lean_ctor_set(x_10, 3, x_411);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_482);
return x_10;
}
}
}
}
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; 
x_483 = lean_ctor_get(x_10, 0);
x_484 = lean_ctor_get(x_10, 1);
x_485 = lean_ctor_get(x_10, 2);
x_486 = lean_ctor_get(x_10, 3);
x_487 = lean_ctor_get(x_10, 4);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_10);
x_488 = lean_ctor_get(x_11, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_11, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_11, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_11, 3);
lean_inc(x_491);
x_492 = lean_ctor_get(x_11, 4);
lean_inc(x_492);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_493 = x_11;
} else {
 lean_dec_ref(x_11);
 x_493 = lean_box(0);
}
x_494 = lean_nat_dec_lt(x_483, x_488);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; 
lean_dec(x_483);
x_495 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_484, x_485, x_486, x_487, lean_box(0), lean_box(0), lean_box(0));
x_496 = lean_ctor_get(x_495, 2);
lean_inc(x_496);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_498);
lean_dec(x_495);
x_499 = lean_ctor_get(x_496, 0);
lean_inc(x_499);
lean_inc(x_492);
lean_inc(x_491);
lean_inc(x_490);
lean_inc(x_489);
lean_inc(x_488);
if (lean_is_scalar(x_493)) {
 x_500 = lean_alloc_ctor(0, 5, 0);
} else {
 x_500 = x_493;
}
lean_ctor_set(x_500, 0, x_488);
lean_ctor_set(x_500, 1, x_489);
lean_ctor_set(x_500, 2, x_490);
lean_ctor_set(x_500, 3, x_491);
lean_ctor_set(x_500, 4, x_492);
x_501 = lean_unsigned_to_nat(3u);
x_502 = lean_nat_mul(x_501, x_499);
x_503 = lean_nat_dec_lt(x_502, x_488);
lean_dec(x_502);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_492);
lean_dec(x_491);
lean_dec(x_490);
lean_dec(x_489);
lean_free_object(x_4);
x_504 = lean_unsigned_to_nat(1u);
x_505 = lean_nat_add(x_504, x_499);
lean_dec(x_499);
x_506 = lean_nat_add(x_505, x_488);
lean_dec(x_488);
lean_dec(x_505);
x_507 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_497);
lean_ctor_set(x_507, 2, x_498);
lean_ctor_set(x_507, 3, x_496);
lean_ctor_set(x_507, 4, x_500);
return x_507;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; 
lean_dec(x_500);
x_508 = lean_ctor_get(x_491, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_491, 1);
lean_inc(x_509);
x_510 = lean_ctor_get(x_491, 2);
lean_inc(x_510);
x_511 = lean_ctor_get(x_491, 3);
lean_inc(x_511);
x_512 = lean_ctor_get(x_491, 4);
lean_inc(x_512);
x_513 = lean_ctor_get(x_492, 0);
lean_inc(x_513);
x_514 = lean_unsigned_to_nat(2u);
x_515 = lean_nat_mul(x_514, x_513);
x_516 = lean_nat_dec_lt(x_508, x_515);
lean_dec(x_515);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_508);
lean_free_object(x_4);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 lean_ctor_release(x_491, 2);
 lean_ctor_release(x_491, 3);
 lean_ctor_release(x_491, 4);
 x_517 = x_491;
} else {
 lean_dec_ref(x_491);
 x_517 = lean_box(0);
}
x_518 = lean_unsigned_to_nat(1u);
x_519 = lean_nat_add(x_518, x_499);
lean_dec(x_499);
x_520 = lean_nat_add(x_519, x_488);
lean_dec(x_488);
x_521 = lean_nat_add(x_518, x_513);
lean_dec(x_513);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_522 = lean_ctor_get(x_511, 0);
lean_inc(x_522);
x_523 = lean_nat_add(x_519, x_522);
lean_dec(x_522);
lean_dec(x_519);
lean_inc(x_496);
if (lean_is_scalar(x_517)) {
 x_524 = lean_alloc_ctor(0, 5, 0);
} else {
 x_524 = x_517;
}
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_497);
lean_ctor_set(x_524, 2, x_498);
lean_ctor_set(x_524, 3, x_496);
lean_ctor_set(x_524, 4, x_511);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 lean_ctor_release(x_496, 2);
 lean_ctor_release(x_496, 3);
 lean_ctor_release(x_496, 4);
 x_525 = x_496;
} else {
 lean_dec_ref(x_496);
 x_525 = lean_box(0);
}
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_526 = lean_ctor_get(x_512, 0);
lean_inc(x_526);
x_527 = lean_nat_add(x_521, x_526);
lean_dec(x_526);
lean_dec(x_521);
if (lean_is_scalar(x_525)) {
 x_528 = lean_alloc_ctor(0, 5, 0);
} else {
 x_528 = x_525;
}
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_489);
lean_ctor_set(x_528, 2, x_490);
lean_ctor_set(x_528, 3, x_512);
lean_ctor_set(x_528, 4, x_492);
x_529 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_529, 0, x_520);
lean_ctor_set(x_529, 1, x_509);
lean_ctor_set(x_529, 2, x_510);
lean_ctor_set(x_529, 3, x_524);
lean_ctor_set(x_529, 4, x_528);
return x_529;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_530 = lean_unsigned_to_nat(0u);
x_531 = lean_nat_add(x_521, x_530);
lean_dec(x_521);
if (lean_is_scalar(x_525)) {
 x_532 = lean_alloc_ctor(0, 5, 0);
} else {
 x_532 = x_525;
}
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_489);
lean_ctor_set(x_532, 2, x_490);
lean_ctor_set(x_532, 3, x_512);
lean_ctor_set(x_532, 4, x_492);
x_533 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_533, 0, x_520);
lean_ctor_set(x_533, 1, x_509);
lean_ctor_set(x_533, 2, x_510);
lean_ctor_set(x_533, 3, x_524);
lean_ctor_set(x_533, 4, x_532);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_534 = lean_unsigned_to_nat(0u);
x_535 = lean_nat_add(x_519, x_534);
lean_dec(x_519);
lean_inc(x_496);
if (lean_is_scalar(x_517)) {
 x_536 = lean_alloc_ctor(0, 5, 0);
} else {
 x_536 = x_517;
}
lean_ctor_set(x_536, 0, x_535);
lean_ctor_set(x_536, 1, x_497);
lean_ctor_set(x_536, 2, x_498);
lean_ctor_set(x_536, 3, x_496);
lean_ctor_set(x_536, 4, x_511);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 lean_ctor_release(x_496, 2);
 lean_ctor_release(x_496, 3);
 lean_ctor_release(x_496, 4);
 x_537 = x_496;
} else {
 lean_dec_ref(x_496);
 x_537 = lean_box(0);
}
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_538 = lean_ctor_get(x_512, 0);
lean_inc(x_538);
x_539 = lean_nat_add(x_521, x_538);
lean_dec(x_538);
lean_dec(x_521);
if (lean_is_scalar(x_537)) {
 x_540 = lean_alloc_ctor(0, 5, 0);
} else {
 x_540 = x_537;
}
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_489);
lean_ctor_set(x_540, 2, x_490);
lean_ctor_set(x_540, 3, x_512);
lean_ctor_set(x_540, 4, x_492);
x_541 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_541, 0, x_520);
lean_ctor_set(x_541, 1, x_509);
lean_ctor_set(x_541, 2, x_510);
lean_ctor_set(x_541, 3, x_536);
lean_ctor_set(x_541, 4, x_540);
return x_541;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_nat_add(x_521, x_534);
lean_dec(x_521);
if (lean_is_scalar(x_537)) {
 x_543 = lean_alloc_ctor(0, 5, 0);
} else {
 x_543 = x_537;
}
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_489);
lean_ctor_set(x_543, 2, x_490);
lean_ctor_set(x_543, 3, x_512);
lean_ctor_set(x_543, 4, x_492);
x_544 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_544, 0, x_520);
lean_ctor_set(x_544, 1, x_509);
lean_ctor_set(x_544, 2, x_510);
lean_ctor_set(x_544, 3, x_536);
lean_ctor_set(x_544, 4, x_543);
return x_544;
}
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
x_545 = lean_unsigned_to_nat(1u);
x_546 = lean_nat_add(x_545, x_499);
lean_dec(x_499);
x_547 = lean_nat_add(x_546, x_488);
lean_dec(x_488);
x_548 = lean_nat_add(x_546, x_508);
lean_dec(x_508);
lean_dec(x_546);
x_549 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_497);
lean_ctor_set(x_549, 2, x_498);
lean_ctor_set(x_549, 3, x_496);
lean_ctor_set(x_549, 4, x_491);
lean_ctor_set(x_4, 4, x_492);
lean_ctor_set(x_4, 3, x_549);
lean_ctor_set(x_4, 2, x_490);
lean_ctor_set(x_4, 1, x_489);
lean_ctor_set(x_4, 0, x_547);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_491) == 0)
{
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_550 = lean_ctor_get(x_495, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_495, 1);
lean_inc(x_551);
lean_dec(x_495);
x_552 = lean_ctor_get(x_491, 0);
lean_inc(x_552);
x_553 = lean_unsigned_to_nat(1u);
x_554 = lean_nat_add(x_553, x_488);
lean_dec(x_488);
x_555 = lean_nat_add(x_553, x_552);
lean_dec(x_552);
x_556 = lean_box(1);
if (lean_is_scalar(x_493)) {
 x_557 = lean_alloc_ctor(0, 5, 0);
} else {
 x_557 = x_493;
}
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_550);
lean_ctor_set(x_557, 2, x_551);
lean_ctor_set(x_557, 3, x_556);
lean_ctor_set(x_557, 4, x_491);
x_558 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_558, 0, x_554);
lean_ctor_set(x_558, 1, x_489);
lean_ctor_set(x_558, 2, x_490);
lean_ctor_set(x_558, 3, x_557);
lean_ctor_set(x_558, 4, x_492);
return x_558;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_488);
x_559 = lean_ctor_get(x_495, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_495, 1);
lean_inc(x_560);
lean_dec(x_495);
x_561 = lean_ctor_get(x_491, 1);
lean_inc(x_561);
x_562 = lean_ctor_get(x_491, 2);
lean_inc(x_562);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 lean_ctor_release(x_491, 2);
 lean_ctor_release(x_491, 3);
 lean_ctor_release(x_491, 4);
 x_563 = x_491;
} else {
 lean_dec_ref(x_491);
 x_563 = lean_box(0);
}
x_564 = lean_box(1);
x_565 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_563)) {
 x_566 = lean_alloc_ctor(0, 5, 0);
} else {
 x_566 = x_563;
}
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_559);
lean_ctor_set(x_566, 2, x_560);
lean_ctor_set(x_566, 3, x_564);
lean_ctor_set(x_566, 4, x_564);
if (lean_is_scalar(x_493)) {
 x_567 = lean_alloc_ctor(0, 5, 0);
} else {
 x_567 = x_493;
}
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_489);
lean_ctor_set(x_567, 2, x_490);
lean_ctor_set(x_567, 3, x_564);
lean_ctor_set(x_567, 4, x_564);
x_568 = lean_unsigned_to_nat(3u);
x_569 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_561);
lean_ctor_set(x_569, 2, x_562);
lean_ctor_set(x_569, 3, x_566);
lean_ctor_set(x_569, 4, x_567);
return x_569;
}
}
else
{
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_488);
x_570 = lean_ctor_get(x_495, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_495, 1);
lean_inc(x_571);
lean_dec(x_495);
x_572 = lean_box(1);
x_573 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_493)) {
 x_574 = lean_alloc_ctor(0, 5, 0);
} else {
 x_574 = x_493;
}
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_570);
lean_ctor_set(x_574, 2, x_571);
lean_ctor_set(x_574, 3, x_572);
lean_ctor_set(x_574, 4, x_572);
x_575 = lean_unsigned_to_nat(3u);
x_576 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_489);
lean_ctor_set(x_576, 2, x_490);
lean_ctor_set(x_576, 3, x_574);
lean_ctor_set(x_576, 4, x_492);
return x_576;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_577 = lean_ctor_get(x_495, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_495, 1);
lean_inc(x_578);
lean_dec(x_495);
if (lean_is_scalar(x_493)) {
 x_579 = lean_alloc_ctor(0, 5, 0);
} else {
 x_579 = x_493;
}
lean_ctor_set(x_579, 0, x_488);
lean_ctor_set(x_579, 1, x_489);
lean_ctor_set(x_579, 2, x_490);
lean_ctor_set(x_579, 3, x_492);
lean_ctor_set(x_579, 4, x_492);
x_580 = lean_box(1);
x_581 = lean_unsigned_to_nat(2u);
x_582 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_577);
lean_ctor_set(x_582, 2, x_578);
lean_ctor_set(x_582, 3, x_580);
lean_ctor_set(x_582, 4, x_579);
return x_582;
}
}
}
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_488);
x_583 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_489, x_490, x_491, x_492, lean_box(0), lean_box(0), lean_box(0));
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
x_586 = lean_ctor_get(x_583, 2);
lean_inc(x_586);
lean_dec(x_583);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
if (lean_is_scalar(x_493)) {
 x_587 = lean_alloc_ctor(0, 5, 0);
} else {
 x_587 = x_493;
}
lean_ctor_set(x_587, 0, x_483);
lean_ctor_set(x_587, 1, x_484);
lean_ctor_set(x_587, 2, x_485);
lean_ctor_set(x_587, 3, x_486);
lean_ctor_set(x_587, 4, x_487);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; 
x_588 = lean_ctor_get(x_586, 0);
lean_inc(x_588);
x_589 = lean_unsigned_to_nat(3u);
x_590 = lean_nat_mul(x_589, x_588);
x_591 = lean_nat_dec_lt(x_590, x_483);
lean_dec(x_590);
if (x_591 == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_484);
lean_free_object(x_4);
x_592 = lean_unsigned_to_nat(1u);
x_593 = lean_nat_add(x_592, x_483);
lean_dec(x_483);
x_594 = lean_nat_add(x_593, x_588);
lean_dec(x_588);
lean_dec(x_593);
x_595 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_595, 0, x_594);
lean_ctor_set(x_595, 1, x_584);
lean_ctor_set(x_595, 2, x_585);
lean_ctor_set(x_595, 3, x_587);
lean_ctor_set(x_595, 4, x_586);
return x_595;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
lean_dec(x_587);
x_596 = lean_ctor_get(x_486, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_487, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_487, 1);
lean_inc(x_598);
x_599 = lean_ctor_get(x_487, 2);
lean_inc(x_599);
x_600 = lean_ctor_get(x_487, 3);
lean_inc(x_600);
x_601 = lean_ctor_get(x_487, 4);
lean_inc(x_601);
x_602 = lean_unsigned_to_nat(2u);
x_603 = lean_nat_mul(x_602, x_596);
x_604 = lean_nat_dec_lt(x_597, x_603);
lean_dec(x_603);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_597);
lean_free_object(x_4);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 lean_ctor_release(x_487, 4);
 x_605 = x_487;
} else {
 lean_dec_ref(x_487);
 x_605 = lean_box(0);
}
x_606 = lean_unsigned_to_nat(1u);
x_607 = lean_nat_add(x_606, x_483);
lean_dec(x_483);
x_608 = lean_nat_add(x_607, x_588);
lean_dec(x_607);
x_609 = lean_nat_add(x_606, x_596);
lean_dec(x_596);
x_610 = lean_nat_add(x_606, x_588);
lean_dec(x_588);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_611 = lean_ctor_get(x_600, 0);
lean_inc(x_611);
x_612 = lean_nat_add(x_609, x_611);
lean_dec(x_611);
lean_dec(x_609);
lean_inc(x_486);
if (lean_is_scalar(x_605)) {
 x_613 = lean_alloc_ctor(0, 5, 0);
} else {
 x_613 = x_605;
}
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_484);
lean_ctor_set(x_613, 2, x_485);
lean_ctor_set(x_613, 3, x_486);
lean_ctor_set(x_613, 4, x_600);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 lean_ctor_release(x_486, 2);
 lean_ctor_release(x_486, 3);
 lean_ctor_release(x_486, 4);
 x_614 = x_486;
} else {
 lean_dec_ref(x_486);
 x_614 = lean_box(0);
}
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_615 = lean_ctor_get(x_601, 0);
lean_inc(x_615);
x_616 = lean_nat_add(x_610, x_615);
lean_dec(x_615);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_614)) {
 x_617 = lean_alloc_ctor(0, 5, 0);
} else {
 x_617 = x_614;
}
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_584);
lean_ctor_set(x_617, 2, x_585);
lean_ctor_set(x_617, 3, x_601);
lean_ctor_set(x_617, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_618 = x_586;
} else {
 lean_dec_ref(x_586);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(0, 5, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_608);
lean_ctor_set(x_619, 1, x_598);
lean_ctor_set(x_619, 2, x_599);
lean_ctor_set(x_619, 3, x_613);
lean_ctor_set(x_619, 4, x_617);
return x_619;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_620 = lean_unsigned_to_nat(0u);
x_621 = lean_nat_add(x_610, x_620);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_614)) {
 x_622 = lean_alloc_ctor(0, 5, 0);
} else {
 x_622 = x_614;
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_584);
lean_ctor_set(x_622, 2, x_585);
lean_ctor_set(x_622, 3, x_601);
lean_ctor_set(x_622, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_623 = x_586;
} else {
 lean_dec_ref(x_586);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(0, 5, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_608);
lean_ctor_set(x_624, 1, x_598);
lean_ctor_set(x_624, 2, x_599);
lean_ctor_set(x_624, 3, x_613);
lean_ctor_set(x_624, 4, x_622);
return x_624;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_625 = lean_unsigned_to_nat(0u);
x_626 = lean_nat_add(x_609, x_625);
lean_dec(x_609);
lean_inc(x_486);
if (lean_is_scalar(x_605)) {
 x_627 = lean_alloc_ctor(0, 5, 0);
} else {
 x_627 = x_605;
}
lean_ctor_set(x_627, 0, x_626);
lean_ctor_set(x_627, 1, x_484);
lean_ctor_set(x_627, 2, x_485);
lean_ctor_set(x_627, 3, x_486);
lean_ctor_set(x_627, 4, x_600);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 lean_ctor_release(x_486, 2);
 lean_ctor_release(x_486, 3);
 lean_ctor_release(x_486, 4);
 x_628 = x_486;
} else {
 lean_dec_ref(x_486);
 x_628 = lean_box(0);
}
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_629 = lean_ctor_get(x_601, 0);
lean_inc(x_629);
x_630 = lean_nat_add(x_610, x_629);
lean_dec(x_629);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_628)) {
 x_631 = lean_alloc_ctor(0, 5, 0);
} else {
 x_631 = x_628;
}
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_584);
lean_ctor_set(x_631, 2, x_585);
lean_ctor_set(x_631, 3, x_601);
lean_ctor_set(x_631, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_632 = x_586;
} else {
 lean_dec_ref(x_586);
 x_632 = lean_box(0);
}
if (lean_is_scalar(x_632)) {
 x_633 = lean_alloc_ctor(0, 5, 0);
} else {
 x_633 = x_632;
}
lean_ctor_set(x_633, 0, x_608);
lean_ctor_set(x_633, 1, x_598);
lean_ctor_set(x_633, 2, x_599);
lean_ctor_set(x_633, 3, x_627);
lean_ctor_set(x_633, 4, x_631);
return x_633;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_634 = lean_nat_add(x_610, x_625);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_628)) {
 x_635 = lean_alloc_ctor(0, 5, 0);
} else {
 x_635 = x_628;
}
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_584);
lean_ctor_set(x_635, 2, x_585);
lean_ctor_set(x_635, 3, x_601);
lean_ctor_set(x_635, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_636 = x_586;
} else {
 lean_dec_ref(x_586);
 x_636 = lean_box(0);
}
if (lean_is_scalar(x_636)) {
 x_637 = lean_alloc_ctor(0, 5, 0);
} else {
 x_637 = x_636;
}
lean_ctor_set(x_637, 0, x_608);
lean_ctor_set(x_637, 1, x_598);
lean_ctor_set(x_637, 2, x_599);
lean_ctor_set(x_637, 3, x_627);
lean_ctor_set(x_637, 4, x_635);
return x_637;
}
}
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_596);
x_638 = lean_unsigned_to_nat(1u);
x_639 = lean_nat_add(x_638, x_483);
lean_dec(x_483);
x_640 = lean_nat_add(x_639, x_588);
lean_dec(x_639);
x_641 = lean_nat_add(x_638, x_588);
lean_dec(x_588);
x_642 = lean_nat_add(x_641, x_597);
lean_dec(x_597);
lean_dec(x_641);
x_643 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_584);
lean_ctor_set(x_643, 2, x_585);
lean_ctor_set(x_643, 3, x_487);
lean_ctor_set(x_643, 4, x_586);
lean_ctor_set(x_4, 4, x_643);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_640);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_486) == 0)
{
lean_dec(x_587);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_644 = lean_ctor_get(x_487, 0);
lean_inc(x_644);
x_645 = lean_unsigned_to_nat(1u);
x_646 = lean_nat_add(x_645, x_483);
lean_dec(x_483);
x_647 = lean_nat_add(x_645, x_644);
lean_dec(x_644);
x_648 = lean_box(1);
x_649 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_649, 0, x_647);
lean_ctor_set(x_649, 1, x_584);
lean_ctor_set(x_649, 2, x_585);
lean_ctor_set(x_649, 3, x_487);
lean_ctor_set(x_649, 4, x_648);
lean_ctor_set(x_4, 4, x_649);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_646);
return x_4;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_483);
x_650 = lean_box(1);
x_651 = lean_unsigned_to_nat(1u);
x_652 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_584);
lean_ctor_set(x_652, 2, x_585);
lean_ctor_set(x_652, 3, x_650);
lean_ctor_set(x_652, 4, x_650);
x_653 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_652);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_653);
return x_4;
}
}
else
{
lean_dec(x_483);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_587);
x_654 = lean_ctor_get(x_487, 1);
lean_inc(x_654);
x_655 = lean_ctor_get(x_487, 2);
lean_inc(x_655);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 lean_ctor_release(x_487, 4);
 x_656 = x_487;
} else {
 lean_dec_ref(x_487);
 x_656 = lean_box(0);
}
x_657 = lean_box(1);
x_658 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_656)) {
 x_659 = lean_alloc_ctor(0, 5, 0);
} else {
 x_659 = x_656;
}
lean_ctor_set(x_659, 0, x_658);
lean_ctor_set(x_659, 1, x_484);
lean_ctor_set(x_659, 2, x_485);
lean_ctor_set(x_659, 3, x_657);
lean_ctor_set(x_659, 4, x_657);
x_660 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_584);
lean_ctor_set(x_660, 2, x_585);
lean_ctor_set(x_660, 3, x_657);
lean_ctor_set(x_660, 4, x_657);
x_661 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_660);
lean_ctor_set(x_4, 3, x_659);
lean_ctor_set(x_4, 2, x_655);
lean_ctor_set(x_4, 1, x_654);
lean_ctor_set(x_4, 0, x_661);
return x_4;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_485);
lean_dec(x_484);
lean_free_object(x_4);
x_662 = lean_box(1);
x_663 = lean_unsigned_to_nat(2u);
x_664 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_584);
lean_ctor_set(x_664, 2, x_585);
lean_ctor_set(x_664, 3, x_587);
lean_ctor_set(x_664, 4, x_662);
return x_664;
}
}
}
}
}
}
else
{
lean_free_object(x_4);
return x_10;
}
}
else
{
lean_free_object(x_4);
return x_11;
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_17, 0);
lean_inc(x_665);
lean_dec(x_17);
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
lean_dec(x_665);
lean_ctor_set(x_4, 2, x_667);
lean_ctor_set(x_4, 1, x_666);
return x_4;
}
}
default: 
{
lean_object* x_668; lean_object* x_669; 
lean_free_object(x_4);
lean_dec(x_7);
x_668 = l_Std_DTreeMap_Internal_Impl_updateCell___rarg(x_1, x_2, x_3, x_11, lean_box(0));
x_669 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_8, x_9, x_10, x_668, lean_box(0), lean_box(0), lean_box(0));
return x_669;
}
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; 
x_670 = lean_ctor_get(x_4, 0);
x_671 = lean_ctor_get(x_4, 1);
x_672 = lean_ctor_get(x_4, 2);
x_673 = lean_ctor_get(x_4, 3);
x_674 = lean_ctor_get(x_4, 4);
lean_inc(x_674);
lean_inc(x_673);
lean_inc(x_672);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_671);
lean_inc(x_2);
x_675 = lean_apply_2(x_1, x_2, x_671);
x_676 = lean_unbox(x_675);
lean_dec(x_675);
switch (x_676) {
case 0:
{
lean_object* x_677; lean_object* x_678; 
lean_dec(x_670);
x_677 = l_Std_DTreeMap_Internal_Impl_updateCell___rarg(x_1, x_2, x_3, x_673, lean_box(0));
x_678 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_671, x_672, x_677, x_674, lean_box(0), lean_box(0), lean_box(0));
return x_678;
}
case 1:
{
lean_object* x_679; lean_object* x_680; 
lean_dec(x_2);
lean_dec(x_1);
x_679 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_671, x_672, lean_box(0));
x_680 = lean_apply_1(x_3, x_679);
if (lean_obj_tag(x_680) == 0)
{
lean_dec(x_670);
if (lean_obj_tag(x_673) == 0)
{
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; uint8_t x_693; 
x_681 = lean_ctor_get(x_673, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_673, 1);
lean_inc(x_682);
x_683 = lean_ctor_get(x_673, 2);
lean_inc(x_683);
x_684 = lean_ctor_get(x_673, 3);
lean_inc(x_684);
x_685 = lean_ctor_get(x_673, 4);
lean_inc(x_685);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 lean_ctor_release(x_673, 2);
 lean_ctor_release(x_673, 3);
 lean_ctor_release(x_673, 4);
 x_686 = x_673;
} else {
 lean_dec_ref(x_673);
 x_686 = lean_box(0);
}
x_687 = lean_ctor_get(x_674, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_674, 1);
lean_inc(x_688);
x_689 = lean_ctor_get(x_674, 2);
lean_inc(x_689);
x_690 = lean_ctor_get(x_674, 3);
lean_inc(x_690);
x_691 = lean_ctor_get(x_674, 4);
lean_inc(x_691);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 lean_ctor_release(x_674, 4);
 x_692 = x_674;
} else {
 lean_dec_ref(x_674);
 x_692 = lean_box(0);
}
x_693 = lean_nat_dec_lt(x_681, x_687);
if (x_693 == 0)
{
lean_object* x_694; lean_object* x_695; 
lean_dec(x_681);
x_694 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_682, x_683, x_684, x_685, lean_box(0), lean_box(0), lean_box(0));
x_695 = lean_ctor_get(x_694, 2);
lean_inc(x_695);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; 
x_696 = lean_ctor_get(x_694, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_694, 1);
lean_inc(x_697);
lean_dec(x_694);
x_698 = lean_ctor_get(x_695, 0);
lean_inc(x_698);
lean_inc(x_691);
lean_inc(x_690);
lean_inc(x_689);
lean_inc(x_688);
lean_inc(x_687);
if (lean_is_scalar(x_692)) {
 x_699 = lean_alloc_ctor(0, 5, 0);
} else {
 x_699 = x_692;
}
lean_ctor_set(x_699, 0, x_687);
lean_ctor_set(x_699, 1, x_688);
lean_ctor_set(x_699, 2, x_689);
lean_ctor_set(x_699, 3, x_690);
lean_ctor_set(x_699, 4, x_691);
x_700 = lean_unsigned_to_nat(3u);
x_701 = lean_nat_mul(x_700, x_698);
x_702 = lean_nat_dec_lt(x_701, x_687);
lean_dec(x_701);
if (x_702 == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_dec(x_691);
lean_dec(x_690);
lean_dec(x_689);
lean_dec(x_688);
x_703 = lean_unsigned_to_nat(1u);
x_704 = lean_nat_add(x_703, x_698);
lean_dec(x_698);
x_705 = lean_nat_add(x_704, x_687);
lean_dec(x_687);
lean_dec(x_704);
if (lean_is_scalar(x_686)) {
 x_706 = lean_alloc_ctor(0, 5, 0);
} else {
 x_706 = x_686;
}
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_696);
lean_ctor_set(x_706, 2, x_697);
lean_ctor_set(x_706, 3, x_695);
lean_ctor_set(x_706, 4, x_699);
return x_706;
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; 
lean_dec(x_699);
x_707 = lean_ctor_get(x_690, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_690, 1);
lean_inc(x_708);
x_709 = lean_ctor_get(x_690, 2);
lean_inc(x_709);
x_710 = lean_ctor_get(x_690, 3);
lean_inc(x_710);
x_711 = lean_ctor_get(x_690, 4);
lean_inc(x_711);
x_712 = lean_ctor_get(x_691, 0);
lean_inc(x_712);
x_713 = lean_unsigned_to_nat(2u);
x_714 = lean_nat_mul(x_713, x_712);
x_715 = lean_nat_dec_lt(x_707, x_714);
lean_dec(x_714);
if (x_715 == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_707);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 lean_ctor_release(x_690, 2);
 lean_ctor_release(x_690, 3);
 lean_ctor_release(x_690, 4);
 x_716 = x_690;
} else {
 lean_dec_ref(x_690);
 x_716 = lean_box(0);
}
x_717 = lean_unsigned_to_nat(1u);
x_718 = lean_nat_add(x_717, x_698);
lean_dec(x_698);
x_719 = lean_nat_add(x_718, x_687);
lean_dec(x_687);
x_720 = lean_nat_add(x_717, x_712);
lean_dec(x_712);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_721 = lean_ctor_get(x_710, 0);
lean_inc(x_721);
x_722 = lean_nat_add(x_718, x_721);
lean_dec(x_721);
lean_dec(x_718);
lean_inc(x_695);
if (lean_is_scalar(x_716)) {
 x_723 = lean_alloc_ctor(0, 5, 0);
} else {
 x_723 = x_716;
}
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_696);
lean_ctor_set(x_723, 2, x_697);
lean_ctor_set(x_723, 3, x_695);
lean_ctor_set(x_723, 4, x_710);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 lean_ctor_release(x_695, 2);
 lean_ctor_release(x_695, 3);
 lean_ctor_release(x_695, 4);
 x_724 = x_695;
} else {
 lean_dec_ref(x_695);
 x_724 = lean_box(0);
}
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_725 = lean_ctor_get(x_711, 0);
lean_inc(x_725);
x_726 = lean_nat_add(x_720, x_725);
lean_dec(x_725);
lean_dec(x_720);
if (lean_is_scalar(x_724)) {
 x_727 = lean_alloc_ctor(0, 5, 0);
} else {
 x_727 = x_724;
}
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_688);
lean_ctor_set(x_727, 2, x_689);
lean_ctor_set(x_727, 3, x_711);
lean_ctor_set(x_727, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_728 = lean_alloc_ctor(0, 5, 0);
} else {
 x_728 = x_686;
}
lean_ctor_set(x_728, 0, x_719);
lean_ctor_set(x_728, 1, x_708);
lean_ctor_set(x_728, 2, x_709);
lean_ctor_set(x_728, 3, x_723);
lean_ctor_set(x_728, 4, x_727);
return x_728;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_729 = lean_unsigned_to_nat(0u);
x_730 = lean_nat_add(x_720, x_729);
lean_dec(x_720);
if (lean_is_scalar(x_724)) {
 x_731 = lean_alloc_ctor(0, 5, 0);
} else {
 x_731 = x_724;
}
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_688);
lean_ctor_set(x_731, 2, x_689);
lean_ctor_set(x_731, 3, x_711);
lean_ctor_set(x_731, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_732 = lean_alloc_ctor(0, 5, 0);
} else {
 x_732 = x_686;
}
lean_ctor_set(x_732, 0, x_719);
lean_ctor_set(x_732, 1, x_708);
lean_ctor_set(x_732, 2, x_709);
lean_ctor_set(x_732, 3, x_723);
lean_ctor_set(x_732, 4, x_731);
return x_732;
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_733 = lean_unsigned_to_nat(0u);
x_734 = lean_nat_add(x_718, x_733);
lean_dec(x_718);
lean_inc(x_695);
if (lean_is_scalar(x_716)) {
 x_735 = lean_alloc_ctor(0, 5, 0);
} else {
 x_735 = x_716;
}
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_696);
lean_ctor_set(x_735, 2, x_697);
lean_ctor_set(x_735, 3, x_695);
lean_ctor_set(x_735, 4, x_710);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 lean_ctor_release(x_695, 2);
 lean_ctor_release(x_695, 3);
 lean_ctor_release(x_695, 4);
 x_736 = x_695;
} else {
 lean_dec_ref(x_695);
 x_736 = lean_box(0);
}
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_737 = lean_ctor_get(x_711, 0);
lean_inc(x_737);
x_738 = lean_nat_add(x_720, x_737);
lean_dec(x_737);
lean_dec(x_720);
if (lean_is_scalar(x_736)) {
 x_739 = lean_alloc_ctor(0, 5, 0);
} else {
 x_739 = x_736;
}
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_688);
lean_ctor_set(x_739, 2, x_689);
lean_ctor_set(x_739, 3, x_711);
lean_ctor_set(x_739, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_740 = lean_alloc_ctor(0, 5, 0);
} else {
 x_740 = x_686;
}
lean_ctor_set(x_740, 0, x_719);
lean_ctor_set(x_740, 1, x_708);
lean_ctor_set(x_740, 2, x_709);
lean_ctor_set(x_740, 3, x_735);
lean_ctor_set(x_740, 4, x_739);
return x_740;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_741 = lean_nat_add(x_720, x_733);
lean_dec(x_720);
if (lean_is_scalar(x_736)) {
 x_742 = lean_alloc_ctor(0, 5, 0);
} else {
 x_742 = x_736;
}
lean_ctor_set(x_742, 0, x_741);
lean_ctor_set(x_742, 1, x_688);
lean_ctor_set(x_742, 2, x_689);
lean_ctor_set(x_742, 3, x_711);
lean_ctor_set(x_742, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_743 = lean_alloc_ctor(0, 5, 0);
} else {
 x_743 = x_686;
}
lean_ctor_set(x_743, 0, x_719);
lean_ctor_set(x_743, 1, x_708);
lean_ctor_set(x_743, 2, x_709);
lean_ctor_set(x_743, 3, x_735);
lean_ctor_set(x_743, 4, x_742);
return x_743;
}
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_dec(x_712);
lean_dec(x_711);
lean_dec(x_710);
lean_dec(x_709);
lean_dec(x_708);
x_744 = lean_unsigned_to_nat(1u);
x_745 = lean_nat_add(x_744, x_698);
lean_dec(x_698);
x_746 = lean_nat_add(x_745, x_687);
lean_dec(x_687);
x_747 = lean_nat_add(x_745, x_707);
lean_dec(x_707);
lean_dec(x_745);
if (lean_is_scalar(x_686)) {
 x_748 = lean_alloc_ctor(0, 5, 0);
} else {
 x_748 = x_686;
}
lean_ctor_set(x_748, 0, x_747);
lean_ctor_set(x_748, 1, x_696);
lean_ctor_set(x_748, 2, x_697);
lean_ctor_set(x_748, 3, x_695);
lean_ctor_set(x_748, 4, x_690);
x_749 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_749, 0, x_746);
lean_ctor_set(x_749, 1, x_688);
lean_ctor_set(x_749, 2, x_689);
lean_ctor_set(x_749, 3, x_748);
lean_ctor_set(x_749, 4, x_691);
return x_749;
}
}
}
else
{
if (lean_obj_tag(x_690) == 0)
{
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_750 = lean_ctor_get(x_694, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_694, 1);
lean_inc(x_751);
lean_dec(x_694);
x_752 = lean_ctor_get(x_690, 0);
lean_inc(x_752);
x_753 = lean_unsigned_to_nat(1u);
x_754 = lean_nat_add(x_753, x_687);
lean_dec(x_687);
x_755 = lean_nat_add(x_753, x_752);
lean_dec(x_752);
x_756 = lean_box(1);
if (lean_is_scalar(x_692)) {
 x_757 = lean_alloc_ctor(0, 5, 0);
} else {
 x_757 = x_692;
}
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set(x_757, 1, x_750);
lean_ctor_set(x_757, 2, x_751);
lean_ctor_set(x_757, 3, x_756);
lean_ctor_set(x_757, 4, x_690);
if (lean_is_scalar(x_686)) {
 x_758 = lean_alloc_ctor(0, 5, 0);
} else {
 x_758 = x_686;
}
lean_ctor_set(x_758, 0, x_754);
lean_ctor_set(x_758, 1, x_688);
lean_ctor_set(x_758, 2, x_689);
lean_ctor_set(x_758, 3, x_757);
lean_ctor_set(x_758, 4, x_691);
return x_758;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_687);
x_759 = lean_ctor_get(x_694, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_694, 1);
lean_inc(x_760);
lean_dec(x_694);
x_761 = lean_ctor_get(x_690, 1);
lean_inc(x_761);
x_762 = lean_ctor_get(x_690, 2);
lean_inc(x_762);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 lean_ctor_release(x_690, 2);
 lean_ctor_release(x_690, 3);
 lean_ctor_release(x_690, 4);
 x_763 = x_690;
} else {
 lean_dec_ref(x_690);
 x_763 = lean_box(0);
}
x_764 = lean_box(1);
x_765 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_763)) {
 x_766 = lean_alloc_ctor(0, 5, 0);
} else {
 x_766 = x_763;
}
lean_ctor_set(x_766, 0, x_765);
lean_ctor_set(x_766, 1, x_759);
lean_ctor_set(x_766, 2, x_760);
lean_ctor_set(x_766, 3, x_764);
lean_ctor_set(x_766, 4, x_764);
if (lean_is_scalar(x_692)) {
 x_767 = lean_alloc_ctor(0, 5, 0);
} else {
 x_767 = x_692;
}
lean_ctor_set(x_767, 0, x_765);
lean_ctor_set(x_767, 1, x_688);
lean_ctor_set(x_767, 2, x_689);
lean_ctor_set(x_767, 3, x_764);
lean_ctor_set(x_767, 4, x_764);
x_768 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_686)) {
 x_769 = lean_alloc_ctor(0, 5, 0);
} else {
 x_769 = x_686;
}
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_761);
lean_ctor_set(x_769, 2, x_762);
lean_ctor_set(x_769, 3, x_766);
lean_ctor_set(x_769, 4, x_767);
return x_769;
}
}
else
{
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
lean_dec(x_687);
x_770 = lean_ctor_get(x_694, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_694, 1);
lean_inc(x_771);
lean_dec(x_694);
x_772 = lean_box(1);
x_773 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_692)) {
 x_774 = lean_alloc_ctor(0, 5, 0);
} else {
 x_774 = x_692;
}
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_770);
lean_ctor_set(x_774, 2, x_771);
lean_ctor_set(x_774, 3, x_772);
lean_ctor_set(x_774, 4, x_772);
x_775 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_686)) {
 x_776 = lean_alloc_ctor(0, 5, 0);
} else {
 x_776 = x_686;
}
lean_ctor_set(x_776, 0, x_775);
lean_ctor_set(x_776, 1, x_688);
lean_ctor_set(x_776, 2, x_689);
lean_ctor_set(x_776, 3, x_774);
lean_ctor_set(x_776, 4, x_691);
return x_776;
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_777 = lean_ctor_get(x_694, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_694, 1);
lean_inc(x_778);
lean_dec(x_694);
if (lean_is_scalar(x_692)) {
 x_779 = lean_alloc_ctor(0, 5, 0);
} else {
 x_779 = x_692;
}
lean_ctor_set(x_779, 0, x_687);
lean_ctor_set(x_779, 1, x_688);
lean_ctor_set(x_779, 2, x_689);
lean_ctor_set(x_779, 3, x_691);
lean_ctor_set(x_779, 4, x_691);
x_780 = lean_box(1);
x_781 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_686)) {
 x_782 = lean_alloc_ctor(0, 5, 0);
} else {
 x_782 = x_686;
}
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_777);
lean_ctor_set(x_782, 2, x_778);
lean_ctor_set(x_782, 3, x_780);
lean_ctor_set(x_782, 4, x_779);
return x_782;
}
}
}
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
lean_dec(x_687);
x_783 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_688, x_689, x_690, x_691, lean_box(0), lean_box(0), lean_box(0));
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
x_786 = lean_ctor_get(x_783, 2);
lean_inc(x_786);
lean_dec(x_783);
lean_inc(x_685);
lean_inc(x_684);
lean_inc(x_683);
lean_inc(x_682);
lean_inc(x_681);
if (lean_is_scalar(x_692)) {
 x_787 = lean_alloc_ctor(0, 5, 0);
} else {
 x_787 = x_692;
}
lean_ctor_set(x_787, 0, x_681);
lean_ctor_set(x_787, 1, x_682);
lean_ctor_set(x_787, 2, x_683);
lean_ctor_set(x_787, 3, x_684);
lean_ctor_set(x_787, 4, x_685);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; 
x_788 = lean_ctor_get(x_786, 0);
lean_inc(x_788);
x_789 = lean_unsigned_to_nat(3u);
x_790 = lean_nat_mul(x_789, x_788);
x_791 = lean_nat_dec_lt(x_790, x_681);
lean_dec(x_790);
if (x_791 == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_683);
lean_dec(x_682);
x_792 = lean_unsigned_to_nat(1u);
x_793 = lean_nat_add(x_792, x_681);
lean_dec(x_681);
x_794 = lean_nat_add(x_793, x_788);
lean_dec(x_788);
lean_dec(x_793);
if (lean_is_scalar(x_686)) {
 x_795 = lean_alloc_ctor(0, 5, 0);
} else {
 x_795 = x_686;
}
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_784);
lean_ctor_set(x_795, 2, x_785);
lean_ctor_set(x_795, 3, x_787);
lean_ctor_set(x_795, 4, x_786);
return x_795;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; uint8_t x_804; 
lean_dec(x_787);
x_796 = lean_ctor_get(x_684, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_685, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_685, 1);
lean_inc(x_798);
x_799 = lean_ctor_get(x_685, 2);
lean_inc(x_799);
x_800 = lean_ctor_get(x_685, 3);
lean_inc(x_800);
x_801 = lean_ctor_get(x_685, 4);
lean_inc(x_801);
x_802 = lean_unsigned_to_nat(2u);
x_803 = lean_nat_mul(x_802, x_796);
x_804 = lean_nat_dec_lt(x_797, x_803);
lean_dec(x_803);
if (x_804 == 0)
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_797);
lean_dec(x_686);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 lean_ctor_release(x_685, 2);
 lean_ctor_release(x_685, 3);
 lean_ctor_release(x_685, 4);
 x_805 = x_685;
} else {
 lean_dec_ref(x_685);
 x_805 = lean_box(0);
}
x_806 = lean_unsigned_to_nat(1u);
x_807 = lean_nat_add(x_806, x_681);
lean_dec(x_681);
x_808 = lean_nat_add(x_807, x_788);
lean_dec(x_807);
x_809 = lean_nat_add(x_806, x_796);
lean_dec(x_796);
x_810 = lean_nat_add(x_806, x_788);
lean_dec(x_788);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_811 = lean_ctor_get(x_800, 0);
lean_inc(x_811);
x_812 = lean_nat_add(x_809, x_811);
lean_dec(x_811);
lean_dec(x_809);
lean_inc(x_684);
if (lean_is_scalar(x_805)) {
 x_813 = lean_alloc_ctor(0, 5, 0);
} else {
 x_813 = x_805;
}
lean_ctor_set(x_813, 0, x_812);
lean_ctor_set(x_813, 1, x_682);
lean_ctor_set(x_813, 2, x_683);
lean_ctor_set(x_813, 3, x_684);
lean_ctor_set(x_813, 4, x_800);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 lean_ctor_release(x_684, 2);
 lean_ctor_release(x_684, 3);
 lean_ctor_release(x_684, 4);
 x_814 = x_684;
} else {
 lean_dec_ref(x_684);
 x_814 = lean_box(0);
}
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_815 = lean_ctor_get(x_801, 0);
lean_inc(x_815);
x_816 = lean_nat_add(x_810, x_815);
lean_dec(x_815);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_814)) {
 x_817 = lean_alloc_ctor(0, 5, 0);
} else {
 x_817 = x_814;
}
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_784);
lean_ctor_set(x_817, 2, x_785);
lean_ctor_set(x_817, 3, x_801);
lean_ctor_set(x_817, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_818 = x_786;
} else {
 lean_dec_ref(x_786);
 x_818 = lean_box(0);
}
if (lean_is_scalar(x_818)) {
 x_819 = lean_alloc_ctor(0, 5, 0);
} else {
 x_819 = x_818;
}
lean_ctor_set(x_819, 0, x_808);
lean_ctor_set(x_819, 1, x_798);
lean_ctor_set(x_819, 2, x_799);
lean_ctor_set(x_819, 3, x_813);
lean_ctor_set(x_819, 4, x_817);
return x_819;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_820 = lean_unsigned_to_nat(0u);
x_821 = lean_nat_add(x_810, x_820);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_814)) {
 x_822 = lean_alloc_ctor(0, 5, 0);
} else {
 x_822 = x_814;
}
lean_ctor_set(x_822, 0, x_821);
lean_ctor_set(x_822, 1, x_784);
lean_ctor_set(x_822, 2, x_785);
lean_ctor_set(x_822, 3, x_801);
lean_ctor_set(x_822, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_823 = x_786;
} else {
 lean_dec_ref(x_786);
 x_823 = lean_box(0);
}
if (lean_is_scalar(x_823)) {
 x_824 = lean_alloc_ctor(0, 5, 0);
} else {
 x_824 = x_823;
}
lean_ctor_set(x_824, 0, x_808);
lean_ctor_set(x_824, 1, x_798);
lean_ctor_set(x_824, 2, x_799);
lean_ctor_set(x_824, 3, x_813);
lean_ctor_set(x_824, 4, x_822);
return x_824;
}
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_825 = lean_unsigned_to_nat(0u);
x_826 = lean_nat_add(x_809, x_825);
lean_dec(x_809);
lean_inc(x_684);
if (lean_is_scalar(x_805)) {
 x_827 = lean_alloc_ctor(0, 5, 0);
} else {
 x_827 = x_805;
}
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_682);
lean_ctor_set(x_827, 2, x_683);
lean_ctor_set(x_827, 3, x_684);
lean_ctor_set(x_827, 4, x_800);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 lean_ctor_release(x_684, 2);
 lean_ctor_release(x_684, 3);
 lean_ctor_release(x_684, 4);
 x_828 = x_684;
} else {
 lean_dec_ref(x_684);
 x_828 = lean_box(0);
}
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_829 = lean_ctor_get(x_801, 0);
lean_inc(x_829);
x_830 = lean_nat_add(x_810, x_829);
lean_dec(x_829);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_828)) {
 x_831 = lean_alloc_ctor(0, 5, 0);
} else {
 x_831 = x_828;
}
lean_ctor_set(x_831, 0, x_830);
lean_ctor_set(x_831, 1, x_784);
lean_ctor_set(x_831, 2, x_785);
lean_ctor_set(x_831, 3, x_801);
lean_ctor_set(x_831, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_832 = x_786;
} else {
 lean_dec_ref(x_786);
 x_832 = lean_box(0);
}
if (lean_is_scalar(x_832)) {
 x_833 = lean_alloc_ctor(0, 5, 0);
} else {
 x_833 = x_832;
}
lean_ctor_set(x_833, 0, x_808);
lean_ctor_set(x_833, 1, x_798);
lean_ctor_set(x_833, 2, x_799);
lean_ctor_set(x_833, 3, x_827);
lean_ctor_set(x_833, 4, x_831);
return x_833;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_834 = lean_nat_add(x_810, x_825);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_828)) {
 x_835 = lean_alloc_ctor(0, 5, 0);
} else {
 x_835 = x_828;
}
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_784);
lean_ctor_set(x_835, 2, x_785);
lean_ctor_set(x_835, 3, x_801);
lean_ctor_set(x_835, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_836 = x_786;
} else {
 lean_dec_ref(x_786);
 x_836 = lean_box(0);
}
if (lean_is_scalar(x_836)) {
 x_837 = lean_alloc_ctor(0, 5, 0);
} else {
 x_837 = x_836;
}
lean_ctor_set(x_837, 0, x_808);
lean_ctor_set(x_837, 1, x_798);
lean_ctor_set(x_837, 2, x_799);
lean_ctor_set(x_837, 3, x_827);
lean_ctor_set(x_837, 4, x_835);
return x_837;
}
}
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
lean_dec(x_801);
lean_dec(x_800);
lean_dec(x_799);
lean_dec(x_798);
lean_dec(x_796);
x_838 = lean_unsigned_to_nat(1u);
x_839 = lean_nat_add(x_838, x_681);
lean_dec(x_681);
x_840 = lean_nat_add(x_839, x_788);
lean_dec(x_839);
x_841 = lean_nat_add(x_838, x_788);
lean_dec(x_788);
x_842 = lean_nat_add(x_841, x_797);
lean_dec(x_797);
lean_dec(x_841);
if (lean_is_scalar(x_686)) {
 x_843 = lean_alloc_ctor(0, 5, 0);
} else {
 x_843 = x_686;
}
lean_ctor_set(x_843, 0, x_842);
lean_ctor_set(x_843, 1, x_784);
lean_ctor_set(x_843, 2, x_785);
lean_ctor_set(x_843, 3, x_685);
lean_ctor_set(x_843, 4, x_786);
x_844 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_844, 0, x_840);
lean_ctor_set(x_844, 1, x_682);
lean_ctor_set(x_844, 2, x_683);
lean_ctor_set(x_844, 3, x_684);
lean_ctor_set(x_844, 4, x_843);
return x_844;
}
}
}
else
{
if (lean_obj_tag(x_684) == 0)
{
lean_dec(x_787);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_845 = lean_ctor_get(x_685, 0);
lean_inc(x_845);
x_846 = lean_unsigned_to_nat(1u);
x_847 = lean_nat_add(x_846, x_681);
lean_dec(x_681);
x_848 = lean_nat_add(x_846, x_845);
lean_dec(x_845);
x_849 = lean_box(1);
if (lean_is_scalar(x_686)) {
 x_850 = lean_alloc_ctor(0, 5, 0);
} else {
 x_850 = x_686;
}
lean_ctor_set(x_850, 0, x_848);
lean_ctor_set(x_850, 1, x_784);
lean_ctor_set(x_850, 2, x_785);
lean_ctor_set(x_850, 3, x_685);
lean_ctor_set(x_850, 4, x_849);
x_851 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_851, 0, x_847);
lean_ctor_set(x_851, 1, x_682);
lean_ctor_set(x_851, 2, x_683);
lean_ctor_set(x_851, 3, x_684);
lean_ctor_set(x_851, 4, x_850);
return x_851;
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_681);
x_852 = lean_box(1);
x_853 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_686)) {
 x_854 = lean_alloc_ctor(0, 5, 0);
} else {
 x_854 = x_686;
}
lean_ctor_set(x_854, 0, x_853);
lean_ctor_set(x_854, 1, x_784);
lean_ctor_set(x_854, 2, x_785);
lean_ctor_set(x_854, 3, x_852);
lean_ctor_set(x_854, 4, x_852);
x_855 = lean_unsigned_to_nat(3u);
x_856 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_682);
lean_ctor_set(x_856, 2, x_683);
lean_ctor_set(x_856, 3, x_684);
lean_ctor_set(x_856, 4, x_854);
return x_856;
}
}
else
{
lean_dec(x_681);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; 
lean_dec(x_787);
x_857 = lean_ctor_get(x_685, 1);
lean_inc(x_857);
x_858 = lean_ctor_get(x_685, 2);
lean_inc(x_858);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 lean_ctor_release(x_685, 2);
 lean_ctor_release(x_685, 3);
 lean_ctor_release(x_685, 4);
 x_859 = x_685;
} else {
 lean_dec_ref(x_685);
 x_859 = lean_box(0);
}
x_860 = lean_box(1);
x_861 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_859)) {
 x_862 = lean_alloc_ctor(0, 5, 0);
} else {
 x_862 = x_859;
}
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_862, 1, x_682);
lean_ctor_set(x_862, 2, x_683);
lean_ctor_set(x_862, 3, x_860);
lean_ctor_set(x_862, 4, x_860);
if (lean_is_scalar(x_686)) {
 x_863 = lean_alloc_ctor(0, 5, 0);
} else {
 x_863 = x_686;
}
lean_ctor_set(x_863, 0, x_861);
lean_ctor_set(x_863, 1, x_784);
lean_ctor_set(x_863, 2, x_785);
lean_ctor_set(x_863, 3, x_860);
lean_ctor_set(x_863, 4, x_860);
x_864 = lean_unsigned_to_nat(3u);
x_865 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_857);
lean_ctor_set(x_865, 2, x_858);
lean_ctor_set(x_865, 3, x_862);
lean_ctor_set(x_865, 4, x_863);
return x_865;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_683);
lean_dec(x_682);
x_866 = lean_box(1);
x_867 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_686)) {
 x_868 = lean_alloc_ctor(0, 5, 0);
} else {
 x_868 = x_686;
}
lean_ctor_set(x_868, 0, x_867);
lean_ctor_set(x_868, 1, x_784);
lean_ctor_set(x_868, 2, x_785);
lean_ctor_set(x_868, 3, x_787);
lean_ctor_set(x_868, 4, x_866);
return x_868;
}
}
}
}
}
else
{
return x_673;
}
}
else
{
return x_674;
}
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_869 = lean_ctor_get(x_680, 0);
lean_inc(x_869);
lean_dec(x_680);
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
x_872 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_872, 0, x_670);
lean_ctor_set(x_872, 1, x_870);
lean_ctor_set(x_872, 2, x_871);
lean_ctor_set(x_872, 3, x_673);
lean_ctor_set(x_872, 4, x_674);
return x_872;
}
}
default: 
{
lean_object* x_873; lean_object* x_874; 
lean_dec(x_670);
x_873 = l_Std_DTreeMap_Internal_Impl_updateCell___rarg(x_1, x_2, x_3, x_674, lean_box(0));
x_874 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_671, x_672, x_673, x_873, lean_box(0), lean_box(0), lean_box(0));
return x_874;
}
}
}
}
else
{
lean_object* x_875; lean_object* x_876; 
lean_dec(x_2);
lean_dec(x_1);
x_875 = lean_box(0);
x_876 = lean_apply_1(x_3, x_875);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; 
x_877 = lean_box(1);
return x_877;
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_878 = lean_ctor_get(x_876, 0);
lean_inc(x_878);
lean_dec(x_876);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_881 = lean_box(1);
x_882 = lean_unsigned_to_nat(1u);
x_883 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_883, 0, x_882);
lean_ctor_set(x_883, 1, x_879);
lean_ctor_set(x_883, 2, x_880);
lean_ctor_set(x_883, 3, x_881);
lean_ctor_set(x_883, 4, x_881);
return x_883;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_updateCell___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_DTreeMap_Internal_Cell_contains___rarg(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg___closed__1;
x_5 = l_Std_DTreeMap_Internal_Impl_applyCell___rarg(x_1, x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg___lambda__1(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Cell_get_x3f___rarg(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg___lambda__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg___closed__1;
x_7 = l_Std_DTreeMap_Internal_Impl_applyCell___rarg(x_1, x_5, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg___closed__1;
x_8 = l_Std_DTreeMap_Internal_Impl_applyCell___rarg(x_1, x_5, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_get_u2098___rarg), 6, 0);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__1;
x_2 = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__2;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg___closed__1;
x_8 = l_Std_DTreeMap_Internal_Impl_applyCell___rarg(x_1, x_5, x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__4;
x_10 = l_panic___rarg(x_6, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg___closed__1;
x_8 = l_Std_DTreeMap_Internal_Impl_applyCell___rarg(x_1, x_4, x_5, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getD_u2098___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_getD_u2098___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Cell_getKey_x3f___rarg(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg___lambda__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg___closed__1;
x_5 = l_Std_DTreeMap_Internal_Impl_applyCell___rarg(x_1, x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg___closed__1;
x_6 = l_Std_DTreeMap_Internal_Impl_applyCell___rarg(x_1, x_3, x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKey_u2098___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg___closed__1;
x_6 = l_Std_DTreeMap_Internal_Impl_applyCell___rarg(x_1, x_3, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__4;
x_8 = l_panic___rarg(x_4, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg___closed__1;
x_6 = l_Std_DTreeMap_Internal_Impl_applyCell___rarg(x_1, x_2, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insert_u2098___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_4, 3);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_8);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
switch (x_13) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_4);
lean_dec(x_7);
x_14 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insert_u2098___spec__1___rarg(x_1, x_2, x_3, x_10, lean_box(0));
x_15 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_8, x_9, x_14, x_11, lean_box(0), lean_box(0), lean_box(0));
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_8, x_9, lean_box(0));
x_17 = lean_apply_1(x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_7);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_10, 2);
x_23 = lean_ctor_get(x_10, 3);
x_24 = lean_ctor_get(x_10, 4);
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
x_27 = lean_ctor_get(x_11, 2);
x_28 = lean_ctor_get(x_11, 3);
x_29 = lean_ctor_get(x_11, 4);
x_30 = lean_nat_dec_lt(x_20, x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_20);
x_31 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_21, x_22, x_23, x_24, lean_box(0), lean_box(0), lean_box(0));
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_mul(x_36, x_35);
x_38 = lean_nat_dec_lt(x_37, x_25);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_4);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_39, x_35);
lean_dec(x_35);
x_41 = lean_nat_add(x_40, x_25);
lean_dec(x_25);
lean_dec(x_40);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_32);
lean_ctor_set(x_10, 2, x_34);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_41);
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_11);
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_28, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_28, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_28, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_29, 0);
lean_inc(x_47);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_mul(x_48, x_47);
x_50 = lean_nat_dec_lt(x_42, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
uint8_t x_51; 
lean_dec(x_42);
lean_free_object(x_4);
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_28, 4);
lean_dec(x_52);
x_53 = lean_ctor_get(x_28, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_28, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_28, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_28, 0);
lean_dec(x_56);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_57, x_35);
lean_dec(x_35);
x_59 = lean_nat_add(x_58, x_25);
lean_dec(x_25);
x_60 = lean_nat_add(x_57, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
x_62 = lean_nat_add(x_58, x_61);
lean_dec(x_61);
lean_dec(x_58);
lean_inc(x_32);
lean_ctor_set(x_28, 4, x_45);
lean_ctor_set(x_28, 3, x_32);
lean_ctor_set(x_28, 2, x_34);
lean_ctor_set(x_28, 1, x_33);
lean_ctor_set(x_28, 0, x_62);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_32, 4);
lean_dec(x_64);
x_65 = lean_ctor_get(x_32, 3);
lean_dec(x_65);
x_66 = lean_ctor_get(x_32, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_32, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_32, 0);
lean_dec(x_68);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_46, 0);
lean_inc(x_69);
x_70 = lean_nat_add(x_60, x_69);
lean_dec(x_69);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_70);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_add(x_60, x_71);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_72);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
else
{
lean_dec(x_32);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_46, 0);
lean_inc(x_73);
x_74 = lean_nat_add(x_60, x_73);
lean_dec(x_73);
lean_dec(x_60);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_26);
lean_ctor_set(x_75, 2, x_27);
lean_ctor_set(x_75, 3, x_46);
lean_ctor_set(x_75, 4, x_29);
lean_ctor_set(x_10, 4, x_75);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_add(x_60, x_76);
lean_dec(x_60);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_26);
lean_ctor_set(x_78, 2, x_27);
lean_ctor_set(x_78, 3, x_46);
lean_ctor_set(x_78, 4, x_29);
lean_ctor_set(x_10, 4, x_78);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_add(x_58, x_79);
lean_dec(x_58);
lean_inc(x_32);
lean_ctor_set(x_28, 4, x_45);
lean_ctor_set(x_28, 3, x_32);
lean_ctor_set(x_28, 2, x_34);
lean_ctor_set(x_28, 1, x_33);
lean_ctor_set(x_28, 0, x_80);
x_81 = !lean_is_exclusive(x_32);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_32, 4);
lean_dec(x_82);
x_83 = lean_ctor_get(x_32, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_32, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_32, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_32, 0);
lean_dec(x_86);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_46, 0);
lean_inc(x_87);
x_88 = lean_nat_add(x_60, x_87);
lean_dec(x_87);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_88);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_89; 
x_89 = lean_nat_add(x_60, x_79);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_89);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
else
{
lean_dec(x_32);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_46, 0);
lean_inc(x_90);
x_91 = lean_nat_add(x_60, x_90);
lean_dec(x_90);
lean_dec(x_60);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_26);
lean_ctor_set(x_92, 2, x_27);
lean_ctor_set(x_92, 3, x_46);
lean_ctor_set(x_92, 4, x_29);
lean_ctor_set(x_10, 4, x_92);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_nat_add(x_60, x_79);
lean_dec(x_60);
x_94 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_26);
lean_ctor_set(x_94, 2, x_27);
lean_ctor_set(x_94, 3, x_46);
lean_ctor_set(x_94, 4, x_29);
lean_ctor_set(x_10, 4, x_94);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_28);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_95, x_35);
lean_dec(x_35);
x_97 = lean_nat_add(x_96, x_25);
lean_dec(x_25);
x_98 = lean_nat_add(x_95, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_45, 0);
lean_inc(x_99);
x_100 = lean_nat_add(x_96, x_99);
lean_dec(x_99);
lean_dec(x_96);
lean_inc(x_32);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_33);
lean_ctor_set(x_101, 2, x_34);
lean_ctor_set(x_101, 3, x_32);
lean_ctor_set(x_101, 4, x_45);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_102 = x_32;
} else {
 lean_dec_ref(x_32);
 x_102 = lean_box(0);
}
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_46, 0);
lean_inc(x_103);
x_104 = lean_nat_add(x_98, x_103);
lean_dec(x_103);
lean_dec(x_98);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 5, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_26);
lean_ctor_set(x_105, 2, x_27);
lean_ctor_set(x_105, 3, x_46);
lean_ctor_set(x_105, 4, x_29);
lean_ctor_set(x_10, 4, x_105);
lean_ctor_set(x_10, 3, x_101);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_nat_add(x_98, x_106);
lean_dec(x_98);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(0, 5, 0);
} else {
 x_108 = x_102;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_26);
lean_ctor_set(x_108, 2, x_27);
lean_ctor_set(x_108, 3, x_46);
lean_ctor_set(x_108, 4, x_29);
lean_ctor_set(x_10, 4, x_108);
lean_ctor_set(x_10, 3, x_101);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_nat_add(x_96, x_109);
lean_dec(x_96);
lean_inc(x_32);
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_33);
lean_ctor_set(x_111, 2, x_34);
lean_ctor_set(x_111, 3, x_32);
lean_ctor_set(x_111, 4, x_45);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_112 = x_32;
} else {
 lean_dec_ref(x_32);
 x_112 = lean_box(0);
}
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_46, 0);
lean_inc(x_113);
x_114 = lean_nat_add(x_98, x_113);
lean_dec(x_113);
lean_dec(x_98);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 5, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_26);
lean_ctor_set(x_115, 2, x_27);
lean_ctor_set(x_115, 3, x_46);
lean_ctor_set(x_115, 4, x_29);
lean_ctor_set(x_10, 4, x_115);
lean_ctor_set(x_10, 3, x_111);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_nat_add(x_98, x_109);
lean_dec(x_98);
if (lean_is_scalar(x_112)) {
 x_117 = lean_alloc_ctor(0, 5, 0);
} else {
 x_117 = x_112;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_26);
lean_ctor_set(x_117, 2, x_27);
lean_ctor_set(x_117, 3, x_46);
lean_ctor_set(x_117, 4, x_29);
lean_ctor_set(x_10, 4, x_117);
lean_ctor_set(x_10, 3, x_111);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_118, x_35);
lean_dec(x_35);
x_120 = lean_nat_add(x_119, x_25);
lean_dec(x_25);
x_121 = lean_nat_add(x_119, x_42);
lean_dec(x_42);
lean_dec(x_119);
lean_ctor_set(x_10, 4, x_28);
lean_ctor_set(x_10, 3, x_32);
lean_ctor_set(x_10, 2, x_34);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_121);
lean_ctor_set(x_4, 4, x_29);
lean_ctor_set(x_4, 2, x_27);
lean_ctor_set(x_4, 1, x_26);
lean_ctor_set(x_4, 0, x_120);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_28) == 0)
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_31, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_31, 1);
lean_inc(x_123);
lean_dec(x_31);
x_124 = lean_ctor_get(x_28, 0);
lean_inc(x_124);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_add(x_125, x_25);
lean_dec(x_25);
x_127 = lean_nat_add(x_125, x_124);
lean_dec(x_124);
x_128 = lean_box(1);
lean_ctor_set(x_11, 4, x_28);
lean_ctor_set(x_11, 3, x_128);
lean_ctor_set(x_11, 2, x_123);
lean_ctor_set(x_11, 1, x_122);
lean_ctor_set(x_11, 0, x_127);
lean_ctor_set(x_10, 4, x_29);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_27);
lean_ctor_set(x_10, 1, x_26);
lean_ctor_set(x_10, 0, x_126);
return x_10;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_25);
x_129 = lean_ctor_get(x_31, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_31, 1);
lean_inc(x_130);
lean_dec(x_31);
x_131 = !lean_is_exclusive(x_28);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_28, 1);
x_133 = lean_ctor_get(x_28, 2);
x_134 = lean_ctor_get(x_28, 4);
lean_dec(x_134);
x_135 = lean_ctor_get(x_28, 3);
lean_dec(x_135);
x_136 = lean_ctor_get(x_28, 0);
lean_dec(x_136);
x_137 = lean_box(1);
x_138 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_28, 4, x_137);
lean_ctor_set(x_28, 3, x_137);
lean_ctor_set(x_28, 2, x_130);
lean_ctor_set(x_28, 1, x_129);
lean_ctor_set(x_28, 0, x_138);
lean_ctor_set(x_11, 4, x_137);
lean_ctor_set(x_11, 3, x_137);
lean_ctor_set(x_11, 0, x_138);
x_139 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_133);
lean_ctor_set(x_10, 1, x_132);
lean_ctor_set(x_10, 0, x_139);
return x_10;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_ctor_get(x_28, 1);
x_141 = lean_ctor_get(x_28, 2);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_28);
x_142 = lean_box(1);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_129);
lean_ctor_set(x_144, 2, x_130);
lean_ctor_set(x_144, 3, x_142);
lean_ctor_set(x_144, 4, x_142);
lean_ctor_set(x_11, 4, x_142);
lean_ctor_set(x_11, 3, x_142);
lean_ctor_set(x_11, 0, x_143);
x_145 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_144);
lean_ctor_set(x_10, 2, x_141);
lean_ctor_set(x_10, 1, x_140);
lean_ctor_set(x_10, 0, x_145);
return x_10;
}
}
}
else
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_25);
x_146 = lean_ctor_get(x_31, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_31, 1);
lean_inc(x_147);
lean_dec(x_31);
x_148 = lean_box(1);
x_149 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_11, 4, x_148);
lean_ctor_set(x_11, 3, x_148);
lean_ctor_set(x_11, 2, x_147);
lean_ctor_set(x_11, 1, x_146);
lean_ctor_set(x_11, 0, x_149);
x_150 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_29);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_27);
lean_ctor_set(x_10, 1, x_26);
lean_ctor_set(x_10, 0, x_150);
return x_10;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_31, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_31, 1);
lean_inc(x_152);
lean_dec(x_31);
lean_ctor_set(x_11, 3, x_29);
x_153 = lean_box(1);
x_154 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_153);
lean_ctor_set(x_10, 2, x_152);
lean_ctor_set(x_10, 1, x_151);
lean_ctor_set(x_10, 0, x_154);
return x_10;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_25);
x_155 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_26, x_27, x_28, x_29, lean_box(0), lean_box(0), lean_box(0));
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 2);
lean_inc(x_158);
lean_dec(x_155);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_ctor_set(x_11, 4, x_24);
lean_ctor_set(x_11, 3, x_23);
lean_ctor_set(x_11, 2, x_22);
lean_ctor_set(x_11, 1, x_21);
lean_ctor_set(x_11, 0, x_20);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_unsigned_to_nat(3u);
x_161 = lean_nat_mul(x_160, x_159);
x_162 = lean_nat_dec_lt(x_161, x_20);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_4);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_nat_add(x_163, x_20);
lean_dec(x_20);
x_165 = lean_nat_add(x_164, x_159);
lean_dec(x_159);
lean_dec(x_164);
lean_ctor_set(x_10, 4, x_158);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_165);
return x_10;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_dec(x_11);
x_166 = lean_ctor_get(x_23, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_24, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_24, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_24, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_24, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_24, 4);
lean_inc(x_171);
x_172 = lean_unsigned_to_nat(2u);
x_173 = lean_nat_mul(x_172, x_166);
x_174 = lean_nat_dec_lt(x_167, x_173);
lean_dec(x_173);
if (x_174 == 0)
{
uint8_t x_175; 
lean_dec(x_167);
lean_free_object(x_10);
lean_free_object(x_4);
x_175 = !lean_is_exclusive(x_24);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_176 = lean_ctor_get(x_24, 4);
lean_dec(x_176);
x_177 = lean_ctor_get(x_24, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_24, 2);
lean_dec(x_178);
x_179 = lean_ctor_get(x_24, 1);
lean_dec(x_179);
x_180 = lean_ctor_get(x_24, 0);
lean_dec(x_180);
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_nat_add(x_181, x_20);
lean_dec(x_20);
x_183 = lean_nat_add(x_182, x_159);
lean_dec(x_182);
x_184 = lean_nat_add(x_181, x_166);
lean_dec(x_166);
x_185 = lean_nat_add(x_181, x_159);
lean_dec(x_159);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_170, 0);
lean_inc(x_186);
x_187 = lean_nat_add(x_184, x_186);
lean_dec(x_186);
lean_dec(x_184);
lean_inc(x_23);
lean_ctor_set(x_24, 4, x_170);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_187);
x_188 = !lean_is_exclusive(x_23);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_23, 4);
lean_dec(x_189);
x_190 = lean_ctor_get(x_23, 3);
lean_dec(x_190);
x_191 = lean_ctor_get(x_23, 2);
lean_dec(x_191);
x_192 = lean_ctor_get(x_23, 1);
lean_dec(x_192);
x_193 = lean_ctor_get(x_23, 0);
lean_dec(x_193);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_171, 0);
lean_inc(x_194);
x_195 = lean_nat_add(x_185, x_194);
lean_dec(x_194);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_195);
x_196 = !lean_is_exclusive(x_158);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_158, 4);
lean_dec(x_197);
x_198 = lean_ctor_get(x_158, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_158, 2);
lean_dec(x_199);
x_200 = lean_ctor_get(x_158, 1);
lean_dec(x_200);
x_201 = lean_ctor_get(x_158, 0);
lean_dec(x_201);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_202; 
lean_dec(x_158);
x_202 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_202, 0, x_183);
lean_ctor_set(x_202, 1, x_168);
lean_ctor_set(x_202, 2, x_169);
lean_ctor_set(x_202, 3, x_24);
lean_ctor_set(x_202, 4, x_23);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_203 = lean_unsigned_to_nat(0u);
x_204 = lean_nat_add(x_185, x_203);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_204);
x_205 = !lean_is_exclusive(x_158);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_158, 4);
lean_dec(x_206);
x_207 = lean_ctor_get(x_158, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_158, 2);
lean_dec(x_208);
x_209 = lean_ctor_get(x_158, 1);
lean_dec(x_209);
x_210 = lean_ctor_get(x_158, 0);
lean_dec(x_210);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_211; 
lean_dec(x_158);
x_211 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_211, 0, x_183);
lean_ctor_set(x_211, 1, x_168);
lean_ctor_set(x_211, 2, x_169);
lean_ctor_set(x_211, 3, x_24);
lean_ctor_set(x_211, 4, x_23);
return x_211;
}
}
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_ctor_get(x_171, 0);
lean_inc(x_212);
x_213 = lean_nat_add(x_185, x_212);
lean_dec(x_212);
lean_dec(x_185);
lean_inc(x_158);
x_214 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_156);
lean_ctor_set(x_214, 2, x_157);
lean_ctor_set(x_214, 3, x_171);
lean_ctor_set(x_214, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_215 = x_158;
} else {
 lean_dec_ref(x_158);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(0, 5, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_183);
lean_ctor_set(x_216, 1, x_168);
lean_ctor_set(x_216, 2, x_169);
lean_ctor_set(x_216, 3, x_24);
lean_ctor_set(x_216, 4, x_214);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_unsigned_to_nat(0u);
x_218 = lean_nat_add(x_185, x_217);
lean_dec(x_185);
lean_inc(x_158);
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_156);
lean_ctor_set(x_219, 2, x_157);
lean_ctor_set(x_219, 3, x_171);
lean_ctor_set(x_219, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_220 = x_158;
} else {
 lean_dec_ref(x_158);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 5, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_183);
lean_ctor_set(x_221, 1, x_168);
lean_ctor_set(x_221, 2, x_169);
lean_ctor_set(x_221, 3, x_24);
lean_ctor_set(x_221, 4, x_219);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_unsigned_to_nat(0u);
x_223 = lean_nat_add(x_184, x_222);
lean_dec(x_184);
lean_inc(x_23);
lean_ctor_set(x_24, 4, x_170);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_223);
x_224 = !lean_is_exclusive(x_23);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_23, 4);
lean_dec(x_225);
x_226 = lean_ctor_get(x_23, 3);
lean_dec(x_226);
x_227 = lean_ctor_get(x_23, 2);
lean_dec(x_227);
x_228 = lean_ctor_get(x_23, 1);
lean_dec(x_228);
x_229 = lean_ctor_get(x_23, 0);
lean_dec(x_229);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_230 = lean_ctor_get(x_171, 0);
lean_inc(x_230);
x_231 = lean_nat_add(x_185, x_230);
lean_dec(x_230);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_231);
x_232 = !lean_is_exclusive(x_158);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_158, 4);
lean_dec(x_233);
x_234 = lean_ctor_get(x_158, 3);
lean_dec(x_234);
x_235 = lean_ctor_get(x_158, 2);
lean_dec(x_235);
x_236 = lean_ctor_get(x_158, 1);
lean_dec(x_236);
x_237 = lean_ctor_get(x_158, 0);
lean_dec(x_237);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_238; 
lean_dec(x_158);
x_238 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_238, 0, x_183);
lean_ctor_set(x_238, 1, x_168);
lean_ctor_set(x_238, 2, x_169);
lean_ctor_set(x_238, 3, x_24);
lean_ctor_set(x_238, 4, x_23);
return x_238;
}
}
else
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_nat_add(x_185, x_222);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_239);
x_240 = !lean_is_exclusive(x_158);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = lean_ctor_get(x_158, 4);
lean_dec(x_241);
x_242 = lean_ctor_get(x_158, 3);
lean_dec(x_242);
x_243 = lean_ctor_get(x_158, 2);
lean_dec(x_243);
x_244 = lean_ctor_get(x_158, 1);
lean_dec(x_244);
x_245 = lean_ctor_get(x_158, 0);
lean_dec(x_245);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_246; 
lean_dec(x_158);
x_246 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_246, 0, x_183);
lean_ctor_set(x_246, 1, x_168);
lean_ctor_set(x_246, 2, x_169);
lean_ctor_set(x_246, 3, x_24);
lean_ctor_set(x_246, 4, x_23);
return x_246;
}
}
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = lean_ctor_get(x_171, 0);
lean_inc(x_247);
x_248 = lean_nat_add(x_185, x_247);
lean_dec(x_247);
lean_dec(x_185);
lean_inc(x_158);
x_249 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_156);
lean_ctor_set(x_249, 2, x_157);
lean_ctor_set(x_249, 3, x_171);
lean_ctor_set(x_249, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_250 = x_158;
} else {
 lean_dec_ref(x_158);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 5, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_183);
lean_ctor_set(x_251, 1, x_168);
lean_ctor_set(x_251, 2, x_169);
lean_ctor_set(x_251, 3, x_24);
lean_ctor_set(x_251, 4, x_249);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_nat_add(x_185, x_222);
lean_dec(x_185);
lean_inc(x_158);
x_253 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_156);
lean_ctor_set(x_253, 2, x_157);
lean_ctor_set(x_253, 3, x_171);
lean_ctor_set(x_253, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_254 = x_158;
} else {
 lean_dec_ref(x_158);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(0, 5, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_183);
lean_ctor_set(x_255, 1, x_168);
lean_ctor_set(x_255, 2, x_169);
lean_ctor_set(x_255, 3, x_24);
lean_ctor_set(x_255, 4, x_253);
return x_255;
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_24);
x_256 = lean_unsigned_to_nat(1u);
x_257 = lean_nat_add(x_256, x_20);
lean_dec(x_20);
x_258 = lean_nat_add(x_257, x_159);
lean_dec(x_257);
x_259 = lean_nat_add(x_256, x_166);
lean_dec(x_166);
x_260 = lean_nat_add(x_256, x_159);
lean_dec(x_159);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_170, 0);
lean_inc(x_261);
x_262 = lean_nat_add(x_259, x_261);
lean_dec(x_261);
lean_dec(x_259);
lean_inc(x_23);
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_21);
lean_ctor_set(x_263, 2, x_22);
lean_ctor_set(x_263, 3, x_23);
lean_ctor_set(x_263, 4, x_170);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 x_264 = x_23;
} else {
 lean_dec_ref(x_23);
 x_264 = lean_box(0);
}
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_265 = lean_ctor_get(x_171, 0);
lean_inc(x_265);
x_266 = lean_nat_add(x_260, x_265);
lean_dec(x_265);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_264)) {
 x_267 = lean_alloc_ctor(0, 5, 0);
} else {
 x_267 = x_264;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_156);
lean_ctor_set(x_267, 2, x_157);
lean_ctor_set(x_267, 3, x_171);
lean_ctor_set(x_267, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_268 = x_158;
} else {
 lean_dec_ref(x_158);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(0, 5, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_258);
lean_ctor_set(x_269, 1, x_168);
lean_ctor_set(x_269, 2, x_169);
lean_ctor_set(x_269, 3, x_263);
lean_ctor_set(x_269, 4, x_267);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_unsigned_to_nat(0u);
x_271 = lean_nat_add(x_260, x_270);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_264)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_264;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_156);
lean_ctor_set(x_272, 2, x_157);
lean_ctor_set(x_272, 3, x_171);
lean_ctor_set(x_272, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_273 = x_158;
} else {
 lean_dec_ref(x_158);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 5, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_258);
lean_ctor_set(x_274, 1, x_168);
lean_ctor_set(x_274, 2, x_169);
lean_ctor_set(x_274, 3, x_263);
lean_ctor_set(x_274, 4, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_unsigned_to_nat(0u);
x_276 = lean_nat_add(x_259, x_275);
lean_dec(x_259);
lean_inc(x_23);
x_277 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_21);
lean_ctor_set(x_277, 2, x_22);
lean_ctor_set(x_277, 3, x_23);
lean_ctor_set(x_277, 4, x_170);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 x_278 = x_23;
} else {
 lean_dec_ref(x_23);
 x_278 = lean_box(0);
}
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_ctor_get(x_171, 0);
lean_inc(x_279);
x_280 = lean_nat_add(x_260, x_279);
lean_dec(x_279);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_278)) {
 x_281 = lean_alloc_ctor(0, 5, 0);
} else {
 x_281 = x_278;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_156);
lean_ctor_set(x_281, 2, x_157);
lean_ctor_set(x_281, 3, x_171);
lean_ctor_set(x_281, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_282 = x_158;
} else {
 lean_dec_ref(x_158);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(0, 5, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_258);
lean_ctor_set(x_283, 1, x_168);
lean_ctor_set(x_283, 2, x_169);
lean_ctor_set(x_283, 3, x_277);
lean_ctor_set(x_283, 4, x_281);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_284 = lean_nat_add(x_260, x_275);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_278)) {
 x_285 = lean_alloc_ctor(0, 5, 0);
} else {
 x_285 = x_278;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_156);
lean_ctor_set(x_285, 2, x_157);
lean_ctor_set(x_285, 3, x_171);
lean_ctor_set(x_285, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_286 = x_158;
} else {
 lean_dec_ref(x_158);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(0, 5, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_258);
lean_ctor_set(x_287, 1, x_168);
lean_ctor_set(x_287, 2, x_169);
lean_ctor_set(x_287, 3, x_277);
lean_ctor_set(x_287, 4, x_285);
return x_287;
}
}
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_166);
x_288 = lean_unsigned_to_nat(1u);
x_289 = lean_nat_add(x_288, x_20);
lean_dec(x_20);
x_290 = lean_nat_add(x_289, x_159);
lean_dec(x_289);
x_291 = lean_nat_add(x_288, x_159);
lean_dec(x_159);
x_292 = lean_nat_add(x_291, x_167);
lean_dec(x_167);
lean_dec(x_291);
lean_ctor_set(x_10, 4, x_158);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_292);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_290);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_24, 0);
lean_inc(x_293);
x_294 = lean_unsigned_to_nat(1u);
x_295 = lean_nat_add(x_294, x_20);
lean_dec(x_20);
x_296 = lean_nat_add(x_294, x_293);
lean_dec(x_293);
x_297 = lean_box(1);
lean_ctor_set(x_10, 4, x_297);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_296);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_295);
return x_4;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_20);
x_298 = lean_box(1);
x_299 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_10, 4, x_298);
lean_ctor_set(x_10, 3, x_298);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_299);
x_300 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_300);
return x_4;
}
}
else
{
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_301; 
lean_dec(x_11);
x_301 = !lean_is_exclusive(x_24);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_302 = lean_ctor_get(x_24, 1);
x_303 = lean_ctor_get(x_24, 2);
x_304 = lean_ctor_get(x_24, 4);
lean_dec(x_304);
x_305 = lean_ctor_get(x_24, 3);
lean_dec(x_305);
x_306 = lean_ctor_get(x_24, 0);
lean_dec(x_306);
x_307 = lean_box(1);
x_308 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_24, 4, x_307);
lean_ctor_set(x_24, 3, x_307);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_308);
lean_ctor_set(x_10, 4, x_307);
lean_ctor_set(x_10, 3, x_307);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_308);
x_309 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_24);
lean_ctor_set(x_4, 2, x_303);
lean_ctor_set(x_4, 1, x_302);
lean_ctor_set(x_4, 0, x_309);
return x_4;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_310 = lean_ctor_get(x_24, 1);
x_311 = lean_ctor_get(x_24, 2);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_24);
x_312 = lean_box(1);
x_313 = lean_unsigned_to_nat(1u);
x_314 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_21);
lean_ctor_set(x_314, 2, x_22);
lean_ctor_set(x_314, 3, x_312);
lean_ctor_set(x_314, 4, x_312);
lean_ctor_set(x_10, 4, x_312);
lean_ctor_set(x_10, 3, x_312);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_313);
x_315 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_314);
lean_ctor_set(x_4, 2, x_311);
lean_ctor_set(x_4, 1, x_310);
lean_ctor_set(x_4, 0, x_315);
return x_4;
}
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_4);
x_316 = lean_box(1);
x_317 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_316);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_317);
return x_10;
}
}
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_318 = lean_ctor_get(x_10, 0);
x_319 = lean_ctor_get(x_10, 1);
x_320 = lean_ctor_get(x_10, 2);
x_321 = lean_ctor_get(x_10, 3);
x_322 = lean_ctor_get(x_10, 4);
x_323 = lean_ctor_get(x_11, 0);
x_324 = lean_ctor_get(x_11, 1);
x_325 = lean_ctor_get(x_11, 2);
x_326 = lean_ctor_get(x_11, 3);
x_327 = lean_ctor_get(x_11, 4);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_11);
x_328 = lean_nat_dec_lt(x_318, x_323);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_318);
x_329 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_319, x_320, x_321, x_322, lean_box(0), lean_box(0), lean_box(0));
x_330 = lean_ctor_get(x_329, 2);
lean_inc(x_330);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_331 = lean_ctor_get(x_329, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_dec(x_329);
x_333 = lean_ctor_get(x_330, 0);
lean_inc(x_333);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
x_334 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_334, 0, x_323);
lean_ctor_set(x_334, 1, x_324);
lean_ctor_set(x_334, 2, x_325);
lean_ctor_set(x_334, 3, x_326);
lean_ctor_set(x_334, 4, x_327);
x_335 = lean_unsigned_to_nat(3u);
x_336 = lean_nat_mul(x_335, x_333);
x_337 = lean_nat_dec_lt(x_336, x_323);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_free_object(x_4);
x_338 = lean_unsigned_to_nat(1u);
x_339 = lean_nat_add(x_338, x_333);
lean_dec(x_333);
x_340 = lean_nat_add(x_339, x_323);
lean_dec(x_323);
lean_dec(x_339);
lean_ctor_set(x_10, 4, x_334);
lean_ctor_set(x_10, 3, x_330);
lean_ctor_set(x_10, 2, x_332);
lean_ctor_set(x_10, 1, x_331);
lean_ctor_set(x_10, 0, x_340);
return x_10;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
lean_dec(x_334);
x_341 = lean_ctor_get(x_326, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_326, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_326, 2);
lean_inc(x_343);
x_344 = lean_ctor_get(x_326, 3);
lean_inc(x_344);
x_345 = lean_ctor_get(x_326, 4);
lean_inc(x_345);
x_346 = lean_ctor_get(x_327, 0);
lean_inc(x_346);
x_347 = lean_unsigned_to_nat(2u);
x_348 = lean_nat_mul(x_347, x_346);
x_349 = lean_nat_dec_lt(x_341, x_348);
lean_dec(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_341);
lean_free_object(x_4);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 x_350 = x_326;
} else {
 lean_dec_ref(x_326);
 x_350 = lean_box(0);
}
x_351 = lean_unsigned_to_nat(1u);
x_352 = lean_nat_add(x_351, x_333);
lean_dec(x_333);
x_353 = lean_nat_add(x_352, x_323);
lean_dec(x_323);
x_354 = lean_nat_add(x_351, x_346);
lean_dec(x_346);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_355 = lean_ctor_get(x_344, 0);
lean_inc(x_355);
x_356 = lean_nat_add(x_352, x_355);
lean_dec(x_355);
lean_dec(x_352);
lean_inc(x_330);
if (lean_is_scalar(x_350)) {
 x_357 = lean_alloc_ctor(0, 5, 0);
} else {
 x_357 = x_350;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_331);
lean_ctor_set(x_357, 2, x_332);
lean_ctor_set(x_357, 3, x_330);
lean_ctor_set(x_357, 4, x_344);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 x_358 = x_330;
} else {
 lean_dec_ref(x_330);
 x_358 = lean_box(0);
}
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_345, 0);
lean_inc(x_359);
x_360 = lean_nat_add(x_354, x_359);
lean_dec(x_359);
lean_dec(x_354);
if (lean_is_scalar(x_358)) {
 x_361 = lean_alloc_ctor(0, 5, 0);
} else {
 x_361 = x_358;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_324);
lean_ctor_set(x_361, 2, x_325);
lean_ctor_set(x_361, 3, x_345);
lean_ctor_set(x_361, 4, x_327);
lean_ctor_set(x_10, 4, x_361);
lean_ctor_set(x_10, 3, x_357);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_unsigned_to_nat(0u);
x_363 = lean_nat_add(x_354, x_362);
lean_dec(x_354);
if (lean_is_scalar(x_358)) {
 x_364 = lean_alloc_ctor(0, 5, 0);
} else {
 x_364 = x_358;
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_324);
lean_ctor_set(x_364, 2, x_325);
lean_ctor_set(x_364, 3, x_345);
lean_ctor_set(x_364, 4, x_327);
lean_ctor_set(x_10, 4, x_364);
lean_ctor_set(x_10, 3, x_357);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = lean_unsigned_to_nat(0u);
x_366 = lean_nat_add(x_352, x_365);
lean_dec(x_352);
lean_inc(x_330);
if (lean_is_scalar(x_350)) {
 x_367 = lean_alloc_ctor(0, 5, 0);
} else {
 x_367 = x_350;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_331);
lean_ctor_set(x_367, 2, x_332);
lean_ctor_set(x_367, 3, x_330);
lean_ctor_set(x_367, 4, x_344);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 x_368 = x_330;
} else {
 lean_dec_ref(x_330);
 x_368 = lean_box(0);
}
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_345, 0);
lean_inc(x_369);
x_370 = lean_nat_add(x_354, x_369);
lean_dec(x_369);
lean_dec(x_354);
if (lean_is_scalar(x_368)) {
 x_371 = lean_alloc_ctor(0, 5, 0);
} else {
 x_371 = x_368;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_324);
lean_ctor_set(x_371, 2, x_325);
lean_ctor_set(x_371, 3, x_345);
lean_ctor_set(x_371, 4, x_327);
lean_ctor_set(x_10, 4, x_371);
lean_ctor_set(x_10, 3, x_367);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_nat_add(x_354, x_365);
lean_dec(x_354);
if (lean_is_scalar(x_368)) {
 x_373 = lean_alloc_ctor(0, 5, 0);
} else {
 x_373 = x_368;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_324);
lean_ctor_set(x_373, 2, x_325);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set(x_373, 4, x_327);
lean_ctor_set(x_10, 4, x_373);
lean_ctor_set(x_10, 3, x_367);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
x_374 = lean_unsigned_to_nat(1u);
x_375 = lean_nat_add(x_374, x_333);
lean_dec(x_333);
x_376 = lean_nat_add(x_375, x_323);
lean_dec(x_323);
x_377 = lean_nat_add(x_375, x_341);
lean_dec(x_341);
lean_dec(x_375);
lean_ctor_set(x_10, 4, x_326);
lean_ctor_set(x_10, 3, x_330);
lean_ctor_set(x_10, 2, x_332);
lean_ctor_set(x_10, 1, x_331);
lean_ctor_set(x_10, 0, x_377);
lean_ctor_set(x_4, 4, x_327);
lean_ctor_set(x_4, 2, x_325);
lean_ctor_set(x_4, 1, x_324);
lean_ctor_set(x_4, 0, x_376);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_326) == 0)
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_378 = lean_ctor_get(x_329, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_329, 1);
lean_inc(x_379);
lean_dec(x_329);
x_380 = lean_ctor_get(x_326, 0);
lean_inc(x_380);
x_381 = lean_unsigned_to_nat(1u);
x_382 = lean_nat_add(x_381, x_323);
lean_dec(x_323);
x_383 = lean_nat_add(x_381, x_380);
lean_dec(x_380);
x_384 = lean_box(1);
x_385 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_378);
lean_ctor_set(x_385, 2, x_379);
lean_ctor_set(x_385, 3, x_384);
lean_ctor_set(x_385, 4, x_326);
lean_ctor_set(x_10, 4, x_327);
lean_ctor_set(x_10, 3, x_385);
lean_ctor_set(x_10, 2, x_325);
lean_ctor_set(x_10, 1, x_324);
lean_ctor_set(x_10, 0, x_382);
return x_10;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_323);
x_386 = lean_ctor_get(x_329, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_329, 1);
lean_inc(x_387);
lean_dec(x_329);
x_388 = lean_ctor_get(x_326, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_326, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 x_390 = x_326;
} else {
 lean_dec_ref(x_326);
 x_390 = lean_box(0);
}
x_391 = lean_box(1);
x_392 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_390)) {
 x_393 = lean_alloc_ctor(0, 5, 0);
} else {
 x_393 = x_390;
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_386);
lean_ctor_set(x_393, 2, x_387);
lean_ctor_set(x_393, 3, x_391);
lean_ctor_set(x_393, 4, x_391);
x_394 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_324);
lean_ctor_set(x_394, 2, x_325);
lean_ctor_set(x_394, 3, x_391);
lean_ctor_set(x_394, 4, x_391);
x_395 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_394);
lean_ctor_set(x_10, 3, x_393);
lean_ctor_set(x_10, 2, x_389);
lean_ctor_set(x_10, 1, x_388);
lean_ctor_set(x_10, 0, x_395);
return x_10;
}
}
else
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_323);
x_396 = lean_ctor_get(x_329, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_329, 1);
lean_inc(x_397);
lean_dec(x_329);
x_398 = lean_box(1);
x_399 = lean_unsigned_to_nat(1u);
x_400 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_396);
lean_ctor_set(x_400, 2, x_397);
lean_ctor_set(x_400, 3, x_398);
lean_ctor_set(x_400, 4, x_398);
x_401 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_327);
lean_ctor_set(x_10, 3, x_400);
lean_ctor_set(x_10, 2, x_325);
lean_ctor_set(x_10, 1, x_324);
lean_ctor_set(x_10, 0, x_401);
return x_10;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_402 = lean_ctor_get(x_329, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_329, 1);
lean_inc(x_403);
lean_dec(x_329);
x_404 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_404, 0, x_323);
lean_ctor_set(x_404, 1, x_324);
lean_ctor_set(x_404, 2, x_325);
lean_ctor_set(x_404, 3, x_327);
lean_ctor_set(x_404, 4, x_327);
x_405 = lean_box(1);
x_406 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_404);
lean_ctor_set(x_10, 3, x_405);
lean_ctor_set(x_10, 2, x_403);
lean_ctor_set(x_10, 1, x_402);
lean_ctor_set(x_10, 0, x_406);
return x_10;
}
}
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_323);
x_407 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_324, x_325, x_326, x_327, lean_box(0), lean_box(0), lean_box(0));
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_407, 2);
lean_inc(x_410);
lean_dec(x_407);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
x_411 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_411, 0, x_318);
lean_ctor_set(x_411, 1, x_319);
lean_ctor_set(x_411, 2, x_320);
lean_ctor_set(x_411, 3, x_321);
lean_ctor_set(x_411, 4, x_322);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_412 = lean_ctor_get(x_410, 0);
lean_inc(x_412);
x_413 = lean_unsigned_to_nat(3u);
x_414 = lean_nat_mul(x_413, x_412);
x_415 = lean_nat_dec_lt(x_414, x_318);
lean_dec(x_414);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_free_object(x_4);
x_416 = lean_unsigned_to_nat(1u);
x_417 = lean_nat_add(x_416, x_318);
lean_dec(x_318);
x_418 = lean_nat_add(x_417, x_412);
lean_dec(x_412);
lean_dec(x_417);
lean_ctor_set(x_10, 4, x_410);
lean_ctor_set(x_10, 3, x_411);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_418);
return x_10;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_dec(x_411);
x_419 = lean_ctor_get(x_321, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_322, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_322, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_322, 2);
lean_inc(x_422);
x_423 = lean_ctor_get(x_322, 3);
lean_inc(x_423);
x_424 = lean_ctor_get(x_322, 4);
lean_inc(x_424);
x_425 = lean_unsigned_to_nat(2u);
x_426 = lean_nat_mul(x_425, x_419);
x_427 = lean_nat_dec_lt(x_420, x_426);
lean_dec(x_426);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_420);
lean_free_object(x_10);
lean_free_object(x_4);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 lean_ctor_release(x_322, 4);
 x_428 = x_322;
} else {
 lean_dec_ref(x_322);
 x_428 = lean_box(0);
}
x_429 = lean_unsigned_to_nat(1u);
x_430 = lean_nat_add(x_429, x_318);
lean_dec(x_318);
x_431 = lean_nat_add(x_430, x_412);
lean_dec(x_430);
x_432 = lean_nat_add(x_429, x_419);
lean_dec(x_419);
x_433 = lean_nat_add(x_429, x_412);
lean_dec(x_412);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = lean_ctor_get(x_423, 0);
lean_inc(x_434);
x_435 = lean_nat_add(x_432, x_434);
lean_dec(x_434);
lean_dec(x_432);
lean_inc(x_321);
if (lean_is_scalar(x_428)) {
 x_436 = lean_alloc_ctor(0, 5, 0);
} else {
 x_436 = x_428;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_319);
lean_ctor_set(x_436, 2, x_320);
lean_ctor_set(x_436, 3, x_321);
lean_ctor_set(x_436, 4, x_423);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 x_437 = x_321;
} else {
 lean_dec_ref(x_321);
 x_437 = lean_box(0);
}
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_438 = lean_ctor_get(x_424, 0);
lean_inc(x_438);
x_439 = lean_nat_add(x_433, x_438);
lean_dec(x_438);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_437)) {
 x_440 = lean_alloc_ctor(0, 5, 0);
} else {
 x_440 = x_437;
}
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_408);
lean_ctor_set(x_440, 2, x_409);
lean_ctor_set(x_440, 3, x_424);
lean_ctor_set(x_440, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_441 = x_410;
} else {
 lean_dec_ref(x_410);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(0, 5, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_431);
lean_ctor_set(x_442, 1, x_421);
lean_ctor_set(x_442, 2, x_422);
lean_ctor_set(x_442, 3, x_436);
lean_ctor_set(x_442, 4, x_440);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_443 = lean_unsigned_to_nat(0u);
x_444 = lean_nat_add(x_433, x_443);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(0, 5, 0);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_408);
lean_ctor_set(x_445, 2, x_409);
lean_ctor_set(x_445, 3, x_424);
lean_ctor_set(x_445, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_446 = x_410;
} else {
 lean_dec_ref(x_410);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(0, 5, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_431);
lean_ctor_set(x_447, 1, x_421);
lean_ctor_set(x_447, 2, x_422);
lean_ctor_set(x_447, 3, x_436);
lean_ctor_set(x_447, 4, x_445);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_448 = lean_unsigned_to_nat(0u);
x_449 = lean_nat_add(x_432, x_448);
lean_dec(x_432);
lean_inc(x_321);
if (lean_is_scalar(x_428)) {
 x_450 = lean_alloc_ctor(0, 5, 0);
} else {
 x_450 = x_428;
}
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_319);
lean_ctor_set(x_450, 2, x_320);
lean_ctor_set(x_450, 3, x_321);
lean_ctor_set(x_450, 4, x_423);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 x_451 = x_321;
} else {
 lean_dec_ref(x_321);
 x_451 = lean_box(0);
}
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_452 = lean_ctor_get(x_424, 0);
lean_inc(x_452);
x_453 = lean_nat_add(x_433, x_452);
lean_dec(x_452);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_451)) {
 x_454 = lean_alloc_ctor(0, 5, 0);
} else {
 x_454 = x_451;
}
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_408);
lean_ctor_set(x_454, 2, x_409);
lean_ctor_set(x_454, 3, x_424);
lean_ctor_set(x_454, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_455 = x_410;
} else {
 lean_dec_ref(x_410);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(0, 5, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_431);
lean_ctor_set(x_456, 1, x_421);
lean_ctor_set(x_456, 2, x_422);
lean_ctor_set(x_456, 3, x_450);
lean_ctor_set(x_456, 4, x_454);
return x_456;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_457 = lean_nat_add(x_433, x_448);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_451)) {
 x_458 = lean_alloc_ctor(0, 5, 0);
} else {
 x_458 = x_451;
}
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_408);
lean_ctor_set(x_458, 2, x_409);
lean_ctor_set(x_458, 3, x_424);
lean_ctor_set(x_458, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_459 = x_410;
} else {
 lean_dec_ref(x_410);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(0, 5, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_431);
lean_ctor_set(x_460, 1, x_421);
lean_ctor_set(x_460, 2, x_422);
lean_ctor_set(x_460, 3, x_450);
lean_ctor_set(x_460, 4, x_458);
return x_460;
}
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_419);
x_461 = lean_unsigned_to_nat(1u);
x_462 = lean_nat_add(x_461, x_318);
lean_dec(x_318);
x_463 = lean_nat_add(x_462, x_412);
lean_dec(x_462);
x_464 = lean_nat_add(x_461, x_412);
lean_dec(x_412);
x_465 = lean_nat_add(x_464, x_420);
lean_dec(x_420);
lean_dec(x_464);
lean_ctor_set(x_10, 4, x_410);
lean_ctor_set(x_10, 3, x_322);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_465);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_463);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_321) == 0)
{
lean_dec(x_411);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_466 = lean_ctor_get(x_322, 0);
lean_inc(x_466);
x_467 = lean_unsigned_to_nat(1u);
x_468 = lean_nat_add(x_467, x_318);
lean_dec(x_318);
x_469 = lean_nat_add(x_467, x_466);
lean_dec(x_466);
x_470 = lean_box(1);
lean_ctor_set(x_10, 4, x_470);
lean_ctor_set(x_10, 3, x_322);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_469);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_468);
return x_4;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_318);
x_471 = lean_box(1);
x_472 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_10, 4, x_471);
lean_ctor_set(x_10, 3, x_471);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_472);
x_473 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_473);
return x_4;
}
}
else
{
lean_dec(x_318);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec(x_411);
x_474 = lean_ctor_get(x_322, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_322, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 lean_ctor_release(x_322, 4);
 x_476 = x_322;
} else {
 lean_dec_ref(x_322);
 x_476 = lean_box(0);
}
x_477 = lean_box(1);
x_478 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_476)) {
 x_479 = lean_alloc_ctor(0, 5, 0);
} else {
 x_479 = x_476;
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_319);
lean_ctor_set(x_479, 2, x_320);
lean_ctor_set(x_479, 3, x_477);
lean_ctor_set(x_479, 4, x_477);
lean_ctor_set(x_10, 4, x_477);
lean_ctor_set(x_10, 3, x_477);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_478);
x_480 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_479);
lean_ctor_set(x_4, 2, x_475);
lean_ctor_set(x_4, 1, x_474);
lean_ctor_set(x_4, 0, x_480);
return x_4;
}
else
{
lean_object* x_481; lean_object* x_482; 
lean_dec(x_320);
lean_dec(x_319);
lean_free_object(x_4);
x_481 = lean_box(1);
x_482 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_481);
lean_ctor_set(x_10, 3, x_411);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_482);
return x_10;
}
}
}
}
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; 
x_483 = lean_ctor_get(x_10, 0);
x_484 = lean_ctor_get(x_10, 1);
x_485 = lean_ctor_get(x_10, 2);
x_486 = lean_ctor_get(x_10, 3);
x_487 = lean_ctor_get(x_10, 4);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_10);
x_488 = lean_ctor_get(x_11, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_11, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_11, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_11, 3);
lean_inc(x_491);
x_492 = lean_ctor_get(x_11, 4);
lean_inc(x_492);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_493 = x_11;
} else {
 lean_dec_ref(x_11);
 x_493 = lean_box(0);
}
x_494 = lean_nat_dec_lt(x_483, x_488);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; 
lean_dec(x_483);
x_495 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_484, x_485, x_486, x_487, lean_box(0), lean_box(0), lean_box(0));
x_496 = lean_ctor_get(x_495, 2);
lean_inc(x_496);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_498);
lean_dec(x_495);
x_499 = lean_ctor_get(x_496, 0);
lean_inc(x_499);
lean_inc(x_492);
lean_inc(x_491);
lean_inc(x_490);
lean_inc(x_489);
lean_inc(x_488);
if (lean_is_scalar(x_493)) {
 x_500 = lean_alloc_ctor(0, 5, 0);
} else {
 x_500 = x_493;
}
lean_ctor_set(x_500, 0, x_488);
lean_ctor_set(x_500, 1, x_489);
lean_ctor_set(x_500, 2, x_490);
lean_ctor_set(x_500, 3, x_491);
lean_ctor_set(x_500, 4, x_492);
x_501 = lean_unsigned_to_nat(3u);
x_502 = lean_nat_mul(x_501, x_499);
x_503 = lean_nat_dec_lt(x_502, x_488);
lean_dec(x_502);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_492);
lean_dec(x_491);
lean_dec(x_490);
lean_dec(x_489);
lean_free_object(x_4);
x_504 = lean_unsigned_to_nat(1u);
x_505 = lean_nat_add(x_504, x_499);
lean_dec(x_499);
x_506 = lean_nat_add(x_505, x_488);
lean_dec(x_488);
lean_dec(x_505);
x_507 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_497);
lean_ctor_set(x_507, 2, x_498);
lean_ctor_set(x_507, 3, x_496);
lean_ctor_set(x_507, 4, x_500);
return x_507;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; 
lean_dec(x_500);
x_508 = lean_ctor_get(x_491, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_491, 1);
lean_inc(x_509);
x_510 = lean_ctor_get(x_491, 2);
lean_inc(x_510);
x_511 = lean_ctor_get(x_491, 3);
lean_inc(x_511);
x_512 = lean_ctor_get(x_491, 4);
lean_inc(x_512);
x_513 = lean_ctor_get(x_492, 0);
lean_inc(x_513);
x_514 = lean_unsigned_to_nat(2u);
x_515 = lean_nat_mul(x_514, x_513);
x_516 = lean_nat_dec_lt(x_508, x_515);
lean_dec(x_515);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_508);
lean_free_object(x_4);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 lean_ctor_release(x_491, 2);
 lean_ctor_release(x_491, 3);
 lean_ctor_release(x_491, 4);
 x_517 = x_491;
} else {
 lean_dec_ref(x_491);
 x_517 = lean_box(0);
}
x_518 = lean_unsigned_to_nat(1u);
x_519 = lean_nat_add(x_518, x_499);
lean_dec(x_499);
x_520 = lean_nat_add(x_519, x_488);
lean_dec(x_488);
x_521 = lean_nat_add(x_518, x_513);
lean_dec(x_513);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_522 = lean_ctor_get(x_511, 0);
lean_inc(x_522);
x_523 = lean_nat_add(x_519, x_522);
lean_dec(x_522);
lean_dec(x_519);
lean_inc(x_496);
if (lean_is_scalar(x_517)) {
 x_524 = lean_alloc_ctor(0, 5, 0);
} else {
 x_524 = x_517;
}
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_497);
lean_ctor_set(x_524, 2, x_498);
lean_ctor_set(x_524, 3, x_496);
lean_ctor_set(x_524, 4, x_511);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 lean_ctor_release(x_496, 2);
 lean_ctor_release(x_496, 3);
 lean_ctor_release(x_496, 4);
 x_525 = x_496;
} else {
 lean_dec_ref(x_496);
 x_525 = lean_box(0);
}
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_526 = lean_ctor_get(x_512, 0);
lean_inc(x_526);
x_527 = lean_nat_add(x_521, x_526);
lean_dec(x_526);
lean_dec(x_521);
if (lean_is_scalar(x_525)) {
 x_528 = lean_alloc_ctor(0, 5, 0);
} else {
 x_528 = x_525;
}
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_489);
lean_ctor_set(x_528, 2, x_490);
lean_ctor_set(x_528, 3, x_512);
lean_ctor_set(x_528, 4, x_492);
x_529 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_529, 0, x_520);
lean_ctor_set(x_529, 1, x_509);
lean_ctor_set(x_529, 2, x_510);
lean_ctor_set(x_529, 3, x_524);
lean_ctor_set(x_529, 4, x_528);
return x_529;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_530 = lean_unsigned_to_nat(0u);
x_531 = lean_nat_add(x_521, x_530);
lean_dec(x_521);
if (lean_is_scalar(x_525)) {
 x_532 = lean_alloc_ctor(0, 5, 0);
} else {
 x_532 = x_525;
}
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_489);
lean_ctor_set(x_532, 2, x_490);
lean_ctor_set(x_532, 3, x_512);
lean_ctor_set(x_532, 4, x_492);
x_533 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_533, 0, x_520);
lean_ctor_set(x_533, 1, x_509);
lean_ctor_set(x_533, 2, x_510);
lean_ctor_set(x_533, 3, x_524);
lean_ctor_set(x_533, 4, x_532);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_534 = lean_unsigned_to_nat(0u);
x_535 = lean_nat_add(x_519, x_534);
lean_dec(x_519);
lean_inc(x_496);
if (lean_is_scalar(x_517)) {
 x_536 = lean_alloc_ctor(0, 5, 0);
} else {
 x_536 = x_517;
}
lean_ctor_set(x_536, 0, x_535);
lean_ctor_set(x_536, 1, x_497);
lean_ctor_set(x_536, 2, x_498);
lean_ctor_set(x_536, 3, x_496);
lean_ctor_set(x_536, 4, x_511);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 lean_ctor_release(x_496, 2);
 lean_ctor_release(x_496, 3);
 lean_ctor_release(x_496, 4);
 x_537 = x_496;
} else {
 lean_dec_ref(x_496);
 x_537 = lean_box(0);
}
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_538 = lean_ctor_get(x_512, 0);
lean_inc(x_538);
x_539 = lean_nat_add(x_521, x_538);
lean_dec(x_538);
lean_dec(x_521);
if (lean_is_scalar(x_537)) {
 x_540 = lean_alloc_ctor(0, 5, 0);
} else {
 x_540 = x_537;
}
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_489);
lean_ctor_set(x_540, 2, x_490);
lean_ctor_set(x_540, 3, x_512);
lean_ctor_set(x_540, 4, x_492);
x_541 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_541, 0, x_520);
lean_ctor_set(x_541, 1, x_509);
lean_ctor_set(x_541, 2, x_510);
lean_ctor_set(x_541, 3, x_536);
lean_ctor_set(x_541, 4, x_540);
return x_541;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_nat_add(x_521, x_534);
lean_dec(x_521);
if (lean_is_scalar(x_537)) {
 x_543 = lean_alloc_ctor(0, 5, 0);
} else {
 x_543 = x_537;
}
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_489);
lean_ctor_set(x_543, 2, x_490);
lean_ctor_set(x_543, 3, x_512);
lean_ctor_set(x_543, 4, x_492);
x_544 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_544, 0, x_520);
lean_ctor_set(x_544, 1, x_509);
lean_ctor_set(x_544, 2, x_510);
lean_ctor_set(x_544, 3, x_536);
lean_ctor_set(x_544, 4, x_543);
return x_544;
}
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
x_545 = lean_unsigned_to_nat(1u);
x_546 = lean_nat_add(x_545, x_499);
lean_dec(x_499);
x_547 = lean_nat_add(x_546, x_488);
lean_dec(x_488);
x_548 = lean_nat_add(x_546, x_508);
lean_dec(x_508);
lean_dec(x_546);
x_549 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_497);
lean_ctor_set(x_549, 2, x_498);
lean_ctor_set(x_549, 3, x_496);
lean_ctor_set(x_549, 4, x_491);
lean_ctor_set(x_4, 4, x_492);
lean_ctor_set(x_4, 3, x_549);
lean_ctor_set(x_4, 2, x_490);
lean_ctor_set(x_4, 1, x_489);
lean_ctor_set(x_4, 0, x_547);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_491) == 0)
{
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_550 = lean_ctor_get(x_495, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_495, 1);
lean_inc(x_551);
lean_dec(x_495);
x_552 = lean_ctor_get(x_491, 0);
lean_inc(x_552);
x_553 = lean_unsigned_to_nat(1u);
x_554 = lean_nat_add(x_553, x_488);
lean_dec(x_488);
x_555 = lean_nat_add(x_553, x_552);
lean_dec(x_552);
x_556 = lean_box(1);
if (lean_is_scalar(x_493)) {
 x_557 = lean_alloc_ctor(0, 5, 0);
} else {
 x_557 = x_493;
}
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_550);
lean_ctor_set(x_557, 2, x_551);
lean_ctor_set(x_557, 3, x_556);
lean_ctor_set(x_557, 4, x_491);
x_558 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_558, 0, x_554);
lean_ctor_set(x_558, 1, x_489);
lean_ctor_set(x_558, 2, x_490);
lean_ctor_set(x_558, 3, x_557);
lean_ctor_set(x_558, 4, x_492);
return x_558;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_488);
x_559 = lean_ctor_get(x_495, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_495, 1);
lean_inc(x_560);
lean_dec(x_495);
x_561 = lean_ctor_get(x_491, 1);
lean_inc(x_561);
x_562 = lean_ctor_get(x_491, 2);
lean_inc(x_562);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 lean_ctor_release(x_491, 2);
 lean_ctor_release(x_491, 3);
 lean_ctor_release(x_491, 4);
 x_563 = x_491;
} else {
 lean_dec_ref(x_491);
 x_563 = lean_box(0);
}
x_564 = lean_box(1);
x_565 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_563)) {
 x_566 = lean_alloc_ctor(0, 5, 0);
} else {
 x_566 = x_563;
}
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_559);
lean_ctor_set(x_566, 2, x_560);
lean_ctor_set(x_566, 3, x_564);
lean_ctor_set(x_566, 4, x_564);
if (lean_is_scalar(x_493)) {
 x_567 = lean_alloc_ctor(0, 5, 0);
} else {
 x_567 = x_493;
}
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_489);
lean_ctor_set(x_567, 2, x_490);
lean_ctor_set(x_567, 3, x_564);
lean_ctor_set(x_567, 4, x_564);
x_568 = lean_unsigned_to_nat(3u);
x_569 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_561);
lean_ctor_set(x_569, 2, x_562);
lean_ctor_set(x_569, 3, x_566);
lean_ctor_set(x_569, 4, x_567);
return x_569;
}
}
else
{
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_488);
x_570 = lean_ctor_get(x_495, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_495, 1);
lean_inc(x_571);
lean_dec(x_495);
x_572 = lean_box(1);
x_573 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_493)) {
 x_574 = lean_alloc_ctor(0, 5, 0);
} else {
 x_574 = x_493;
}
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_570);
lean_ctor_set(x_574, 2, x_571);
lean_ctor_set(x_574, 3, x_572);
lean_ctor_set(x_574, 4, x_572);
x_575 = lean_unsigned_to_nat(3u);
x_576 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_489);
lean_ctor_set(x_576, 2, x_490);
lean_ctor_set(x_576, 3, x_574);
lean_ctor_set(x_576, 4, x_492);
return x_576;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_577 = lean_ctor_get(x_495, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_495, 1);
lean_inc(x_578);
lean_dec(x_495);
if (lean_is_scalar(x_493)) {
 x_579 = lean_alloc_ctor(0, 5, 0);
} else {
 x_579 = x_493;
}
lean_ctor_set(x_579, 0, x_488);
lean_ctor_set(x_579, 1, x_489);
lean_ctor_set(x_579, 2, x_490);
lean_ctor_set(x_579, 3, x_492);
lean_ctor_set(x_579, 4, x_492);
x_580 = lean_box(1);
x_581 = lean_unsigned_to_nat(2u);
x_582 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_577);
lean_ctor_set(x_582, 2, x_578);
lean_ctor_set(x_582, 3, x_580);
lean_ctor_set(x_582, 4, x_579);
return x_582;
}
}
}
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_488);
x_583 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_489, x_490, x_491, x_492, lean_box(0), lean_box(0), lean_box(0));
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
x_586 = lean_ctor_get(x_583, 2);
lean_inc(x_586);
lean_dec(x_583);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
if (lean_is_scalar(x_493)) {
 x_587 = lean_alloc_ctor(0, 5, 0);
} else {
 x_587 = x_493;
}
lean_ctor_set(x_587, 0, x_483);
lean_ctor_set(x_587, 1, x_484);
lean_ctor_set(x_587, 2, x_485);
lean_ctor_set(x_587, 3, x_486);
lean_ctor_set(x_587, 4, x_487);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; 
x_588 = lean_ctor_get(x_586, 0);
lean_inc(x_588);
x_589 = lean_unsigned_to_nat(3u);
x_590 = lean_nat_mul(x_589, x_588);
x_591 = lean_nat_dec_lt(x_590, x_483);
lean_dec(x_590);
if (x_591 == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_484);
lean_free_object(x_4);
x_592 = lean_unsigned_to_nat(1u);
x_593 = lean_nat_add(x_592, x_483);
lean_dec(x_483);
x_594 = lean_nat_add(x_593, x_588);
lean_dec(x_588);
lean_dec(x_593);
x_595 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_595, 0, x_594);
lean_ctor_set(x_595, 1, x_584);
lean_ctor_set(x_595, 2, x_585);
lean_ctor_set(x_595, 3, x_587);
lean_ctor_set(x_595, 4, x_586);
return x_595;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
lean_dec(x_587);
x_596 = lean_ctor_get(x_486, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_487, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_487, 1);
lean_inc(x_598);
x_599 = lean_ctor_get(x_487, 2);
lean_inc(x_599);
x_600 = lean_ctor_get(x_487, 3);
lean_inc(x_600);
x_601 = lean_ctor_get(x_487, 4);
lean_inc(x_601);
x_602 = lean_unsigned_to_nat(2u);
x_603 = lean_nat_mul(x_602, x_596);
x_604 = lean_nat_dec_lt(x_597, x_603);
lean_dec(x_603);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_597);
lean_free_object(x_4);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 lean_ctor_release(x_487, 4);
 x_605 = x_487;
} else {
 lean_dec_ref(x_487);
 x_605 = lean_box(0);
}
x_606 = lean_unsigned_to_nat(1u);
x_607 = lean_nat_add(x_606, x_483);
lean_dec(x_483);
x_608 = lean_nat_add(x_607, x_588);
lean_dec(x_607);
x_609 = lean_nat_add(x_606, x_596);
lean_dec(x_596);
x_610 = lean_nat_add(x_606, x_588);
lean_dec(x_588);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_611 = lean_ctor_get(x_600, 0);
lean_inc(x_611);
x_612 = lean_nat_add(x_609, x_611);
lean_dec(x_611);
lean_dec(x_609);
lean_inc(x_486);
if (lean_is_scalar(x_605)) {
 x_613 = lean_alloc_ctor(0, 5, 0);
} else {
 x_613 = x_605;
}
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_484);
lean_ctor_set(x_613, 2, x_485);
lean_ctor_set(x_613, 3, x_486);
lean_ctor_set(x_613, 4, x_600);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 lean_ctor_release(x_486, 2);
 lean_ctor_release(x_486, 3);
 lean_ctor_release(x_486, 4);
 x_614 = x_486;
} else {
 lean_dec_ref(x_486);
 x_614 = lean_box(0);
}
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_615 = lean_ctor_get(x_601, 0);
lean_inc(x_615);
x_616 = lean_nat_add(x_610, x_615);
lean_dec(x_615);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_614)) {
 x_617 = lean_alloc_ctor(0, 5, 0);
} else {
 x_617 = x_614;
}
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_584);
lean_ctor_set(x_617, 2, x_585);
lean_ctor_set(x_617, 3, x_601);
lean_ctor_set(x_617, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_618 = x_586;
} else {
 lean_dec_ref(x_586);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(0, 5, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_608);
lean_ctor_set(x_619, 1, x_598);
lean_ctor_set(x_619, 2, x_599);
lean_ctor_set(x_619, 3, x_613);
lean_ctor_set(x_619, 4, x_617);
return x_619;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_620 = lean_unsigned_to_nat(0u);
x_621 = lean_nat_add(x_610, x_620);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_614)) {
 x_622 = lean_alloc_ctor(0, 5, 0);
} else {
 x_622 = x_614;
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_584);
lean_ctor_set(x_622, 2, x_585);
lean_ctor_set(x_622, 3, x_601);
lean_ctor_set(x_622, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_623 = x_586;
} else {
 lean_dec_ref(x_586);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(0, 5, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_608);
lean_ctor_set(x_624, 1, x_598);
lean_ctor_set(x_624, 2, x_599);
lean_ctor_set(x_624, 3, x_613);
lean_ctor_set(x_624, 4, x_622);
return x_624;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_625 = lean_unsigned_to_nat(0u);
x_626 = lean_nat_add(x_609, x_625);
lean_dec(x_609);
lean_inc(x_486);
if (lean_is_scalar(x_605)) {
 x_627 = lean_alloc_ctor(0, 5, 0);
} else {
 x_627 = x_605;
}
lean_ctor_set(x_627, 0, x_626);
lean_ctor_set(x_627, 1, x_484);
lean_ctor_set(x_627, 2, x_485);
lean_ctor_set(x_627, 3, x_486);
lean_ctor_set(x_627, 4, x_600);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 lean_ctor_release(x_486, 2);
 lean_ctor_release(x_486, 3);
 lean_ctor_release(x_486, 4);
 x_628 = x_486;
} else {
 lean_dec_ref(x_486);
 x_628 = lean_box(0);
}
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_629 = lean_ctor_get(x_601, 0);
lean_inc(x_629);
x_630 = lean_nat_add(x_610, x_629);
lean_dec(x_629);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_628)) {
 x_631 = lean_alloc_ctor(0, 5, 0);
} else {
 x_631 = x_628;
}
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_584);
lean_ctor_set(x_631, 2, x_585);
lean_ctor_set(x_631, 3, x_601);
lean_ctor_set(x_631, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_632 = x_586;
} else {
 lean_dec_ref(x_586);
 x_632 = lean_box(0);
}
if (lean_is_scalar(x_632)) {
 x_633 = lean_alloc_ctor(0, 5, 0);
} else {
 x_633 = x_632;
}
lean_ctor_set(x_633, 0, x_608);
lean_ctor_set(x_633, 1, x_598);
lean_ctor_set(x_633, 2, x_599);
lean_ctor_set(x_633, 3, x_627);
lean_ctor_set(x_633, 4, x_631);
return x_633;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_634 = lean_nat_add(x_610, x_625);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_628)) {
 x_635 = lean_alloc_ctor(0, 5, 0);
} else {
 x_635 = x_628;
}
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_584);
lean_ctor_set(x_635, 2, x_585);
lean_ctor_set(x_635, 3, x_601);
lean_ctor_set(x_635, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_636 = x_586;
} else {
 lean_dec_ref(x_586);
 x_636 = lean_box(0);
}
if (lean_is_scalar(x_636)) {
 x_637 = lean_alloc_ctor(0, 5, 0);
} else {
 x_637 = x_636;
}
lean_ctor_set(x_637, 0, x_608);
lean_ctor_set(x_637, 1, x_598);
lean_ctor_set(x_637, 2, x_599);
lean_ctor_set(x_637, 3, x_627);
lean_ctor_set(x_637, 4, x_635);
return x_637;
}
}
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_596);
x_638 = lean_unsigned_to_nat(1u);
x_639 = lean_nat_add(x_638, x_483);
lean_dec(x_483);
x_640 = lean_nat_add(x_639, x_588);
lean_dec(x_639);
x_641 = lean_nat_add(x_638, x_588);
lean_dec(x_588);
x_642 = lean_nat_add(x_641, x_597);
lean_dec(x_597);
lean_dec(x_641);
x_643 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_584);
lean_ctor_set(x_643, 2, x_585);
lean_ctor_set(x_643, 3, x_487);
lean_ctor_set(x_643, 4, x_586);
lean_ctor_set(x_4, 4, x_643);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_640);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_486) == 0)
{
lean_dec(x_587);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_644 = lean_ctor_get(x_487, 0);
lean_inc(x_644);
x_645 = lean_unsigned_to_nat(1u);
x_646 = lean_nat_add(x_645, x_483);
lean_dec(x_483);
x_647 = lean_nat_add(x_645, x_644);
lean_dec(x_644);
x_648 = lean_box(1);
x_649 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_649, 0, x_647);
lean_ctor_set(x_649, 1, x_584);
lean_ctor_set(x_649, 2, x_585);
lean_ctor_set(x_649, 3, x_487);
lean_ctor_set(x_649, 4, x_648);
lean_ctor_set(x_4, 4, x_649);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_646);
return x_4;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_483);
x_650 = lean_box(1);
x_651 = lean_unsigned_to_nat(1u);
x_652 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_584);
lean_ctor_set(x_652, 2, x_585);
lean_ctor_set(x_652, 3, x_650);
lean_ctor_set(x_652, 4, x_650);
x_653 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_652);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_653);
return x_4;
}
}
else
{
lean_dec(x_483);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_587);
x_654 = lean_ctor_get(x_487, 1);
lean_inc(x_654);
x_655 = lean_ctor_get(x_487, 2);
lean_inc(x_655);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 lean_ctor_release(x_487, 4);
 x_656 = x_487;
} else {
 lean_dec_ref(x_487);
 x_656 = lean_box(0);
}
x_657 = lean_box(1);
x_658 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_656)) {
 x_659 = lean_alloc_ctor(0, 5, 0);
} else {
 x_659 = x_656;
}
lean_ctor_set(x_659, 0, x_658);
lean_ctor_set(x_659, 1, x_484);
lean_ctor_set(x_659, 2, x_485);
lean_ctor_set(x_659, 3, x_657);
lean_ctor_set(x_659, 4, x_657);
x_660 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_584);
lean_ctor_set(x_660, 2, x_585);
lean_ctor_set(x_660, 3, x_657);
lean_ctor_set(x_660, 4, x_657);
x_661 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_660);
lean_ctor_set(x_4, 3, x_659);
lean_ctor_set(x_4, 2, x_655);
lean_ctor_set(x_4, 1, x_654);
lean_ctor_set(x_4, 0, x_661);
return x_4;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_485);
lean_dec(x_484);
lean_free_object(x_4);
x_662 = lean_box(1);
x_663 = lean_unsigned_to_nat(2u);
x_664 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_584);
lean_ctor_set(x_664, 2, x_585);
lean_ctor_set(x_664, 3, x_587);
lean_ctor_set(x_664, 4, x_662);
return x_664;
}
}
}
}
}
}
else
{
lean_free_object(x_4);
return x_10;
}
}
else
{
lean_free_object(x_4);
return x_11;
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_17, 0);
lean_inc(x_665);
lean_dec(x_17);
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
lean_dec(x_665);
lean_ctor_set(x_4, 2, x_667);
lean_ctor_set(x_4, 1, x_666);
return x_4;
}
}
default: 
{
lean_object* x_668; lean_object* x_669; 
lean_free_object(x_4);
lean_dec(x_7);
x_668 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insert_u2098___spec__1___rarg(x_1, x_2, x_3, x_11, lean_box(0));
x_669 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_8, x_9, x_10, x_668, lean_box(0), lean_box(0), lean_box(0));
return x_669;
}
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; 
x_670 = lean_ctor_get(x_4, 0);
x_671 = lean_ctor_get(x_4, 1);
x_672 = lean_ctor_get(x_4, 2);
x_673 = lean_ctor_get(x_4, 3);
x_674 = lean_ctor_get(x_4, 4);
lean_inc(x_674);
lean_inc(x_673);
lean_inc(x_672);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_671);
lean_inc(x_2);
x_675 = lean_apply_2(x_1, x_2, x_671);
x_676 = lean_unbox(x_675);
lean_dec(x_675);
switch (x_676) {
case 0:
{
lean_object* x_677; lean_object* x_678; 
lean_dec(x_670);
x_677 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insert_u2098___spec__1___rarg(x_1, x_2, x_3, x_673, lean_box(0));
x_678 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_671, x_672, x_677, x_674, lean_box(0), lean_box(0), lean_box(0));
return x_678;
}
case 1:
{
lean_object* x_679; lean_object* x_680; 
lean_dec(x_2);
lean_dec(x_1);
x_679 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_671, x_672, lean_box(0));
x_680 = lean_apply_1(x_3, x_679);
if (lean_obj_tag(x_680) == 0)
{
lean_dec(x_670);
if (lean_obj_tag(x_673) == 0)
{
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; uint8_t x_693; 
x_681 = lean_ctor_get(x_673, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_673, 1);
lean_inc(x_682);
x_683 = lean_ctor_get(x_673, 2);
lean_inc(x_683);
x_684 = lean_ctor_get(x_673, 3);
lean_inc(x_684);
x_685 = lean_ctor_get(x_673, 4);
lean_inc(x_685);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 lean_ctor_release(x_673, 2);
 lean_ctor_release(x_673, 3);
 lean_ctor_release(x_673, 4);
 x_686 = x_673;
} else {
 lean_dec_ref(x_673);
 x_686 = lean_box(0);
}
x_687 = lean_ctor_get(x_674, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_674, 1);
lean_inc(x_688);
x_689 = lean_ctor_get(x_674, 2);
lean_inc(x_689);
x_690 = lean_ctor_get(x_674, 3);
lean_inc(x_690);
x_691 = lean_ctor_get(x_674, 4);
lean_inc(x_691);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 lean_ctor_release(x_674, 4);
 x_692 = x_674;
} else {
 lean_dec_ref(x_674);
 x_692 = lean_box(0);
}
x_693 = lean_nat_dec_lt(x_681, x_687);
if (x_693 == 0)
{
lean_object* x_694; lean_object* x_695; 
lean_dec(x_681);
x_694 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_682, x_683, x_684, x_685, lean_box(0), lean_box(0), lean_box(0));
x_695 = lean_ctor_get(x_694, 2);
lean_inc(x_695);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; 
x_696 = lean_ctor_get(x_694, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_694, 1);
lean_inc(x_697);
lean_dec(x_694);
x_698 = lean_ctor_get(x_695, 0);
lean_inc(x_698);
lean_inc(x_691);
lean_inc(x_690);
lean_inc(x_689);
lean_inc(x_688);
lean_inc(x_687);
if (lean_is_scalar(x_692)) {
 x_699 = lean_alloc_ctor(0, 5, 0);
} else {
 x_699 = x_692;
}
lean_ctor_set(x_699, 0, x_687);
lean_ctor_set(x_699, 1, x_688);
lean_ctor_set(x_699, 2, x_689);
lean_ctor_set(x_699, 3, x_690);
lean_ctor_set(x_699, 4, x_691);
x_700 = lean_unsigned_to_nat(3u);
x_701 = lean_nat_mul(x_700, x_698);
x_702 = lean_nat_dec_lt(x_701, x_687);
lean_dec(x_701);
if (x_702 == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_dec(x_691);
lean_dec(x_690);
lean_dec(x_689);
lean_dec(x_688);
x_703 = lean_unsigned_to_nat(1u);
x_704 = lean_nat_add(x_703, x_698);
lean_dec(x_698);
x_705 = lean_nat_add(x_704, x_687);
lean_dec(x_687);
lean_dec(x_704);
if (lean_is_scalar(x_686)) {
 x_706 = lean_alloc_ctor(0, 5, 0);
} else {
 x_706 = x_686;
}
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_696);
lean_ctor_set(x_706, 2, x_697);
lean_ctor_set(x_706, 3, x_695);
lean_ctor_set(x_706, 4, x_699);
return x_706;
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; 
lean_dec(x_699);
x_707 = lean_ctor_get(x_690, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_690, 1);
lean_inc(x_708);
x_709 = lean_ctor_get(x_690, 2);
lean_inc(x_709);
x_710 = lean_ctor_get(x_690, 3);
lean_inc(x_710);
x_711 = lean_ctor_get(x_690, 4);
lean_inc(x_711);
x_712 = lean_ctor_get(x_691, 0);
lean_inc(x_712);
x_713 = lean_unsigned_to_nat(2u);
x_714 = lean_nat_mul(x_713, x_712);
x_715 = lean_nat_dec_lt(x_707, x_714);
lean_dec(x_714);
if (x_715 == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_707);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 lean_ctor_release(x_690, 2);
 lean_ctor_release(x_690, 3);
 lean_ctor_release(x_690, 4);
 x_716 = x_690;
} else {
 lean_dec_ref(x_690);
 x_716 = lean_box(0);
}
x_717 = lean_unsigned_to_nat(1u);
x_718 = lean_nat_add(x_717, x_698);
lean_dec(x_698);
x_719 = lean_nat_add(x_718, x_687);
lean_dec(x_687);
x_720 = lean_nat_add(x_717, x_712);
lean_dec(x_712);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_721 = lean_ctor_get(x_710, 0);
lean_inc(x_721);
x_722 = lean_nat_add(x_718, x_721);
lean_dec(x_721);
lean_dec(x_718);
lean_inc(x_695);
if (lean_is_scalar(x_716)) {
 x_723 = lean_alloc_ctor(0, 5, 0);
} else {
 x_723 = x_716;
}
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_696);
lean_ctor_set(x_723, 2, x_697);
lean_ctor_set(x_723, 3, x_695);
lean_ctor_set(x_723, 4, x_710);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 lean_ctor_release(x_695, 2);
 lean_ctor_release(x_695, 3);
 lean_ctor_release(x_695, 4);
 x_724 = x_695;
} else {
 lean_dec_ref(x_695);
 x_724 = lean_box(0);
}
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_725 = lean_ctor_get(x_711, 0);
lean_inc(x_725);
x_726 = lean_nat_add(x_720, x_725);
lean_dec(x_725);
lean_dec(x_720);
if (lean_is_scalar(x_724)) {
 x_727 = lean_alloc_ctor(0, 5, 0);
} else {
 x_727 = x_724;
}
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_688);
lean_ctor_set(x_727, 2, x_689);
lean_ctor_set(x_727, 3, x_711);
lean_ctor_set(x_727, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_728 = lean_alloc_ctor(0, 5, 0);
} else {
 x_728 = x_686;
}
lean_ctor_set(x_728, 0, x_719);
lean_ctor_set(x_728, 1, x_708);
lean_ctor_set(x_728, 2, x_709);
lean_ctor_set(x_728, 3, x_723);
lean_ctor_set(x_728, 4, x_727);
return x_728;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_729 = lean_unsigned_to_nat(0u);
x_730 = lean_nat_add(x_720, x_729);
lean_dec(x_720);
if (lean_is_scalar(x_724)) {
 x_731 = lean_alloc_ctor(0, 5, 0);
} else {
 x_731 = x_724;
}
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_688);
lean_ctor_set(x_731, 2, x_689);
lean_ctor_set(x_731, 3, x_711);
lean_ctor_set(x_731, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_732 = lean_alloc_ctor(0, 5, 0);
} else {
 x_732 = x_686;
}
lean_ctor_set(x_732, 0, x_719);
lean_ctor_set(x_732, 1, x_708);
lean_ctor_set(x_732, 2, x_709);
lean_ctor_set(x_732, 3, x_723);
lean_ctor_set(x_732, 4, x_731);
return x_732;
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_733 = lean_unsigned_to_nat(0u);
x_734 = lean_nat_add(x_718, x_733);
lean_dec(x_718);
lean_inc(x_695);
if (lean_is_scalar(x_716)) {
 x_735 = lean_alloc_ctor(0, 5, 0);
} else {
 x_735 = x_716;
}
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_696);
lean_ctor_set(x_735, 2, x_697);
lean_ctor_set(x_735, 3, x_695);
lean_ctor_set(x_735, 4, x_710);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 lean_ctor_release(x_695, 2);
 lean_ctor_release(x_695, 3);
 lean_ctor_release(x_695, 4);
 x_736 = x_695;
} else {
 lean_dec_ref(x_695);
 x_736 = lean_box(0);
}
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_737 = lean_ctor_get(x_711, 0);
lean_inc(x_737);
x_738 = lean_nat_add(x_720, x_737);
lean_dec(x_737);
lean_dec(x_720);
if (lean_is_scalar(x_736)) {
 x_739 = lean_alloc_ctor(0, 5, 0);
} else {
 x_739 = x_736;
}
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_688);
lean_ctor_set(x_739, 2, x_689);
lean_ctor_set(x_739, 3, x_711);
lean_ctor_set(x_739, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_740 = lean_alloc_ctor(0, 5, 0);
} else {
 x_740 = x_686;
}
lean_ctor_set(x_740, 0, x_719);
lean_ctor_set(x_740, 1, x_708);
lean_ctor_set(x_740, 2, x_709);
lean_ctor_set(x_740, 3, x_735);
lean_ctor_set(x_740, 4, x_739);
return x_740;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_741 = lean_nat_add(x_720, x_733);
lean_dec(x_720);
if (lean_is_scalar(x_736)) {
 x_742 = lean_alloc_ctor(0, 5, 0);
} else {
 x_742 = x_736;
}
lean_ctor_set(x_742, 0, x_741);
lean_ctor_set(x_742, 1, x_688);
lean_ctor_set(x_742, 2, x_689);
lean_ctor_set(x_742, 3, x_711);
lean_ctor_set(x_742, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_743 = lean_alloc_ctor(0, 5, 0);
} else {
 x_743 = x_686;
}
lean_ctor_set(x_743, 0, x_719);
lean_ctor_set(x_743, 1, x_708);
lean_ctor_set(x_743, 2, x_709);
lean_ctor_set(x_743, 3, x_735);
lean_ctor_set(x_743, 4, x_742);
return x_743;
}
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_dec(x_712);
lean_dec(x_711);
lean_dec(x_710);
lean_dec(x_709);
lean_dec(x_708);
x_744 = lean_unsigned_to_nat(1u);
x_745 = lean_nat_add(x_744, x_698);
lean_dec(x_698);
x_746 = lean_nat_add(x_745, x_687);
lean_dec(x_687);
x_747 = lean_nat_add(x_745, x_707);
lean_dec(x_707);
lean_dec(x_745);
if (lean_is_scalar(x_686)) {
 x_748 = lean_alloc_ctor(0, 5, 0);
} else {
 x_748 = x_686;
}
lean_ctor_set(x_748, 0, x_747);
lean_ctor_set(x_748, 1, x_696);
lean_ctor_set(x_748, 2, x_697);
lean_ctor_set(x_748, 3, x_695);
lean_ctor_set(x_748, 4, x_690);
x_749 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_749, 0, x_746);
lean_ctor_set(x_749, 1, x_688);
lean_ctor_set(x_749, 2, x_689);
lean_ctor_set(x_749, 3, x_748);
lean_ctor_set(x_749, 4, x_691);
return x_749;
}
}
}
else
{
if (lean_obj_tag(x_690) == 0)
{
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_750 = lean_ctor_get(x_694, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_694, 1);
lean_inc(x_751);
lean_dec(x_694);
x_752 = lean_ctor_get(x_690, 0);
lean_inc(x_752);
x_753 = lean_unsigned_to_nat(1u);
x_754 = lean_nat_add(x_753, x_687);
lean_dec(x_687);
x_755 = lean_nat_add(x_753, x_752);
lean_dec(x_752);
x_756 = lean_box(1);
if (lean_is_scalar(x_692)) {
 x_757 = lean_alloc_ctor(0, 5, 0);
} else {
 x_757 = x_692;
}
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set(x_757, 1, x_750);
lean_ctor_set(x_757, 2, x_751);
lean_ctor_set(x_757, 3, x_756);
lean_ctor_set(x_757, 4, x_690);
if (lean_is_scalar(x_686)) {
 x_758 = lean_alloc_ctor(0, 5, 0);
} else {
 x_758 = x_686;
}
lean_ctor_set(x_758, 0, x_754);
lean_ctor_set(x_758, 1, x_688);
lean_ctor_set(x_758, 2, x_689);
lean_ctor_set(x_758, 3, x_757);
lean_ctor_set(x_758, 4, x_691);
return x_758;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_687);
x_759 = lean_ctor_get(x_694, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_694, 1);
lean_inc(x_760);
lean_dec(x_694);
x_761 = lean_ctor_get(x_690, 1);
lean_inc(x_761);
x_762 = lean_ctor_get(x_690, 2);
lean_inc(x_762);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 lean_ctor_release(x_690, 2);
 lean_ctor_release(x_690, 3);
 lean_ctor_release(x_690, 4);
 x_763 = x_690;
} else {
 lean_dec_ref(x_690);
 x_763 = lean_box(0);
}
x_764 = lean_box(1);
x_765 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_763)) {
 x_766 = lean_alloc_ctor(0, 5, 0);
} else {
 x_766 = x_763;
}
lean_ctor_set(x_766, 0, x_765);
lean_ctor_set(x_766, 1, x_759);
lean_ctor_set(x_766, 2, x_760);
lean_ctor_set(x_766, 3, x_764);
lean_ctor_set(x_766, 4, x_764);
if (lean_is_scalar(x_692)) {
 x_767 = lean_alloc_ctor(0, 5, 0);
} else {
 x_767 = x_692;
}
lean_ctor_set(x_767, 0, x_765);
lean_ctor_set(x_767, 1, x_688);
lean_ctor_set(x_767, 2, x_689);
lean_ctor_set(x_767, 3, x_764);
lean_ctor_set(x_767, 4, x_764);
x_768 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_686)) {
 x_769 = lean_alloc_ctor(0, 5, 0);
} else {
 x_769 = x_686;
}
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_761);
lean_ctor_set(x_769, 2, x_762);
lean_ctor_set(x_769, 3, x_766);
lean_ctor_set(x_769, 4, x_767);
return x_769;
}
}
else
{
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
lean_dec(x_687);
x_770 = lean_ctor_get(x_694, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_694, 1);
lean_inc(x_771);
lean_dec(x_694);
x_772 = lean_box(1);
x_773 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_692)) {
 x_774 = lean_alloc_ctor(0, 5, 0);
} else {
 x_774 = x_692;
}
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_770);
lean_ctor_set(x_774, 2, x_771);
lean_ctor_set(x_774, 3, x_772);
lean_ctor_set(x_774, 4, x_772);
x_775 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_686)) {
 x_776 = lean_alloc_ctor(0, 5, 0);
} else {
 x_776 = x_686;
}
lean_ctor_set(x_776, 0, x_775);
lean_ctor_set(x_776, 1, x_688);
lean_ctor_set(x_776, 2, x_689);
lean_ctor_set(x_776, 3, x_774);
lean_ctor_set(x_776, 4, x_691);
return x_776;
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_777 = lean_ctor_get(x_694, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_694, 1);
lean_inc(x_778);
lean_dec(x_694);
if (lean_is_scalar(x_692)) {
 x_779 = lean_alloc_ctor(0, 5, 0);
} else {
 x_779 = x_692;
}
lean_ctor_set(x_779, 0, x_687);
lean_ctor_set(x_779, 1, x_688);
lean_ctor_set(x_779, 2, x_689);
lean_ctor_set(x_779, 3, x_691);
lean_ctor_set(x_779, 4, x_691);
x_780 = lean_box(1);
x_781 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_686)) {
 x_782 = lean_alloc_ctor(0, 5, 0);
} else {
 x_782 = x_686;
}
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_777);
lean_ctor_set(x_782, 2, x_778);
lean_ctor_set(x_782, 3, x_780);
lean_ctor_set(x_782, 4, x_779);
return x_782;
}
}
}
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
lean_dec(x_687);
x_783 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_688, x_689, x_690, x_691, lean_box(0), lean_box(0), lean_box(0));
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
x_786 = lean_ctor_get(x_783, 2);
lean_inc(x_786);
lean_dec(x_783);
lean_inc(x_685);
lean_inc(x_684);
lean_inc(x_683);
lean_inc(x_682);
lean_inc(x_681);
if (lean_is_scalar(x_692)) {
 x_787 = lean_alloc_ctor(0, 5, 0);
} else {
 x_787 = x_692;
}
lean_ctor_set(x_787, 0, x_681);
lean_ctor_set(x_787, 1, x_682);
lean_ctor_set(x_787, 2, x_683);
lean_ctor_set(x_787, 3, x_684);
lean_ctor_set(x_787, 4, x_685);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; 
x_788 = lean_ctor_get(x_786, 0);
lean_inc(x_788);
x_789 = lean_unsigned_to_nat(3u);
x_790 = lean_nat_mul(x_789, x_788);
x_791 = lean_nat_dec_lt(x_790, x_681);
lean_dec(x_790);
if (x_791 == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_683);
lean_dec(x_682);
x_792 = lean_unsigned_to_nat(1u);
x_793 = lean_nat_add(x_792, x_681);
lean_dec(x_681);
x_794 = lean_nat_add(x_793, x_788);
lean_dec(x_788);
lean_dec(x_793);
if (lean_is_scalar(x_686)) {
 x_795 = lean_alloc_ctor(0, 5, 0);
} else {
 x_795 = x_686;
}
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_784);
lean_ctor_set(x_795, 2, x_785);
lean_ctor_set(x_795, 3, x_787);
lean_ctor_set(x_795, 4, x_786);
return x_795;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; uint8_t x_804; 
lean_dec(x_787);
x_796 = lean_ctor_get(x_684, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_685, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_685, 1);
lean_inc(x_798);
x_799 = lean_ctor_get(x_685, 2);
lean_inc(x_799);
x_800 = lean_ctor_get(x_685, 3);
lean_inc(x_800);
x_801 = lean_ctor_get(x_685, 4);
lean_inc(x_801);
x_802 = lean_unsigned_to_nat(2u);
x_803 = lean_nat_mul(x_802, x_796);
x_804 = lean_nat_dec_lt(x_797, x_803);
lean_dec(x_803);
if (x_804 == 0)
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_797);
lean_dec(x_686);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 lean_ctor_release(x_685, 2);
 lean_ctor_release(x_685, 3);
 lean_ctor_release(x_685, 4);
 x_805 = x_685;
} else {
 lean_dec_ref(x_685);
 x_805 = lean_box(0);
}
x_806 = lean_unsigned_to_nat(1u);
x_807 = lean_nat_add(x_806, x_681);
lean_dec(x_681);
x_808 = lean_nat_add(x_807, x_788);
lean_dec(x_807);
x_809 = lean_nat_add(x_806, x_796);
lean_dec(x_796);
x_810 = lean_nat_add(x_806, x_788);
lean_dec(x_788);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_811 = lean_ctor_get(x_800, 0);
lean_inc(x_811);
x_812 = lean_nat_add(x_809, x_811);
lean_dec(x_811);
lean_dec(x_809);
lean_inc(x_684);
if (lean_is_scalar(x_805)) {
 x_813 = lean_alloc_ctor(0, 5, 0);
} else {
 x_813 = x_805;
}
lean_ctor_set(x_813, 0, x_812);
lean_ctor_set(x_813, 1, x_682);
lean_ctor_set(x_813, 2, x_683);
lean_ctor_set(x_813, 3, x_684);
lean_ctor_set(x_813, 4, x_800);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 lean_ctor_release(x_684, 2);
 lean_ctor_release(x_684, 3);
 lean_ctor_release(x_684, 4);
 x_814 = x_684;
} else {
 lean_dec_ref(x_684);
 x_814 = lean_box(0);
}
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_815 = lean_ctor_get(x_801, 0);
lean_inc(x_815);
x_816 = lean_nat_add(x_810, x_815);
lean_dec(x_815);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_814)) {
 x_817 = lean_alloc_ctor(0, 5, 0);
} else {
 x_817 = x_814;
}
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_784);
lean_ctor_set(x_817, 2, x_785);
lean_ctor_set(x_817, 3, x_801);
lean_ctor_set(x_817, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_818 = x_786;
} else {
 lean_dec_ref(x_786);
 x_818 = lean_box(0);
}
if (lean_is_scalar(x_818)) {
 x_819 = lean_alloc_ctor(0, 5, 0);
} else {
 x_819 = x_818;
}
lean_ctor_set(x_819, 0, x_808);
lean_ctor_set(x_819, 1, x_798);
lean_ctor_set(x_819, 2, x_799);
lean_ctor_set(x_819, 3, x_813);
lean_ctor_set(x_819, 4, x_817);
return x_819;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_820 = lean_unsigned_to_nat(0u);
x_821 = lean_nat_add(x_810, x_820);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_814)) {
 x_822 = lean_alloc_ctor(0, 5, 0);
} else {
 x_822 = x_814;
}
lean_ctor_set(x_822, 0, x_821);
lean_ctor_set(x_822, 1, x_784);
lean_ctor_set(x_822, 2, x_785);
lean_ctor_set(x_822, 3, x_801);
lean_ctor_set(x_822, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_823 = x_786;
} else {
 lean_dec_ref(x_786);
 x_823 = lean_box(0);
}
if (lean_is_scalar(x_823)) {
 x_824 = lean_alloc_ctor(0, 5, 0);
} else {
 x_824 = x_823;
}
lean_ctor_set(x_824, 0, x_808);
lean_ctor_set(x_824, 1, x_798);
lean_ctor_set(x_824, 2, x_799);
lean_ctor_set(x_824, 3, x_813);
lean_ctor_set(x_824, 4, x_822);
return x_824;
}
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_825 = lean_unsigned_to_nat(0u);
x_826 = lean_nat_add(x_809, x_825);
lean_dec(x_809);
lean_inc(x_684);
if (lean_is_scalar(x_805)) {
 x_827 = lean_alloc_ctor(0, 5, 0);
} else {
 x_827 = x_805;
}
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_682);
lean_ctor_set(x_827, 2, x_683);
lean_ctor_set(x_827, 3, x_684);
lean_ctor_set(x_827, 4, x_800);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 lean_ctor_release(x_684, 2);
 lean_ctor_release(x_684, 3);
 lean_ctor_release(x_684, 4);
 x_828 = x_684;
} else {
 lean_dec_ref(x_684);
 x_828 = lean_box(0);
}
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_829 = lean_ctor_get(x_801, 0);
lean_inc(x_829);
x_830 = lean_nat_add(x_810, x_829);
lean_dec(x_829);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_828)) {
 x_831 = lean_alloc_ctor(0, 5, 0);
} else {
 x_831 = x_828;
}
lean_ctor_set(x_831, 0, x_830);
lean_ctor_set(x_831, 1, x_784);
lean_ctor_set(x_831, 2, x_785);
lean_ctor_set(x_831, 3, x_801);
lean_ctor_set(x_831, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_832 = x_786;
} else {
 lean_dec_ref(x_786);
 x_832 = lean_box(0);
}
if (lean_is_scalar(x_832)) {
 x_833 = lean_alloc_ctor(0, 5, 0);
} else {
 x_833 = x_832;
}
lean_ctor_set(x_833, 0, x_808);
lean_ctor_set(x_833, 1, x_798);
lean_ctor_set(x_833, 2, x_799);
lean_ctor_set(x_833, 3, x_827);
lean_ctor_set(x_833, 4, x_831);
return x_833;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_834 = lean_nat_add(x_810, x_825);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_828)) {
 x_835 = lean_alloc_ctor(0, 5, 0);
} else {
 x_835 = x_828;
}
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_784);
lean_ctor_set(x_835, 2, x_785);
lean_ctor_set(x_835, 3, x_801);
lean_ctor_set(x_835, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_836 = x_786;
} else {
 lean_dec_ref(x_786);
 x_836 = lean_box(0);
}
if (lean_is_scalar(x_836)) {
 x_837 = lean_alloc_ctor(0, 5, 0);
} else {
 x_837 = x_836;
}
lean_ctor_set(x_837, 0, x_808);
lean_ctor_set(x_837, 1, x_798);
lean_ctor_set(x_837, 2, x_799);
lean_ctor_set(x_837, 3, x_827);
lean_ctor_set(x_837, 4, x_835);
return x_837;
}
}
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
lean_dec(x_801);
lean_dec(x_800);
lean_dec(x_799);
lean_dec(x_798);
lean_dec(x_796);
x_838 = lean_unsigned_to_nat(1u);
x_839 = lean_nat_add(x_838, x_681);
lean_dec(x_681);
x_840 = lean_nat_add(x_839, x_788);
lean_dec(x_839);
x_841 = lean_nat_add(x_838, x_788);
lean_dec(x_788);
x_842 = lean_nat_add(x_841, x_797);
lean_dec(x_797);
lean_dec(x_841);
if (lean_is_scalar(x_686)) {
 x_843 = lean_alloc_ctor(0, 5, 0);
} else {
 x_843 = x_686;
}
lean_ctor_set(x_843, 0, x_842);
lean_ctor_set(x_843, 1, x_784);
lean_ctor_set(x_843, 2, x_785);
lean_ctor_set(x_843, 3, x_685);
lean_ctor_set(x_843, 4, x_786);
x_844 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_844, 0, x_840);
lean_ctor_set(x_844, 1, x_682);
lean_ctor_set(x_844, 2, x_683);
lean_ctor_set(x_844, 3, x_684);
lean_ctor_set(x_844, 4, x_843);
return x_844;
}
}
}
else
{
if (lean_obj_tag(x_684) == 0)
{
lean_dec(x_787);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_845 = lean_ctor_get(x_685, 0);
lean_inc(x_845);
x_846 = lean_unsigned_to_nat(1u);
x_847 = lean_nat_add(x_846, x_681);
lean_dec(x_681);
x_848 = lean_nat_add(x_846, x_845);
lean_dec(x_845);
x_849 = lean_box(1);
if (lean_is_scalar(x_686)) {
 x_850 = lean_alloc_ctor(0, 5, 0);
} else {
 x_850 = x_686;
}
lean_ctor_set(x_850, 0, x_848);
lean_ctor_set(x_850, 1, x_784);
lean_ctor_set(x_850, 2, x_785);
lean_ctor_set(x_850, 3, x_685);
lean_ctor_set(x_850, 4, x_849);
x_851 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_851, 0, x_847);
lean_ctor_set(x_851, 1, x_682);
lean_ctor_set(x_851, 2, x_683);
lean_ctor_set(x_851, 3, x_684);
lean_ctor_set(x_851, 4, x_850);
return x_851;
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_681);
x_852 = lean_box(1);
x_853 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_686)) {
 x_854 = lean_alloc_ctor(0, 5, 0);
} else {
 x_854 = x_686;
}
lean_ctor_set(x_854, 0, x_853);
lean_ctor_set(x_854, 1, x_784);
lean_ctor_set(x_854, 2, x_785);
lean_ctor_set(x_854, 3, x_852);
lean_ctor_set(x_854, 4, x_852);
x_855 = lean_unsigned_to_nat(3u);
x_856 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_682);
lean_ctor_set(x_856, 2, x_683);
lean_ctor_set(x_856, 3, x_684);
lean_ctor_set(x_856, 4, x_854);
return x_856;
}
}
else
{
lean_dec(x_681);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; 
lean_dec(x_787);
x_857 = lean_ctor_get(x_685, 1);
lean_inc(x_857);
x_858 = lean_ctor_get(x_685, 2);
lean_inc(x_858);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 lean_ctor_release(x_685, 2);
 lean_ctor_release(x_685, 3);
 lean_ctor_release(x_685, 4);
 x_859 = x_685;
} else {
 lean_dec_ref(x_685);
 x_859 = lean_box(0);
}
x_860 = lean_box(1);
x_861 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_859)) {
 x_862 = lean_alloc_ctor(0, 5, 0);
} else {
 x_862 = x_859;
}
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_862, 1, x_682);
lean_ctor_set(x_862, 2, x_683);
lean_ctor_set(x_862, 3, x_860);
lean_ctor_set(x_862, 4, x_860);
if (lean_is_scalar(x_686)) {
 x_863 = lean_alloc_ctor(0, 5, 0);
} else {
 x_863 = x_686;
}
lean_ctor_set(x_863, 0, x_861);
lean_ctor_set(x_863, 1, x_784);
lean_ctor_set(x_863, 2, x_785);
lean_ctor_set(x_863, 3, x_860);
lean_ctor_set(x_863, 4, x_860);
x_864 = lean_unsigned_to_nat(3u);
x_865 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_857);
lean_ctor_set(x_865, 2, x_858);
lean_ctor_set(x_865, 3, x_862);
lean_ctor_set(x_865, 4, x_863);
return x_865;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_683);
lean_dec(x_682);
x_866 = lean_box(1);
x_867 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_686)) {
 x_868 = lean_alloc_ctor(0, 5, 0);
} else {
 x_868 = x_686;
}
lean_ctor_set(x_868, 0, x_867);
lean_ctor_set(x_868, 1, x_784);
lean_ctor_set(x_868, 2, x_785);
lean_ctor_set(x_868, 3, x_787);
lean_ctor_set(x_868, 4, x_866);
return x_868;
}
}
}
}
}
else
{
return x_673;
}
}
else
{
return x_674;
}
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_869 = lean_ctor_get(x_680, 0);
lean_inc(x_869);
lean_dec(x_680);
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
x_872 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_872, 0, x_670);
lean_ctor_set(x_872, 1, x_870);
lean_ctor_set(x_872, 2, x_871);
lean_ctor_set(x_872, 3, x_673);
lean_ctor_set(x_872, 4, x_674);
return x_872;
}
}
default: 
{
lean_object* x_873; lean_object* x_874; 
lean_dec(x_670);
x_873 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insert_u2098___spec__1___rarg(x_1, x_2, x_3, x_674, lean_box(0));
x_874 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_671, x_672, x_673, x_873, lean_box(0), lean_box(0), lean_box(0));
return x_874;
}
}
}
}
else
{
lean_object* x_875; lean_object* x_876; 
lean_dec(x_2);
lean_dec(x_1);
x_875 = lean_box(0);
x_876 = lean_apply_1(x_3, x_875);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; 
x_877 = lean_box(1);
return x_877;
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_878 = lean_ctor_get(x_876, 0);
lean_inc(x_878);
lean_dec(x_876);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_881 = lean_box(1);
x_882 = lean_unsigned_to_nat(1u);
x_883 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_883, 0, x_882);
lean_ctor_set(x_883, 1, x_879);
lean_ctor_set(x_883, 2, x_880);
lean_ctor_set(x_883, 3, x_881);
lean_ctor_set(x_883, 4, x_881);
return x_883;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insert_u2098___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insert_u2098___spec__1___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_u2098___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_1, x_2, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_insert_u2098___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
x_7 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insert_u2098___spec__1___rarg(x_1, x_2, x_6, x_4, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_insert_u2098___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_u2098___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_insert_u2098___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_erase_u2098___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_4, 3);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_8);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
switch (x_13) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_4);
lean_dec(x_7);
x_14 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_erase_u2098___spec__1___rarg(x_1, x_2, x_3, x_10, lean_box(0));
x_15 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_8, x_9, x_14, x_11, lean_box(0), lean_box(0), lean_box(0));
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_8, x_9, lean_box(0));
x_17 = lean_apply_1(x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_7);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_10, 2);
x_23 = lean_ctor_get(x_10, 3);
x_24 = lean_ctor_get(x_10, 4);
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
x_27 = lean_ctor_get(x_11, 2);
x_28 = lean_ctor_get(x_11, 3);
x_29 = lean_ctor_get(x_11, 4);
x_30 = lean_nat_dec_lt(x_20, x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_20);
x_31 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_21, x_22, x_23, x_24, lean_box(0), lean_box(0), lean_box(0));
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_mul(x_36, x_35);
x_38 = lean_nat_dec_lt(x_37, x_25);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_4);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_39, x_35);
lean_dec(x_35);
x_41 = lean_nat_add(x_40, x_25);
lean_dec(x_25);
lean_dec(x_40);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_32);
lean_ctor_set(x_10, 2, x_34);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_41);
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_11);
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_28, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_28, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_28, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_29, 0);
lean_inc(x_47);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_mul(x_48, x_47);
x_50 = lean_nat_dec_lt(x_42, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
uint8_t x_51; 
lean_dec(x_42);
lean_free_object(x_4);
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_28, 4);
lean_dec(x_52);
x_53 = lean_ctor_get(x_28, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_28, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_28, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_28, 0);
lean_dec(x_56);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_57, x_35);
lean_dec(x_35);
x_59 = lean_nat_add(x_58, x_25);
lean_dec(x_25);
x_60 = lean_nat_add(x_57, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
x_62 = lean_nat_add(x_58, x_61);
lean_dec(x_61);
lean_dec(x_58);
lean_inc(x_32);
lean_ctor_set(x_28, 4, x_45);
lean_ctor_set(x_28, 3, x_32);
lean_ctor_set(x_28, 2, x_34);
lean_ctor_set(x_28, 1, x_33);
lean_ctor_set(x_28, 0, x_62);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_32, 4);
lean_dec(x_64);
x_65 = lean_ctor_get(x_32, 3);
lean_dec(x_65);
x_66 = lean_ctor_get(x_32, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_32, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_32, 0);
lean_dec(x_68);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_46, 0);
lean_inc(x_69);
x_70 = lean_nat_add(x_60, x_69);
lean_dec(x_69);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_70);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_add(x_60, x_71);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_72);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
else
{
lean_dec(x_32);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_46, 0);
lean_inc(x_73);
x_74 = lean_nat_add(x_60, x_73);
lean_dec(x_73);
lean_dec(x_60);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_26);
lean_ctor_set(x_75, 2, x_27);
lean_ctor_set(x_75, 3, x_46);
lean_ctor_set(x_75, 4, x_29);
lean_ctor_set(x_10, 4, x_75);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_add(x_60, x_76);
lean_dec(x_60);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_26);
lean_ctor_set(x_78, 2, x_27);
lean_ctor_set(x_78, 3, x_46);
lean_ctor_set(x_78, 4, x_29);
lean_ctor_set(x_10, 4, x_78);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_add(x_58, x_79);
lean_dec(x_58);
lean_inc(x_32);
lean_ctor_set(x_28, 4, x_45);
lean_ctor_set(x_28, 3, x_32);
lean_ctor_set(x_28, 2, x_34);
lean_ctor_set(x_28, 1, x_33);
lean_ctor_set(x_28, 0, x_80);
x_81 = !lean_is_exclusive(x_32);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_32, 4);
lean_dec(x_82);
x_83 = lean_ctor_get(x_32, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_32, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_32, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_32, 0);
lean_dec(x_86);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_46, 0);
lean_inc(x_87);
x_88 = lean_nat_add(x_60, x_87);
lean_dec(x_87);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_88);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_89; 
x_89 = lean_nat_add(x_60, x_79);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_89);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
else
{
lean_dec(x_32);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_46, 0);
lean_inc(x_90);
x_91 = lean_nat_add(x_60, x_90);
lean_dec(x_90);
lean_dec(x_60);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_26);
lean_ctor_set(x_92, 2, x_27);
lean_ctor_set(x_92, 3, x_46);
lean_ctor_set(x_92, 4, x_29);
lean_ctor_set(x_10, 4, x_92);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_nat_add(x_60, x_79);
lean_dec(x_60);
x_94 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_26);
lean_ctor_set(x_94, 2, x_27);
lean_ctor_set(x_94, 3, x_46);
lean_ctor_set(x_94, 4, x_29);
lean_ctor_set(x_10, 4, x_94);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_28);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_95, x_35);
lean_dec(x_35);
x_97 = lean_nat_add(x_96, x_25);
lean_dec(x_25);
x_98 = lean_nat_add(x_95, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_45, 0);
lean_inc(x_99);
x_100 = lean_nat_add(x_96, x_99);
lean_dec(x_99);
lean_dec(x_96);
lean_inc(x_32);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_33);
lean_ctor_set(x_101, 2, x_34);
lean_ctor_set(x_101, 3, x_32);
lean_ctor_set(x_101, 4, x_45);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_102 = x_32;
} else {
 lean_dec_ref(x_32);
 x_102 = lean_box(0);
}
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_46, 0);
lean_inc(x_103);
x_104 = lean_nat_add(x_98, x_103);
lean_dec(x_103);
lean_dec(x_98);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 5, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_26);
lean_ctor_set(x_105, 2, x_27);
lean_ctor_set(x_105, 3, x_46);
lean_ctor_set(x_105, 4, x_29);
lean_ctor_set(x_10, 4, x_105);
lean_ctor_set(x_10, 3, x_101);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_nat_add(x_98, x_106);
lean_dec(x_98);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(0, 5, 0);
} else {
 x_108 = x_102;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_26);
lean_ctor_set(x_108, 2, x_27);
lean_ctor_set(x_108, 3, x_46);
lean_ctor_set(x_108, 4, x_29);
lean_ctor_set(x_10, 4, x_108);
lean_ctor_set(x_10, 3, x_101);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_nat_add(x_96, x_109);
lean_dec(x_96);
lean_inc(x_32);
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_33);
lean_ctor_set(x_111, 2, x_34);
lean_ctor_set(x_111, 3, x_32);
lean_ctor_set(x_111, 4, x_45);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_112 = x_32;
} else {
 lean_dec_ref(x_32);
 x_112 = lean_box(0);
}
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_46, 0);
lean_inc(x_113);
x_114 = lean_nat_add(x_98, x_113);
lean_dec(x_113);
lean_dec(x_98);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 5, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_26);
lean_ctor_set(x_115, 2, x_27);
lean_ctor_set(x_115, 3, x_46);
lean_ctor_set(x_115, 4, x_29);
lean_ctor_set(x_10, 4, x_115);
lean_ctor_set(x_10, 3, x_111);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_nat_add(x_98, x_109);
lean_dec(x_98);
if (lean_is_scalar(x_112)) {
 x_117 = lean_alloc_ctor(0, 5, 0);
} else {
 x_117 = x_112;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_26);
lean_ctor_set(x_117, 2, x_27);
lean_ctor_set(x_117, 3, x_46);
lean_ctor_set(x_117, 4, x_29);
lean_ctor_set(x_10, 4, x_117);
lean_ctor_set(x_10, 3, x_111);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_118, x_35);
lean_dec(x_35);
x_120 = lean_nat_add(x_119, x_25);
lean_dec(x_25);
x_121 = lean_nat_add(x_119, x_42);
lean_dec(x_42);
lean_dec(x_119);
lean_ctor_set(x_10, 4, x_28);
lean_ctor_set(x_10, 3, x_32);
lean_ctor_set(x_10, 2, x_34);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_121);
lean_ctor_set(x_4, 4, x_29);
lean_ctor_set(x_4, 2, x_27);
lean_ctor_set(x_4, 1, x_26);
lean_ctor_set(x_4, 0, x_120);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_28) == 0)
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_31, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_31, 1);
lean_inc(x_123);
lean_dec(x_31);
x_124 = lean_ctor_get(x_28, 0);
lean_inc(x_124);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_add(x_125, x_25);
lean_dec(x_25);
x_127 = lean_nat_add(x_125, x_124);
lean_dec(x_124);
x_128 = lean_box(1);
lean_ctor_set(x_11, 4, x_28);
lean_ctor_set(x_11, 3, x_128);
lean_ctor_set(x_11, 2, x_123);
lean_ctor_set(x_11, 1, x_122);
lean_ctor_set(x_11, 0, x_127);
lean_ctor_set(x_10, 4, x_29);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_27);
lean_ctor_set(x_10, 1, x_26);
lean_ctor_set(x_10, 0, x_126);
return x_10;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_25);
x_129 = lean_ctor_get(x_31, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_31, 1);
lean_inc(x_130);
lean_dec(x_31);
x_131 = !lean_is_exclusive(x_28);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_28, 1);
x_133 = lean_ctor_get(x_28, 2);
x_134 = lean_ctor_get(x_28, 4);
lean_dec(x_134);
x_135 = lean_ctor_get(x_28, 3);
lean_dec(x_135);
x_136 = lean_ctor_get(x_28, 0);
lean_dec(x_136);
x_137 = lean_box(1);
x_138 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_28, 4, x_137);
lean_ctor_set(x_28, 3, x_137);
lean_ctor_set(x_28, 2, x_130);
lean_ctor_set(x_28, 1, x_129);
lean_ctor_set(x_28, 0, x_138);
lean_ctor_set(x_11, 4, x_137);
lean_ctor_set(x_11, 3, x_137);
lean_ctor_set(x_11, 0, x_138);
x_139 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_133);
lean_ctor_set(x_10, 1, x_132);
lean_ctor_set(x_10, 0, x_139);
return x_10;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_ctor_get(x_28, 1);
x_141 = lean_ctor_get(x_28, 2);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_28);
x_142 = lean_box(1);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_129);
lean_ctor_set(x_144, 2, x_130);
lean_ctor_set(x_144, 3, x_142);
lean_ctor_set(x_144, 4, x_142);
lean_ctor_set(x_11, 4, x_142);
lean_ctor_set(x_11, 3, x_142);
lean_ctor_set(x_11, 0, x_143);
x_145 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_144);
lean_ctor_set(x_10, 2, x_141);
lean_ctor_set(x_10, 1, x_140);
lean_ctor_set(x_10, 0, x_145);
return x_10;
}
}
}
else
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_25);
x_146 = lean_ctor_get(x_31, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_31, 1);
lean_inc(x_147);
lean_dec(x_31);
x_148 = lean_box(1);
x_149 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_11, 4, x_148);
lean_ctor_set(x_11, 3, x_148);
lean_ctor_set(x_11, 2, x_147);
lean_ctor_set(x_11, 1, x_146);
lean_ctor_set(x_11, 0, x_149);
x_150 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_29);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_27);
lean_ctor_set(x_10, 1, x_26);
lean_ctor_set(x_10, 0, x_150);
return x_10;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_31, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_31, 1);
lean_inc(x_152);
lean_dec(x_31);
lean_ctor_set(x_11, 3, x_29);
x_153 = lean_box(1);
x_154 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_153);
lean_ctor_set(x_10, 2, x_152);
lean_ctor_set(x_10, 1, x_151);
lean_ctor_set(x_10, 0, x_154);
return x_10;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_25);
x_155 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_26, x_27, x_28, x_29, lean_box(0), lean_box(0), lean_box(0));
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 2);
lean_inc(x_158);
lean_dec(x_155);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_ctor_set(x_11, 4, x_24);
lean_ctor_set(x_11, 3, x_23);
lean_ctor_set(x_11, 2, x_22);
lean_ctor_set(x_11, 1, x_21);
lean_ctor_set(x_11, 0, x_20);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_unsigned_to_nat(3u);
x_161 = lean_nat_mul(x_160, x_159);
x_162 = lean_nat_dec_lt(x_161, x_20);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_4);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_nat_add(x_163, x_20);
lean_dec(x_20);
x_165 = lean_nat_add(x_164, x_159);
lean_dec(x_159);
lean_dec(x_164);
lean_ctor_set(x_10, 4, x_158);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_165);
return x_10;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_dec(x_11);
x_166 = lean_ctor_get(x_23, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_24, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_24, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_24, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_24, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_24, 4);
lean_inc(x_171);
x_172 = lean_unsigned_to_nat(2u);
x_173 = lean_nat_mul(x_172, x_166);
x_174 = lean_nat_dec_lt(x_167, x_173);
lean_dec(x_173);
if (x_174 == 0)
{
uint8_t x_175; 
lean_dec(x_167);
lean_free_object(x_10);
lean_free_object(x_4);
x_175 = !lean_is_exclusive(x_24);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_176 = lean_ctor_get(x_24, 4);
lean_dec(x_176);
x_177 = lean_ctor_get(x_24, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_24, 2);
lean_dec(x_178);
x_179 = lean_ctor_get(x_24, 1);
lean_dec(x_179);
x_180 = lean_ctor_get(x_24, 0);
lean_dec(x_180);
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_nat_add(x_181, x_20);
lean_dec(x_20);
x_183 = lean_nat_add(x_182, x_159);
lean_dec(x_182);
x_184 = lean_nat_add(x_181, x_166);
lean_dec(x_166);
x_185 = lean_nat_add(x_181, x_159);
lean_dec(x_159);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_170, 0);
lean_inc(x_186);
x_187 = lean_nat_add(x_184, x_186);
lean_dec(x_186);
lean_dec(x_184);
lean_inc(x_23);
lean_ctor_set(x_24, 4, x_170);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_187);
x_188 = !lean_is_exclusive(x_23);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_23, 4);
lean_dec(x_189);
x_190 = lean_ctor_get(x_23, 3);
lean_dec(x_190);
x_191 = lean_ctor_get(x_23, 2);
lean_dec(x_191);
x_192 = lean_ctor_get(x_23, 1);
lean_dec(x_192);
x_193 = lean_ctor_get(x_23, 0);
lean_dec(x_193);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_171, 0);
lean_inc(x_194);
x_195 = lean_nat_add(x_185, x_194);
lean_dec(x_194);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_195);
x_196 = !lean_is_exclusive(x_158);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_158, 4);
lean_dec(x_197);
x_198 = lean_ctor_get(x_158, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_158, 2);
lean_dec(x_199);
x_200 = lean_ctor_get(x_158, 1);
lean_dec(x_200);
x_201 = lean_ctor_get(x_158, 0);
lean_dec(x_201);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_202; 
lean_dec(x_158);
x_202 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_202, 0, x_183);
lean_ctor_set(x_202, 1, x_168);
lean_ctor_set(x_202, 2, x_169);
lean_ctor_set(x_202, 3, x_24);
lean_ctor_set(x_202, 4, x_23);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_203 = lean_unsigned_to_nat(0u);
x_204 = lean_nat_add(x_185, x_203);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_204);
x_205 = !lean_is_exclusive(x_158);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_158, 4);
lean_dec(x_206);
x_207 = lean_ctor_get(x_158, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_158, 2);
lean_dec(x_208);
x_209 = lean_ctor_get(x_158, 1);
lean_dec(x_209);
x_210 = lean_ctor_get(x_158, 0);
lean_dec(x_210);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_211; 
lean_dec(x_158);
x_211 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_211, 0, x_183);
lean_ctor_set(x_211, 1, x_168);
lean_ctor_set(x_211, 2, x_169);
lean_ctor_set(x_211, 3, x_24);
lean_ctor_set(x_211, 4, x_23);
return x_211;
}
}
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_ctor_get(x_171, 0);
lean_inc(x_212);
x_213 = lean_nat_add(x_185, x_212);
lean_dec(x_212);
lean_dec(x_185);
lean_inc(x_158);
x_214 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_156);
lean_ctor_set(x_214, 2, x_157);
lean_ctor_set(x_214, 3, x_171);
lean_ctor_set(x_214, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_215 = x_158;
} else {
 lean_dec_ref(x_158);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(0, 5, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_183);
lean_ctor_set(x_216, 1, x_168);
lean_ctor_set(x_216, 2, x_169);
lean_ctor_set(x_216, 3, x_24);
lean_ctor_set(x_216, 4, x_214);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_unsigned_to_nat(0u);
x_218 = lean_nat_add(x_185, x_217);
lean_dec(x_185);
lean_inc(x_158);
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_156);
lean_ctor_set(x_219, 2, x_157);
lean_ctor_set(x_219, 3, x_171);
lean_ctor_set(x_219, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_220 = x_158;
} else {
 lean_dec_ref(x_158);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 5, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_183);
lean_ctor_set(x_221, 1, x_168);
lean_ctor_set(x_221, 2, x_169);
lean_ctor_set(x_221, 3, x_24);
lean_ctor_set(x_221, 4, x_219);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_unsigned_to_nat(0u);
x_223 = lean_nat_add(x_184, x_222);
lean_dec(x_184);
lean_inc(x_23);
lean_ctor_set(x_24, 4, x_170);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_223);
x_224 = !lean_is_exclusive(x_23);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_23, 4);
lean_dec(x_225);
x_226 = lean_ctor_get(x_23, 3);
lean_dec(x_226);
x_227 = lean_ctor_get(x_23, 2);
lean_dec(x_227);
x_228 = lean_ctor_get(x_23, 1);
lean_dec(x_228);
x_229 = lean_ctor_get(x_23, 0);
lean_dec(x_229);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_230 = lean_ctor_get(x_171, 0);
lean_inc(x_230);
x_231 = lean_nat_add(x_185, x_230);
lean_dec(x_230);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_231);
x_232 = !lean_is_exclusive(x_158);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_158, 4);
lean_dec(x_233);
x_234 = lean_ctor_get(x_158, 3);
lean_dec(x_234);
x_235 = lean_ctor_get(x_158, 2);
lean_dec(x_235);
x_236 = lean_ctor_get(x_158, 1);
lean_dec(x_236);
x_237 = lean_ctor_get(x_158, 0);
lean_dec(x_237);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_238; 
lean_dec(x_158);
x_238 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_238, 0, x_183);
lean_ctor_set(x_238, 1, x_168);
lean_ctor_set(x_238, 2, x_169);
lean_ctor_set(x_238, 3, x_24);
lean_ctor_set(x_238, 4, x_23);
return x_238;
}
}
else
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_nat_add(x_185, x_222);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_239);
x_240 = !lean_is_exclusive(x_158);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = lean_ctor_get(x_158, 4);
lean_dec(x_241);
x_242 = lean_ctor_get(x_158, 3);
lean_dec(x_242);
x_243 = lean_ctor_get(x_158, 2);
lean_dec(x_243);
x_244 = lean_ctor_get(x_158, 1);
lean_dec(x_244);
x_245 = lean_ctor_get(x_158, 0);
lean_dec(x_245);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_246; 
lean_dec(x_158);
x_246 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_246, 0, x_183);
lean_ctor_set(x_246, 1, x_168);
lean_ctor_set(x_246, 2, x_169);
lean_ctor_set(x_246, 3, x_24);
lean_ctor_set(x_246, 4, x_23);
return x_246;
}
}
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = lean_ctor_get(x_171, 0);
lean_inc(x_247);
x_248 = lean_nat_add(x_185, x_247);
lean_dec(x_247);
lean_dec(x_185);
lean_inc(x_158);
x_249 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_156);
lean_ctor_set(x_249, 2, x_157);
lean_ctor_set(x_249, 3, x_171);
lean_ctor_set(x_249, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_250 = x_158;
} else {
 lean_dec_ref(x_158);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 5, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_183);
lean_ctor_set(x_251, 1, x_168);
lean_ctor_set(x_251, 2, x_169);
lean_ctor_set(x_251, 3, x_24);
lean_ctor_set(x_251, 4, x_249);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_nat_add(x_185, x_222);
lean_dec(x_185);
lean_inc(x_158);
x_253 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_156);
lean_ctor_set(x_253, 2, x_157);
lean_ctor_set(x_253, 3, x_171);
lean_ctor_set(x_253, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_254 = x_158;
} else {
 lean_dec_ref(x_158);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(0, 5, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_183);
lean_ctor_set(x_255, 1, x_168);
lean_ctor_set(x_255, 2, x_169);
lean_ctor_set(x_255, 3, x_24);
lean_ctor_set(x_255, 4, x_253);
return x_255;
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_24);
x_256 = lean_unsigned_to_nat(1u);
x_257 = lean_nat_add(x_256, x_20);
lean_dec(x_20);
x_258 = lean_nat_add(x_257, x_159);
lean_dec(x_257);
x_259 = lean_nat_add(x_256, x_166);
lean_dec(x_166);
x_260 = lean_nat_add(x_256, x_159);
lean_dec(x_159);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_170, 0);
lean_inc(x_261);
x_262 = lean_nat_add(x_259, x_261);
lean_dec(x_261);
lean_dec(x_259);
lean_inc(x_23);
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_21);
lean_ctor_set(x_263, 2, x_22);
lean_ctor_set(x_263, 3, x_23);
lean_ctor_set(x_263, 4, x_170);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 x_264 = x_23;
} else {
 lean_dec_ref(x_23);
 x_264 = lean_box(0);
}
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_265 = lean_ctor_get(x_171, 0);
lean_inc(x_265);
x_266 = lean_nat_add(x_260, x_265);
lean_dec(x_265);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_264)) {
 x_267 = lean_alloc_ctor(0, 5, 0);
} else {
 x_267 = x_264;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_156);
lean_ctor_set(x_267, 2, x_157);
lean_ctor_set(x_267, 3, x_171);
lean_ctor_set(x_267, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_268 = x_158;
} else {
 lean_dec_ref(x_158);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(0, 5, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_258);
lean_ctor_set(x_269, 1, x_168);
lean_ctor_set(x_269, 2, x_169);
lean_ctor_set(x_269, 3, x_263);
lean_ctor_set(x_269, 4, x_267);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_unsigned_to_nat(0u);
x_271 = lean_nat_add(x_260, x_270);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_264)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_264;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_156);
lean_ctor_set(x_272, 2, x_157);
lean_ctor_set(x_272, 3, x_171);
lean_ctor_set(x_272, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_273 = x_158;
} else {
 lean_dec_ref(x_158);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 5, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_258);
lean_ctor_set(x_274, 1, x_168);
lean_ctor_set(x_274, 2, x_169);
lean_ctor_set(x_274, 3, x_263);
lean_ctor_set(x_274, 4, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_unsigned_to_nat(0u);
x_276 = lean_nat_add(x_259, x_275);
lean_dec(x_259);
lean_inc(x_23);
x_277 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_21);
lean_ctor_set(x_277, 2, x_22);
lean_ctor_set(x_277, 3, x_23);
lean_ctor_set(x_277, 4, x_170);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 x_278 = x_23;
} else {
 lean_dec_ref(x_23);
 x_278 = lean_box(0);
}
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_ctor_get(x_171, 0);
lean_inc(x_279);
x_280 = lean_nat_add(x_260, x_279);
lean_dec(x_279);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_278)) {
 x_281 = lean_alloc_ctor(0, 5, 0);
} else {
 x_281 = x_278;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_156);
lean_ctor_set(x_281, 2, x_157);
lean_ctor_set(x_281, 3, x_171);
lean_ctor_set(x_281, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_282 = x_158;
} else {
 lean_dec_ref(x_158);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(0, 5, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_258);
lean_ctor_set(x_283, 1, x_168);
lean_ctor_set(x_283, 2, x_169);
lean_ctor_set(x_283, 3, x_277);
lean_ctor_set(x_283, 4, x_281);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_284 = lean_nat_add(x_260, x_275);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_278)) {
 x_285 = lean_alloc_ctor(0, 5, 0);
} else {
 x_285 = x_278;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_156);
lean_ctor_set(x_285, 2, x_157);
lean_ctor_set(x_285, 3, x_171);
lean_ctor_set(x_285, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_286 = x_158;
} else {
 lean_dec_ref(x_158);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(0, 5, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_258);
lean_ctor_set(x_287, 1, x_168);
lean_ctor_set(x_287, 2, x_169);
lean_ctor_set(x_287, 3, x_277);
lean_ctor_set(x_287, 4, x_285);
return x_287;
}
}
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_166);
x_288 = lean_unsigned_to_nat(1u);
x_289 = lean_nat_add(x_288, x_20);
lean_dec(x_20);
x_290 = lean_nat_add(x_289, x_159);
lean_dec(x_289);
x_291 = lean_nat_add(x_288, x_159);
lean_dec(x_159);
x_292 = lean_nat_add(x_291, x_167);
lean_dec(x_167);
lean_dec(x_291);
lean_ctor_set(x_10, 4, x_158);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_292);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_290);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_24, 0);
lean_inc(x_293);
x_294 = lean_unsigned_to_nat(1u);
x_295 = lean_nat_add(x_294, x_20);
lean_dec(x_20);
x_296 = lean_nat_add(x_294, x_293);
lean_dec(x_293);
x_297 = lean_box(1);
lean_ctor_set(x_10, 4, x_297);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_296);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_295);
return x_4;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_20);
x_298 = lean_box(1);
x_299 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_10, 4, x_298);
lean_ctor_set(x_10, 3, x_298);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_299);
x_300 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_300);
return x_4;
}
}
else
{
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_301; 
lean_dec(x_11);
x_301 = !lean_is_exclusive(x_24);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_302 = lean_ctor_get(x_24, 1);
x_303 = lean_ctor_get(x_24, 2);
x_304 = lean_ctor_get(x_24, 4);
lean_dec(x_304);
x_305 = lean_ctor_get(x_24, 3);
lean_dec(x_305);
x_306 = lean_ctor_get(x_24, 0);
lean_dec(x_306);
x_307 = lean_box(1);
x_308 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_24, 4, x_307);
lean_ctor_set(x_24, 3, x_307);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_308);
lean_ctor_set(x_10, 4, x_307);
lean_ctor_set(x_10, 3, x_307);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_308);
x_309 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_24);
lean_ctor_set(x_4, 2, x_303);
lean_ctor_set(x_4, 1, x_302);
lean_ctor_set(x_4, 0, x_309);
return x_4;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_310 = lean_ctor_get(x_24, 1);
x_311 = lean_ctor_get(x_24, 2);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_24);
x_312 = lean_box(1);
x_313 = lean_unsigned_to_nat(1u);
x_314 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_21);
lean_ctor_set(x_314, 2, x_22);
lean_ctor_set(x_314, 3, x_312);
lean_ctor_set(x_314, 4, x_312);
lean_ctor_set(x_10, 4, x_312);
lean_ctor_set(x_10, 3, x_312);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_313);
x_315 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_314);
lean_ctor_set(x_4, 2, x_311);
lean_ctor_set(x_4, 1, x_310);
lean_ctor_set(x_4, 0, x_315);
return x_4;
}
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_4);
x_316 = lean_box(1);
x_317 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_316);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_317);
return x_10;
}
}
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_318 = lean_ctor_get(x_10, 0);
x_319 = lean_ctor_get(x_10, 1);
x_320 = lean_ctor_get(x_10, 2);
x_321 = lean_ctor_get(x_10, 3);
x_322 = lean_ctor_get(x_10, 4);
x_323 = lean_ctor_get(x_11, 0);
x_324 = lean_ctor_get(x_11, 1);
x_325 = lean_ctor_get(x_11, 2);
x_326 = lean_ctor_get(x_11, 3);
x_327 = lean_ctor_get(x_11, 4);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_11);
x_328 = lean_nat_dec_lt(x_318, x_323);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_318);
x_329 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_319, x_320, x_321, x_322, lean_box(0), lean_box(0), lean_box(0));
x_330 = lean_ctor_get(x_329, 2);
lean_inc(x_330);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_331 = lean_ctor_get(x_329, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_dec(x_329);
x_333 = lean_ctor_get(x_330, 0);
lean_inc(x_333);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
x_334 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_334, 0, x_323);
lean_ctor_set(x_334, 1, x_324);
lean_ctor_set(x_334, 2, x_325);
lean_ctor_set(x_334, 3, x_326);
lean_ctor_set(x_334, 4, x_327);
x_335 = lean_unsigned_to_nat(3u);
x_336 = lean_nat_mul(x_335, x_333);
x_337 = lean_nat_dec_lt(x_336, x_323);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_free_object(x_4);
x_338 = lean_unsigned_to_nat(1u);
x_339 = lean_nat_add(x_338, x_333);
lean_dec(x_333);
x_340 = lean_nat_add(x_339, x_323);
lean_dec(x_323);
lean_dec(x_339);
lean_ctor_set(x_10, 4, x_334);
lean_ctor_set(x_10, 3, x_330);
lean_ctor_set(x_10, 2, x_332);
lean_ctor_set(x_10, 1, x_331);
lean_ctor_set(x_10, 0, x_340);
return x_10;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
lean_dec(x_334);
x_341 = lean_ctor_get(x_326, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_326, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_326, 2);
lean_inc(x_343);
x_344 = lean_ctor_get(x_326, 3);
lean_inc(x_344);
x_345 = lean_ctor_get(x_326, 4);
lean_inc(x_345);
x_346 = lean_ctor_get(x_327, 0);
lean_inc(x_346);
x_347 = lean_unsigned_to_nat(2u);
x_348 = lean_nat_mul(x_347, x_346);
x_349 = lean_nat_dec_lt(x_341, x_348);
lean_dec(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_341);
lean_free_object(x_4);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 x_350 = x_326;
} else {
 lean_dec_ref(x_326);
 x_350 = lean_box(0);
}
x_351 = lean_unsigned_to_nat(1u);
x_352 = lean_nat_add(x_351, x_333);
lean_dec(x_333);
x_353 = lean_nat_add(x_352, x_323);
lean_dec(x_323);
x_354 = lean_nat_add(x_351, x_346);
lean_dec(x_346);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_355 = lean_ctor_get(x_344, 0);
lean_inc(x_355);
x_356 = lean_nat_add(x_352, x_355);
lean_dec(x_355);
lean_dec(x_352);
lean_inc(x_330);
if (lean_is_scalar(x_350)) {
 x_357 = lean_alloc_ctor(0, 5, 0);
} else {
 x_357 = x_350;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_331);
lean_ctor_set(x_357, 2, x_332);
lean_ctor_set(x_357, 3, x_330);
lean_ctor_set(x_357, 4, x_344);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 x_358 = x_330;
} else {
 lean_dec_ref(x_330);
 x_358 = lean_box(0);
}
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_345, 0);
lean_inc(x_359);
x_360 = lean_nat_add(x_354, x_359);
lean_dec(x_359);
lean_dec(x_354);
if (lean_is_scalar(x_358)) {
 x_361 = lean_alloc_ctor(0, 5, 0);
} else {
 x_361 = x_358;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_324);
lean_ctor_set(x_361, 2, x_325);
lean_ctor_set(x_361, 3, x_345);
lean_ctor_set(x_361, 4, x_327);
lean_ctor_set(x_10, 4, x_361);
lean_ctor_set(x_10, 3, x_357);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_unsigned_to_nat(0u);
x_363 = lean_nat_add(x_354, x_362);
lean_dec(x_354);
if (lean_is_scalar(x_358)) {
 x_364 = lean_alloc_ctor(0, 5, 0);
} else {
 x_364 = x_358;
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_324);
lean_ctor_set(x_364, 2, x_325);
lean_ctor_set(x_364, 3, x_345);
lean_ctor_set(x_364, 4, x_327);
lean_ctor_set(x_10, 4, x_364);
lean_ctor_set(x_10, 3, x_357);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = lean_unsigned_to_nat(0u);
x_366 = lean_nat_add(x_352, x_365);
lean_dec(x_352);
lean_inc(x_330);
if (lean_is_scalar(x_350)) {
 x_367 = lean_alloc_ctor(0, 5, 0);
} else {
 x_367 = x_350;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_331);
lean_ctor_set(x_367, 2, x_332);
lean_ctor_set(x_367, 3, x_330);
lean_ctor_set(x_367, 4, x_344);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 x_368 = x_330;
} else {
 lean_dec_ref(x_330);
 x_368 = lean_box(0);
}
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_345, 0);
lean_inc(x_369);
x_370 = lean_nat_add(x_354, x_369);
lean_dec(x_369);
lean_dec(x_354);
if (lean_is_scalar(x_368)) {
 x_371 = lean_alloc_ctor(0, 5, 0);
} else {
 x_371 = x_368;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_324);
lean_ctor_set(x_371, 2, x_325);
lean_ctor_set(x_371, 3, x_345);
lean_ctor_set(x_371, 4, x_327);
lean_ctor_set(x_10, 4, x_371);
lean_ctor_set(x_10, 3, x_367);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_nat_add(x_354, x_365);
lean_dec(x_354);
if (lean_is_scalar(x_368)) {
 x_373 = lean_alloc_ctor(0, 5, 0);
} else {
 x_373 = x_368;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_324);
lean_ctor_set(x_373, 2, x_325);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set(x_373, 4, x_327);
lean_ctor_set(x_10, 4, x_373);
lean_ctor_set(x_10, 3, x_367);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
x_374 = lean_unsigned_to_nat(1u);
x_375 = lean_nat_add(x_374, x_333);
lean_dec(x_333);
x_376 = lean_nat_add(x_375, x_323);
lean_dec(x_323);
x_377 = lean_nat_add(x_375, x_341);
lean_dec(x_341);
lean_dec(x_375);
lean_ctor_set(x_10, 4, x_326);
lean_ctor_set(x_10, 3, x_330);
lean_ctor_set(x_10, 2, x_332);
lean_ctor_set(x_10, 1, x_331);
lean_ctor_set(x_10, 0, x_377);
lean_ctor_set(x_4, 4, x_327);
lean_ctor_set(x_4, 2, x_325);
lean_ctor_set(x_4, 1, x_324);
lean_ctor_set(x_4, 0, x_376);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_326) == 0)
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_378 = lean_ctor_get(x_329, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_329, 1);
lean_inc(x_379);
lean_dec(x_329);
x_380 = lean_ctor_get(x_326, 0);
lean_inc(x_380);
x_381 = lean_unsigned_to_nat(1u);
x_382 = lean_nat_add(x_381, x_323);
lean_dec(x_323);
x_383 = lean_nat_add(x_381, x_380);
lean_dec(x_380);
x_384 = lean_box(1);
x_385 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_378);
lean_ctor_set(x_385, 2, x_379);
lean_ctor_set(x_385, 3, x_384);
lean_ctor_set(x_385, 4, x_326);
lean_ctor_set(x_10, 4, x_327);
lean_ctor_set(x_10, 3, x_385);
lean_ctor_set(x_10, 2, x_325);
lean_ctor_set(x_10, 1, x_324);
lean_ctor_set(x_10, 0, x_382);
return x_10;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_323);
x_386 = lean_ctor_get(x_329, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_329, 1);
lean_inc(x_387);
lean_dec(x_329);
x_388 = lean_ctor_get(x_326, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_326, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 x_390 = x_326;
} else {
 lean_dec_ref(x_326);
 x_390 = lean_box(0);
}
x_391 = lean_box(1);
x_392 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_390)) {
 x_393 = lean_alloc_ctor(0, 5, 0);
} else {
 x_393 = x_390;
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_386);
lean_ctor_set(x_393, 2, x_387);
lean_ctor_set(x_393, 3, x_391);
lean_ctor_set(x_393, 4, x_391);
x_394 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_324);
lean_ctor_set(x_394, 2, x_325);
lean_ctor_set(x_394, 3, x_391);
lean_ctor_set(x_394, 4, x_391);
x_395 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_394);
lean_ctor_set(x_10, 3, x_393);
lean_ctor_set(x_10, 2, x_389);
lean_ctor_set(x_10, 1, x_388);
lean_ctor_set(x_10, 0, x_395);
return x_10;
}
}
else
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_323);
x_396 = lean_ctor_get(x_329, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_329, 1);
lean_inc(x_397);
lean_dec(x_329);
x_398 = lean_box(1);
x_399 = lean_unsigned_to_nat(1u);
x_400 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_396);
lean_ctor_set(x_400, 2, x_397);
lean_ctor_set(x_400, 3, x_398);
lean_ctor_set(x_400, 4, x_398);
x_401 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_327);
lean_ctor_set(x_10, 3, x_400);
lean_ctor_set(x_10, 2, x_325);
lean_ctor_set(x_10, 1, x_324);
lean_ctor_set(x_10, 0, x_401);
return x_10;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_402 = lean_ctor_get(x_329, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_329, 1);
lean_inc(x_403);
lean_dec(x_329);
x_404 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_404, 0, x_323);
lean_ctor_set(x_404, 1, x_324);
lean_ctor_set(x_404, 2, x_325);
lean_ctor_set(x_404, 3, x_327);
lean_ctor_set(x_404, 4, x_327);
x_405 = lean_box(1);
x_406 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_404);
lean_ctor_set(x_10, 3, x_405);
lean_ctor_set(x_10, 2, x_403);
lean_ctor_set(x_10, 1, x_402);
lean_ctor_set(x_10, 0, x_406);
return x_10;
}
}
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_323);
x_407 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_324, x_325, x_326, x_327, lean_box(0), lean_box(0), lean_box(0));
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_407, 2);
lean_inc(x_410);
lean_dec(x_407);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
x_411 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_411, 0, x_318);
lean_ctor_set(x_411, 1, x_319);
lean_ctor_set(x_411, 2, x_320);
lean_ctor_set(x_411, 3, x_321);
lean_ctor_set(x_411, 4, x_322);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_412 = lean_ctor_get(x_410, 0);
lean_inc(x_412);
x_413 = lean_unsigned_to_nat(3u);
x_414 = lean_nat_mul(x_413, x_412);
x_415 = lean_nat_dec_lt(x_414, x_318);
lean_dec(x_414);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_free_object(x_4);
x_416 = lean_unsigned_to_nat(1u);
x_417 = lean_nat_add(x_416, x_318);
lean_dec(x_318);
x_418 = lean_nat_add(x_417, x_412);
lean_dec(x_412);
lean_dec(x_417);
lean_ctor_set(x_10, 4, x_410);
lean_ctor_set(x_10, 3, x_411);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_418);
return x_10;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_dec(x_411);
x_419 = lean_ctor_get(x_321, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_322, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_322, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_322, 2);
lean_inc(x_422);
x_423 = lean_ctor_get(x_322, 3);
lean_inc(x_423);
x_424 = lean_ctor_get(x_322, 4);
lean_inc(x_424);
x_425 = lean_unsigned_to_nat(2u);
x_426 = lean_nat_mul(x_425, x_419);
x_427 = lean_nat_dec_lt(x_420, x_426);
lean_dec(x_426);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_420);
lean_free_object(x_10);
lean_free_object(x_4);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 lean_ctor_release(x_322, 4);
 x_428 = x_322;
} else {
 lean_dec_ref(x_322);
 x_428 = lean_box(0);
}
x_429 = lean_unsigned_to_nat(1u);
x_430 = lean_nat_add(x_429, x_318);
lean_dec(x_318);
x_431 = lean_nat_add(x_430, x_412);
lean_dec(x_430);
x_432 = lean_nat_add(x_429, x_419);
lean_dec(x_419);
x_433 = lean_nat_add(x_429, x_412);
lean_dec(x_412);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = lean_ctor_get(x_423, 0);
lean_inc(x_434);
x_435 = lean_nat_add(x_432, x_434);
lean_dec(x_434);
lean_dec(x_432);
lean_inc(x_321);
if (lean_is_scalar(x_428)) {
 x_436 = lean_alloc_ctor(0, 5, 0);
} else {
 x_436 = x_428;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_319);
lean_ctor_set(x_436, 2, x_320);
lean_ctor_set(x_436, 3, x_321);
lean_ctor_set(x_436, 4, x_423);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 x_437 = x_321;
} else {
 lean_dec_ref(x_321);
 x_437 = lean_box(0);
}
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_438 = lean_ctor_get(x_424, 0);
lean_inc(x_438);
x_439 = lean_nat_add(x_433, x_438);
lean_dec(x_438);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_437)) {
 x_440 = lean_alloc_ctor(0, 5, 0);
} else {
 x_440 = x_437;
}
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_408);
lean_ctor_set(x_440, 2, x_409);
lean_ctor_set(x_440, 3, x_424);
lean_ctor_set(x_440, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_441 = x_410;
} else {
 lean_dec_ref(x_410);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(0, 5, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_431);
lean_ctor_set(x_442, 1, x_421);
lean_ctor_set(x_442, 2, x_422);
lean_ctor_set(x_442, 3, x_436);
lean_ctor_set(x_442, 4, x_440);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_443 = lean_unsigned_to_nat(0u);
x_444 = lean_nat_add(x_433, x_443);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(0, 5, 0);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_408);
lean_ctor_set(x_445, 2, x_409);
lean_ctor_set(x_445, 3, x_424);
lean_ctor_set(x_445, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_446 = x_410;
} else {
 lean_dec_ref(x_410);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(0, 5, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_431);
lean_ctor_set(x_447, 1, x_421);
lean_ctor_set(x_447, 2, x_422);
lean_ctor_set(x_447, 3, x_436);
lean_ctor_set(x_447, 4, x_445);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_448 = lean_unsigned_to_nat(0u);
x_449 = lean_nat_add(x_432, x_448);
lean_dec(x_432);
lean_inc(x_321);
if (lean_is_scalar(x_428)) {
 x_450 = lean_alloc_ctor(0, 5, 0);
} else {
 x_450 = x_428;
}
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_319);
lean_ctor_set(x_450, 2, x_320);
lean_ctor_set(x_450, 3, x_321);
lean_ctor_set(x_450, 4, x_423);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 x_451 = x_321;
} else {
 lean_dec_ref(x_321);
 x_451 = lean_box(0);
}
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_452 = lean_ctor_get(x_424, 0);
lean_inc(x_452);
x_453 = lean_nat_add(x_433, x_452);
lean_dec(x_452);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_451)) {
 x_454 = lean_alloc_ctor(0, 5, 0);
} else {
 x_454 = x_451;
}
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_408);
lean_ctor_set(x_454, 2, x_409);
lean_ctor_set(x_454, 3, x_424);
lean_ctor_set(x_454, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_455 = x_410;
} else {
 lean_dec_ref(x_410);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(0, 5, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_431);
lean_ctor_set(x_456, 1, x_421);
lean_ctor_set(x_456, 2, x_422);
lean_ctor_set(x_456, 3, x_450);
lean_ctor_set(x_456, 4, x_454);
return x_456;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_457 = lean_nat_add(x_433, x_448);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_451)) {
 x_458 = lean_alloc_ctor(0, 5, 0);
} else {
 x_458 = x_451;
}
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_408);
lean_ctor_set(x_458, 2, x_409);
lean_ctor_set(x_458, 3, x_424);
lean_ctor_set(x_458, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_459 = x_410;
} else {
 lean_dec_ref(x_410);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(0, 5, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_431);
lean_ctor_set(x_460, 1, x_421);
lean_ctor_set(x_460, 2, x_422);
lean_ctor_set(x_460, 3, x_450);
lean_ctor_set(x_460, 4, x_458);
return x_460;
}
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_419);
x_461 = lean_unsigned_to_nat(1u);
x_462 = lean_nat_add(x_461, x_318);
lean_dec(x_318);
x_463 = lean_nat_add(x_462, x_412);
lean_dec(x_462);
x_464 = lean_nat_add(x_461, x_412);
lean_dec(x_412);
x_465 = lean_nat_add(x_464, x_420);
lean_dec(x_420);
lean_dec(x_464);
lean_ctor_set(x_10, 4, x_410);
lean_ctor_set(x_10, 3, x_322);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_465);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_463);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_321) == 0)
{
lean_dec(x_411);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_466 = lean_ctor_get(x_322, 0);
lean_inc(x_466);
x_467 = lean_unsigned_to_nat(1u);
x_468 = lean_nat_add(x_467, x_318);
lean_dec(x_318);
x_469 = lean_nat_add(x_467, x_466);
lean_dec(x_466);
x_470 = lean_box(1);
lean_ctor_set(x_10, 4, x_470);
lean_ctor_set(x_10, 3, x_322);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_469);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_468);
return x_4;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_318);
x_471 = lean_box(1);
x_472 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_10, 4, x_471);
lean_ctor_set(x_10, 3, x_471);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_472);
x_473 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_473);
return x_4;
}
}
else
{
lean_dec(x_318);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec(x_411);
x_474 = lean_ctor_get(x_322, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_322, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 lean_ctor_release(x_322, 4);
 x_476 = x_322;
} else {
 lean_dec_ref(x_322);
 x_476 = lean_box(0);
}
x_477 = lean_box(1);
x_478 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_476)) {
 x_479 = lean_alloc_ctor(0, 5, 0);
} else {
 x_479 = x_476;
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_319);
lean_ctor_set(x_479, 2, x_320);
lean_ctor_set(x_479, 3, x_477);
lean_ctor_set(x_479, 4, x_477);
lean_ctor_set(x_10, 4, x_477);
lean_ctor_set(x_10, 3, x_477);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_478);
x_480 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_479);
lean_ctor_set(x_4, 2, x_475);
lean_ctor_set(x_4, 1, x_474);
lean_ctor_set(x_4, 0, x_480);
return x_4;
}
else
{
lean_object* x_481; lean_object* x_482; 
lean_dec(x_320);
lean_dec(x_319);
lean_free_object(x_4);
x_481 = lean_box(1);
x_482 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_481);
lean_ctor_set(x_10, 3, x_411);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_482);
return x_10;
}
}
}
}
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; 
x_483 = lean_ctor_get(x_10, 0);
x_484 = lean_ctor_get(x_10, 1);
x_485 = lean_ctor_get(x_10, 2);
x_486 = lean_ctor_get(x_10, 3);
x_487 = lean_ctor_get(x_10, 4);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_10);
x_488 = lean_ctor_get(x_11, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_11, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_11, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_11, 3);
lean_inc(x_491);
x_492 = lean_ctor_get(x_11, 4);
lean_inc(x_492);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_493 = x_11;
} else {
 lean_dec_ref(x_11);
 x_493 = lean_box(0);
}
x_494 = lean_nat_dec_lt(x_483, x_488);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; 
lean_dec(x_483);
x_495 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_484, x_485, x_486, x_487, lean_box(0), lean_box(0), lean_box(0));
x_496 = lean_ctor_get(x_495, 2);
lean_inc(x_496);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_498);
lean_dec(x_495);
x_499 = lean_ctor_get(x_496, 0);
lean_inc(x_499);
lean_inc(x_492);
lean_inc(x_491);
lean_inc(x_490);
lean_inc(x_489);
lean_inc(x_488);
if (lean_is_scalar(x_493)) {
 x_500 = lean_alloc_ctor(0, 5, 0);
} else {
 x_500 = x_493;
}
lean_ctor_set(x_500, 0, x_488);
lean_ctor_set(x_500, 1, x_489);
lean_ctor_set(x_500, 2, x_490);
lean_ctor_set(x_500, 3, x_491);
lean_ctor_set(x_500, 4, x_492);
x_501 = lean_unsigned_to_nat(3u);
x_502 = lean_nat_mul(x_501, x_499);
x_503 = lean_nat_dec_lt(x_502, x_488);
lean_dec(x_502);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_492);
lean_dec(x_491);
lean_dec(x_490);
lean_dec(x_489);
lean_free_object(x_4);
x_504 = lean_unsigned_to_nat(1u);
x_505 = lean_nat_add(x_504, x_499);
lean_dec(x_499);
x_506 = lean_nat_add(x_505, x_488);
lean_dec(x_488);
lean_dec(x_505);
x_507 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_497);
lean_ctor_set(x_507, 2, x_498);
lean_ctor_set(x_507, 3, x_496);
lean_ctor_set(x_507, 4, x_500);
return x_507;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; 
lean_dec(x_500);
x_508 = lean_ctor_get(x_491, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_491, 1);
lean_inc(x_509);
x_510 = lean_ctor_get(x_491, 2);
lean_inc(x_510);
x_511 = lean_ctor_get(x_491, 3);
lean_inc(x_511);
x_512 = lean_ctor_get(x_491, 4);
lean_inc(x_512);
x_513 = lean_ctor_get(x_492, 0);
lean_inc(x_513);
x_514 = lean_unsigned_to_nat(2u);
x_515 = lean_nat_mul(x_514, x_513);
x_516 = lean_nat_dec_lt(x_508, x_515);
lean_dec(x_515);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_508);
lean_free_object(x_4);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 lean_ctor_release(x_491, 2);
 lean_ctor_release(x_491, 3);
 lean_ctor_release(x_491, 4);
 x_517 = x_491;
} else {
 lean_dec_ref(x_491);
 x_517 = lean_box(0);
}
x_518 = lean_unsigned_to_nat(1u);
x_519 = lean_nat_add(x_518, x_499);
lean_dec(x_499);
x_520 = lean_nat_add(x_519, x_488);
lean_dec(x_488);
x_521 = lean_nat_add(x_518, x_513);
lean_dec(x_513);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_522 = lean_ctor_get(x_511, 0);
lean_inc(x_522);
x_523 = lean_nat_add(x_519, x_522);
lean_dec(x_522);
lean_dec(x_519);
lean_inc(x_496);
if (lean_is_scalar(x_517)) {
 x_524 = lean_alloc_ctor(0, 5, 0);
} else {
 x_524 = x_517;
}
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_497);
lean_ctor_set(x_524, 2, x_498);
lean_ctor_set(x_524, 3, x_496);
lean_ctor_set(x_524, 4, x_511);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 lean_ctor_release(x_496, 2);
 lean_ctor_release(x_496, 3);
 lean_ctor_release(x_496, 4);
 x_525 = x_496;
} else {
 lean_dec_ref(x_496);
 x_525 = lean_box(0);
}
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_526 = lean_ctor_get(x_512, 0);
lean_inc(x_526);
x_527 = lean_nat_add(x_521, x_526);
lean_dec(x_526);
lean_dec(x_521);
if (lean_is_scalar(x_525)) {
 x_528 = lean_alloc_ctor(0, 5, 0);
} else {
 x_528 = x_525;
}
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_489);
lean_ctor_set(x_528, 2, x_490);
lean_ctor_set(x_528, 3, x_512);
lean_ctor_set(x_528, 4, x_492);
x_529 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_529, 0, x_520);
lean_ctor_set(x_529, 1, x_509);
lean_ctor_set(x_529, 2, x_510);
lean_ctor_set(x_529, 3, x_524);
lean_ctor_set(x_529, 4, x_528);
return x_529;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_530 = lean_unsigned_to_nat(0u);
x_531 = lean_nat_add(x_521, x_530);
lean_dec(x_521);
if (lean_is_scalar(x_525)) {
 x_532 = lean_alloc_ctor(0, 5, 0);
} else {
 x_532 = x_525;
}
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_489);
lean_ctor_set(x_532, 2, x_490);
lean_ctor_set(x_532, 3, x_512);
lean_ctor_set(x_532, 4, x_492);
x_533 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_533, 0, x_520);
lean_ctor_set(x_533, 1, x_509);
lean_ctor_set(x_533, 2, x_510);
lean_ctor_set(x_533, 3, x_524);
lean_ctor_set(x_533, 4, x_532);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_534 = lean_unsigned_to_nat(0u);
x_535 = lean_nat_add(x_519, x_534);
lean_dec(x_519);
lean_inc(x_496);
if (lean_is_scalar(x_517)) {
 x_536 = lean_alloc_ctor(0, 5, 0);
} else {
 x_536 = x_517;
}
lean_ctor_set(x_536, 0, x_535);
lean_ctor_set(x_536, 1, x_497);
lean_ctor_set(x_536, 2, x_498);
lean_ctor_set(x_536, 3, x_496);
lean_ctor_set(x_536, 4, x_511);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 lean_ctor_release(x_496, 2);
 lean_ctor_release(x_496, 3);
 lean_ctor_release(x_496, 4);
 x_537 = x_496;
} else {
 lean_dec_ref(x_496);
 x_537 = lean_box(0);
}
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_538 = lean_ctor_get(x_512, 0);
lean_inc(x_538);
x_539 = lean_nat_add(x_521, x_538);
lean_dec(x_538);
lean_dec(x_521);
if (lean_is_scalar(x_537)) {
 x_540 = lean_alloc_ctor(0, 5, 0);
} else {
 x_540 = x_537;
}
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_489);
lean_ctor_set(x_540, 2, x_490);
lean_ctor_set(x_540, 3, x_512);
lean_ctor_set(x_540, 4, x_492);
x_541 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_541, 0, x_520);
lean_ctor_set(x_541, 1, x_509);
lean_ctor_set(x_541, 2, x_510);
lean_ctor_set(x_541, 3, x_536);
lean_ctor_set(x_541, 4, x_540);
return x_541;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_nat_add(x_521, x_534);
lean_dec(x_521);
if (lean_is_scalar(x_537)) {
 x_543 = lean_alloc_ctor(0, 5, 0);
} else {
 x_543 = x_537;
}
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_489);
lean_ctor_set(x_543, 2, x_490);
lean_ctor_set(x_543, 3, x_512);
lean_ctor_set(x_543, 4, x_492);
x_544 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_544, 0, x_520);
lean_ctor_set(x_544, 1, x_509);
lean_ctor_set(x_544, 2, x_510);
lean_ctor_set(x_544, 3, x_536);
lean_ctor_set(x_544, 4, x_543);
return x_544;
}
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
x_545 = lean_unsigned_to_nat(1u);
x_546 = lean_nat_add(x_545, x_499);
lean_dec(x_499);
x_547 = lean_nat_add(x_546, x_488);
lean_dec(x_488);
x_548 = lean_nat_add(x_546, x_508);
lean_dec(x_508);
lean_dec(x_546);
x_549 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_497);
lean_ctor_set(x_549, 2, x_498);
lean_ctor_set(x_549, 3, x_496);
lean_ctor_set(x_549, 4, x_491);
lean_ctor_set(x_4, 4, x_492);
lean_ctor_set(x_4, 3, x_549);
lean_ctor_set(x_4, 2, x_490);
lean_ctor_set(x_4, 1, x_489);
lean_ctor_set(x_4, 0, x_547);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_491) == 0)
{
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_550 = lean_ctor_get(x_495, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_495, 1);
lean_inc(x_551);
lean_dec(x_495);
x_552 = lean_ctor_get(x_491, 0);
lean_inc(x_552);
x_553 = lean_unsigned_to_nat(1u);
x_554 = lean_nat_add(x_553, x_488);
lean_dec(x_488);
x_555 = lean_nat_add(x_553, x_552);
lean_dec(x_552);
x_556 = lean_box(1);
if (lean_is_scalar(x_493)) {
 x_557 = lean_alloc_ctor(0, 5, 0);
} else {
 x_557 = x_493;
}
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_550);
lean_ctor_set(x_557, 2, x_551);
lean_ctor_set(x_557, 3, x_556);
lean_ctor_set(x_557, 4, x_491);
x_558 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_558, 0, x_554);
lean_ctor_set(x_558, 1, x_489);
lean_ctor_set(x_558, 2, x_490);
lean_ctor_set(x_558, 3, x_557);
lean_ctor_set(x_558, 4, x_492);
return x_558;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_488);
x_559 = lean_ctor_get(x_495, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_495, 1);
lean_inc(x_560);
lean_dec(x_495);
x_561 = lean_ctor_get(x_491, 1);
lean_inc(x_561);
x_562 = lean_ctor_get(x_491, 2);
lean_inc(x_562);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 lean_ctor_release(x_491, 2);
 lean_ctor_release(x_491, 3);
 lean_ctor_release(x_491, 4);
 x_563 = x_491;
} else {
 lean_dec_ref(x_491);
 x_563 = lean_box(0);
}
x_564 = lean_box(1);
x_565 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_563)) {
 x_566 = lean_alloc_ctor(0, 5, 0);
} else {
 x_566 = x_563;
}
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_559);
lean_ctor_set(x_566, 2, x_560);
lean_ctor_set(x_566, 3, x_564);
lean_ctor_set(x_566, 4, x_564);
if (lean_is_scalar(x_493)) {
 x_567 = lean_alloc_ctor(0, 5, 0);
} else {
 x_567 = x_493;
}
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_489);
lean_ctor_set(x_567, 2, x_490);
lean_ctor_set(x_567, 3, x_564);
lean_ctor_set(x_567, 4, x_564);
x_568 = lean_unsigned_to_nat(3u);
x_569 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_561);
lean_ctor_set(x_569, 2, x_562);
lean_ctor_set(x_569, 3, x_566);
lean_ctor_set(x_569, 4, x_567);
return x_569;
}
}
else
{
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_488);
x_570 = lean_ctor_get(x_495, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_495, 1);
lean_inc(x_571);
lean_dec(x_495);
x_572 = lean_box(1);
x_573 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_493)) {
 x_574 = lean_alloc_ctor(0, 5, 0);
} else {
 x_574 = x_493;
}
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_570);
lean_ctor_set(x_574, 2, x_571);
lean_ctor_set(x_574, 3, x_572);
lean_ctor_set(x_574, 4, x_572);
x_575 = lean_unsigned_to_nat(3u);
x_576 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_489);
lean_ctor_set(x_576, 2, x_490);
lean_ctor_set(x_576, 3, x_574);
lean_ctor_set(x_576, 4, x_492);
return x_576;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_577 = lean_ctor_get(x_495, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_495, 1);
lean_inc(x_578);
lean_dec(x_495);
if (lean_is_scalar(x_493)) {
 x_579 = lean_alloc_ctor(0, 5, 0);
} else {
 x_579 = x_493;
}
lean_ctor_set(x_579, 0, x_488);
lean_ctor_set(x_579, 1, x_489);
lean_ctor_set(x_579, 2, x_490);
lean_ctor_set(x_579, 3, x_492);
lean_ctor_set(x_579, 4, x_492);
x_580 = lean_box(1);
x_581 = lean_unsigned_to_nat(2u);
x_582 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_577);
lean_ctor_set(x_582, 2, x_578);
lean_ctor_set(x_582, 3, x_580);
lean_ctor_set(x_582, 4, x_579);
return x_582;
}
}
}
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_488);
x_583 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_489, x_490, x_491, x_492, lean_box(0), lean_box(0), lean_box(0));
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
x_586 = lean_ctor_get(x_583, 2);
lean_inc(x_586);
lean_dec(x_583);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
if (lean_is_scalar(x_493)) {
 x_587 = lean_alloc_ctor(0, 5, 0);
} else {
 x_587 = x_493;
}
lean_ctor_set(x_587, 0, x_483);
lean_ctor_set(x_587, 1, x_484);
lean_ctor_set(x_587, 2, x_485);
lean_ctor_set(x_587, 3, x_486);
lean_ctor_set(x_587, 4, x_487);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; 
x_588 = lean_ctor_get(x_586, 0);
lean_inc(x_588);
x_589 = lean_unsigned_to_nat(3u);
x_590 = lean_nat_mul(x_589, x_588);
x_591 = lean_nat_dec_lt(x_590, x_483);
lean_dec(x_590);
if (x_591 == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_484);
lean_free_object(x_4);
x_592 = lean_unsigned_to_nat(1u);
x_593 = lean_nat_add(x_592, x_483);
lean_dec(x_483);
x_594 = lean_nat_add(x_593, x_588);
lean_dec(x_588);
lean_dec(x_593);
x_595 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_595, 0, x_594);
lean_ctor_set(x_595, 1, x_584);
lean_ctor_set(x_595, 2, x_585);
lean_ctor_set(x_595, 3, x_587);
lean_ctor_set(x_595, 4, x_586);
return x_595;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
lean_dec(x_587);
x_596 = lean_ctor_get(x_486, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_487, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_487, 1);
lean_inc(x_598);
x_599 = lean_ctor_get(x_487, 2);
lean_inc(x_599);
x_600 = lean_ctor_get(x_487, 3);
lean_inc(x_600);
x_601 = lean_ctor_get(x_487, 4);
lean_inc(x_601);
x_602 = lean_unsigned_to_nat(2u);
x_603 = lean_nat_mul(x_602, x_596);
x_604 = lean_nat_dec_lt(x_597, x_603);
lean_dec(x_603);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_597);
lean_free_object(x_4);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 lean_ctor_release(x_487, 4);
 x_605 = x_487;
} else {
 lean_dec_ref(x_487);
 x_605 = lean_box(0);
}
x_606 = lean_unsigned_to_nat(1u);
x_607 = lean_nat_add(x_606, x_483);
lean_dec(x_483);
x_608 = lean_nat_add(x_607, x_588);
lean_dec(x_607);
x_609 = lean_nat_add(x_606, x_596);
lean_dec(x_596);
x_610 = lean_nat_add(x_606, x_588);
lean_dec(x_588);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_611 = lean_ctor_get(x_600, 0);
lean_inc(x_611);
x_612 = lean_nat_add(x_609, x_611);
lean_dec(x_611);
lean_dec(x_609);
lean_inc(x_486);
if (lean_is_scalar(x_605)) {
 x_613 = lean_alloc_ctor(0, 5, 0);
} else {
 x_613 = x_605;
}
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_484);
lean_ctor_set(x_613, 2, x_485);
lean_ctor_set(x_613, 3, x_486);
lean_ctor_set(x_613, 4, x_600);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 lean_ctor_release(x_486, 2);
 lean_ctor_release(x_486, 3);
 lean_ctor_release(x_486, 4);
 x_614 = x_486;
} else {
 lean_dec_ref(x_486);
 x_614 = lean_box(0);
}
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_615 = lean_ctor_get(x_601, 0);
lean_inc(x_615);
x_616 = lean_nat_add(x_610, x_615);
lean_dec(x_615);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_614)) {
 x_617 = lean_alloc_ctor(0, 5, 0);
} else {
 x_617 = x_614;
}
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_584);
lean_ctor_set(x_617, 2, x_585);
lean_ctor_set(x_617, 3, x_601);
lean_ctor_set(x_617, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_618 = x_586;
} else {
 lean_dec_ref(x_586);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(0, 5, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_608);
lean_ctor_set(x_619, 1, x_598);
lean_ctor_set(x_619, 2, x_599);
lean_ctor_set(x_619, 3, x_613);
lean_ctor_set(x_619, 4, x_617);
return x_619;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_620 = lean_unsigned_to_nat(0u);
x_621 = lean_nat_add(x_610, x_620);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_614)) {
 x_622 = lean_alloc_ctor(0, 5, 0);
} else {
 x_622 = x_614;
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_584);
lean_ctor_set(x_622, 2, x_585);
lean_ctor_set(x_622, 3, x_601);
lean_ctor_set(x_622, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_623 = x_586;
} else {
 lean_dec_ref(x_586);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(0, 5, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_608);
lean_ctor_set(x_624, 1, x_598);
lean_ctor_set(x_624, 2, x_599);
lean_ctor_set(x_624, 3, x_613);
lean_ctor_set(x_624, 4, x_622);
return x_624;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_625 = lean_unsigned_to_nat(0u);
x_626 = lean_nat_add(x_609, x_625);
lean_dec(x_609);
lean_inc(x_486);
if (lean_is_scalar(x_605)) {
 x_627 = lean_alloc_ctor(0, 5, 0);
} else {
 x_627 = x_605;
}
lean_ctor_set(x_627, 0, x_626);
lean_ctor_set(x_627, 1, x_484);
lean_ctor_set(x_627, 2, x_485);
lean_ctor_set(x_627, 3, x_486);
lean_ctor_set(x_627, 4, x_600);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 lean_ctor_release(x_486, 2);
 lean_ctor_release(x_486, 3);
 lean_ctor_release(x_486, 4);
 x_628 = x_486;
} else {
 lean_dec_ref(x_486);
 x_628 = lean_box(0);
}
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_629 = lean_ctor_get(x_601, 0);
lean_inc(x_629);
x_630 = lean_nat_add(x_610, x_629);
lean_dec(x_629);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_628)) {
 x_631 = lean_alloc_ctor(0, 5, 0);
} else {
 x_631 = x_628;
}
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_584);
lean_ctor_set(x_631, 2, x_585);
lean_ctor_set(x_631, 3, x_601);
lean_ctor_set(x_631, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_632 = x_586;
} else {
 lean_dec_ref(x_586);
 x_632 = lean_box(0);
}
if (lean_is_scalar(x_632)) {
 x_633 = lean_alloc_ctor(0, 5, 0);
} else {
 x_633 = x_632;
}
lean_ctor_set(x_633, 0, x_608);
lean_ctor_set(x_633, 1, x_598);
lean_ctor_set(x_633, 2, x_599);
lean_ctor_set(x_633, 3, x_627);
lean_ctor_set(x_633, 4, x_631);
return x_633;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_634 = lean_nat_add(x_610, x_625);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_628)) {
 x_635 = lean_alloc_ctor(0, 5, 0);
} else {
 x_635 = x_628;
}
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_584);
lean_ctor_set(x_635, 2, x_585);
lean_ctor_set(x_635, 3, x_601);
lean_ctor_set(x_635, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_636 = x_586;
} else {
 lean_dec_ref(x_586);
 x_636 = lean_box(0);
}
if (lean_is_scalar(x_636)) {
 x_637 = lean_alloc_ctor(0, 5, 0);
} else {
 x_637 = x_636;
}
lean_ctor_set(x_637, 0, x_608);
lean_ctor_set(x_637, 1, x_598);
lean_ctor_set(x_637, 2, x_599);
lean_ctor_set(x_637, 3, x_627);
lean_ctor_set(x_637, 4, x_635);
return x_637;
}
}
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_596);
x_638 = lean_unsigned_to_nat(1u);
x_639 = lean_nat_add(x_638, x_483);
lean_dec(x_483);
x_640 = lean_nat_add(x_639, x_588);
lean_dec(x_639);
x_641 = lean_nat_add(x_638, x_588);
lean_dec(x_588);
x_642 = lean_nat_add(x_641, x_597);
lean_dec(x_597);
lean_dec(x_641);
x_643 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_584);
lean_ctor_set(x_643, 2, x_585);
lean_ctor_set(x_643, 3, x_487);
lean_ctor_set(x_643, 4, x_586);
lean_ctor_set(x_4, 4, x_643);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_640);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_486) == 0)
{
lean_dec(x_587);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_644 = lean_ctor_get(x_487, 0);
lean_inc(x_644);
x_645 = lean_unsigned_to_nat(1u);
x_646 = lean_nat_add(x_645, x_483);
lean_dec(x_483);
x_647 = lean_nat_add(x_645, x_644);
lean_dec(x_644);
x_648 = lean_box(1);
x_649 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_649, 0, x_647);
lean_ctor_set(x_649, 1, x_584);
lean_ctor_set(x_649, 2, x_585);
lean_ctor_set(x_649, 3, x_487);
lean_ctor_set(x_649, 4, x_648);
lean_ctor_set(x_4, 4, x_649);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_646);
return x_4;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_483);
x_650 = lean_box(1);
x_651 = lean_unsigned_to_nat(1u);
x_652 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_584);
lean_ctor_set(x_652, 2, x_585);
lean_ctor_set(x_652, 3, x_650);
lean_ctor_set(x_652, 4, x_650);
x_653 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_652);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_653);
return x_4;
}
}
else
{
lean_dec(x_483);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_587);
x_654 = lean_ctor_get(x_487, 1);
lean_inc(x_654);
x_655 = lean_ctor_get(x_487, 2);
lean_inc(x_655);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 lean_ctor_release(x_487, 4);
 x_656 = x_487;
} else {
 lean_dec_ref(x_487);
 x_656 = lean_box(0);
}
x_657 = lean_box(1);
x_658 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_656)) {
 x_659 = lean_alloc_ctor(0, 5, 0);
} else {
 x_659 = x_656;
}
lean_ctor_set(x_659, 0, x_658);
lean_ctor_set(x_659, 1, x_484);
lean_ctor_set(x_659, 2, x_485);
lean_ctor_set(x_659, 3, x_657);
lean_ctor_set(x_659, 4, x_657);
x_660 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_584);
lean_ctor_set(x_660, 2, x_585);
lean_ctor_set(x_660, 3, x_657);
lean_ctor_set(x_660, 4, x_657);
x_661 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_660);
lean_ctor_set(x_4, 3, x_659);
lean_ctor_set(x_4, 2, x_655);
lean_ctor_set(x_4, 1, x_654);
lean_ctor_set(x_4, 0, x_661);
return x_4;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_485);
lean_dec(x_484);
lean_free_object(x_4);
x_662 = lean_box(1);
x_663 = lean_unsigned_to_nat(2u);
x_664 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_584);
lean_ctor_set(x_664, 2, x_585);
lean_ctor_set(x_664, 3, x_587);
lean_ctor_set(x_664, 4, x_662);
return x_664;
}
}
}
}
}
}
else
{
lean_free_object(x_4);
return x_10;
}
}
else
{
lean_free_object(x_4);
return x_11;
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_17, 0);
lean_inc(x_665);
lean_dec(x_17);
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
lean_dec(x_665);
lean_ctor_set(x_4, 2, x_667);
lean_ctor_set(x_4, 1, x_666);
return x_4;
}
}
default: 
{
lean_object* x_668; lean_object* x_669; 
lean_free_object(x_4);
lean_dec(x_7);
x_668 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_erase_u2098___spec__1___rarg(x_1, x_2, x_3, x_11, lean_box(0));
x_669 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_8, x_9, x_10, x_668, lean_box(0), lean_box(0), lean_box(0));
return x_669;
}
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; 
x_670 = lean_ctor_get(x_4, 0);
x_671 = lean_ctor_get(x_4, 1);
x_672 = lean_ctor_get(x_4, 2);
x_673 = lean_ctor_get(x_4, 3);
x_674 = lean_ctor_get(x_4, 4);
lean_inc(x_674);
lean_inc(x_673);
lean_inc(x_672);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_671);
lean_inc(x_2);
x_675 = lean_apply_2(x_1, x_2, x_671);
x_676 = lean_unbox(x_675);
lean_dec(x_675);
switch (x_676) {
case 0:
{
lean_object* x_677; lean_object* x_678; 
lean_dec(x_670);
x_677 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_erase_u2098___spec__1___rarg(x_1, x_2, x_3, x_673, lean_box(0));
x_678 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_671, x_672, x_677, x_674, lean_box(0), lean_box(0), lean_box(0));
return x_678;
}
case 1:
{
lean_object* x_679; lean_object* x_680; 
lean_dec(x_2);
lean_dec(x_1);
x_679 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_671, x_672, lean_box(0));
x_680 = lean_apply_1(x_3, x_679);
if (lean_obj_tag(x_680) == 0)
{
lean_dec(x_670);
if (lean_obj_tag(x_673) == 0)
{
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; uint8_t x_693; 
x_681 = lean_ctor_get(x_673, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_673, 1);
lean_inc(x_682);
x_683 = lean_ctor_get(x_673, 2);
lean_inc(x_683);
x_684 = lean_ctor_get(x_673, 3);
lean_inc(x_684);
x_685 = lean_ctor_get(x_673, 4);
lean_inc(x_685);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 lean_ctor_release(x_673, 2);
 lean_ctor_release(x_673, 3);
 lean_ctor_release(x_673, 4);
 x_686 = x_673;
} else {
 lean_dec_ref(x_673);
 x_686 = lean_box(0);
}
x_687 = lean_ctor_get(x_674, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_674, 1);
lean_inc(x_688);
x_689 = lean_ctor_get(x_674, 2);
lean_inc(x_689);
x_690 = lean_ctor_get(x_674, 3);
lean_inc(x_690);
x_691 = lean_ctor_get(x_674, 4);
lean_inc(x_691);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 lean_ctor_release(x_674, 4);
 x_692 = x_674;
} else {
 lean_dec_ref(x_674);
 x_692 = lean_box(0);
}
x_693 = lean_nat_dec_lt(x_681, x_687);
if (x_693 == 0)
{
lean_object* x_694; lean_object* x_695; 
lean_dec(x_681);
x_694 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_682, x_683, x_684, x_685, lean_box(0), lean_box(0), lean_box(0));
x_695 = lean_ctor_get(x_694, 2);
lean_inc(x_695);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; 
x_696 = lean_ctor_get(x_694, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_694, 1);
lean_inc(x_697);
lean_dec(x_694);
x_698 = lean_ctor_get(x_695, 0);
lean_inc(x_698);
lean_inc(x_691);
lean_inc(x_690);
lean_inc(x_689);
lean_inc(x_688);
lean_inc(x_687);
if (lean_is_scalar(x_692)) {
 x_699 = lean_alloc_ctor(0, 5, 0);
} else {
 x_699 = x_692;
}
lean_ctor_set(x_699, 0, x_687);
lean_ctor_set(x_699, 1, x_688);
lean_ctor_set(x_699, 2, x_689);
lean_ctor_set(x_699, 3, x_690);
lean_ctor_set(x_699, 4, x_691);
x_700 = lean_unsigned_to_nat(3u);
x_701 = lean_nat_mul(x_700, x_698);
x_702 = lean_nat_dec_lt(x_701, x_687);
lean_dec(x_701);
if (x_702 == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_dec(x_691);
lean_dec(x_690);
lean_dec(x_689);
lean_dec(x_688);
x_703 = lean_unsigned_to_nat(1u);
x_704 = lean_nat_add(x_703, x_698);
lean_dec(x_698);
x_705 = lean_nat_add(x_704, x_687);
lean_dec(x_687);
lean_dec(x_704);
if (lean_is_scalar(x_686)) {
 x_706 = lean_alloc_ctor(0, 5, 0);
} else {
 x_706 = x_686;
}
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_696);
lean_ctor_set(x_706, 2, x_697);
lean_ctor_set(x_706, 3, x_695);
lean_ctor_set(x_706, 4, x_699);
return x_706;
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; 
lean_dec(x_699);
x_707 = lean_ctor_get(x_690, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_690, 1);
lean_inc(x_708);
x_709 = lean_ctor_get(x_690, 2);
lean_inc(x_709);
x_710 = lean_ctor_get(x_690, 3);
lean_inc(x_710);
x_711 = lean_ctor_get(x_690, 4);
lean_inc(x_711);
x_712 = lean_ctor_get(x_691, 0);
lean_inc(x_712);
x_713 = lean_unsigned_to_nat(2u);
x_714 = lean_nat_mul(x_713, x_712);
x_715 = lean_nat_dec_lt(x_707, x_714);
lean_dec(x_714);
if (x_715 == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_707);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 lean_ctor_release(x_690, 2);
 lean_ctor_release(x_690, 3);
 lean_ctor_release(x_690, 4);
 x_716 = x_690;
} else {
 lean_dec_ref(x_690);
 x_716 = lean_box(0);
}
x_717 = lean_unsigned_to_nat(1u);
x_718 = lean_nat_add(x_717, x_698);
lean_dec(x_698);
x_719 = lean_nat_add(x_718, x_687);
lean_dec(x_687);
x_720 = lean_nat_add(x_717, x_712);
lean_dec(x_712);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_721 = lean_ctor_get(x_710, 0);
lean_inc(x_721);
x_722 = lean_nat_add(x_718, x_721);
lean_dec(x_721);
lean_dec(x_718);
lean_inc(x_695);
if (lean_is_scalar(x_716)) {
 x_723 = lean_alloc_ctor(0, 5, 0);
} else {
 x_723 = x_716;
}
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_696);
lean_ctor_set(x_723, 2, x_697);
lean_ctor_set(x_723, 3, x_695);
lean_ctor_set(x_723, 4, x_710);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 lean_ctor_release(x_695, 2);
 lean_ctor_release(x_695, 3);
 lean_ctor_release(x_695, 4);
 x_724 = x_695;
} else {
 lean_dec_ref(x_695);
 x_724 = lean_box(0);
}
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_725 = lean_ctor_get(x_711, 0);
lean_inc(x_725);
x_726 = lean_nat_add(x_720, x_725);
lean_dec(x_725);
lean_dec(x_720);
if (lean_is_scalar(x_724)) {
 x_727 = lean_alloc_ctor(0, 5, 0);
} else {
 x_727 = x_724;
}
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_688);
lean_ctor_set(x_727, 2, x_689);
lean_ctor_set(x_727, 3, x_711);
lean_ctor_set(x_727, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_728 = lean_alloc_ctor(0, 5, 0);
} else {
 x_728 = x_686;
}
lean_ctor_set(x_728, 0, x_719);
lean_ctor_set(x_728, 1, x_708);
lean_ctor_set(x_728, 2, x_709);
lean_ctor_set(x_728, 3, x_723);
lean_ctor_set(x_728, 4, x_727);
return x_728;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_729 = lean_unsigned_to_nat(0u);
x_730 = lean_nat_add(x_720, x_729);
lean_dec(x_720);
if (lean_is_scalar(x_724)) {
 x_731 = lean_alloc_ctor(0, 5, 0);
} else {
 x_731 = x_724;
}
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_688);
lean_ctor_set(x_731, 2, x_689);
lean_ctor_set(x_731, 3, x_711);
lean_ctor_set(x_731, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_732 = lean_alloc_ctor(0, 5, 0);
} else {
 x_732 = x_686;
}
lean_ctor_set(x_732, 0, x_719);
lean_ctor_set(x_732, 1, x_708);
lean_ctor_set(x_732, 2, x_709);
lean_ctor_set(x_732, 3, x_723);
lean_ctor_set(x_732, 4, x_731);
return x_732;
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_733 = lean_unsigned_to_nat(0u);
x_734 = lean_nat_add(x_718, x_733);
lean_dec(x_718);
lean_inc(x_695);
if (lean_is_scalar(x_716)) {
 x_735 = lean_alloc_ctor(0, 5, 0);
} else {
 x_735 = x_716;
}
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_696);
lean_ctor_set(x_735, 2, x_697);
lean_ctor_set(x_735, 3, x_695);
lean_ctor_set(x_735, 4, x_710);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 lean_ctor_release(x_695, 2);
 lean_ctor_release(x_695, 3);
 lean_ctor_release(x_695, 4);
 x_736 = x_695;
} else {
 lean_dec_ref(x_695);
 x_736 = lean_box(0);
}
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_737 = lean_ctor_get(x_711, 0);
lean_inc(x_737);
x_738 = lean_nat_add(x_720, x_737);
lean_dec(x_737);
lean_dec(x_720);
if (lean_is_scalar(x_736)) {
 x_739 = lean_alloc_ctor(0, 5, 0);
} else {
 x_739 = x_736;
}
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_688);
lean_ctor_set(x_739, 2, x_689);
lean_ctor_set(x_739, 3, x_711);
lean_ctor_set(x_739, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_740 = lean_alloc_ctor(0, 5, 0);
} else {
 x_740 = x_686;
}
lean_ctor_set(x_740, 0, x_719);
lean_ctor_set(x_740, 1, x_708);
lean_ctor_set(x_740, 2, x_709);
lean_ctor_set(x_740, 3, x_735);
lean_ctor_set(x_740, 4, x_739);
return x_740;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_741 = lean_nat_add(x_720, x_733);
lean_dec(x_720);
if (lean_is_scalar(x_736)) {
 x_742 = lean_alloc_ctor(0, 5, 0);
} else {
 x_742 = x_736;
}
lean_ctor_set(x_742, 0, x_741);
lean_ctor_set(x_742, 1, x_688);
lean_ctor_set(x_742, 2, x_689);
lean_ctor_set(x_742, 3, x_711);
lean_ctor_set(x_742, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_743 = lean_alloc_ctor(0, 5, 0);
} else {
 x_743 = x_686;
}
lean_ctor_set(x_743, 0, x_719);
lean_ctor_set(x_743, 1, x_708);
lean_ctor_set(x_743, 2, x_709);
lean_ctor_set(x_743, 3, x_735);
lean_ctor_set(x_743, 4, x_742);
return x_743;
}
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_dec(x_712);
lean_dec(x_711);
lean_dec(x_710);
lean_dec(x_709);
lean_dec(x_708);
x_744 = lean_unsigned_to_nat(1u);
x_745 = lean_nat_add(x_744, x_698);
lean_dec(x_698);
x_746 = lean_nat_add(x_745, x_687);
lean_dec(x_687);
x_747 = lean_nat_add(x_745, x_707);
lean_dec(x_707);
lean_dec(x_745);
if (lean_is_scalar(x_686)) {
 x_748 = lean_alloc_ctor(0, 5, 0);
} else {
 x_748 = x_686;
}
lean_ctor_set(x_748, 0, x_747);
lean_ctor_set(x_748, 1, x_696);
lean_ctor_set(x_748, 2, x_697);
lean_ctor_set(x_748, 3, x_695);
lean_ctor_set(x_748, 4, x_690);
x_749 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_749, 0, x_746);
lean_ctor_set(x_749, 1, x_688);
lean_ctor_set(x_749, 2, x_689);
lean_ctor_set(x_749, 3, x_748);
lean_ctor_set(x_749, 4, x_691);
return x_749;
}
}
}
else
{
if (lean_obj_tag(x_690) == 0)
{
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_750 = lean_ctor_get(x_694, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_694, 1);
lean_inc(x_751);
lean_dec(x_694);
x_752 = lean_ctor_get(x_690, 0);
lean_inc(x_752);
x_753 = lean_unsigned_to_nat(1u);
x_754 = lean_nat_add(x_753, x_687);
lean_dec(x_687);
x_755 = lean_nat_add(x_753, x_752);
lean_dec(x_752);
x_756 = lean_box(1);
if (lean_is_scalar(x_692)) {
 x_757 = lean_alloc_ctor(0, 5, 0);
} else {
 x_757 = x_692;
}
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set(x_757, 1, x_750);
lean_ctor_set(x_757, 2, x_751);
lean_ctor_set(x_757, 3, x_756);
lean_ctor_set(x_757, 4, x_690);
if (lean_is_scalar(x_686)) {
 x_758 = lean_alloc_ctor(0, 5, 0);
} else {
 x_758 = x_686;
}
lean_ctor_set(x_758, 0, x_754);
lean_ctor_set(x_758, 1, x_688);
lean_ctor_set(x_758, 2, x_689);
lean_ctor_set(x_758, 3, x_757);
lean_ctor_set(x_758, 4, x_691);
return x_758;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_687);
x_759 = lean_ctor_get(x_694, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_694, 1);
lean_inc(x_760);
lean_dec(x_694);
x_761 = lean_ctor_get(x_690, 1);
lean_inc(x_761);
x_762 = lean_ctor_get(x_690, 2);
lean_inc(x_762);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 lean_ctor_release(x_690, 2);
 lean_ctor_release(x_690, 3);
 lean_ctor_release(x_690, 4);
 x_763 = x_690;
} else {
 lean_dec_ref(x_690);
 x_763 = lean_box(0);
}
x_764 = lean_box(1);
x_765 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_763)) {
 x_766 = lean_alloc_ctor(0, 5, 0);
} else {
 x_766 = x_763;
}
lean_ctor_set(x_766, 0, x_765);
lean_ctor_set(x_766, 1, x_759);
lean_ctor_set(x_766, 2, x_760);
lean_ctor_set(x_766, 3, x_764);
lean_ctor_set(x_766, 4, x_764);
if (lean_is_scalar(x_692)) {
 x_767 = lean_alloc_ctor(0, 5, 0);
} else {
 x_767 = x_692;
}
lean_ctor_set(x_767, 0, x_765);
lean_ctor_set(x_767, 1, x_688);
lean_ctor_set(x_767, 2, x_689);
lean_ctor_set(x_767, 3, x_764);
lean_ctor_set(x_767, 4, x_764);
x_768 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_686)) {
 x_769 = lean_alloc_ctor(0, 5, 0);
} else {
 x_769 = x_686;
}
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_761);
lean_ctor_set(x_769, 2, x_762);
lean_ctor_set(x_769, 3, x_766);
lean_ctor_set(x_769, 4, x_767);
return x_769;
}
}
else
{
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
lean_dec(x_687);
x_770 = lean_ctor_get(x_694, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_694, 1);
lean_inc(x_771);
lean_dec(x_694);
x_772 = lean_box(1);
x_773 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_692)) {
 x_774 = lean_alloc_ctor(0, 5, 0);
} else {
 x_774 = x_692;
}
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_770);
lean_ctor_set(x_774, 2, x_771);
lean_ctor_set(x_774, 3, x_772);
lean_ctor_set(x_774, 4, x_772);
x_775 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_686)) {
 x_776 = lean_alloc_ctor(0, 5, 0);
} else {
 x_776 = x_686;
}
lean_ctor_set(x_776, 0, x_775);
lean_ctor_set(x_776, 1, x_688);
lean_ctor_set(x_776, 2, x_689);
lean_ctor_set(x_776, 3, x_774);
lean_ctor_set(x_776, 4, x_691);
return x_776;
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_777 = lean_ctor_get(x_694, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_694, 1);
lean_inc(x_778);
lean_dec(x_694);
if (lean_is_scalar(x_692)) {
 x_779 = lean_alloc_ctor(0, 5, 0);
} else {
 x_779 = x_692;
}
lean_ctor_set(x_779, 0, x_687);
lean_ctor_set(x_779, 1, x_688);
lean_ctor_set(x_779, 2, x_689);
lean_ctor_set(x_779, 3, x_691);
lean_ctor_set(x_779, 4, x_691);
x_780 = lean_box(1);
x_781 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_686)) {
 x_782 = lean_alloc_ctor(0, 5, 0);
} else {
 x_782 = x_686;
}
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_777);
lean_ctor_set(x_782, 2, x_778);
lean_ctor_set(x_782, 3, x_780);
lean_ctor_set(x_782, 4, x_779);
return x_782;
}
}
}
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
lean_dec(x_687);
x_783 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_688, x_689, x_690, x_691, lean_box(0), lean_box(0), lean_box(0));
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
x_786 = lean_ctor_get(x_783, 2);
lean_inc(x_786);
lean_dec(x_783);
lean_inc(x_685);
lean_inc(x_684);
lean_inc(x_683);
lean_inc(x_682);
lean_inc(x_681);
if (lean_is_scalar(x_692)) {
 x_787 = lean_alloc_ctor(0, 5, 0);
} else {
 x_787 = x_692;
}
lean_ctor_set(x_787, 0, x_681);
lean_ctor_set(x_787, 1, x_682);
lean_ctor_set(x_787, 2, x_683);
lean_ctor_set(x_787, 3, x_684);
lean_ctor_set(x_787, 4, x_685);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; 
x_788 = lean_ctor_get(x_786, 0);
lean_inc(x_788);
x_789 = lean_unsigned_to_nat(3u);
x_790 = lean_nat_mul(x_789, x_788);
x_791 = lean_nat_dec_lt(x_790, x_681);
lean_dec(x_790);
if (x_791 == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_683);
lean_dec(x_682);
x_792 = lean_unsigned_to_nat(1u);
x_793 = lean_nat_add(x_792, x_681);
lean_dec(x_681);
x_794 = lean_nat_add(x_793, x_788);
lean_dec(x_788);
lean_dec(x_793);
if (lean_is_scalar(x_686)) {
 x_795 = lean_alloc_ctor(0, 5, 0);
} else {
 x_795 = x_686;
}
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_784);
lean_ctor_set(x_795, 2, x_785);
lean_ctor_set(x_795, 3, x_787);
lean_ctor_set(x_795, 4, x_786);
return x_795;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; uint8_t x_804; 
lean_dec(x_787);
x_796 = lean_ctor_get(x_684, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_685, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_685, 1);
lean_inc(x_798);
x_799 = lean_ctor_get(x_685, 2);
lean_inc(x_799);
x_800 = lean_ctor_get(x_685, 3);
lean_inc(x_800);
x_801 = lean_ctor_get(x_685, 4);
lean_inc(x_801);
x_802 = lean_unsigned_to_nat(2u);
x_803 = lean_nat_mul(x_802, x_796);
x_804 = lean_nat_dec_lt(x_797, x_803);
lean_dec(x_803);
if (x_804 == 0)
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_797);
lean_dec(x_686);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 lean_ctor_release(x_685, 2);
 lean_ctor_release(x_685, 3);
 lean_ctor_release(x_685, 4);
 x_805 = x_685;
} else {
 lean_dec_ref(x_685);
 x_805 = lean_box(0);
}
x_806 = lean_unsigned_to_nat(1u);
x_807 = lean_nat_add(x_806, x_681);
lean_dec(x_681);
x_808 = lean_nat_add(x_807, x_788);
lean_dec(x_807);
x_809 = lean_nat_add(x_806, x_796);
lean_dec(x_796);
x_810 = lean_nat_add(x_806, x_788);
lean_dec(x_788);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_811 = lean_ctor_get(x_800, 0);
lean_inc(x_811);
x_812 = lean_nat_add(x_809, x_811);
lean_dec(x_811);
lean_dec(x_809);
lean_inc(x_684);
if (lean_is_scalar(x_805)) {
 x_813 = lean_alloc_ctor(0, 5, 0);
} else {
 x_813 = x_805;
}
lean_ctor_set(x_813, 0, x_812);
lean_ctor_set(x_813, 1, x_682);
lean_ctor_set(x_813, 2, x_683);
lean_ctor_set(x_813, 3, x_684);
lean_ctor_set(x_813, 4, x_800);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 lean_ctor_release(x_684, 2);
 lean_ctor_release(x_684, 3);
 lean_ctor_release(x_684, 4);
 x_814 = x_684;
} else {
 lean_dec_ref(x_684);
 x_814 = lean_box(0);
}
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_815 = lean_ctor_get(x_801, 0);
lean_inc(x_815);
x_816 = lean_nat_add(x_810, x_815);
lean_dec(x_815);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_814)) {
 x_817 = lean_alloc_ctor(0, 5, 0);
} else {
 x_817 = x_814;
}
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_784);
lean_ctor_set(x_817, 2, x_785);
lean_ctor_set(x_817, 3, x_801);
lean_ctor_set(x_817, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_818 = x_786;
} else {
 lean_dec_ref(x_786);
 x_818 = lean_box(0);
}
if (lean_is_scalar(x_818)) {
 x_819 = lean_alloc_ctor(0, 5, 0);
} else {
 x_819 = x_818;
}
lean_ctor_set(x_819, 0, x_808);
lean_ctor_set(x_819, 1, x_798);
lean_ctor_set(x_819, 2, x_799);
lean_ctor_set(x_819, 3, x_813);
lean_ctor_set(x_819, 4, x_817);
return x_819;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_820 = lean_unsigned_to_nat(0u);
x_821 = lean_nat_add(x_810, x_820);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_814)) {
 x_822 = lean_alloc_ctor(0, 5, 0);
} else {
 x_822 = x_814;
}
lean_ctor_set(x_822, 0, x_821);
lean_ctor_set(x_822, 1, x_784);
lean_ctor_set(x_822, 2, x_785);
lean_ctor_set(x_822, 3, x_801);
lean_ctor_set(x_822, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_823 = x_786;
} else {
 lean_dec_ref(x_786);
 x_823 = lean_box(0);
}
if (lean_is_scalar(x_823)) {
 x_824 = lean_alloc_ctor(0, 5, 0);
} else {
 x_824 = x_823;
}
lean_ctor_set(x_824, 0, x_808);
lean_ctor_set(x_824, 1, x_798);
lean_ctor_set(x_824, 2, x_799);
lean_ctor_set(x_824, 3, x_813);
lean_ctor_set(x_824, 4, x_822);
return x_824;
}
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_825 = lean_unsigned_to_nat(0u);
x_826 = lean_nat_add(x_809, x_825);
lean_dec(x_809);
lean_inc(x_684);
if (lean_is_scalar(x_805)) {
 x_827 = lean_alloc_ctor(0, 5, 0);
} else {
 x_827 = x_805;
}
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_682);
lean_ctor_set(x_827, 2, x_683);
lean_ctor_set(x_827, 3, x_684);
lean_ctor_set(x_827, 4, x_800);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 lean_ctor_release(x_684, 2);
 lean_ctor_release(x_684, 3);
 lean_ctor_release(x_684, 4);
 x_828 = x_684;
} else {
 lean_dec_ref(x_684);
 x_828 = lean_box(0);
}
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_829 = lean_ctor_get(x_801, 0);
lean_inc(x_829);
x_830 = lean_nat_add(x_810, x_829);
lean_dec(x_829);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_828)) {
 x_831 = lean_alloc_ctor(0, 5, 0);
} else {
 x_831 = x_828;
}
lean_ctor_set(x_831, 0, x_830);
lean_ctor_set(x_831, 1, x_784);
lean_ctor_set(x_831, 2, x_785);
lean_ctor_set(x_831, 3, x_801);
lean_ctor_set(x_831, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_832 = x_786;
} else {
 lean_dec_ref(x_786);
 x_832 = lean_box(0);
}
if (lean_is_scalar(x_832)) {
 x_833 = lean_alloc_ctor(0, 5, 0);
} else {
 x_833 = x_832;
}
lean_ctor_set(x_833, 0, x_808);
lean_ctor_set(x_833, 1, x_798);
lean_ctor_set(x_833, 2, x_799);
lean_ctor_set(x_833, 3, x_827);
lean_ctor_set(x_833, 4, x_831);
return x_833;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_834 = lean_nat_add(x_810, x_825);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_828)) {
 x_835 = lean_alloc_ctor(0, 5, 0);
} else {
 x_835 = x_828;
}
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_784);
lean_ctor_set(x_835, 2, x_785);
lean_ctor_set(x_835, 3, x_801);
lean_ctor_set(x_835, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_836 = x_786;
} else {
 lean_dec_ref(x_786);
 x_836 = lean_box(0);
}
if (lean_is_scalar(x_836)) {
 x_837 = lean_alloc_ctor(0, 5, 0);
} else {
 x_837 = x_836;
}
lean_ctor_set(x_837, 0, x_808);
lean_ctor_set(x_837, 1, x_798);
lean_ctor_set(x_837, 2, x_799);
lean_ctor_set(x_837, 3, x_827);
lean_ctor_set(x_837, 4, x_835);
return x_837;
}
}
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
lean_dec(x_801);
lean_dec(x_800);
lean_dec(x_799);
lean_dec(x_798);
lean_dec(x_796);
x_838 = lean_unsigned_to_nat(1u);
x_839 = lean_nat_add(x_838, x_681);
lean_dec(x_681);
x_840 = lean_nat_add(x_839, x_788);
lean_dec(x_839);
x_841 = lean_nat_add(x_838, x_788);
lean_dec(x_788);
x_842 = lean_nat_add(x_841, x_797);
lean_dec(x_797);
lean_dec(x_841);
if (lean_is_scalar(x_686)) {
 x_843 = lean_alloc_ctor(0, 5, 0);
} else {
 x_843 = x_686;
}
lean_ctor_set(x_843, 0, x_842);
lean_ctor_set(x_843, 1, x_784);
lean_ctor_set(x_843, 2, x_785);
lean_ctor_set(x_843, 3, x_685);
lean_ctor_set(x_843, 4, x_786);
x_844 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_844, 0, x_840);
lean_ctor_set(x_844, 1, x_682);
lean_ctor_set(x_844, 2, x_683);
lean_ctor_set(x_844, 3, x_684);
lean_ctor_set(x_844, 4, x_843);
return x_844;
}
}
}
else
{
if (lean_obj_tag(x_684) == 0)
{
lean_dec(x_787);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_845 = lean_ctor_get(x_685, 0);
lean_inc(x_845);
x_846 = lean_unsigned_to_nat(1u);
x_847 = lean_nat_add(x_846, x_681);
lean_dec(x_681);
x_848 = lean_nat_add(x_846, x_845);
lean_dec(x_845);
x_849 = lean_box(1);
if (lean_is_scalar(x_686)) {
 x_850 = lean_alloc_ctor(0, 5, 0);
} else {
 x_850 = x_686;
}
lean_ctor_set(x_850, 0, x_848);
lean_ctor_set(x_850, 1, x_784);
lean_ctor_set(x_850, 2, x_785);
lean_ctor_set(x_850, 3, x_685);
lean_ctor_set(x_850, 4, x_849);
x_851 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_851, 0, x_847);
lean_ctor_set(x_851, 1, x_682);
lean_ctor_set(x_851, 2, x_683);
lean_ctor_set(x_851, 3, x_684);
lean_ctor_set(x_851, 4, x_850);
return x_851;
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_681);
x_852 = lean_box(1);
x_853 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_686)) {
 x_854 = lean_alloc_ctor(0, 5, 0);
} else {
 x_854 = x_686;
}
lean_ctor_set(x_854, 0, x_853);
lean_ctor_set(x_854, 1, x_784);
lean_ctor_set(x_854, 2, x_785);
lean_ctor_set(x_854, 3, x_852);
lean_ctor_set(x_854, 4, x_852);
x_855 = lean_unsigned_to_nat(3u);
x_856 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_682);
lean_ctor_set(x_856, 2, x_683);
lean_ctor_set(x_856, 3, x_684);
lean_ctor_set(x_856, 4, x_854);
return x_856;
}
}
else
{
lean_dec(x_681);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; 
lean_dec(x_787);
x_857 = lean_ctor_get(x_685, 1);
lean_inc(x_857);
x_858 = lean_ctor_get(x_685, 2);
lean_inc(x_858);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 lean_ctor_release(x_685, 2);
 lean_ctor_release(x_685, 3);
 lean_ctor_release(x_685, 4);
 x_859 = x_685;
} else {
 lean_dec_ref(x_685);
 x_859 = lean_box(0);
}
x_860 = lean_box(1);
x_861 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_859)) {
 x_862 = lean_alloc_ctor(0, 5, 0);
} else {
 x_862 = x_859;
}
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_862, 1, x_682);
lean_ctor_set(x_862, 2, x_683);
lean_ctor_set(x_862, 3, x_860);
lean_ctor_set(x_862, 4, x_860);
if (lean_is_scalar(x_686)) {
 x_863 = lean_alloc_ctor(0, 5, 0);
} else {
 x_863 = x_686;
}
lean_ctor_set(x_863, 0, x_861);
lean_ctor_set(x_863, 1, x_784);
lean_ctor_set(x_863, 2, x_785);
lean_ctor_set(x_863, 3, x_860);
lean_ctor_set(x_863, 4, x_860);
x_864 = lean_unsigned_to_nat(3u);
x_865 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_857);
lean_ctor_set(x_865, 2, x_858);
lean_ctor_set(x_865, 3, x_862);
lean_ctor_set(x_865, 4, x_863);
return x_865;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_683);
lean_dec(x_682);
x_866 = lean_box(1);
x_867 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_686)) {
 x_868 = lean_alloc_ctor(0, 5, 0);
} else {
 x_868 = x_686;
}
lean_ctor_set(x_868, 0, x_867);
lean_ctor_set(x_868, 1, x_784);
lean_ctor_set(x_868, 2, x_785);
lean_ctor_set(x_868, 3, x_787);
lean_ctor_set(x_868, 4, x_866);
return x_868;
}
}
}
}
}
else
{
return x_673;
}
}
else
{
return x_674;
}
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_869 = lean_ctor_get(x_680, 0);
lean_inc(x_869);
lean_dec(x_680);
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
x_872 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_872, 0, x_670);
lean_ctor_set(x_872, 1, x_870);
lean_ctor_set(x_872, 2, x_871);
lean_ctor_set(x_872, 3, x_673);
lean_ctor_set(x_872, 4, x_674);
return x_872;
}
}
default: 
{
lean_object* x_873; lean_object* x_874; 
lean_dec(x_670);
x_873 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_erase_u2098___spec__1___rarg(x_1, x_2, x_3, x_674, lean_box(0));
x_874 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_671, x_672, x_673, x_873, lean_box(0), lean_box(0), lean_box(0));
return x_874;
}
}
}
}
else
{
lean_object* x_875; lean_object* x_876; 
lean_dec(x_2);
lean_dec(x_1);
x_875 = lean_box(0);
x_876 = lean_apply_1(x_3, x_875);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; 
x_877 = lean_box(1);
return x_877;
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_878 = lean_ctor_get(x_876, 0);
lean_inc(x_878);
lean_dec(x_876);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_881 = lean_box(1);
x_882 = lean_unsigned_to_nat(1u);
x_883 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_883, 0, x_882);
lean_ctor_set(x_883, 1, x_879);
lean_ctor_set(x_883, 2, x_880);
lean_ctor_set(x_883, 3, x_881);
lean_ctor_set(x_883, 4, x_881);
return x_883;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_erase_u2098___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_erase_u2098___spec__1___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg___closed__1;
x_6 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_erase_u2098___spec__1___rarg(x_1, x_2, x_5, x_3, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_4, 3);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_8);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
switch (x_13) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_4);
lean_dec(x_7);
x_14 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___spec__1___rarg(x_1, x_2, x_3, x_10, lean_box(0));
x_15 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_8, x_9, x_14, x_11, lean_box(0), lean_box(0), lean_box(0));
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_8, x_9, lean_box(0));
x_17 = lean_apply_1(x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_7);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_10, 2);
x_23 = lean_ctor_get(x_10, 3);
x_24 = lean_ctor_get(x_10, 4);
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
x_27 = lean_ctor_get(x_11, 2);
x_28 = lean_ctor_get(x_11, 3);
x_29 = lean_ctor_get(x_11, 4);
x_30 = lean_nat_dec_lt(x_20, x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_20);
x_31 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_21, x_22, x_23, x_24, lean_box(0), lean_box(0), lean_box(0));
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_mul(x_36, x_35);
x_38 = lean_nat_dec_lt(x_37, x_25);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_4);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_39, x_35);
lean_dec(x_35);
x_41 = lean_nat_add(x_40, x_25);
lean_dec(x_25);
lean_dec(x_40);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_32);
lean_ctor_set(x_10, 2, x_34);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_41);
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_11);
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_28, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_28, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_28, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_29, 0);
lean_inc(x_47);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_mul(x_48, x_47);
x_50 = lean_nat_dec_lt(x_42, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
uint8_t x_51; 
lean_dec(x_42);
lean_free_object(x_4);
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_28, 4);
lean_dec(x_52);
x_53 = lean_ctor_get(x_28, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_28, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_28, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_28, 0);
lean_dec(x_56);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_57, x_35);
lean_dec(x_35);
x_59 = lean_nat_add(x_58, x_25);
lean_dec(x_25);
x_60 = lean_nat_add(x_57, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
x_62 = lean_nat_add(x_58, x_61);
lean_dec(x_61);
lean_dec(x_58);
lean_inc(x_32);
lean_ctor_set(x_28, 4, x_45);
lean_ctor_set(x_28, 3, x_32);
lean_ctor_set(x_28, 2, x_34);
lean_ctor_set(x_28, 1, x_33);
lean_ctor_set(x_28, 0, x_62);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_32, 4);
lean_dec(x_64);
x_65 = lean_ctor_get(x_32, 3);
lean_dec(x_65);
x_66 = lean_ctor_get(x_32, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_32, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_32, 0);
lean_dec(x_68);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_46, 0);
lean_inc(x_69);
x_70 = lean_nat_add(x_60, x_69);
lean_dec(x_69);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_70);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_add(x_60, x_71);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_72);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
else
{
lean_dec(x_32);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_46, 0);
lean_inc(x_73);
x_74 = lean_nat_add(x_60, x_73);
lean_dec(x_73);
lean_dec(x_60);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_26);
lean_ctor_set(x_75, 2, x_27);
lean_ctor_set(x_75, 3, x_46);
lean_ctor_set(x_75, 4, x_29);
lean_ctor_set(x_10, 4, x_75);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_add(x_60, x_76);
lean_dec(x_60);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_26);
lean_ctor_set(x_78, 2, x_27);
lean_ctor_set(x_78, 3, x_46);
lean_ctor_set(x_78, 4, x_29);
lean_ctor_set(x_10, 4, x_78);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_add(x_58, x_79);
lean_dec(x_58);
lean_inc(x_32);
lean_ctor_set(x_28, 4, x_45);
lean_ctor_set(x_28, 3, x_32);
lean_ctor_set(x_28, 2, x_34);
lean_ctor_set(x_28, 1, x_33);
lean_ctor_set(x_28, 0, x_80);
x_81 = !lean_is_exclusive(x_32);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_32, 4);
lean_dec(x_82);
x_83 = lean_ctor_get(x_32, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_32, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_32, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_32, 0);
lean_dec(x_86);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_46, 0);
lean_inc(x_87);
x_88 = lean_nat_add(x_60, x_87);
lean_dec(x_87);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_88);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_89; 
x_89 = lean_nat_add(x_60, x_79);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_89);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
else
{
lean_dec(x_32);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_46, 0);
lean_inc(x_90);
x_91 = lean_nat_add(x_60, x_90);
lean_dec(x_90);
lean_dec(x_60);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_26);
lean_ctor_set(x_92, 2, x_27);
lean_ctor_set(x_92, 3, x_46);
lean_ctor_set(x_92, 4, x_29);
lean_ctor_set(x_10, 4, x_92);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_nat_add(x_60, x_79);
lean_dec(x_60);
x_94 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_26);
lean_ctor_set(x_94, 2, x_27);
lean_ctor_set(x_94, 3, x_46);
lean_ctor_set(x_94, 4, x_29);
lean_ctor_set(x_10, 4, x_94);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_28);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_95, x_35);
lean_dec(x_35);
x_97 = lean_nat_add(x_96, x_25);
lean_dec(x_25);
x_98 = lean_nat_add(x_95, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_45, 0);
lean_inc(x_99);
x_100 = lean_nat_add(x_96, x_99);
lean_dec(x_99);
lean_dec(x_96);
lean_inc(x_32);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_33);
lean_ctor_set(x_101, 2, x_34);
lean_ctor_set(x_101, 3, x_32);
lean_ctor_set(x_101, 4, x_45);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_102 = x_32;
} else {
 lean_dec_ref(x_32);
 x_102 = lean_box(0);
}
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_46, 0);
lean_inc(x_103);
x_104 = lean_nat_add(x_98, x_103);
lean_dec(x_103);
lean_dec(x_98);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 5, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_26);
lean_ctor_set(x_105, 2, x_27);
lean_ctor_set(x_105, 3, x_46);
lean_ctor_set(x_105, 4, x_29);
lean_ctor_set(x_10, 4, x_105);
lean_ctor_set(x_10, 3, x_101);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_nat_add(x_98, x_106);
lean_dec(x_98);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(0, 5, 0);
} else {
 x_108 = x_102;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_26);
lean_ctor_set(x_108, 2, x_27);
lean_ctor_set(x_108, 3, x_46);
lean_ctor_set(x_108, 4, x_29);
lean_ctor_set(x_10, 4, x_108);
lean_ctor_set(x_10, 3, x_101);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_nat_add(x_96, x_109);
lean_dec(x_96);
lean_inc(x_32);
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_33);
lean_ctor_set(x_111, 2, x_34);
lean_ctor_set(x_111, 3, x_32);
lean_ctor_set(x_111, 4, x_45);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_112 = x_32;
} else {
 lean_dec_ref(x_32);
 x_112 = lean_box(0);
}
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_46, 0);
lean_inc(x_113);
x_114 = lean_nat_add(x_98, x_113);
lean_dec(x_113);
lean_dec(x_98);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 5, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_26);
lean_ctor_set(x_115, 2, x_27);
lean_ctor_set(x_115, 3, x_46);
lean_ctor_set(x_115, 4, x_29);
lean_ctor_set(x_10, 4, x_115);
lean_ctor_set(x_10, 3, x_111);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_nat_add(x_98, x_109);
lean_dec(x_98);
if (lean_is_scalar(x_112)) {
 x_117 = lean_alloc_ctor(0, 5, 0);
} else {
 x_117 = x_112;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_26);
lean_ctor_set(x_117, 2, x_27);
lean_ctor_set(x_117, 3, x_46);
lean_ctor_set(x_117, 4, x_29);
lean_ctor_set(x_10, 4, x_117);
lean_ctor_set(x_10, 3, x_111);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_118, x_35);
lean_dec(x_35);
x_120 = lean_nat_add(x_119, x_25);
lean_dec(x_25);
x_121 = lean_nat_add(x_119, x_42);
lean_dec(x_42);
lean_dec(x_119);
lean_ctor_set(x_10, 4, x_28);
lean_ctor_set(x_10, 3, x_32);
lean_ctor_set(x_10, 2, x_34);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_121);
lean_ctor_set(x_4, 4, x_29);
lean_ctor_set(x_4, 2, x_27);
lean_ctor_set(x_4, 1, x_26);
lean_ctor_set(x_4, 0, x_120);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_28) == 0)
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_31, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_31, 1);
lean_inc(x_123);
lean_dec(x_31);
x_124 = lean_ctor_get(x_28, 0);
lean_inc(x_124);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_add(x_125, x_25);
lean_dec(x_25);
x_127 = lean_nat_add(x_125, x_124);
lean_dec(x_124);
x_128 = lean_box(1);
lean_ctor_set(x_11, 4, x_28);
lean_ctor_set(x_11, 3, x_128);
lean_ctor_set(x_11, 2, x_123);
lean_ctor_set(x_11, 1, x_122);
lean_ctor_set(x_11, 0, x_127);
lean_ctor_set(x_10, 4, x_29);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_27);
lean_ctor_set(x_10, 1, x_26);
lean_ctor_set(x_10, 0, x_126);
return x_10;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_25);
x_129 = lean_ctor_get(x_31, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_31, 1);
lean_inc(x_130);
lean_dec(x_31);
x_131 = !lean_is_exclusive(x_28);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_28, 1);
x_133 = lean_ctor_get(x_28, 2);
x_134 = lean_ctor_get(x_28, 4);
lean_dec(x_134);
x_135 = lean_ctor_get(x_28, 3);
lean_dec(x_135);
x_136 = lean_ctor_get(x_28, 0);
lean_dec(x_136);
x_137 = lean_box(1);
x_138 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_28, 4, x_137);
lean_ctor_set(x_28, 3, x_137);
lean_ctor_set(x_28, 2, x_130);
lean_ctor_set(x_28, 1, x_129);
lean_ctor_set(x_28, 0, x_138);
lean_ctor_set(x_11, 4, x_137);
lean_ctor_set(x_11, 3, x_137);
lean_ctor_set(x_11, 0, x_138);
x_139 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_133);
lean_ctor_set(x_10, 1, x_132);
lean_ctor_set(x_10, 0, x_139);
return x_10;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_ctor_get(x_28, 1);
x_141 = lean_ctor_get(x_28, 2);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_28);
x_142 = lean_box(1);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_129);
lean_ctor_set(x_144, 2, x_130);
lean_ctor_set(x_144, 3, x_142);
lean_ctor_set(x_144, 4, x_142);
lean_ctor_set(x_11, 4, x_142);
lean_ctor_set(x_11, 3, x_142);
lean_ctor_set(x_11, 0, x_143);
x_145 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_144);
lean_ctor_set(x_10, 2, x_141);
lean_ctor_set(x_10, 1, x_140);
lean_ctor_set(x_10, 0, x_145);
return x_10;
}
}
}
else
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_25);
x_146 = lean_ctor_get(x_31, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_31, 1);
lean_inc(x_147);
lean_dec(x_31);
x_148 = lean_box(1);
x_149 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_11, 4, x_148);
lean_ctor_set(x_11, 3, x_148);
lean_ctor_set(x_11, 2, x_147);
lean_ctor_set(x_11, 1, x_146);
lean_ctor_set(x_11, 0, x_149);
x_150 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_29);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_27);
lean_ctor_set(x_10, 1, x_26);
lean_ctor_set(x_10, 0, x_150);
return x_10;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_31, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_31, 1);
lean_inc(x_152);
lean_dec(x_31);
lean_ctor_set(x_11, 3, x_29);
x_153 = lean_box(1);
x_154 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_153);
lean_ctor_set(x_10, 2, x_152);
lean_ctor_set(x_10, 1, x_151);
lean_ctor_set(x_10, 0, x_154);
return x_10;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_25);
x_155 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_26, x_27, x_28, x_29, lean_box(0), lean_box(0), lean_box(0));
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 2);
lean_inc(x_158);
lean_dec(x_155);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_ctor_set(x_11, 4, x_24);
lean_ctor_set(x_11, 3, x_23);
lean_ctor_set(x_11, 2, x_22);
lean_ctor_set(x_11, 1, x_21);
lean_ctor_set(x_11, 0, x_20);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_unsigned_to_nat(3u);
x_161 = lean_nat_mul(x_160, x_159);
x_162 = lean_nat_dec_lt(x_161, x_20);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_4);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_nat_add(x_163, x_20);
lean_dec(x_20);
x_165 = lean_nat_add(x_164, x_159);
lean_dec(x_159);
lean_dec(x_164);
lean_ctor_set(x_10, 4, x_158);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_165);
return x_10;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_dec(x_11);
x_166 = lean_ctor_get(x_23, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_24, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_24, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_24, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_24, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_24, 4);
lean_inc(x_171);
x_172 = lean_unsigned_to_nat(2u);
x_173 = lean_nat_mul(x_172, x_166);
x_174 = lean_nat_dec_lt(x_167, x_173);
lean_dec(x_173);
if (x_174 == 0)
{
uint8_t x_175; 
lean_dec(x_167);
lean_free_object(x_10);
lean_free_object(x_4);
x_175 = !lean_is_exclusive(x_24);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_176 = lean_ctor_get(x_24, 4);
lean_dec(x_176);
x_177 = lean_ctor_get(x_24, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_24, 2);
lean_dec(x_178);
x_179 = lean_ctor_get(x_24, 1);
lean_dec(x_179);
x_180 = lean_ctor_get(x_24, 0);
lean_dec(x_180);
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_nat_add(x_181, x_20);
lean_dec(x_20);
x_183 = lean_nat_add(x_182, x_159);
lean_dec(x_182);
x_184 = lean_nat_add(x_181, x_166);
lean_dec(x_166);
x_185 = lean_nat_add(x_181, x_159);
lean_dec(x_159);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_170, 0);
lean_inc(x_186);
x_187 = lean_nat_add(x_184, x_186);
lean_dec(x_186);
lean_dec(x_184);
lean_inc(x_23);
lean_ctor_set(x_24, 4, x_170);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_187);
x_188 = !lean_is_exclusive(x_23);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_23, 4);
lean_dec(x_189);
x_190 = lean_ctor_get(x_23, 3);
lean_dec(x_190);
x_191 = lean_ctor_get(x_23, 2);
lean_dec(x_191);
x_192 = lean_ctor_get(x_23, 1);
lean_dec(x_192);
x_193 = lean_ctor_get(x_23, 0);
lean_dec(x_193);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_171, 0);
lean_inc(x_194);
x_195 = lean_nat_add(x_185, x_194);
lean_dec(x_194);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_195);
x_196 = !lean_is_exclusive(x_158);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_158, 4);
lean_dec(x_197);
x_198 = lean_ctor_get(x_158, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_158, 2);
lean_dec(x_199);
x_200 = lean_ctor_get(x_158, 1);
lean_dec(x_200);
x_201 = lean_ctor_get(x_158, 0);
lean_dec(x_201);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_202; 
lean_dec(x_158);
x_202 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_202, 0, x_183);
lean_ctor_set(x_202, 1, x_168);
lean_ctor_set(x_202, 2, x_169);
lean_ctor_set(x_202, 3, x_24);
lean_ctor_set(x_202, 4, x_23);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_203 = lean_unsigned_to_nat(0u);
x_204 = lean_nat_add(x_185, x_203);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_204);
x_205 = !lean_is_exclusive(x_158);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_158, 4);
lean_dec(x_206);
x_207 = lean_ctor_get(x_158, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_158, 2);
lean_dec(x_208);
x_209 = lean_ctor_get(x_158, 1);
lean_dec(x_209);
x_210 = lean_ctor_get(x_158, 0);
lean_dec(x_210);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_211; 
lean_dec(x_158);
x_211 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_211, 0, x_183);
lean_ctor_set(x_211, 1, x_168);
lean_ctor_set(x_211, 2, x_169);
lean_ctor_set(x_211, 3, x_24);
lean_ctor_set(x_211, 4, x_23);
return x_211;
}
}
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_ctor_get(x_171, 0);
lean_inc(x_212);
x_213 = lean_nat_add(x_185, x_212);
lean_dec(x_212);
lean_dec(x_185);
lean_inc(x_158);
x_214 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_156);
lean_ctor_set(x_214, 2, x_157);
lean_ctor_set(x_214, 3, x_171);
lean_ctor_set(x_214, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_215 = x_158;
} else {
 lean_dec_ref(x_158);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(0, 5, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_183);
lean_ctor_set(x_216, 1, x_168);
lean_ctor_set(x_216, 2, x_169);
lean_ctor_set(x_216, 3, x_24);
lean_ctor_set(x_216, 4, x_214);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_unsigned_to_nat(0u);
x_218 = lean_nat_add(x_185, x_217);
lean_dec(x_185);
lean_inc(x_158);
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_156);
lean_ctor_set(x_219, 2, x_157);
lean_ctor_set(x_219, 3, x_171);
lean_ctor_set(x_219, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_220 = x_158;
} else {
 lean_dec_ref(x_158);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 5, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_183);
lean_ctor_set(x_221, 1, x_168);
lean_ctor_set(x_221, 2, x_169);
lean_ctor_set(x_221, 3, x_24);
lean_ctor_set(x_221, 4, x_219);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_unsigned_to_nat(0u);
x_223 = lean_nat_add(x_184, x_222);
lean_dec(x_184);
lean_inc(x_23);
lean_ctor_set(x_24, 4, x_170);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_223);
x_224 = !lean_is_exclusive(x_23);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_23, 4);
lean_dec(x_225);
x_226 = lean_ctor_get(x_23, 3);
lean_dec(x_226);
x_227 = lean_ctor_get(x_23, 2);
lean_dec(x_227);
x_228 = lean_ctor_get(x_23, 1);
lean_dec(x_228);
x_229 = lean_ctor_get(x_23, 0);
lean_dec(x_229);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_230 = lean_ctor_get(x_171, 0);
lean_inc(x_230);
x_231 = lean_nat_add(x_185, x_230);
lean_dec(x_230);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_231);
x_232 = !lean_is_exclusive(x_158);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_158, 4);
lean_dec(x_233);
x_234 = lean_ctor_get(x_158, 3);
lean_dec(x_234);
x_235 = lean_ctor_get(x_158, 2);
lean_dec(x_235);
x_236 = lean_ctor_get(x_158, 1);
lean_dec(x_236);
x_237 = lean_ctor_get(x_158, 0);
lean_dec(x_237);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_238; 
lean_dec(x_158);
x_238 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_238, 0, x_183);
lean_ctor_set(x_238, 1, x_168);
lean_ctor_set(x_238, 2, x_169);
lean_ctor_set(x_238, 3, x_24);
lean_ctor_set(x_238, 4, x_23);
return x_238;
}
}
else
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_nat_add(x_185, x_222);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_239);
x_240 = !lean_is_exclusive(x_158);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = lean_ctor_get(x_158, 4);
lean_dec(x_241);
x_242 = lean_ctor_get(x_158, 3);
lean_dec(x_242);
x_243 = lean_ctor_get(x_158, 2);
lean_dec(x_243);
x_244 = lean_ctor_get(x_158, 1);
lean_dec(x_244);
x_245 = lean_ctor_get(x_158, 0);
lean_dec(x_245);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_246; 
lean_dec(x_158);
x_246 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_246, 0, x_183);
lean_ctor_set(x_246, 1, x_168);
lean_ctor_set(x_246, 2, x_169);
lean_ctor_set(x_246, 3, x_24);
lean_ctor_set(x_246, 4, x_23);
return x_246;
}
}
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = lean_ctor_get(x_171, 0);
lean_inc(x_247);
x_248 = lean_nat_add(x_185, x_247);
lean_dec(x_247);
lean_dec(x_185);
lean_inc(x_158);
x_249 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_156);
lean_ctor_set(x_249, 2, x_157);
lean_ctor_set(x_249, 3, x_171);
lean_ctor_set(x_249, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_250 = x_158;
} else {
 lean_dec_ref(x_158);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 5, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_183);
lean_ctor_set(x_251, 1, x_168);
lean_ctor_set(x_251, 2, x_169);
lean_ctor_set(x_251, 3, x_24);
lean_ctor_set(x_251, 4, x_249);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_nat_add(x_185, x_222);
lean_dec(x_185);
lean_inc(x_158);
x_253 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_156);
lean_ctor_set(x_253, 2, x_157);
lean_ctor_set(x_253, 3, x_171);
lean_ctor_set(x_253, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_254 = x_158;
} else {
 lean_dec_ref(x_158);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(0, 5, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_183);
lean_ctor_set(x_255, 1, x_168);
lean_ctor_set(x_255, 2, x_169);
lean_ctor_set(x_255, 3, x_24);
lean_ctor_set(x_255, 4, x_253);
return x_255;
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_24);
x_256 = lean_unsigned_to_nat(1u);
x_257 = lean_nat_add(x_256, x_20);
lean_dec(x_20);
x_258 = lean_nat_add(x_257, x_159);
lean_dec(x_257);
x_259 = lean_nat_add(x_256, x_166);
lean_dec(x_166);
x_260 = lean_nat_add(x_256, x_159);
lean_dec(x_159);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_170, 0);
lean_inc(x_261);
x_262 = lean_nat_add(x_259, x_261);
lean_dec(x_261);
lean_dec(x_259);
lean_inc(x_23);
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_21);
lean_ctor_set(x_263, 2, x_22);
lean_ctor_set(x_263, 3, x_23);
lean_ctor_set(x_263, 4, x_170);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 x_264 = x_23;
} else {
 lean_dec_ref(x_23);
 x_264 = lean_box(0);
}
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_265 = lean_ctor_get(x_171, 0);
lean_inc(x_265);
x_266 = lean_nat_add(x_260, x_265);
lean_dec(x_265);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_264)) {
 x_267 = lean_alloc_ctor(0, 5, 0);
} else {
 x_267 = x_264;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_156);
lean_ctor_set(x_267, 2, x_157);
lean_ctor_set(x_267, 3, x_171);
lean_ctor_set(x_267, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_268 = x_158;
} else {
 lean_dec_ref(x_158);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(0, 5, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_258);
lean_ctor_set(x_269, 1, x_168);
lean_ctor_set(x_269, 2, x_169);
lean_ctor_set(x_269, 3, x_263);
lean_ctor_set(x_269, 4, x_267);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_unsigned_to_nat(0u);
x_271 = lean_nat_add(x_260, x_270);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_264)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_264;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_156);
lean_ctor_set(x_272, 2, x_157);
lean_ctor_set(x_272, 3, x_171);
lean_ctor_set(x_272, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_273 = x_158;
} else {
 lean_dec_ref(x_158);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 5, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_258);
lean_ctor_set(x_274, 1, x_168);
lean_ctor_set(x_274, 2, x_169);
lean_ctor_set(x_274, 3, x_263);
lean_ctor_set(x_274, 4, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_unsigned_to_nat(0u);
x_276 = lean_nat_add(x_259, x_275);
lean_dec(x_259);
lean_inc(x_23);
x_277 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_21);
lean_ctor_set(x_277, 2, x_22);
lean_ctor_set(x_277, 3, x_23);
lean_ctor_set(x_277, 4, x_170);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 x_278 = x_23;
} else {
 lean_dec_ref(x_23);
 x_278 = lean_box(0);
}
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_ctor_get(x_171, 0);
lean_inc(x_279);
x_280 = lean_nat_add(x_260, x_279);
lean_dec(x_279);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_278)) {
 x_281 = lean_alloc_ctor(0, 5, 0);
} else {
 x_281 = x_278;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_156);
lean_ctor_set(x_281, 2, x_157);
lean_ctor_set(x_281, 3, x_171);
lean_ctor_set(x_281, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_282 = x_158;
} else {
 lean_dec_ref(x_158);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(0, 5, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_258);
lean_ctor_set(x_283, 1, x_168);
lean_ctor_set(x_283, 2, x_169);
lean_ctor_set(x_283, 3, x_277);
lean_ctor_set(x_283, 4, x_281);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_284 = lean_nat_add(x_260, x_275);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_278)) {
 x_285 = lean_alloc_ctor(0, 5, 0);
} else {
 x_285 = x_278;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_156);
lean_ctor_set(x_285, 2, x_157);
lean_ctor_set(x_285, 3, x_171);
lean_ctor_set(x_285, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_286 = x_158;
} else {
 lean_dec_ref(x_158);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(0, 5, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_258);
lean_ctor_set(x_287, 1, x_168);
lean_ctor_set(x_287, 2, x_169);
lean_ctor_set(x_287, 3, x_277);
lean_ctor_set(x_287, 4, x_285);
return x_287;
}
}
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_166);
x_288 = lean_unsigned_to_nat(1u);
x_289 = lean_nat_add(x_288, x_20);
lean_dec(x_20);
x_290 = lean_nat_add(x_289, x_159);
lean_dec(x_289);
x_291 = lean_nat_add(x_288, x_159);
lean_dec(x_159);
x_292 = lean_nat_add(x_291, x_167);
lean_dec(x_167);
lean_dec(x_291);
lean_ctor_set(x_10, 4, x_158);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_292);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_290);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_24, 0);
lean_inc(x_293);
x_294 = lean_unsigned_to_nat(1u);
x_295 = lean_nat_add(x_294, x_20);
lean_dec(x_20);
x_296 = lean_nat_add(x_294, x_293);
lean_dec(x_293);
x_297 = lean_box(1);
lean_ctor_set(x_10, 4, x_297);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_296);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_295);
return x_4;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_20);
x_298 = lean_box(1);
x_299 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_10, 4, x_298);
lean_ctor_set(x_10, 3, x_298);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_299);
x_300 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_300);
return x_4;
}
}
else
{
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_301; 
lean_dec(x_11);
x_301 = !lean_is_exclusive(x_24);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_302 = lean_ctor_get(x_24, 1);
x_303 = lean_ctor_get(x_24, 2);
x_304 = lean_ctor_get(x_24, 4);
lean_dec(x_304);
x_305 = lean_ctor_get(x_24, 3);
lean_dec(x_305);
x_306 = lean_ctor_get(x_24, 0);
lean_dec(x_306);
x_307 = lean_box(1);
x_308 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_24, 4, x_307);
lean_ctor_set(x_24, 3, x_307);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_308);
lean_ctor_set(x_10, 4, x_307);
lean_ctor_set(x_10, 3, x_307);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_308);
x_309 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_24);
lean_ctor_set(x_4, 2, x_303);
lean_ctor_set(x_4, 1, x_302);
lean_ctor_set(x_4, 0, x_309);
return x_4;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_310 = lean_ctor_get(x_24, 1);
x_311 = lean_ctor_get(x_24, 2);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_24);
x_312 = lean_box(1);
x_313 = lean_unsigned_to_nat(1u);
x_314 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_21);
lean_ctor_set(x_314, 2, x_22);
lean_ctor_set(x_314, 3, x_312);
lean_ctor_set(x_314, 4, x_312);
lean_ctor_set(x_10, 4, x_312);
lean_ctor_set(x_10, 3, x_312);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_313);
x_315 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_314);
lean_ctor_set(x_4, 2, x_311);
lean_ctor_set(x_4, 1, x_310);
lean_ctor_set(x_4, 0, x_315);
return x_4;
}
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_4);
x_316 = lean_box(1);
x_317 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_316);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_317);
return x_10;
}
}
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_318 = lean_ctor_get(x_10, 0);
x_319 = lean_ctor_get(x_10, 1);
x_320 = lean_ctor_get(x_10, 2);
x_321 = lean_ctor_get(x_10, 3);
x_322 = lean_ctor_get(x_10, 4);
x_323 = lean_ctor_get(x_11, 0);
x_324 = lean_ctor_get(x_11, 1);
x_325 = lean_ctor_get(x_11, 2);
x_326 = lean_ctor_get(x_11, 3);
x_327 = lean_ctor_get(x_11, 4);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_11);
x_328 = lean_nat_dec_lt(x_318, x_323);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_318);
x_329 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_319, x_320, x_321, x_322, lean_box(0), lean_box(0), lean_box(0));
x_330 = lean_ctor_get(x_329, 2);
lean_inc(x_330);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_331 = lean_ctor_get(x_329, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_dec(x_329);
x_333 = lean_ctor_get(x_330, 0);
lean_inc(x_333);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
x_334 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_334, 0, x_323);
lean_ctor_set(x_334, 1, x_324);
lean_ctor_set(x_334, 2, x_325);
lean_ctor_set(x_334, 3, x_326);
lean_ctor_set(x_334, 4, x_327);
x_335 = lean_unsigned_to_nat(3u);
x_336 = lean_nat_mul(x_335, x_333);
x_337 = lean_nat_dec_lt(x_336, x_323);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_free_object(x_4);
x_338 = lean_unsigned_to_nat(1u);
x_339 = lean_nat_add(x_338, x_333);
lean_dec(x_333);
x_340 = lean_nat_add(x_339, x_323);
lean_dec(x_323);
lean_dec(x_339);
lean_ctor_set(x_10, 4, x_334);
lean_ctor_set(x_10, 3, x_330);
lean_ctor_set(x_10, 2, x_332);
lean_ctor_set(x_10, 1, x_331);
lean_ctor_set(x_10, 0, x_340);
return x_10;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
lean_dec(x_334);
x_341 = lean_ctor_get(x_326, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_326, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_326, 2);
lean_inc(x_343);
x_344 = lean_ctor_get(x_326, 3);
lean_inc(x_344);
x_345 = lean_ctor_get(x_326, 4);
lean_inc(x_345);
x_346 = lean_ctor_get(x_327, 0);
lean_inc(x_346);
x_347 = lean_unsigned_to_nat(2u);
x_348 = lean_nat_mul(x_347, x_346);
x_349 = lean_nat_dec_lt(x_341, x_348);
lean_dec(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_341);
lean_free_object(x_4);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 x_350 = x_326;
} else {
 lean_dec_ref(x_326);
 x_350 = lean_box(0);
}
x_351 = lean_unsigned_to_nat(1u);
x_352 = lean_nat_add(x_351, x_333);
lean_dec(x_333);
x_353 = lean_nat_add(x_352, x_323);
lean_dec(x_323);
x_354 = lean_nat_add(x_351, x_346);
lean_dec(x_346);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_355 = lean_ctor_get(x_344, 0);
lean_inc(x_355);
x_356 = lean_nat_add(x_352, x_355);
lean_dec(x_355);
lean_dec(x_352);
lean_inc(x_330);
if (lean_is_scalar(x_350)) {
 x_357 = lean_alloc_ctor(0, 5, 0);
} else {
 x_357 = x_350;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_331);
lean_ctor_set(x_357, 2, x_332);
lean_ctor_set(x_357, 3, x_330);
lean_ctor_set(x_357, 4, x_344);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 x_358 = x_330;
} else {
 lean_dec_ref(x_330);
 x_358 = lean_box(0);
}
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_345, 0);
lean_inc(x_359);
x_360 = lean_nat_add(x_354, x_359);
lean_dec(x_359);
lean_dec(x_354);
if (lean_is_scalar(x_358)) {
 x_361 = lean_alloc_ctor(0, 5, 0);
} else {
 x_361 = x_358;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_324);
lean_ctor_set(x_361, 2, x_325);
lean_ctor_set(x_361, 3, x_345);
lean_ctor_set(x_361, 4, x_327);
lean_ctor_set(x_10, 4, x_361);
lean_ctor_set(x_10, 3, x_357);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_unsigned_to_nat(0u);
x_363 = lean_nat_add(x_354, x_362);
lean_dec(x_354);
if (lean_is_scalar(x_358)) {
 x_364 = lean_alloc_ctor(0, 5, 0);
} else {
 x_364 = x_358;
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_324);
lean_ctor_set(x_364, 2, x_325);
lean_ctor_set(x_364, 3, x_345);
lean_ctor_set(x_364, 4, x_327);
lean_ctor_set(x_10, 4, x_364);
lean_ctor_set(x_10, 3, x_357);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = lean_unsigned_to_nat(0u);
x_366 = lean_nat_add(x_352, x_365);
lean_dec(x_352);
lean_inc(x_330);
if (lean_is_scalar(x_350)) {
 x_367 = lean_alloc_ctor(0, 5, 0);
} else {
 x_367 = x_350;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_331);
lean_ctor_set(x_367, 2, x_332);
lean_ctor_set(x_367, 3, x_330);
lean_ctor_set(x_367, 4, x_344);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 x_368 = x_330;
} else {
 lean_dec_ref(x_330);
 x_368 = lean_box(0);
}
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_345, 0);
lean_inc(x_369);
x_370 = lean_nat_add(x_354, x_369);
lean_dec(x_369);
lean_dec(x_354);
if (lean_is_scalar(x_368)) {
 x_371 = lean_alloc_ctor(0, 5, 0);
} else {
 x_371 = x_368;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_324);
lean_ctor_set(x_371, 2, x_325);
lean_ctor_set(x_371, 3, x_345);
lean_ctor_set(x_371, 4, x_327);
lean_ctor_set(x_10, 4, x_371);
lean_ctor_set(x_10, 3, x_367);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_nat_add(x_354, x_365);
lean_dec(x_354);
if (lean_is_scalar(x_368)) {
 x_373 = lean_alloc_ctor(0, 5, 0);
} else {
 x_373 = x_368;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_324);
lean_ctor_set(x_373, 2, x_325);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set(x_373, 4, x_327);
lean_ctor_set(x_10, 4, x_373);
lean_ctor_set(x_10, 3, x_367);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
x_374 = lean_unsigned_to_nat(1u);
x_375 = lean_nat_add(x_374, x_333);
lean_dec(x_333);
x_376 = lean_nat_add(x_375, x_323);
lean_dec(x_323);
x_377 = lean_nat_add(x_375, x_341);
lean_dec(x_341);
lean_dec(x_375);
lean_ctor_set(x_10, 4, x_326);
lean_ctor_set(x_10, 3, x_330);
lean_ctor_set(x_10, 2, x_332);
lean_ctor_set(x_10, 1, x_331);
lean_ctor_set(x_10, 0, x_377);
lean_ctor_set(x_4, 4, x_327);
lean_ctor_set(x_4, 2, x_325);
lean_ctor_set(x_4, 1, x_324);
lean_ctor_set(x_4, 0, x_376);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_326) == 0)
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_378 = lean_ctor_get(x_329, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_329, 1);
lean_inc(x_379);
lean_dec(x_329);
x_380 = lean_ctor_get(x_326, 0);
lean_inc(x_380);
x_381 = lean_unsigned_to_nat(1u);
x_382 = lean_nat_add(x_381, x_323);
lean_dec(x_323);
x_383 = lean_nat_add(x_381, x_380);
lean_dec(x_380);
x_384 = lean_box(1);
x_385 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_378);
lean_ctor_set(x_385, 2, x_379);
lean_ctor_set(x_385, 3, x_384);
lean_ctor_set(x_385, 4, x_326);
lean_ctor_set(x_10, 4, x_327);
lean_ctor_set(x_10, 3, x_385);
lean_ctor_set(x_10, 2, x_325);
lean_ctor_set(x_10, 1, x_324);
lean_ctor_set(x_10, 0, x_382);
return x_10;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_323);
x_386 = lean_ctor_get(x_329, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_329, 1);
lean_inc(x_387);
lean_dec(x_329);
x_388 = lean_ctor_get(x_326, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_326, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 x_390 = x_326;
} else {
 lean_dec_ref(x_326);
 x_390 = lean_box(0);
}
x_391 = lean_box(1);
x_392 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_390)) {
 x_393 = lean_alloc_ctor(0, 5, 0);
} else {
 x_393 = x_390;
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_386);
lean_ctor_set(x_393, 2, x_387);
lean_ctor_set(x_393, 3, x_391);
lean_ctor_set(x_393, 4, x_391);
x_394 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_324);
lean_ctor_set(x_394, 2, x_325);
lean_ctor_set(x_394, 3, x_391);
lean_ctor_set(x_394, 4, x_391);
x_395 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_394);
lean_ctor_set(x_10, 3, x_393);
lean_ctor_set(x_10, 2, x_389);
lean_ctor_set(x_10, 1, x_388);
lean_ctor_set(x_10, 0, x_395);
return x_10;
}
}
else
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_323);
x_396 = lean_ctor_get(x_329, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_329, 1);
lean_inc(x_397);
lean_dec(x_329);
x_398 = lean_box(1);
x_399 = lean_unsigned_to_nat(1u);
x_400 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_396);
lean_ctor_set(x_400, 2, x_397);
lean_ctor_set(x_400, 3, x_398);
lean_ctor_set(x_400, 4, x_398);
x_401 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_327);
lean_ctor_set(x_10, 3, x_400);
lean_ctor_set(x_10, 2, x_325);
lean_ctor_set(x_10, 1, x_324);
lean_ctor_set(x_10, 0, x_401);
return x_10;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_402 = lean_ctor_get(x_329, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_329, 1);
lean_inc(x_403);
lean_dec(x_329);
x_404 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_404, 0, x_323);
lean_ctor_set(x_404, 1, x_324);
lean_ctor_set(x_404, 2, x_325);
lean_ctor_set(x_404, 3, x_327);
lean_ctor_set(x_404, 4, x_327);
x_405 = lean_box(1);
x_406 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_404);
lean_ctor_set(x_10, 3, x_405);
lean_ctor_set(x_10, 2, x_403);
lean_ctor_set(x_10, 1, x_402);
lean_ctor_set(x_10, 0, x_406);
return x_10;
}
}
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_323);
x_407 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_324, x_325, x_326, x_327, lean_box(0), lean_box(0), lean_box(0));
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_407, 2);
lean_inc(x_410);
lean_dec(x_407);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
x_411 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_411, 0, x_318);
lean_ctor_set(x_411, 1, x_319);
lean_ctor_set(x_411, 2, x_320);
lean_ctor_set(x_411, 3, x_321);
lean_ctor_set(x_411, 4, x_322);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_412 = lean_ctor_get(x_410, 0);
lean_inc(x_412);
x_413 = lean_unsigned_to_nat(3u);
x_414 = lean_nat_mul(x_413, x_412);
x_415 = lean_nat_dec_lt(x_414, x_318);
lean_dec(x_414);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_free_object(x_4);
x_416 = lean_unsigned_to_nat(1u);
x_417 = lean_nat_add(x_416, x_318);
lean_dec(x_318);
x_418 = lean_nat_add(x_417, x_412);
lean_dec(x_412);
lean_dec(x_417);
lean_ctor_set(x_10, 4, x_410);
lean_ctor_set(x_10, 3, x_411);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_418);
return x_10;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_dec(x_411);
x_419 = lean_ctor_get(x_321, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_322, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_322, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_322, 2);
lean_inc(x_422);
x_423 = lean_ctor_get(x_322, 3);
lean_inc(x_423);
x_424 = lean_ctor_get(x_322, 4);
lean_inc(x_424);
x_425 = lean_unsigned_to_nat(2u);
x_426 = lean_nat_mul(x_425, x_419);
x_427 = lean_nat_dec_lt(x_420, x_426);
lean_dec(x_426);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_420);
lean_free_object(x_10);
lean_free_object(x_4);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 lean_ctor_release(x_322, 4);
 x_428 = x_322;
} else {
 lean_dec_ref(x_322);
 x_428 = lean_box(0);
}
x_429 = lean_unsigned_to_nat(1u);
x_430 = lean_nat_add(x_429, x_318);
lean_dec(x_318);
x_431 = lean_nat_add(x_430, x_412);
lean_dec(x_430);
x_432 = lean_nat_add(x_429, x_419);
lean_dec(x_419);
x_433 = lean_nat_add(x_429, x_412);
lean_dec(x_412);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = lean_ctor_get(x_423, 0);
lean_inc(x_434);
x_435 = lean_nat_add(x_432, x_434);
lean_dec(x_434);
lean_dec(x_432);
lean_inc(x_321);
if (lean_is_scalar(x_428)) {
 x_436 = lean_alloc_ctor(0, 5, 0);
} else {
 x_436 = x_428;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_319);
lean_ctor_set(x_436, 2, x_320);
lean_ctor_set(x_436, 3, x_321);
lean_ctor_set(x_436, 4, x_423);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 x_437 = x_321;
} else {
 lean_dec_ref(x_321);
 x_437 = lean_box(0);
}
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_438 = lean_ctor_get(x_424, 0);
lean_inc(x_438);
x_439 = lean_nat_add(x_433, x_438);
lean_dec(x_438);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_437)) {
 x_440 = lean_alloc_ctor(0, 5, 0);
} else {
 x_440 = x_437;
}
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_408);
lean_ctor_set(x_440, 2, x_409);
lean_ctor_set(x_440, 3, x_424);
lean_ctor_set(x_440, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_441 = x_410;
} else {
 lean_dec_ref(x_410);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(0, 5, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_431);
lean_ctor_set(x_442, 1, x_421);
lean_ctor_set(x_442, 2, x_422);
lean_ctor_set(x_442, 3, x_436);
lean_ctor_set(x_442, 4, x_440);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_443 = lean_unsigned_to_nat(0u);
x_444 = lean_nat_add(x_433, x_443);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(0, 5, 0);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_408);
lean_ctor_set(x_445, 2, x_409);
lean_ctor_set(x_445, 3, x_424);
lean_ctor_set(x_445, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_446 = x_410;
} else {
 lean_dec_ref(x_410);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(0, 5, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_431);
lean_ctor_set(x_447, 1, x_421);
lean_ctor_set(x_447, 2, x_422);
lean_ctor_set(x_447, 3, x_436);
lean_ctor_set(x_447, 4, x_445);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_448 = lean_unsigned_to_nat(0u);
x_449 = lean_nat_add(x_432, x_448);
lean_dec(x_432);
lean_inc(x_321);
if (lean_is_scalar(x_428)) {
 x_450 = lean_alloc_ctor(0, 5, 0);
} else {
 x_450 = x_428;
}
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_319);
lean_ctor_set(x_450, 2, x_320);
lean_ctor_set(x_450, 3, x_321);
lean_ctor_set(x_450, 4, x_423);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 x_451 = x_321;
} else {
 lean_dec_ref(x_321);
 x_451 = lean_box(0);
}
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_452 = lean_ctor_get(x_424, 0);
lean_inc(x_452);
x_453 = lean_nat_add(x_433, x_452);
lean_dec(x_452);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_451)) {
 x_454 = lean_alloc_ctor(0, 5, 0);
} else {
 x_454 = x_451;
}
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_408);
lean_ctor_set(x_454, 2, x_409);
lean_ctor_set(x_454, 3, x_424);
lean_ctor_set(x_454, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_455 = x_410;
} else {
 lean_dec_ref(x_410);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(0, 5, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_431);
lean_ctor_set(x_456, 1, x_421);
lean_ctor_set(x_456, 2, x_422);
lean_ctor_set(x_456, 3, x_450);
lean_ctor_set(x_456, 4, x_454);
return x_456;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_457 = lean_nat_add(x_433, x_448);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_451)) {
 x_458 = lean_alloc_ctor(0, 5, 0);
} else {
 x_458 = x_451;
}
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_408);
lean_ctor_set(x_458, 2, x_409);
lean_ctor_set(x_458, 3, x_424);
lean_ctor_set(x_458, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_459 = x_410;
} else {
 lean_dec_ref(x_410);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(0, 5, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_431);
lean_ctor_set(x_460, 1, x_421);
lean_ctor_set(x_460, 2, x_422);
lean_ctor_set(x_460, 3, x_450);
lean_ctor_set(x_460, 4, x_458);
return x_460;
}
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_419);
x_461 = lean_unsigned_to_nat(1u);
x_462 = lean_nat_add(x_461, x_318);
lean_dec(x_318);
x_463 = lean_nat_add(x_462, x_412);
lean_dec(x_462);
x_464 = lean_nat_add(x_461, x_412);
lean_dec(x_412);
x_465 = lean_nat_add(x_464, x_420);
lean_dec(x_420);
lean_dec(x_464);
lean_ctor_set(x_10, 4, x_410);
lean_ctor_set(x_10, 3, x_322);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_465);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_463);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_321) == 0)
{
lean_dec(x_411);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_466 = lean_ctor_get(x_322, 0);
lean_inc(x_466);
x_467 = lean_unsigned_to_nat(1u);
x_468 = lean_nat_add(x_467, x_318);
lean_dec(x_318);
x_469 = lean_nat_add(x_467, x_466);
lean_dec(x_466);
x_470 = lean_box(1);
lean_ctor_set(x_10, 4, x_470);
lean_ctor_set(x_10, 3, x_322);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_469);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_468);
return x_4;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_318);
x_471 = lean_box(1);
x_472 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_10, 4, x_471);
lean_ctor_set(x_10, 3, x_471);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_472);
x_473 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_473);
return x_4;
}
}
else
{
lean_dec(x_318);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec(x_411);
x_474 = lean_ctor_get(x_322, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_322, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 lean_ctor_release(x_322, 4);
 x_476 = x_322;
} else {
 lean_dec_ref(x_322);
 x_476 = lean_box(0);
}
x_477 = lean_box(1);
x_478 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_476)) {
 x_479 = lean_alloc_ctor(0, 5, 0);
} else {
 x_479 = x_476;
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_319);
lean_ctor_set(x_479, 2, x_320);
lean_ctor_set(x_479, 3, x_477);
lean_ctor_set(x_479, 4, x_477);
lean_ctor_set(x_10, 4, x_477);
lean_ctor_set(x_10, 3, x_477);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_478);
x_480 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_479);
lean_ctor_set(x_4, 2, x_475);
lean_ctor_set(x_4, 1, x_474);
lean_ctor_set(x_4, 0, x_480);
return x_4;
}
else
{
lean_object* x_481; lean_object* x_482; 
lean_dec(x_320);
lean_dec(x_319);
lean_free_object(x_4);
x_481 = lean_box(1);
x_482 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_481);
lean_ctor_set(x_10, 3, x_411);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_482);
return x_10;
}
}
}
}
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; 
x_483 = lean_ctor_get(x_10, 0);
x_484 = lean_ctor_get(x_10, 1);
x_485 = lean_ctor_get(x_10, 2);
x_486 = lean_ctor_get(x_10, 3);
x_487 = lean_ctor_get(x_10, 4);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_10);
x_488 = lean_ctor_get(x_11, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_11, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_11, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_11, 3);
lean_inc(x_491);
x_492 = lean_ctor_get(x_11, 4);
lean_inc(x_492);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_493 = x_11;
} else {
 lean_dec_ref(x_11);
 x_493 = lean_box(0);
}
x_494 = lean_nat_dec_lt(x_483, x_488);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; 
lean_dec(x_483);
x_495 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_484, x_485, x_486, x_487, lean_box(0), lean_box(0), lean_box(0));
x_496 = lean_ctor_get(x_495, 2);
lean_inc(x_496);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_498);
lean_dec(x_495);
x_499 = lean_ctor_get(x_496, 0);
lean_inc(x_499);
lean_inc(x_492);
lean_inc(x_491);
lean_inc(x_490);
lean_inc(x_489);
lean_inc(x_488);
if (lean_is_scalar(x_493)) {
 x_500 = lean_alloc_ctor(0, 5, 0);
} else {
 x_500 = x_493;
}
lean_ctor_set(x_500, 0, x_488);
lean_ctor_set(x_500, 1, x_489);
lean_ctor_set(x_500, 2, x_490);
lean_ctor_set(x_500, 3, x_491);
lean_ctor_set(x_500, 4, x_492);
x_501 = lean_unsigned_to_nat(3u);
x_502 = lean_nat_mul(x_501, x_499);
x_503 = lean_nat_dec_lt(x_502, x_488);
lean_dec(x_502);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_492);
lean_dec(x_491);
lean_dec(x_490);
lean_dec(x_489);
lean_free_object(x_4);
x_504 = lean_unsigned_to_nat(1u);
x_505 = lean_nat_add(x_504, x_499);
lean_dec(x_499);
x_506 = lean_nat_add(x_505, x_488);
lean_dec(x_488);
lean_dec(x_505);
x_507 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_497);
lean_ctor_set(x_507, 2, x_498);
lean_ctor_set(x_507, 3, x_496);
lean_ctor_set(x_507, 4, x_500);
return x_507;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; 
lean_dec(x_500);
x_508 = lean_ctor_get(x_491, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_491, 1);
lean_inc(x_509);
x_510 = lean_ctor_get(x_491, 2);
lean_inc(x_510);
x_511 = lean_ctor_get(x_491, 3);
lean_inc(x_511);
x_512 = lean_ctor_get(x_491, 4);
lean_inc(x_512);
x_513 = lean_ctor_get(x_492, 0);
lean_inc(x_513);
x_514 = lean_unsigned_to_nat(2u);
x_515 = lean_nat_mul(x_514, x_513);
x_516 = lean_nat_dec_lt(x_508, x_515);
lean_dec(x_515);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_508);
lean_free_object(x_4);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 lean_ctor_release(x_491, 2);
 lean_ctor_release(x_491, 3);
 lean_ctor_release(x_491, 4);
 x_517 = x_491;
} else {
 lean_dec_ref(x_491);
 x_517 = lean_box(0);
}
x_518 = lean_unsigned_to_nat(1u);
x_519 = lean_nat_add(x_518, x_499);
lean_dec(x_499);
x_520 = lean_nat_add(x_519, x_488);
lean_dec(x_488);
x_521 = lean_nat_add(x_518, x_513);
lean_dec(x_513);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_522 = lean_ctor_get(x_511, 0);
lean_inc(x_522);
x_523 = lean_nat_add(x_519, x_522);
lean_dec(x_522);
lean_dec(x_519);
lean_inc(x_496);
if (lean_is_scalar(x_517)) {
 x_524 = lean_alloc_ctor(0, 5, 0);
} else {
 x_524 = x_517;
}
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_497);
lean_ctor_set(x_524, 2, x_498);
lean_ctor_set(x_524, 3, x_496);
lean_ctor_set(x_524, 4, x_511);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 lean_ctor_release(x_496, 2);
 lean_ctor_release(x_496, 3);
 lean_ctor_release(x_496, 4);
 x_525 = x_496;
} else {
 lean_dec_ref(x_496);
 x_525 = lean_box(0);
}
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_526 = lean_ctor_get(x_512, 0);
lean_inc(x_526);
x_527 = lean_nat_add(x_521, x_526);
lean_dec(x_526);
lean_dec(x_521);
if (lean_is_scalar(x_525)) {
 x_528 = lean_alloc_ctor(0, 5, 0);
} else {
 x_528 = x_525;
}
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_489);
lean_ctor_set(x_528, 2, x_490);
lean_ctor_set(x_528, 3, x_512);
lean_ctor_set(x_528, 4, x_492);
x_529 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_529, 0, x_520);
lean_ctor_set(x_529, 1, x_509);
lean_ctor_set(x_529, 2, x_510);
lean_ctor_set(x_529, 3, x_524);
lean_ctor_set(x_529, 4, x_528);
return x_529;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_530 = lean_unsigned_to_nat(0u);
x_531 = lean_nat_add(x_521, x_530);
lean_dec(x_521);
if (lean_is_scalar(x_525)) {
 x_532 = lean_alloc_ctor(0, 5, 0);
} else {
 x_532 = x_525;
}
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_489);
lean_ctor_set(x_532, 2, x_490);
lean_ctor_set(x_532, 3, x_512);
lean_ctor_set(x_532, 4, x_492);
x_533 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_533, 0, x_520);
lean_ctor_set(x_533, 1, x_509);
lean_ctor_set(x_533, 2, x_510);
lean_ctor_set(x_533, 3, x_524);
lean_ctor_set(x_533, 4, x_532);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_534 = lean_unsigned_to_nat(0u);
x_535 = lean_nat_add(x_519, x_534);
lean_dec(x_519);
lean_inc(x_496);
if (lean_is_scalar(x_517)) {
 x_536 = lean_alloc_ctor(0, 5, 0);
} else {
 x_536 = x_517;
}
lean_ctor_set(x_536, 0, x_535);
lean_ctor_set(x_536, 1, x_497);
lean_ctor_set(x_536, 2, x_498);
lean_ctor_set(x_536, 3, x_496);
lean_ctor_set(x_536, 4, x_511);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 lean_ctor_release(x_496, 2);
 lean_ctor_release(x_496, 3);
 lean_ctor_release(x_496, 4);
 x_537 = x_496;
} else {
 lean_dec_ref(x_496);
 x_537 = lean_box(0);
}
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_538 = lean_ctor_get(x_512, 0);
lean_inc(x_538);
x_539 = lean_nat_add(x_521, x_538);
lean_dec(x_538);
lean_dec(x_521);
if (lean_is_scalar(x_537)) {
 x_540 = lean_alloc_ctor(0, 5, 0);
} else {
 x_540 = x_537;
}
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_489);
lean_ctor_set(x_540, 2, x_490);
lean_ctor_set(x_540, 3, x_512);
lean_ctor_set(x_540, 4, x_492);
x_541 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_541, 0, x_520);
lean_ctor_set(x_541, 1, x_509);
lean_ctor_set(x_541, 2, x_510);
lean_ctor_set(x_541, 3, x_536);
lean_ctor_set(x_541, 4, x_540);
return x_541;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_nat_add(x_521, x_534);
lean_dec(x_521);
if (lean_is_scalar(x_537)) {
 x_543 = lean_alloc_ctor(0, 5, 0);
} else {
 x_543 = x_537;
}
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_489);
lean_ctor_set(x_543, 2, x_490);
lean_ctor_set(x_543, 3, x_512);
lean_ctor_set(x_543, 4, x_492);
x_544 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_544, 0, x_520);
lean_ctor_set(x_544, 1, x_509);
lean_ctor_set(x_544, 2, x_510);
lean_ctor_set(x_544, 3, x_536);
lean_ctor_set(x_544, 4, x_543);
return x_544;
}
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
x_545 = lean_unsigned_to_nat(1u);
x_546 = lean_nat_add(x_545, x_499);
lean_dec(x_499);
x_547 = lean_nat_add(x_546, x_488);
lean_dec(x_488);
x_548 = lean_nat_add(x_546, x_508);
lean_dec(x_508);
lean_dec(x_546);
x_549 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_497);
lean_ctor_set(x_549, 2, x_498);
lean_ctor_set(x_549, 3, x_496);
lean_ctor_set(x_549, 4, x_491);
lean_ctor_set(x_4, 4, x_492);
lean_ctor_set(x_4, 3, x_549);
lean_ctor_set(x_4, 2, x_490);
lean_ctor_set(x_4, 1, x_489);
lean_ctor_set(x_4, 0, x_547);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_491) == 0)
{
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_550 = lean_ctor_get(x_495, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_495, 1);
lean_inc(x_551);
lean_dec(x_495);
x_552 = lean_ctor_get(x_491, 0);
lean_inc(x_552);
x_553 = lean_unsigned_to_nat(1u);
x_554 = lean_nat_add(x_553, x_488);
lean_dec(x_488);
x_555 = lean_nat_add(x_553, x_552);
lean_dec(x_552);
x_556 = lean_box(1);
if (lean_is_scalar(x_493)) {
 x_557 = lean_alloc_ctor(0, 5, 0);
} else {
 x_557 = x_493;
}
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_550);
lean_ctor_set(x_557, 2, x_551);
lean_ctor_set(x_557, 3, x_556);
lean_ctor_set(x_557, 4, x_491);
x_558 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_558, 0, x_554);
lean_ctor_set(x_558, 1, x_489);
lean_ctor_set(x_558, 2, x_490);
lean_ctor_set(x_558, 3, x_557);
lean_ctor_set(x_558, 4, x_492);
return x_558;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_488);
x_559 = lean_ctor_get(x_495, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_495, 1);
lean_inc(x_560);
lean_dec(x_495);
x_561 = lean_ctor_get(x_491, 1);
lean_inc(x_561);
x_562 = lean_ctor_get(x_491, 2);
lean_inc(x_562);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 lean_ctor_release(x_491, 2);
 lean_ctor_release(x_491, 3);
 lean_ctor_release(x_491, 4);
 x_563 = x_491;
} else {
 lean_dec_ref(x_491);
 x_563 = lean_box(0);
}
x_564 = lean_box(1);
x_565 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_563)) {
 x_566 = lean_alloc_ctor(0, 5, 0);
} else {
 x_566 = x_563;
}
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_559);
lean_ctor_set(x_566, 2, x_560);
lean_ctor_set(x_566, 3, x_564);
lean_ctor_set(x_566, 4, x_564);
if (lean_is_scalar(x_493)) {
 x_567 = lean_alloc_ctor(0, 5, 0);
} else {
 x_567 = x_493;
}
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_489);
lean_ctor_set(x_567, 2, x_490);
lean_ctor_set(x_567, 3, x_564);
lean_ctor_set(x_567, 4, x_564);
x_568 = lean_unsigned_to_nat(3u);
x_569 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_561);
lean_ctor_set(x_569, 2, x_562);
lean_ctor_set(x_569, 3, x_566);
lean_ctor_set(x_569, 4, x_567);
return x_569;
}
}
else
{
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_488);
x_570 = lean_ctor_get(x_495, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_495, 1);
lean_inc(x_571);
lean_dec(x_495);
x_572 = lean_box(1);
x_573 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_493)) {
 x_574 = lean_alloc_ctor(0, 5, 0);
} else {
 x_574 = x_493;
}
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_570);
lean_ctor_set(x_574, 2, x_571);
lean_ctor_set(x_574, 3, x_572);
lean_ctor_set(x_574, 4, x_572);
x_575 = lean_unsigned_to_nat(3u);
x_576 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_489);
lean_ctor_set(x_576, 2, x_490);
lean_ctor_set(x_576, 3, x_574);
lean_ctor_set(x_576, 4, x_492);
return x_576;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_577 = lean_ctor_get(x_495, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_495, 1);
lean_inc(x_578);
lean_dec(x_495);
if (lean_is_scalar(x_493)) {
 x_579 = lean_alloc_ctor(0, 5, 0);
} else {
 x_579 = x_493;
}
lean_ctor_set(x_579, 0, x_488);
lean_ctor_set(x_579, 1, x_489);
lean_ctor_set(x_579, 2, x_490);
lean_ctor_set(x_579, 3, x_492);
lean_ctor_set(x_579, 4, x_492);
x_580 = lean_box(1);
x_581 = lean_unsigned_to_nat(2u);
x_582 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_577);
lean_ctor_set(x_582, 2, x_578);
lean_ctor_set(x_582, 3, x_580);
lean_ctor_set(x_582, 4, x_579);
return x_582;
}
}
}
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_488);
x_583 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_489, x_490, x_491, x_492, lean_box(0), lean_box(0), lean_box(0));
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
x_586 = lean_ctor_get(x_583, 2);
lean_inc(x_586);
lean_dec(x_583);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
if (lean_is_scalar(x_493)) {
 x_587 = lean_alloc_ctor(0, 5, 0);
} else {
 x_587 = x_493;
}
lean_ctor_set(x_587, 0, x_483);
lean_ctor_set(x_587, 1, x_484);
lean_ctor_set(x_587, 2, x_485);
lean_ctor_set(x_587, 3, x_486);
lean_ctor_set(x_587, 4, x_487);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; 
x_588 = lean_ctor_get(x_586, 0);
lean_inc(x_588);
x_589 = lean_unsigned_to_nat(3u);
x_590 = lean_nat_mul(x_589, x_588);
x_591 = lean_nat_dec_lt(x_590, x_483);
lean_dec(x_590);
if (x_591 == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_484);
lean_free_object(x_4);
x_592 = lean_unsigned_to_nat(1u);
x_593 = lean_nat_add(x_592, x_483);
lean_dec(x_483);
x_594 = lean_nat_add(x_593, x_588);
lean_dec(x_588);
lean_dec(x_593);
x_595 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_595, 0, x_594);
lean_ctor_set(x_595, 1, x_584);
lean_ctor_set(x_595, 2, x_585);
lean_ctor_set(x_595, 3, x_587);
lean_ctor_set(x_595, 4, x_586);
return x_595;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
lean_dec(x_587);
x_596 = lean_ctor_get(x_486, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_487, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_487, 1);
lean_inc(x_598);
x_599 = lean_ctor_get(x_487, 2);
lean_inc(x_599);
x_600 = lean_ctor_get(x_487, 3);
lean_inc(x_600);
x_601 = lean_ctor_get(x_487, 4);
lean_inc(x_601);
x_602 = lean_unsigned_to_nat(2u);
x_603 = lean_nat_mul(x_602, x_596);
x_604 = lean_nat_dec_lt(x_597, x_603);
lean_dec(x_603);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_597);
lean_free_object(x_4);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 lean_ctor_release(x_487, 4);
 x_605 = x_487;
} else {
 lean_dec_ref(x_487);
 x_605 = lean_box(0);
}
x_606 = lean_unsigned_to_nat(1u);
x_607 = lean_nat_add(x_606, x_483);
lean_dec(x_483);
x_608 = lean_nat_add(x_607, x_588);
lean_dec(x_607);
x_609 = lean_nat_add(x_606, x_596);
lean_dec(x_596);
x_610 = lean_nat_add(x_606, x_588);
lean_dec(x_588);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_611 = lean_ctor_get(x_600, 0);
lean_inc(x_611);
x_612 = lean_nat_add(x_609, x_611);
lean_dec(x_611);
lean_dec(x_609);
lean_inc(x_486);
if (lean_is_scalar(x_605)) {
 x_613 = lean_alloc_ctor(0, 5, 0);
} else {
 x_613 = x_605;
}
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_484);
lean_ctor_set(x_613, 2, x_485);
lean_ctor_set(x_613, 3, x_486);
lean_ctor_set(x_613, 4, x_600);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 lean_ctor_release(x_486, 2);
 lean_ctor_release(x_486, 3);
 lean_ctor_release(x_486, 4);
 x_614 = x_486;
} else {
 lean_dec_ref(x_486);
 x_614 = lean_box(0);
}
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_615 = lean_ctor_get(x_601, 0);
lean_inc(x_615);
x_616 = lean_nat_add(x_610, x_615);
lean_dec(x_615);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_614)) {
 x_617 = lean_alloc_ctor(0, 5, 0);
} else {
 x_617 = x_614;
}
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_584);
lean_ctor_set(x_617, 2, x_585);
lean_ctor_set(x_617, 3, x_601);
lean_ctor_set(x_617, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_618 = x_586;
} else {
 lean_dec_ref(x_586);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(0, 5, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_608);
lean_ctor_set(x_619, 1, x_598);
lean_ctor_set(x_619, 2, x_599);
lean_ctor_set(x_619, 3, x_613);
lean_ctor_set(x_619, 4, x_617);
return x_619;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_620 = lean_unsigned_to_nat(0u);
x_621 = lean_nat_add(x_610, x_620);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_614)) {
 x_622 = lean_alloc_ctor(0, 5, 0);
} else {
 x_622 = x_614;
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_584);
lean_ctor_set(x_622, 2, x_585);
lean_ctor_set(x_622, 3, x_601);
lean_ctor_set(x_622, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_623 = x_586;
} else {
 lean_dec_ref(x_586);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(0, 5, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_608);
lean_ctor_set(x_624, 1, x_598);
lean_ctor_set(x_624, 2, x_599);
lean_ctor_set(x_624, 3, x_613);
lean_ctor_set(x_624, 4, x_622);
return x_624;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_625 = lean_unsigned_to_nat(0u);
x_626 = lean_nat_add(x_609, x_625);
lean_dec(x_609);
lean_inc(x_486);
if (lean_is_scalar(x_605)) {
 x_627 = lean_alloc_ctor(0, 5, 0);
} else {
 x_627 = x_605;
}
lean_ctor_set(x_627, 0, x_626);
lean_ctor_set(x_627, 1, x_484);
lean_ctor_set(x_627, 2, x_485);
lean_ctor_set(x_627, 3, x_486);
lean_ctor_set(x_627, 4, x_600);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 lean_ctor_release(x_486, 2);
 lean_ctor_release(x_486, 3);
 lean_ctor_release(x_486, 4);
 x_628 = x_486;
} else {
 lean_dec_ref(x_486);
 x_628 = lean_box(0);
}
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_629 = lean_ctor_get(x_601, 0);
lean_inc(x_629);
x_630 = lean_nat_add(x_610, x_629);
lean_dec(x_629);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_628)) {
 x_631 = lean_alloc_ctor(0, 5, 0);
} else {
 x_631 = x_628;
}
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_584);
lean_ctor_set(x_631, 2, x_585);
lean_ctor_set(x_631, 3, x_601);
lean_ctor_set(x_631, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_632 = x_586;
} else {
 lean_dec_ref(x_586);
 x_632 = lean_box(0);
}
if (lean_is_scalar(x_632)) {
 x_633 = lean_alloc_ctor(0, 5, 0);
} else {
 x_633 = x_632;
}
lean_ctor_set(x_633, 0, x_608);
lean_ctor_set(x_633, 1, x_598);
lean_ctor_set(x_633, 2, x_599);
lean_ctor_set(x_633, 3, x_627);
lean_ctor_set(x_633, 4, x_631);
return x_633;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_634 = lean_nat_add(x_610, x_625);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_628)) {
 x_635 = lean_alloc_ctor(0, 5, 0);
} else {
 x_635 = x_628;
}
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_584);
lean_ctor_set(x_635, 2, x_585);
lean_ctor_set(x_635, 3, x_601);
lean_ctor_set(x_635, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_636 = x_586;
} else {
 lean_dec_ref(x_586);
 x_636 = lean_box(0);
}
if (lean_is_scalar(x_636)) {
 x_637 = lean_alloc_ctor(0, 5, 0);
} else {
 x_637 = x_636;
}
lean_ctor_set(x_637, 0, x_608);
lean_ctor_set(x_637, 1, x_598);
lean_ctor_set(x_637, 2, x_599);
lean_ctor_set(x_637, 3, x_627);
lean_ctor_set(x_637, 4, x_635);
return x_637;
}
}
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_596);
x_638 = lean_unsigned_to_nat(1u);
x_639 = lean_nat_add(x_638, x_483);
lean_dec(x_483);
x_640 = lean_nat_add(x_639, x_588);
lean_dec(x_639);
x_641 = lean_nat_add(x_638, x_588);
lean_dec(x_588);
x_642 = lean_nat_add(x_641, x_597);
lean_dec(x_597);
lean_dec(x_641);
x_643 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_584);
lean_ctor_set(x_643, 2, x_585);
lean_ctor_set(x_643, 3, x_487);
lean_ctor_set(x_643, 4, x_586);
lean_ctor_set(x_4, 4, x_643);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_640);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_486) == 0)
{
lean_dec(x_587);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_644 = lean_ctor_get(x_487, 0);
lean_inc(x_644);
x_645 = lean_unsigned_to_nat(1u);
x_646 = lean_nat_add(x_645, x_483);
lean_dec(x_483);
x_647 = lean_nat_add(x_645, x_644);
lean_dec(x_644);
x_648 = lean_box(1);
x_649 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_649, 0, x_647);
lean_ctor_set(x_649, 1, x_584);
lean_ctor_set(x_649, 2, x_585);
lean_ctor_set(x_649, 3, x_487);
lean_ctor_set(x_649, 4, x_648);
lean_ctor_set(x_4, 4, x_649);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_646);
return x_4;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_483);
x_650 = lean_box(1);
x_651 = lean_unsigned_to_nat(1u);
x_652 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_584);
lean_ctor_set(x_652, 2, x_585);
lean_ctor_set(x_652, 3, x_650);
lean_ctor_set(x_652, 4, x_650);
x_653 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_652);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_653);
return x_4;
}
}
else
{
lean_dec(x_483);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_587);
x_654 = lean_ctor_get(x_487, 1);
lean_inc(x_654);
x_655 = lean_ctor_get(x_487, 2);
lean_inc(x_655);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 lean_ctor_release(x_487, 4);
 x_656 = x_487;
} else {
 lean_dec_ref(x_487);
 x_656 = lean_box(0);
}
x_657 = lean_box(1);
x_658 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_656)) {
 x_659 = lean_alloc_ctor(0, 5, 0);
} else {
 x_659 = x_656;
}
lean_ctor_set(x_659, 0, x_658);
lean_ctor_set(x_659, 1, x_484);
lean_ctor_set(x_659, 2, x_485);
lean_ctor_set(x_659, 3, x_657);
lean_ctor_set(x_659, 4, x_657);
x_660 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_584);
lean_ctor_set(x_660, 2, x_585);
lean_ctor_set(x_660, 3, x_657);
lean_ctor_set(x_660, 4, x_657);
x_661 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_660);
lean_ctor_set(x_4, 3, x_659);
lean_ctor_set(x_4, 2, x_655);
lean_ctor_set(x_4, 1, x_654);
lean_ctor_set(x_4, 0, x_661);
return x_4;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_485);
lean_dec(x_484);
lean_free_object(x_4);
x_662 = lean_box(1);
x_663 = lean_unsigned_to_nat(2u);
x_664 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_584);
lean_ctor_set(x_664, 2, x_585);
lean_ctor_set(x_664, 3, x_587);
lean_ctor_set(x_664, 4, x_662);
return x_664;
}
}
}
}
}
}
else
{
lean_free_object(x_4);
return x_10;
}
}
else
{
lean_free_object(x_4);
return x_11;
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_17, 0);
lean_inc(x_665);
lean_dec(x_17);
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
lean_dec(x_665);
lean_ctor_set(x_4, 2, x_667);
lean_ctor_set(x_4, 1, x_666);
return x_4;
}
}
default: 
{
lean_object* x_668; lean_object* x_669; 
lean_free_object(x_4);
lean_dec(x_7);
x_668 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___spec__1___rarg(x_1, x_2, x_3, x_11, lean_box(0));
x_669 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_8, x_9, x_10, x_668, lean_box(0), lean_box(0), lean_box(0));
return x_669;
}
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; 
x_670 = lean_ctor_get(x_4, 0);
x_671 = lean_ctor_get(x_4, 1);
x_672 = lean_ctor_get(x_4, 2);
x_673 = lean_ctor_get(x_4, 3);
x_674 = lean_ctor_get(x_4, 4);
lean_inc(x_674);
lean_inc(x_673);
lean_inc(x_672);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_671);
lean_inc(x_2);
x_675 = lean_apply_2(x_1, x_2, x_671);
x_676 = lean_unbox(x_675);
lean_dec(x_675);
switch (x_676) {
case 0:
{
lean_object* x_677; lean_object* x_678; 
lean_dec(x_670);
x_677 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___spec__1___rarg(x_1, x_2, x_3, x_673, lean_box(0));
x_678 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_671, x_672, x_677, x_674, lean_box(0), lean_box(0), lean_box(0));
return x_678;
}
case 1:
{
lean_object* x_679; lean_object* x_680; 
lean_dec(x_2);
lean_dec(x_1);
x_679 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_671, x_672, lean_box(0));
x_680 = lean_apply_1(x_3, x_679);
if (lean_obj_tag(x_680) == 0)
{
lean_dec(x_670);
if (lean_obj_tag(x_673) == 0)
{
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; uint8_t x_693; 
x_681 = lean_ctor_get(x_673, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_673, 1);
lean_inc(x_682);
x_683 = lean_ctor_get(x_673, 2);
lean_inc(x_683);
x_684 = lean_ctor_get(x_673, 3);
lean_inc(x_684);
x_685 = lean_ctor_get(x_673, 4);
lean_inc(x_685);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 lean_ctor_release(x_673, 2);
 lean_ctor_release(x_673, 3);
 lean_ctor_release(x_673, 4);
 x_686 = x_673;
} else {
 lean_dec_ref(x_673);
 x_686 = lean_box(0);
}
x_687 = lean_ctor_get(x_674, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_674, 1);
lean_inc(x_688);
x_689 = lean_ctor_get(x_674, 2);
lean_inc(x_689);
x_690 = lean_ctor_get(x_674, 3);
lean_inc(x_690);
x_691 = lean_ctor_get(x_674, 4);
lean_inc(x_691);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 lean_ctor_release(x_674, 4);
 x_692 = x_674;
} else {
 lean_dec_ref(x_674);
 x_692 = lean_box(0);
}
x_693 = lean_nat_dec_lt(x_681, x_687);
if (x_693 == 0)
{
lean_object* x_694; lean_object* x_695; 
lean_dec(x_681);
x_694 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_682, x_683, x_684, x_685, lean_box(0), lean_box(0), lean_box(0));
x_695 = lean_ctor_get(x_694, 2);
lean_inc(x_695);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; 
x_696 = lean_ctor_get(x_694, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_694, 1);
lean_inc(x_697);
lean_dec(x_694);
x_698 = lean_ctor_get(x_695, 0);
lean_inc(x_698);
lean_inc(x_691);
lean_inc(x_690);
lean_inc(x_689);
lean_inc(x_688);
lean_inc(x_687);
if (lean_is_scalar(x_692)) {
 x_699 = lean_alloc_ctor(0, 5, 0);
} else {
 x_699 = x_692;
}
lean_ctor_set(x_699, 0, x_687);
lean_ctor_set(x_699, 1, x_688);
lean_ctor_set(x_699, 2, x_689);
lean_ctor_set(x_699, 3, x_690);
lean_ctor_set(x_699, 4, x_691);
x_700 = lean_unsigned_to_nat(3u);
x_701 = lean_nat_mul(x_700, x_698);
x_702 = lean_nat_dec_lt(x_701, x_687);
lean_dec(x_701);
if (x_702 == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_dec(x_691);
lean_dec(x_690);
lean_dec(x_689);
lean_dec(x_688);
x_703 = lean_unsigned_to_nat(1u);
x_704 = lean_nat_add(x_703, x_698);
lean_dec(x_698);
x_705 = lean_nat_add(x_704, x_687);
lean_dec(x_687);
lean_dec(x_704);
if (lean_is_scalar(x_686)) {
 x_706 = lean_alloc_ctor(0, 5, 0);
} else {
 x_706 = x_686;
}
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_696);
lean_ctor_set(x_706, 2, x_697);
lean_ctor_set(x_706, 3, x_695);
lean_ctor_set(x_706, 4, x_699);
return x_706;
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; 
lean_dec(x_699);
x_707 = lean_ctor_get(x_690, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_690, 1);
lean_inc(x_708);
x_709 = lean_ctor_get(x_690, 2);
lean_inc(x_709);
x_710 = lean_ctor_get(x_690, 3);
lean_inc(x_710);
x_711 = lean_ctor_get(x_690, 4);
lean_inc(x_711);
x_712 = lean_ctor_get(x_691, 0);
lean_inc(x_712);
x_713 = lean_unsigned_to_nat(2u);
x_714 = lean_nat_mul(x_713, x_712);
x_715 = lean_nat_dec_lt(x_707, x_714);
lean_dec(x_714);
if (x_715 == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_707);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 lean_ctor_release(x_690, 2);
 lean_ctor_release(x_690, 3);
 lean_ctor_release(x_690, 4);
 x_716 = x_690;
} else {
 lean_dec_ref(x_690);
 x_716 = lean_box(0);
}
x_717 = lean_unsigned_to_nat(1u);
x_718 = lean_nat_add(x_717, x_698);
lean_dec(x_698);
x_719 = lean_nat_add(x_718, x_687);
lean_dec(x_687);
x_720 = lean_nat_add(x_717, x_712);
lean_dec(x_712);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_721 = lean_ctor_get(x_710, 0);
lean_inc(x_721);
x_722 = lean_nat_add(x_718, x_721);
lean_dec(x_721);
lean_dec(x_718);
lean_inc(x_695);
if (lean_is_scalar(x_716)) {
 x_723 = lean_alloc_ctor(0, 5, 0);
} else {
 x_723 = x_716;
}
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_696);
lean_ctor_set(x_723, 2, x_697);
lean_ctor_set(x_723, 3, x_695);
lean_ctor_set(x_723, 4, x_710);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 lean_ctor_release(x_695, 2);
 lean_ctor_release(x_695, 3);
 lean_ctor_release(x_695, 4);
 x_724 = x_695;
} else {
 lean_dec_ref(x_695);
 x_724 = lean_box(0);
}
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_725 = lean_ctor_get(x_711, 0);
lean_inc(x_725);
x_726 = lean_nat_add(x_720, x_725);
lean_dec(x_725);
lean_dec(x_720);
if (lean_is_scalar(x_724)) {
 x_727 = lean_alloc_ctor(0, 5, 0);
} else {
 x_727 = x_724;
}
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_688);
lean_ctor_set(x_727, 2, x_689);
lean_ctor_set(x_727, 3, x_711);
lean_ctor_set(x_727, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_728 = lean_alloc_ctor(0, 5, 0);
} else {
 x_728 = x_686;
}
lean_ctor_set(x_728, 0, x_719);
lean_ctor_set(x_728, 1, x_708);
lean_ctor_set(x_728, 2, x_709);
lean_ctor_set(x_728, 3, x_723);
lean_ctor_set(x_728, 4, x_727);
return x_728;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_729 = lean_unsigned_to_nat(0u);
x_730 = lean_nat_add(x_720, x_729);
lean_dec(x_720);
if (lean_is_scalar(x_724)) {
 x_731 = lean_alloc_ctor(0, 5, 0);
} else {
 x_731 = x_724;
}
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_688);
lean_ctor_set(x_731, 2, x_689);
lean_ctor_set(x_731, 3, x_711);
lean_ctor_set(x_731, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_732 = lean_alloc_ctor(0, 5, 0);
} else {
 x_732 = x_686;
}
lean_ctor_set(x_732, 0, x_719);
lean_ctor_set(x_732, 1, x_708);
lean_ctor_set(x_732, 2, x_709);
lean_ctor_set(x_732, 3, x_723);
lean_ctor_set(x_732, 4, x_731);
return x_732;
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_733 = lean_unsigned_to_nat(0u);
x_734 = lean_nat_add(x_718, x_733);
lean_dec(x_718);
lean_inc(x_695);
if (lean_is_scalar(x_716)) {
 x_735 = lean_alloc_ctor(0, 5, 0);
} else {
 x_735 = x_716;
}
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_696);
lean_ctor_set(x_735, 2, x_697);
lean_ctor_set(x_735, 3, x_695);
lean_ctor_set(x_735, 4, x_710);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 lean_ctor_release(x_695, 2);
 lean_ctor_release(x_695, 3);
 lean_ctor_release(x_695, 4);
 x_736 = x_695;
} else {
 lean_dec_ref(x_695);
 x_736 = lean_box(0);
}
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_737 = lean_ctor_get(x_711, 0);
lean_inc(x_737);
x_738 = lean_nat_add(x_720, x_737);
lean_dec(x_737);
lean_dec(x_720);
if (lean_is_scalar(x_736)) {
 x_739 = lean_alloc_ctor(0, 5, 0);
} else {
 x_739 = x_736;
}
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_688);
lean_ctor_set(x_739, 2, x_689);
lean_ctor_set(x_739, 3, x_711);
lean_ctor_set(x_739, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_740 = lean_alloc_ctor(0, 5, 0);
} else {
 x_740 = x_686;
}
lean_ctor_set(x_740, 0, x_719);
lean_ctor_set(x_740, 1, x_708);
lean_ctor_set(x_740, 2, x_709);
lean_ctor_set(x_740, 3, x_735);
lean_ctor_set(x_740, 4, x_739);
return x_740;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_741 = lean_nat_add(x_720, x_733);
lean_dec(x_720);
if (lean_is_scalar(x_736)) {
 x_742 = lean_alloc_ctor(0, 5, 0);
} else {
 x_742 = x_736;
}
lean_ctor_set(x_742, 0, x_741);
lean_ctor_set(x_742, 1, x_688);
lean_ctor_set(x_742, 2, x_689);
lean_ctor_set(x_742, 3, x_711);
lean_ctor_set(x_742, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_743 = lean_alloc_ctor(0, 5, 0);
} else {
 x_743 = x_686;
}
lean_ctor_set(x_743, 0, x_719);
lean_ctor_set(x_743, 1, x_708);
lean_ctor_set(x_743, 2, x_709);
lean_ctor_set(x_743, 3, x_735);
lean_ctor_set(x_743, 4, x_742);
return x_743;
}
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_dec(x_712);
lean_dec(x_711);
lean_dec(x_710);
lean_dec(x_709);
lean_dec(x_708);
x_744 = lean_unsigned_to_nat(1u);
x_745 = lean_nat_add(x_744, x_698);
lean_dec(x_698);
x_746 = lean_nat_add(x_745, x_687);
lean_dec(x_687);
x_747 = lean_nat_add(x_745, x_707);
lean_dec(x_707);
lean_dec(x_745);
if (lean_is_scalar(x_686)) {
 x_748 = lean_alloc_ctor(0, 5, 0);
} else {
 x_748 = x_686;
}
lean_ctor_set(x_748, 0, x_747);
lean_ctor_set(x_748, 1, x_696);
lean_ctor_set(x_748, 2, x_697);
lean_ctor_set(x_748, 3, x_695);
lean_ctor_set(x_748, 4, x_690);
x_749 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_749, 0, x_746);
lean_ctor_set(x_749, 1, x_688);
lean_ctor_set(x_749, 2, x_689);
lean_ctor_set(x_749, 3, x_748);
lean_ctor_set(x_749, 4, x_691);
return x_749;
}
}
}
else
{
if (lean_obj_tag(x_690) == 0)
{
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_750 = lean_ctor_get(x_694, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_694, 1);
lean_inc(x_751);
lean_dec(x_694);
x_752 = lean_ctor_get(x_690, 0);
lean_inc(x_752);
x_753 = lean_unsigned_to_nat(1u);
x_754 = lean_nat_add(x_753, x_687);
lean_dec(x_687);
x_755 = lean_nat_add(x_753, x_752);
lean_dec(x_752);
x_756 = lean_box(1);
if (lean_is_scalar(x_692)) {
 x_757 = lean_alloc_ctor(0, 5, 0);
} else {
 x_757 = x_692;
}
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set(x_757, 1, x_750);
lean_ctor_set(x_757, 2, x_751);
lean_ctor_set(x_757, 3, x_756);
lean_ctor_set(x_757, 4, x_690);
if (lean_is_scalar(x_686)) {
 x_758 = lean_alloc_ctor(0, 5, 0);
} else {
 x_758 = x_686;
}
lean_ctor_set(x_758, 0, x_754);
lean_ctor_set(x_758, 1, x_688);
lean_ctor_set(x_758, 2, x_689);
lean_ctor_set(x_758, 3, x_757);
lean_ctor_set(x_758, 4, x_691);
return x_758;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_687);
x_759 = lean_ctor_get(x_694, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_694, 1);
lean_inc(x_760);
lean_dec(x_694);
x_761 = lean_ctor_get(x_690, 1);
lean_inc(x_761);
x_762 = lean_ctor_get(x_690, 2);
lean_inc(x_762);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 lean_ctor_release(x_690, 2);
 lean_ctor_release(x_690, 3);
 lean_ctor_release(x_690, 4);
 x_763 = x_690;
} else {
 lean_dec_ref(x_690);
 x_763 = lean_box(0);
}
x_764 = lean_box(1);
x_765 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_763)) {
 x_766 = lean_alloc_ctor(0, 5, 0);
} else {
 x_766 = x_763;
}
lean_ctor_set(x_766, 0, x_765);
lean_ctor_set(x_766, 1, x_759);
lean_ctor_set(x_766, 2, x_760);
lean_ctor_set(x_766, 3, x_764);
lean_ctor_set(x_766, 4, x_764);
if (lean_is_scalar(x_692)) {
 x_767 = lean_alloc_ctor(0, 5, 0);
} else {
 x_767 = x_692;
}
lean_ctor_set(x_767, 0, x_765);
lean_ctor_set(x_767, 1, x_688);
lean_ctor_set(x_767, 2, x_689);
lean_ctor_set(x_767, 3, x_764);
lean_ctor_set(x_767, 4, x_764);
x_768 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_686)) {
 x_769 = lean_alloc_ctor(0, 5, 0);
} else {
 x_769 = x_686;
}
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_761);
lean_ctor_set(x_769, 2, x_762);
lean_ctor_set(x_769, 3, x_766);
lean_ctor_set(x_769, 4, x_767);
return x_769;
}
}
else
{
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
lean_dec(x_687);
x_770 = lean_ctor_get(x_694, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_694, 1);
lean_inc(x_771);
lean_dec(x_694);
x_772 = lean_box(1);
x_773 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_692)) {
 x_774 = lean_alloc_ctor(0, 5, 0);
} else {
 x_774 = x_692;
}
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_770);
lean_ctor_set(x_774, 2, x_771);
lean_ctor_set(x_774, 3, x_772);
lean_ctor_set(x_774, 4, x_772);
x_775 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_686)) {
 x_776 = lean_alloc_ctor(0, 5, 0);
} else {
 x_776 = x_686;
}
lean_ctor_set(x_776, 0, x_775);
lean_ctor_set(x_776, 1, x_688);
lean_ctor_set(x_776, 2, x_689);
lean_ctor_set(x_776, 3, x_774);
lean_ctor_set(x_776, 4, x_691);
return x_776;
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_777 = lean_ctor_get(x_694, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_694, 1);
lean_inc(x_778);
lean_dec(x_694);
if (lean_is_scalar(x_692)) {
 x_779 = lean_alloc_ctor(0, 5, 0);
} else {
 x_779 = x_692;
}
lean_ctor_set(x_779, 0, x_687);
lean_ctor_set(x_779, 1, x_688);
lean_ctor_set(x_779, 2, x_689);
lean_ctor_set(x_779, 3, x_691);
lean_ctor_set(x_779, 4, x_691);
x_780 = lean_box(1);
x_781 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_686)) {
 x_782 = lean_alloc_ctor(0, 5, 0);
} else {
 x_782 = x_686;
}
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_777);
lean_ctor_set(x_782, 2, x_778);
lean_ctor_set(x_782, 3, x_780);
lean_ctor_set(x_782, 4, x_779);
return x_782;
}
}
}
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
lean_dec(x_687);
x_783 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_688, x_689, x_690, x_691, lean_box(0), lean_box(0), lean_box(0));
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
x_786 = lean_ctor_get(x_783, 2);
lean_inc(x_786);
lean_dec(x_783);
lean_inc(x_685);
lean_inc(x_684);
lean_inc(x_683);
lean_inc(x_682);
lean_inc(x_681);
if (lean_is_scalar(x_692)) {
 x_787 = lean_alloc_ctor(0, 5, 0);
} else {
 x_787 = x_692;
}
lean_ctor_set(x_787, 0, x_681);
lean_ctor_set(x_787, 1, x_682);
lean_ctor_set(x_787, 2, x_683);
lean_ctor_set(x_787, 3, x_684);
lean_ctor_set(x_787, 4, x_685);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; 
x_788 = lean_ctor_get(x_786, 0);
lean_inc(x_788);
x_789 = lean_unsigned_to_nat(3u);
x_790 = lean_nat_mul(x_789, x_788);
x_791 = lean_nat_dec_lt(x_790, x_681);
lean_dec(x_790);
if (x_791 == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_683);
lean_dec(x_682);
x_792 = lean_unsigned_to_nat(1u);
x_793 = lean_nat_add(x_792, x_681);
lean_dec(x_681);
x_794 = lean_nat_add(x_793, x_788);
lean_dec(x_788);
lean_dec(x_793);
if (lean_is_scalar(x_686)) {
 x_795 = lean_alloc_ctor(0, 5, 0);
} else {
 x_795 = x_686;
}
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_784);
lean_ctor_set(x_795, 2, x_785);
lean_ctor_set(x_795, 3, x_787);
lean_ctor_set(x_795, 4, x_786);
return x_795;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; uint8_t x_804; 
lean_dec(x_787);
x_796 = lean_ctor_get(x_684, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_685, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_685, 1);
lean_inc(x_798);
x_799 = lean_ctor_get(x_685, 2);
lean_inc(x_799);
x_800 = lean_ctor_get(x_685, 3);
lean_inc(x_800);
x_801 = lean_ctor_get(x_685, 4);
lean_inc(x_801);
x_802 = lean_unsigned_to_nat(2u);
x_803 = lean_nat_mul(x_802, x_796);
x_804 = lean_nat_dec_lt(x_797, x_803);
lean_dec(x_803);
if (x_804 == 0)
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_797);
lean_dec(x_686);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 lean_ctor_release(x_685, 2);
 lean_ctor_release(x_685, 3);
 lean_ctor_release(x_685, 4);
 x_805 = x_685;
} else {
 lean_dec_ref(x_685);
 x_805 = lean_box(0);
}
x_806 = lean_unsigned_to_nat(1u);
x_807 = lean_nat_add(x_806, x_681);
lean_dec(x_681);
x_808 = lean_nat_add(x_807, x_788);
lean_dec(x_807);
x_809 = lean_nat_add(x_806, x_796);
lean_dec(x_796);
x_810 = lean_nat_add(x_806, x_788);
lean_dec(x_788);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_811 = lean_ctor_get(x_800, 0);
lean_inc(x_811);
x_812 = lean_nat_add(x_809, x_811);
lean_dec(x_811);
lean_dec(x_809);
lean_inc(x_684);
if (lean_is_scalar(x_805)) {
 x_813 = lean_alloc_ctor(0, 5, 0);
} else {
 x_813 = x_805;
}
lean_ctor_set(x_813, 0, x_812);
lean_ctor_set(x_813, 1, x_682);
lean_ctor_set(x_813, 2, x_683);
lean_ctor_set(x_813, 3, x_684);
lean_ctor_set(x_813, 4, x_800);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 lean_ctor_release(x_684, 2);
 lean_ctor_release(x_684, 3);
 lean_ctor_release(x_684, 4);
 x_814 = x_684;
} else {
 lean_dec_ref(x_684);
 x_814 = lean_box(0);
}
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_815 = lean_ctor_get(x_801, 0);
lean_inc(x_815);
x_816 = lean_nat_add(x_810, x_815);
lean_dec(x_815);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_814)) {
 x_817 = lean_alloc_ctor(0, 5, 0);
} else {
 x_817 = x_814;
}
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_784);
lean_ctor_set(x_817, 2, x_785);
lean_ctor_set(x_817, 3, x_801);
lean_ctor_set(x_817, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_818 = x_786;
} else {
 lean_dec_ref(x_786);
 x_818 = lean_box(0);
}
if (lean_is_scalar(x_818)) {
 x_819 = lean_alloc_ctor(0, 5, 0);
} else {
 x_819 = x_818;
}
lean_ctor_set(x_819, 0, x_808);
lean_ctor_set(x_819, 1, x_798);
lean_ctor_set(x_819, 2, x_799);
lean_ctor_set(x_819, 3, x_813);
lean_ctor_set(x_819, 4, x_817);
return x_819;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_820 = lean_unsigned_to_nat(0u);
x_821 = lean_nat_add(x_810, x_820);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_814)) {
 x_822 = lean_alloc_ctor(0, 5, 0);
} else {
 x_822 = x_814;
}
lean_ctor_set(x_822, 0, x_821);
lean_ctor_set(x_822, 1, x_784);
lean_ctor_set(x_822, 2, x_785);
lean_ctor_set(x_822, 3, x_801);
lean_ctor_set(x_822, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_823 = x_786;
} else {
 lean_dec_ref(x_786);
 x_823 = lean_box(0);
}
if (lean_is_scalar(x_823)) {
 x_824 = lean_alloc_ctor(0, 5, 0);
} else {
 x_824 = x_823;
}
lean_ctor_set(x_824, 0, x_808);
lean_ctor_set(x_824, 1, x_798);
lean_ctor_set(x_824, 2, x_799);
lean_ctor_set(x_824, 3, x_813);
lean_ctor_set(x_824, 4, x_822);
return x_824;
}
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_825 = lean_unsigned_to_nat(0u);
x_826 = lean_nat_add(x_809, x_825);
lean_dec(x_809);
lean_inc(x_684);
if (lean_is_scalar(x_805)) {
 x_827 = lean_alloc_ctor(0, 5, 0);
} else {
 x_827 = x_805;
}
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_682);
lean_ctor_set(x_827, 2, x_683);
lean_ctor_set(x_827, 3, x_684);
lean_ctor_set(x_827, 4, x_800);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 lean_ctor_release(x_684, 2);
 lean_ctor_release(x_684, 3);
 lean_ctor_release(x_684, 4);
 x_828 = x_684;
} else {
 lean_dec_ref(x_684);
 x_828 = lean_box(0);
}
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_829 = lean_ctor_get(x_801, 0);
lean_inc(x_829);
x_830 = lean_nat_add(x_810, x_829);
lean_dec(x_829);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_828)) {
 x_831 = lean_alloc_ctor(0, 5, 0);
} else {
 x_831 = x_828;
}
lean_ctor_set(x_831, 0, x_830);
lean_ctor_set(x_831, 1, x_784);
lean_ctor_set(x_831, 2, x_785);
lean_ctor_set(x_831, 3, x_801);
lean_ctor_set(x_831, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_832 = x_786;
} else {
 lean_dec_ref(x_786);
 x_832 = lean_box(0);
}
if (lean_is_scalar(x_832)) {
 x_833 = lean_alloc_ctor(0, 5, 0);
} else {
 x_833 = x_832;
}
lean_ctor_set(x_833, 0, x_808);
lean_ctor_set(x_833, 1, x_798);
lean_ctor_set(x_833, 2, x_799);
lean_ctor_set(x_833, 3, x_827);
lean_ctor_set(x_833, 4, x_831);
return x_833;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_834 = lean_nat_add(x_810, x_825);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_828)) {
 x_835 = lean_alloc_ctor(0, 5, 0);
} else {
 x_835 = x_828;
}
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_784);
lean_ctor_set(x_835, 2, x_785);
lean_ctor_set(x_835, 3, x_801);
lean_ctor_set(x_835, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_836 = x_786;
} else {
 lean_dec_ref(x_786);
 x_836 = lean_box(0);
}
if (lean_is_scalar(x_836)) {
 x_837 = lean_alloc_ctor(0, 5, 0);
} else {
 x_837 = x_836;
}
lean_ctor_set(x_837, 0, x_808);
lean_ctor_set(x_837, 1, x_798);
lean_ctor_set(x_837, 2, x_799);
lean_ctor_set(x_837, 3, x_827);
lean_ctor_set(x_837, 4, x_835);
return x_837;
}
}
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
lean_dec(x_801);
lean_dec(x_800);
lean_dec(x_799);
lean_dec(x_798);
lean_dec(x_796);
x_838 = lean_unsigned_to_nat(1u);
x_839 = lean_nat_add(x_838, x_681);
lean_dec(x_681);
x_840 = lean_nat_add(x_839, x_788);
lean_dec(x_839);
x_841 = lean_nat_add(x_838, x_788);
lean_dec(x_788);
x_842 = lean_nat_add(x_841, x_797);
lean_dec(x_797);
lean_dec(x_841);
if (lean_is_scalar(x_686)) {
 x_843 = lean_alloc_ctor(0, 5, 0);
} else {
 x_843 = x_686;
}
lean_ctor_set(x_843, 0, x_842);
lean_ctor_set(x_843, 1, x_784);
lean_ctor_set(x_843, 2, x_785);
lean_ctor_set(x_843, 3, x_685);
lean_ctor_set(x_843, 4, x_786);
x_844 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_844, 0, x_840);
lean_ctor_set(x_844, 1, x_682);
lean_ctor_set(x_844, 2, x_683);
lean_ctor_set(x_844, 3, x_684);
lean_ctor_set(x_844, 4, x_843);
return x_844;
}
}
}
else
{
if (lean_obj_tag(x_684) == 0)
{
lean_dec(x_787);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_845 = lean_ctor_get(x_685, 0);
lean_inc(x_845);
x_846 = lean_unsigned_to_nat(1u);
x_847 = lean_nat_add(x_846, x_681);
lean_dec(x_681);
x_848 = lean_nat_add(x_846, x_845);
lean_dec(x_845);
x_849 = lean_box(1);
if (lean_is_scalar(x_686)) {
 x_850 = lean_alloc_ctor(0, 5, 0);
} else {
 x_850 = x_686;
}
lean_ctor_set(x_850, 0, x_848);
lean_ctor_set(x_850, 1, x_784);
lean_ctor_set(x_850, 2, x_785);
lean_ctor_set(x_850, 3, x_685);
lean_ctor_set(x_850, 4, x_849);
x_851 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_851, 0, x_847);
lean_ctor_set(x_851, 1, x_682);
lean_ctor_set(x_851, 2, x_683);
lean_ctor_set(x_851, 3, x_684);
lean_ctor_set(x_851, 4, x_850);
return x_851;
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_681);
x_852 = lean_box(1);
x_853 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_686)) {
 x_854 = lean_alloc_ctor(0, 5, 0);
} else {
 x_854 = x_686;
}
lean_ctor_set(x_854, 0, x_853);
lean_ctor_set(x_854, 1, x_784);
lean_ctor_set(x_854, 2, x_785);
lean_ctor_set(x_854, 3, x_852);
lean_ctor_set(x_854, 4, x_852);
x_855 = lean_unsigned_to_nat(3u);
x_856 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_682);
lean_ctor_set(x_856, 2, x_683);
lean_ctor_set(x_856, 3, x_684);
lean_ctor_set(x_856, 4, x_854);
return x_856;
}
}
else
{
lean_dec(x_681);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; 
lean_dec(x_787);
x_857 = lean_ctor_get(x_685, 1);
lean_inc(x_857);
x_858 = lean_ctor_get(x_685, 2);
lean_inc(x_858);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 lean_ctor_release(x_685, 2);
 lean_ctor_release(x_685, 3);
 lean_ctor_release(x_685, 4);
 x_859 = x_685;
} else {
 lean_dec_ref(x_685);
 x_859 = lean_box(0);
}
x_860 = lean_box(1);
x_861 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_859)) {
 x_862 = lean_alloc_ctor(0, 5, 0);
} else {
 x_862 = x_859;
}
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_862, 1, x_682);
lean_ctor_set(x_862, 2, x_683);
lean_ctor_set(x_862, 3, x_860);
lean_ctor_set(x_862, 4, x_860);
if (lean_is_scalar(x_686)) {
 x_863 = lean_alloc_ctor(0, 5, 0);
} else {
 x_863 = x_686;
}
lean_ctor_set(x_863, 0, x_861);
lean_ctor_set(x_863, 1, x_784);
lean_ctor_set(x_863, 2, x_785);
lean_ctor_set(x_863, 3, x_860);
lean_ctor_set(x_863, 4, x_860);
x_864 = lean_unsigned_to_nat(3u);
x_865 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_857);
lean_ctor_set(x_865, 2, x_858);
lean_ctor_set(x_865, 3, x_862);
lean_ctor_set(x_865, 4, x_863);
return x_865;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_683);
lean_dec(x_682);
x_866 = lean_box(1);
x_867 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_686)) {
 x_868 = lean_alloc_ctor(0, 5, 0);
} else {
 x_868 = x_686;
}
lean_ctor_set(x_868, 0, x_867);
lean_ctor_set(x_868, 1, x_784);
lean_ctor_set(x_868, 2, x_785);
lean_ctor_set(x_868, 3, x_787);
lean_ctor_set(x_868, 4, x_866);
return x_868;
}
}
}
}
}
else
{
return x_673;
}
}
else
{
return x_674;
}
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_869 = lean_ctor_get(x_680, 0);
lean_inc(x_869);
lean_dec(x_680);
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
x_872 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_872, 0, x_670);
lean_ctor_set(x_872, 1, x_870);
lean_ctor_set(x_872, 2, x_871);
lean_ctor_set(x_872, 3, x_673);
lean_ctor_set(x_872, 4, x_674);
return x_872;
}
}
default: 
{
lean_object* x_873; lean_object* x_874; 
lean_dec(x_670);
x_873 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___spec__1___rarg(x_1, x_2, x_3, x_674, lean_box(0));
x_874 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_671, x_672, x_673, x_873, lean_box(0), lean_box(0), lean_box(0));
return x_874;
}
}
}
}
else
{
lean_object* x_875; lean_object* x_876; 
lean_dec(x_2);
lean_dec(x_1);
x_875 = lean_box(0);
x_876 = lean_apply_1(x_3, x_875);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; 
x_877 = lean_box(1);
return x_877;
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_878 = lean_ctor_get(x_876, 0);
lean_inc(x_878);
lean_dec(x_876);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_881 = lean_box(1);
x_882 = lean_unsigned_to_nat(1u);
x_883 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_883, 0, x_882);
lean_ctor_set(x_883, 1, x_879);
lean_ctor_set(x_883, 2, x_880);
lean_ctor_set(x_883, 3, x_881);
lean_ctor_set(x_883, 4, x_881);
return x_883;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___spec__1___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_1, x_2, lean_box(0));
return x_4;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
x_7 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___spec__1___rarg(x_1, x_2, x_6, x_4, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_insertIfNew_u2098___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_alter_u2098___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_4, 3);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_8);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
switch (x_13) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_4);
lean_dec(x_7);
x_14 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_alter_u2098___spec__1___rarg(x_1, x_2, x_3, x_10, lean_box(0));
x_15 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_8, x_9, x_14, x_11, lean_box(0), lean_box(0), lean_box(0));
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_8, x_9, lean_box(0));
x_17 = lean_apply_1(x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_7);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_10, 2);
x_23 = lean_ctor_get(x_10, 3);
x_24 = lean_ctor_get(x_10, 4);
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
x_27 = lean_ctor_get(x_11, 2);
x_28 = lean_ctor_get(x_11, 3);
x_29 = lean_ctor_get(x_11, 4);
x_30 = lean_nat_dec_lt(x_20, x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_20);
x_31 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_21, x_22, x_23, x_24, lean_box(0), lean_box(0), lean_box(0));
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_mul(x_36, x_35);
x_38 = lean_nat_dec_lt(x_37, x_25);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_4);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_39, x_35);
lean_dec(x_35);
x_41 = lean_nat_add(x_40, x_25);
lean_dec(x_25);
lean_dec(x_40);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_32);
lean_ctor_set(x_10, 2, x_34);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_41);
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_11);
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_28, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_28, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_28, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_29, 0);
lean_inc(x_47);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_mul(x_48, x_47);
x_50 = lean_nat_dec_lt(x_42, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
uint8_t x_51; 
lean_dec(x_42);
lean_free_object(x_4);
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_28, 4);
lean_dec(x_52);
x_53 = lean_ctor_get(x_28, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_28, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_28, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_28, 0);
lean_dec(x_56);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_57, x_35);
lean_dec(x_35);
x_59 = lean_nat_add(x_58, x_25);
lean_dec(x_25);
x_60 = lean_nat_add(x_57, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
x_62 = lean_nat_add(x_58, x_61);
lean_dec(x_61);
lean_dec(x_58);
lean_inc(x_32);
lean_ctor_set(x_28, 4, x_45);
lean_ctor_set(x_28, 3, x_32);
lean_ctor_set(x_28, 2, x_34);
lean_ctor_set(x_28, 1, x_33);
lean_ctor_set(x_28, 0, x_62);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_32, 4);
lean_dec(x_64);
x_65 = lean_ctor_get(x_32, 3);
lean_dec(x_65);
x_66 = lean_ctor_get(x_32, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_32, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_32, 0);
lean_dec(x_68);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_46, 0);
lean_inc(x_69);
x_70 = lean_nat_add(x_60, x_69);
lean_dec(x_69);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_70);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_add(x_60, x_71);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_72);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
else
{
lean_dec(x_32);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_46, 0);
lean_inc(x_73);
x_74 = lean_nat_add(x_60, x_73);
lean_dec(x_73);
lean_dec(x_60);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_26);
lean_ctor_set(x_75, 2, x_27);
lean_ctor_set(x_75, 3, x_46);
lean_ctor_set(x_75, 4, x_29);
lean_ctor_set(x_10, 4, x_75);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_add(x_60, x_76);
lean_dec(x_60);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_26);
lean_ctor_set(x_78, 2, x_27);
lean_ctor_set(x_78, 3, x_46);
lean_ctor_set(x_78, 4, x_29);
lean_ctor_set(x_10, 4, x_78);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_add(x_58, x_79);
lean_dec(x_58);
lean_inc(x_32);
lean_ctor_set(x_28, 4, x_45);
lean_ctor_set(x_28, 3, x_32);
lean_ctor_set(x_28, 2, x_34);
lean_ctor_set(x_28, 1, x_33);
lean_ctor_set(x_28, 0, x_80);
x_81 = !lean_is_exclusive(x_32);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_32, 4);
lean_dec(x_82);
x_83 = lean_ctor_get(x_32, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_32, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_32, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_32, 0);
lean_dec(x_86);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_46, 0);
lean_inc(x_87);
x_88 = lean_nat_add(x_60, x_87);
lean_dec(x_87);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_88);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_89; 
x_89 = lean_nat_add(x_60, x_79);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_89);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
else
{
lean_dec(x_32);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_46, 0);
lean_inc(x_90);
x_91 = lean_nat_add(x_60, x_90);
lean_dec(x_90);
lean_dec(x_60);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_26);
lean_ctor_set(x_92, 2, x_27);
lean_ctor_set(x_92, 3, x_46);
lean_ctor_set(x_92, 4, x_29);
lean_ctor_set(x_10, 4, x_92);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_nat_add(x_60, x_79);
lean_dec(x_60);
x_94 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_26);
lean_ctor_set(x_94, 2, x_27);
lean_ctor_set(x_94, 3, x_46);
lean_ctor_set(x_94, 4, x_29);
lean_ctor_set(x_10, 4, x_94);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_28);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_95, x_35);
lean_dec(x_35);
x_97 = lean_nat_add(x_96, x_25);
lean_dec(x_25);
x_98 = lean_nat_add(x_95, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_45, 0);
lean_inc(x_99);
x_100 = lean_nat_add(x_96, x_99);
lean_dec(x_99);
lean_dec(x_96);
lean_inc(x_32);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_33);
lean_ctor_set(x_101, 2, x_34);
lean_ctor_set(x_101, 3, x_32);
lean_ctor_set(x_101, 4, x_45);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_102 = x_32;
} else {
 lean_dec_ref(x_32);
 x_102 = lean_box(0);
}
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_46, 0);
lean_inc(x_103);
x_104 = lean_nat_add(x_98, x_103);
lean_dec(x_103);
lean_dec(x_98);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 5, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_26);
lean_ctor_set(x_105, 2, x_27);
lean_ctor_set(x_105, 3, x_46);
lean_ctor_set(x_105, 4, x_29);
lean_ctor_set(x_10, 4, x_105);
lean_ctor_set(x_10, 3, x_101);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_nat_add(x_98, x_106);
lean_dec(x_98);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(0, 5, 0);
} else {
 x_108 = x_102;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_26);
lean_ctor_set(x_108, 2, x_27);
lean_ctor_set(x_108, 3, x_46);
lean_ctor_set(x_108, 4, x_29);
lean_ctor_set(x_10, 4, x_108);
lean_ctor_set(x_10, 3, x_101);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_nat_add(x_96, x_109);
lean_dec(x_96);
lean_inc(x_32);
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_33);
lean_ctor_set(x_111, 2, x_34);
lean_ctor_set(x_111, 3, x_32);
lean_ctor_set(x_111, 4, x_45);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_112 = x_32;
} else {
 lean_dec_ref(x_32);
 x_112 = lean_box(0);
}
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_46, 0);
lean_inc(x_113);
x_114 = lean_nat_add(x_98, x_113);
lean_dec(x_113);
lean_dec(x_98);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 5, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_26);
lean_ctor_set(x_115, 2, x_27);
lean_ctor_set(x_115, 3, x_46);
lean_ctor_set(x_115, 4, x_29);
lean_ctor_set(x_10, 4, x_115);
lean_ctor_set(x_10, 3, x_111);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_nat_add(x_98, x_109);
lean_dec(x_98);
if (lean_is_scalar(x_112)) {
 x_117 = lean_alloc_ctor(0, 5, 0);
} else {
 x_117 = x_112;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_26);
lean_ctor_set(x_117, 2, x_27);
lean_ctor_set(x_117, 3, x_46);
lean_ctor_set(x_117, 4, x_29);
lean_ctor_set(x_10, 4, x_117);
lean_ctor_set(x_10, 3, x_111);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_118, x_35);
lean_dec(x_35);
x_120 = lean_nat_add(x_119, x_25);
lean_dec(x_25);
x_121 = lean_nat_add(x_119, x_42);
lean_dec(x_42);
lean_dec(x_119);
lean_ctor_set(x_10, 4, x_28);
lean_ctor_set(x_10, 3, x_32);
lean_ctor_set(x_10, 2, x_34);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_121);
lean_ctor_set(x_4, 4, x_29);
lean_ctor_set(x_4, 2, x_27);
lean_ctor_set(x_4, 1, x_26);
lean_ctor_set(x_4, 0, x_120);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_28) == 0)
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_31, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_31, 1);
lean_inc(x_123);
lean_dec(x_31);
x_124 = lean_ctor_get(x_28, 0);
lean_inc(x_124);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_add(x_125, x_25);
lean_dec(x_25);
x_127 = lean_nat_add(x_125, x_124);
lean_dec(x_124);
x_128 = lean_box(1);
lean_ctor_set(x_11, 4, x_28);
lean_ctor_set(x_11, 3, x_128);
lean_ctor_set(x_11, 2, x_123);
lean_ctor_set(x_11, 1, x_122);
lean_ctor_set(x_11, 0, x_127);
lean_ctor_set(x_10, 4, x_29);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_27);
lean_ctor_set(x_10, 1, x_26);
lean_ctor_set(x_10, 0, x_126);
return x_10;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_25);
x_129 = lean_ctor_get(x_31, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_31, 1);
lean_inc(x_130);
lean_dec(x_31);
x_131 = !lean_is_exclusive(x_28);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_28, 1);
x_133 = lean_ctor_get(x_28, 2);
x_134 = lean_ctor_get(x_28, 4);
lean_dec(x_134);
x_135 = lean_ctor_get(x_28, 3);
lean_dec(x_135);
x_136 = lean_ctor_get(x_28, 0);
lean_dec(x_136);
x_137 = lean_box(1);
x_138 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_28, 4, x_137);
lean_ctor_set(x_28, 3, x_137);
lean_ctor_set(x_28, 2, x_130);
lean_ctor_set(x_28, 1, x_129);
lean_ctor_set(x_28, 0, x_138);
lean_ctor_set(x_11, 4, x_137);
lean_ctor_set(x_11, 3, x_137);
lean_ctor_set(x_11, 0, x_138);
x_139 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_133);
lean_ctor_set(x_10, 1, x_132);
lean_ctor_set(x_10, 0, x_139);
return x_10;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_ctor_get(x_28, 1);
x_141 = lean_ctor_get(x_28, 2);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_28);
x_142 = lean_box(1);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_129);
lean_ctor_set(x_144, 2, x_130);
lean_ctor_set(x_144, 3, x_142);
lean_ctor_set(x_144, 4, x_142);
lean_ctor_set(x_11, 4, x_142);
lean_ctor_set(x_11, 3, x_142);
lean_ctor_set(x_11, 0, x_143);
x_145 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_144);
lean_ctor_set(x_10, 2, x_141);
lean_ctor_set(x_10, 1, x_140);
lean_ctor_set(x_10, 0, x_145);
return x_10;
}
}
}
else
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_25);
x_146 = lean_ctor_get(x_31, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_31, 1);
lean_inc(x_147);
lean_dec(x_31);
x_148 = lean_box(1);
x_149 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_11, 4, x_148);
lean_ctor_set(x_11, 3, x_148);
lean_ctor_set(x_11, 2, x_147);
lean_ctor_set(x_11, 1, x_146);
lean_ctor_set(x_11, 0, x_149);
x_150 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_29);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_27);
lean_ctor_set(x_10, 1, x_26);
lean_ctor_set(x_10, 0, x_150);
return x_10;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_31, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_31, 1);
lean_inc(x_152);
lean_dec(x_31);
lean_ctor_set(x_11, 3, x_29);
x_153 = lean_box(1);
x_154 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_153);
lean_ctor_set(x_10, 2, x_152);
lean_ctor_set(x_10, 1, x_151);
lean_ctor_set(x_10, 0, x_154);
return x_10;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_25);
x_155 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_26, x_27, x_28, x_29, lean_box(0), lean_box(0), lean_box(0));
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 2);
lean_inc(x_158);
lean_dec(x_155);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_ctor_set(x_11, 4, x_24);
lean_ctor_set(x_11, 3, x_23);
lean_ctor_set(x_11, 2, x_22);
lean_ctor_set(x_11, 1, x_21);
lean_ctor_set(x_11, 0, x_20);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_unsigned_to_nat(3u);
x_161 = lean_nat_mul(x_160, x_159);
x_162 = lean_nat_dec_lt(x_161, x_20);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_4);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_nat_add(x_163, x_20);
lean_dec(x_20);
x_165 = lean_nat_add(x_164, x_159);
lean_dec(x_159);
lean_dec(x_164);
lean_ctor_set(x_10, 4, x_158);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_165);
return x_10;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_dec(x_11);
x_166 = lean_ctor_get(x_23, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_24, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_24, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_24, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_24, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_24, 4);
lean_inc(x_171);
x_172 = lean_unsigned_to_nat(2u);
x_173 = lean_nat_mul(x_172, x_166);
x_174 = lean_nat_dec_lt(x_167, x_173);
lean_dec(x_173);
if (x_174 == 0)
{
uint8_t x_175; 
lean_dec(x_167);
lean_free_object(x_10);
lean_free_object(x_4);
x_175 = !lean_is_exclusive(x_24);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_176 = lean_ctor_get(x_24, 4);
lean_dec(x_176);
x_177 = lean_ctor_get(x_24, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_24, 2);
lean_dec(x_178);
x_179 = lean_ctor_get(x_24, 1);
lean_dec(x_179);
x_180 = lean_ctor_get(x_24, 0);
lean_dec(x_180);
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_nat_add(x_181, x_20);
lean_dec(x_20);
x_183 = lean_nat_add(x_182, x_159);
lean_dec(x_182);
x_184 = lean_nat_add(x_181, x_166);
lean_dec(x_166);
x_185 = lean_nat_add(x_181, x_159);
lean_dec(x_159);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_170, 0);
lean_inc(x_186);
x_187 = lean_nat_add(x_184, x_186);
lean_dec(x_186);
lean_dec(x_184);
lean_inc(x_23);
lean_ctor_set(x_24, 4, x_170);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_187);
x_188 = !lean_is_exclusive(x_23);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_23, 4);
lean_dec(x_189);
x_190 = lean_ctor_get(x_23, 3);
lean_dec(x_190);
x_191 = lean_ctor_get(x_23, 2);
lean_dec(x_191);
x_192 = lean_ctor_get(x_23, 1);
lean_dec(x_192);
x_193 = lean_ctor_get(x_23, 0);
lean_dec(x_193);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_171, 0);
lean_inc(x_194);
x_195 = lean_nat_add(x_185, x_194);
lean_dec(x_194);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_195);
x_196 = !lean_is_exclusive(x_158);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_158, 4);
lean_dec(x_197);
x_198 = lean_ctor_get(x_158, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_158, 2);
lean_dec(x_199);
x_200 = lean_ctor_get(x_158, 1);
lean_dec(x_200);
x_201 = lean_ctor_get(x_158, 0);
lean_dec(x_201);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_202; 
lean_dec(x_158);
x_202 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_202, 0, x_183);
lean_ctor_set(x_202, 1, x_168);
lean_ctor_set(x_202, 2, x_169);
lean_ctor_set(x_202, 3, x_24);
lean_ctor_set(x_202, 4, x_23);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_203 = lean_unsigned_to_nat(0u);
x_204 = lean_nat_add(x_185, x_203);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_204);
x_205 = !lean_is_exclusive(x_158);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_158, 4);
lean_dec(x_206);
x_207 = lean_ctor_get(x_158, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_158, 2);
lean_dec(x_208);
x_209 = lean_ctor_get(x_158, 1);
lean_dec(x_209);
x_210 = lean_ctor_get(x_158, 0);
lean_dec(x_210);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_211; 
lean_dec(x_158);
x_211 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_211, 0, x_183);
lean_ctor_set(x_211, 1, x_168);
lean_ctor_set(x_211, 2, x_169);
lean_ctor_set(x_211, 3, x_24);
lean_ctor_set(x_211, 4, x_23);
return x_211;
}
}
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_ctor_get(x_171, 0);
lean_inc(x_212);
x_213 = lean_nat_add(x_185, x_212);
lean_dec(x_212);
lean_dec(x_185);
lean_inc(x_158);
x_214 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_156);
lean_ctor_set(x_214, 2, x_157);
lean_ctor_set(x_214, 3, x_171);
lean_ctor_set(x_214, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_215 = x_158;
} else {
 lean_dec_ref(x_158);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(0, 5, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_183);
lean_ctor_set(x_216, 1, x_168);
lean_ctor_set(x_216, 2, x_169);
lean_ctor_set(x_216, 3, x_24);
lean_ctor_set(x_216, 4, x_214);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_unsigned_to_nat(0u);
x_218 = lean_nat_add(x_185, x_217);
lean_dec(x_185);
lean_inc(x_158);
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_156);
lean_ctor_set(x_219, 2, x_157);
lean_ctor_set(x_219, 3, x_171);
lean_ctor_set(x_219, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_220 = x_158;
} else {
 lean_dec_ref(x_158);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 5, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_183);
lean_ctor_set(x_221, 1, x_168);
lean_ctor_set(x_221, 2, x_169);
lean_ctor_set(x_221, 3, x_24);
lean_ctor_set(x_221, 4, x_219);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_unsigned_to_nat(0u);
x_223 = lean_nat_add(x_184, x_222);
lean_dec(x_184);
lean_inc(x_23);
lean_ctor_set(x_24, 4, x_170);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_223);
x_224 = !lean_is_exclusive(x_23);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_23, 4);
lean_dec(x_225);
x_226 = lean_ctor_get(x_23, 3);
lean_dec(x_226);
x_227 = lean_ctor_get(x_23, 2);
lean_dec(x_227);
x_228 = lean_ctor_get(x_23, 1);
lean_dec(x_228);
x_229 = lean_ctor_get(x_23, 0);
lean_dec(x_229);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_230 = lean_ctor_get(x_171, 0);
lean_inc(x_230);
x_231 = lean_nat_add(x_185, x_230);
lean_dec(x_230);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_231);
x_232 = !lean_is_exclusive(x_158);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_158, 4);
lean_dec(x_233);
x_234 = lean_ctor_get(x_158, 3);
lean_dec(x_234);
x_235 = lean_ctor_get(x_158, 2);
lean_dec(x_235);
x_236 = lean_ctor_get(x_158, 1);
lean_dec(x_236);
x_237 = lean_ctor_get(x_158, 0);
lean_dec(x_237);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_238; 
lean_dec(x_158);
x_238 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_238, 0, x_183);
lean_ctor_set(x_238, 1, x_168);
lean_ctor_set(x_238, 2, x_169);
lean_ctor_set(x_238, 3, x_24);
lean_ctor_set(x_238, 4, x_23);
return x_238;
}
}
else
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_nat_add(x_185, x_222);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_239);
x_240 = !lean_is_exclusive(x_158);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = lean_ctor_get(x_158, 4);
lean_dec(x_241);
x_242 = lean_ctor_get(x_158, 3);
lean_dec(x_242);
x_243 = lean_ctor_get(x_158, 2);
lean_dec(x_243);
x_244 = lean_ctor_get(x_158, 1);
lean_dec(x_244);
x_245 = lean_ctor_get(x_158, 0);
lean_dec(x_245);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_246; 
lean_dec(x_158);
x_246 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_246, 0, x_183);
lean_ctor_set(x_246, 1, x_168);
lean_ctor_set(x_246, 2, x_169);
lean_ctor_set(x_246, 3, x_24);
lean_ctor_set(x_246, 4, x_23);
return x_246;
}
}
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = lean_ctor_get(x_171, 0);
lean_inc(x_247);
x_248 = lean_nat_add(x_185, x_247);
lean_dec(x_247);
lean_dec(x_185);
lean_inc(x_158);
x_249 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_156);
lean_ctor_set(x_249, 2, x_157);
lean_ctor_set(x_249, 3, x_171);
lean_ctor_set(x_249, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_250 = x_158;
} else {
 lean_dec_ref(x_158);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 5, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_183);
lean_ctor_set(x_251, 1, x_168);
lean_ctor_set(x_251, 2, x_169);
lean_ctor_set(x_251, 3, x_24);
lean_ctor_set(x_251, 4, x_249);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_nat_add(x_185, x_222);
lean_dec(x_185);
lean_inc(x_158);
x_253 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_156);
lean_ctor_set(x_253, 2, x_157);
lean_ctor_set(x_253, 3, x_171);
lean_ctor_set(x_253, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_254 = x_158;
} else {
 lean_dec_ref(x_158);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(0, 5, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_183);
lean_ctor_set(x_255, 1, x_168);
lean_ctor_set(x_255, 2, x_169);
lean_ctor_set(x_255, 3, x_24);
lean_ctor_set(x_255, 4, x_253);
return x_255;
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_24);
x_256 = lean_unsigned_to_nat(1u);
x_257 = lean_nat_add(x_256, x_20);
lean_dec(x_20);
x_258 = lean_nat_add(x_257, x_159);
lean_dec(x_257);
x_259 = lean_nat_add(x_256, x_166);
lean_dec(x_166);
x_260 = lean_nat_add(x_256, x_159);
lean_dec(x_159);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_170, 0);
lean_inc(x_261);
x_262 = lean_nat_add(x_259, x_261);
lean_dec(x_261);
lean_dec(x_259);
lean_inc(x_23);
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_21);
lean_ctor_set(x_263, 2, x_22);
lean_ctor_set(x_263, 3, x_23);
lean_ctor_set(x_263, 4, x_170);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 x_264 = x_23;
} else {
 lean_dec_ref(x_23);
 x_264 = lean_box(0);
}
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_265 = lean_ctor_get(x_171, 0);
lean_inc(x_265);
x_266 = lean_nat_add(x_260, x_265);
lean_dec(x_265);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_264)) {
 x_267 = lean_alloc_ctor(0, 5, 0);
} else {
 x_267 = x_264;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_156);
lean_ctor_set(x_267, 2, x_157);
lean_ctor_set(x_267, 3, x_171);
lean_ctor_set(x_267, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_268 = x_158;
} else {
 lean_dec_ref(x_158);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(0, 5, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_258);
lean_ctor_set(x_269, 1, x_168);
lean_ctor_set(x_269, 2, x_169);
lean_ctor_set(x_269, 3, x_263);
lean_ctor_set(x_269, 4, x_267);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_unsigned_to_nat(0u);
x_271 = lean_nat_add(x_260, x_270);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_264)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_264;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_156);
lean_ctor_set(x_272, 2, x_157);
lean_ctor_set(x_272, 3, x_171);
lean_ctor_set(x_272, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_273 = x_158;
} else {
 lean_dec_ref(x_158);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 5, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_258);
lean_ctor_set(x_274, 1, x_168);
lean_ctor_set(x_274, 2, x_169);
lean_ctor_set(x_274, 3, x_263);
lean_ctor_set(x_274, 4, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_unsigned_to_nat(0u);
x_276 = lean_nat_add(x_259, x_275);
lean_dec(x_259);
lean_inc(x_23);
x_277 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_21);
lean_ctor_set(x_277, 2, x_22);
lean_ctor_set(x_277, 3, x_23);
lean_ctor_set(x_277, 4, x_170);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 x_278 = x_23;
} else {
 lean_dec_ref(x_23);
 x_278 = lean_box(0);
}
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_ctor_get(x_171, 0);
lean_inc(x_279);
x_280 = lean_nat_add(x_260, x_279);
lean_dec(x_279);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_278)) {
 x_281 = lean_alloc_ctor(0, 5, 0);
} else {
 x_281 = x_278;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_156);
lean_ctor_set(x_281, 2, x_157);
lean_ctor_set(x_281, 3, x_171);
lean_ctor_set(x_281, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_282 = x_158;
} else {
 lean_dec_ref(x_158);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(0, 5, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_258);
lean_ctor_set(x_283, 1, x_168);
lean_ctor_set(x_283, 2, x_169);
lean_ctor_set(x_283, 3, x_277);
lean_ctor_set(x_283, 4, x_281);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_284 = lean_nat_add(x_260, x_275);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_278)) {
 x_285 = lean_alloc_ctor(0, 5, 0);
} else {
 x_285 = x_278;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_156);
lean_ctor_set(x_285, 2, x_157);
lean_ctor_set(x_285, 3, x_171);
lean_ctor_set(x_285, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_286 = x_158;
} else {
 lean_dec_ref(x_158);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(0, 5, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_258);
lean_ctor_set(x_287, 1, x_168);
lean_ctor_set(x_287, 2, x_169);
lean_ctor_set(x_287, 3, x_277);
lean_ctor_set(x_287, 4, x_285);
return x_287;
}
}
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_166);
x_288 = lean_unsigned_to_nat(1u);
x_289 = lean_nat_add(x_288, x_20);
lean_dec(x_20);
x_290 = lean_nat_add(x_289, x_159);
lean_dec(x_289);
x_291 = lean_nat_add(x_288, x_159);
lean_dec(x_159);
x_292 = lean_nat_add(x_291, x_167);
lean_dec(x_167);
lean_dec(x_291);
lean_ctor_set(x_10, 4, x_158);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_292);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_290);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_24, 0);
lean_inc(x_293);
x_294 = lean_unsigned_to_nat(1u);
x_295 = lean_nat_add(x_294, x_20);
lean_dec(x_20);
x_296 = lean_nat_add(x_294, x_293);
lean_dec(x_293);
x_297 = lean_box(1);
lean_ctor_set(x_10, 4, x_297);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_296);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_295);
return x_4;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_20);
x_298 = lean_box(1);
x_299 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_10, 4, x_298);
lean_ctor_set(x_10, 3, x_298);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_299);
x_300 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_300);
return x_4;
}
}
else
{
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_301; 
lean_dec(x_11);
x_301 = !lean_is_exclusive(x_24);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_302 = lean_ctor_get(x_24, 1);
x_303 = lean_ctor_get(x_24, 2);
x_304 = lean_ctor_get(x_24, 4);
lean_dec(x_304);
x_305 = lean_ctor_get(x_24, 3);
lean_dec(x_305);
x_306 = lean_ctor_get(x_24, 0);
lean_dec(x_306);
x_307 = lean_box(1);
x_308 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_24, 4, x_307);
lean_ctor_set(x_24, 3, x_307);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_308);
lean_ctor_set(x_10, 4, x_307);
lean_ctor_set(x_10, 3, x_307);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_308);
x_309 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_24);
lean_ctor_set(x_4, 2, x_303);
lean_ctor_set(x_4, 1, x_302);
lean_ctor_set(x_4, 0, x_309);
return x_4;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_310 = lean_ctor_get(x_24, 1);
x_311 = lean_ctor_get(x_24, 2);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_24);
x_312 = lean_box(1);
x_313 = lean_unsigned_to_nat(1u);
x_314 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_21);
lean_ctor_set(x_314, 2, x_22);
lean_ctor_set(x_314, 3, x_312);
lean_ctor_set(x_314, 4, x_312);
lean_ctor_set(x_10, 4, x_312);
lean_ctor_set(x_10, 3, x_312);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_313);
x_315 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_314);
lean_ctor_set(x_4, 2, x_311);
lean_ctor_set(x_4, 1, x_310);
lean_ctor_set(x_4, 0, x_315);
return x_4;
}
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_4);
x_316 = lean_box(1);
x_317 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_316);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_317);
return x_10;
}
}
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_318 = lean_ctor_get(x_10, 0);
x_319 = lean_ctor_get(x_10, 1);
x_320 = lean_ctor_get(x_10, 2);
x_321 = lean_ctor_get(x_10, 3);
x_322 = lean_ctor_get(x_10, 4);
x_323 = lean_ctor_get(x_11, 0);
x_324 = lean_ctor_get(x_11, 1);
x_325 = lean_ctor_get(x_11, 2);
x_326 = lean_ctor_get(x_11, 3);
x_327 = lean_ctor_get(x_11, 4);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_11);
x_328 = lean_nat_dec_lt(x_318, x_323);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_318);
x_329 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_319, x_320, x_321, x_322, lean_box(0), lean_box(0), lean_box(0));
x_330 = lean_ctor_get(x_329, 2);
lean_inc(x_330);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_331 = lean_ctor_get(x_329, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_dec(x_329);
x_333 = lean_ctor_get(x_330, 0);
lean_inc(x_333);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
x_334 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_334, 0, x_323);
lean_ctor_set(x_334, 1, x_324);
lean_ctor_set(x_334, 2, x_325);
lean_ctor_set(x_334, 3, x_326);
lean_ctor_set(x_334, 4, x_327);
x_335 = lean_unsigned_to_nat(3u);
x_336 = lean_nat_mul(x_335, x_333);
x_337 = lean_nat_dec_lt(x_336, x_323);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_free_object(x_4);
x_338 = lean_unsigned_to_nat(1u);
x_339 = lean_nat_add(x_338, x_333);
lean_dec(x_333);
x_340 = lean_nat_add(x_339, x_323);
lean_dec(x_323);
lean_dec(x_339);
lean_ctor_set(x_10, 4, x_334);
lean_ctor_set(x_10, 3, x_330);
lean_ctor_set(x_10, 2, x_332);
lean_ctor_set(x_10, 1, x_331);
lean_ctor_set(x_10, 0, x_340);
return x_10;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
lean_dec(x_334);
x_341 = lean_ctor_get(x_326, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_326, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_326, 2);
lean_inc(x_343);
x_344 = lean_ctor_get(x_326, 3);
lean_inc(x_344);
x_345 = lean_ctor_get(x_326, 4);
lean_inc(x_345);
x_346 = lean_ctor_get(x_327, 0);
lean_inc(x_346);
x_347 = lean_unsigned_to_nat(2u);
x_348 = lean_nat_mul(x_347, x_346);
x_349 = lean_nat_dec_lt(x_341, x_348);
lean_dec(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_341);
lean_free_object(x_4);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 x_350 = x_326;
} else {
 lean_dec_ref(x_326);
 x_350 = lean_box(0);
}
x_351 = lean_unsigned_to_nat(1u);
x_352 = lean_nat_add(x_351, x_333);
lean_dec(x_333);
x_353 = lean_nat_add(x_352, x_323);
lean_dec(x_323);
x_354 = lean_nat_add(x_351, x_346);
lean_dec(x_346);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_355 = lean_ctor_get(x_344, 0);
lean_inc(x_355);
x_356 = lean_nat_add(x_352, x_355);
lean_dec(x_355);
lean_dec(x_352);
lean_inc(x_330);
if (lean_is_scalar(x_350)) {
 x_357 = lean_alloc_ctor(0, 5, 0);
} else {
 x_357 = x_350;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_331);
lean_ctor_set(x_357, 2, x_332);
lean_ctor_set(x_357, 3, x_330);
lean_ctor_set(x_357, 4, x_344);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 x_358 = x_330;
} else {
 lean_dec_ref(x_330);
 x_358 = lean_box(0);
}
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_345, 0);
lean_inc(x_359);
x_360 = lean_nat_add(x_354, x_359);
lean_dec(x_359);
lean_dec(x_354);
if (lean_is_scalar(x_358)) {
 x_361 = lean_alloc_ctor(0, 5, 0);
} else {
 x_361 = x_358;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_324);
lean_ctor_set(x_361, 2, x_325);
lean_ctor_set(x_361, 3, x_345);
lean_ctor_set(x_361, 4, x_327);
lean_ctor_set(x_10, 4, x_361);
lean_ctor_set(x_10, 3, x_357);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_unsigned_to_nat(0u);
x_363 = lean_nat_add(x_354, x_362);
lean_dec(x_354);
if (lean_is_scalar(x_358)) {
 x_364 = lean_alloc_ctor(0, 5, 0);
} else {
 x_364 = x_358;
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_324);
lean_ctor_set(x_364, 2, x_325);
lean_ctor_set(x_364, 3, x_345);
lean_ctor_set(x_364, 4, x_327);
lean_ctor_set(x_10, 4, x_364);
lean_ctor_set(x_10, 3, x_357);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = lean_unsigned_to_nat(0u);
x_366 = lean_nat_add(x_352, x_365);
lean_dec(x_352);
lean_inc(x_330);
if (lean_is_scalar(x_350)) {
 x_367 = lean_alloc_ctor(0, 5, 0);
} else {
 x_367 = x_350;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_331);
lean_ctor_set(x_367, 2, x_332);
lean_ctor_set(x_367, 3, x_330);
lean_ctor_set(x_367, 4, x_344);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 x_368 = x_330;
} else {
 lean_dec_ref(x_330);
 x_368 = lean_box(0);
}
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_345, 0);
lean_inc(x_369);
x_370 = lean_nat_add(x_354, x_369);
lean_dec(x_369);
lean_dec(x_354);
if (lean_is_scalar(x_368)) {
 x_371 = lean_alloc_ctor(0, 5, 0);
} else {
 x_371 = x_368;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_324);
lean_ctor_set(x_371, 2, x_325);
lean_ctor_set(x_371, 3, x_345);
lean_ctor_set(x_371, 4, x_327);
lean_ctor_set(x_10, 4, x_371);
lean_ctor_set(x_10, 3, x_367);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_nat_add(x_354, x_365);
lean_dec(x_354);
if (lean_is_scalar(x_368)) {
 x_373 = lean_alloc_ctor(0, 5, 0);
} else {
 x_373 = x_368;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_324);
lean_ctor_set(x_373, 2, x_325);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set(x_373, 4, x_327);
lean_ctor_set(x_10, 4, x_373);
lean_ctor_set(x_10, 3, x_367);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
x_374 = lean_unsigned_to_nat(1u);
x_375 = lean_nat_add(x_374, x_333);
lean_dec(x_333);
x_376 = lean_nat_add(x_375, x_323);
lean_dec(x_323);
x_377 = lean_nat_add(x_375, x_341);
lean_dec(x_341);
lean_dec(x_375);
lean_ctor_set(x_10, 4, x_326);
lean_ctor_set(x_10, 3, x_330);
lean_ctor_set(x_10, 2, x_332);
lean_ctor_set(x_10, 1, x_331);
lean_ctor_set(x_10, 0, x_377);
lean_ctor_set(x_4, 4, x_327);
lean_ctor_set(x_4, 2, x_325);
lean_ctor_set(x_4, 1, x_324);
lean_ctor_set(x_4, 0, x_376);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_326) == 0)
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_378 = lean_ctor_get(x_329, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_329, 1);
lean_inc(x_379);
lean_dec(x_329);
x_380 = lean_ctor_get(x_326, 0);
lean_inc(x_380);
x_381 = lean_unsigned_to_nat(1u);
x_382 = lean_nat_add(x_381, x_323);
lean_dec(x_323);
x_383 = lean_nat_add(x_381, x_380);
lean_dec(x_380);
x_384 = lean_box(1);
x_385 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_378);
lean_ctor_set(x_385, 2, x_379);
lean_ctor_set(x_385, 3, x_384);
lean_ctor_set(x_385, 4, x_326);
lean_ctor_set(x_10, 4, x_327);
lean_ctor_set(x_10, 3, x_385);
lean_ctor_set(x_10, 2, x_325);
lean_ctor_set(x_10, 1, x_324);
lean_ctor_set(x_10, 0, x_382);
return x_10;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_323);
x_386 = lean_ctor_get(x_329, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_329, 1);
lean_inc(x_387);
lean_dec(x_329);
x_388 = lean_ctor_get(x_326, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_326, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 x_390 = x_326;
} else {
 lean_dec_ref(x_326);
 x_390 = lean_box(0);
}
x_391 = lean_box(1);
x_392 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_390)) {
 x_393 = lean_alloc_ctor(0, 5, 0);
} else {
 x_393 = x_390;
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_386);
lean_ctor_set(x_393, 2, x_387);
lean_ctor_set(x_393, 3, x_391);
lean_ctor_set(x_393, 4, x_391);
x_394 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_324);
lean_ctor_set(x_394, 2, x_325);
lean_ctor_set(x_394, 3, x_391);
lean_ctor_set(x_394, 4, x_391);
x_395 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_394);
lean_ctor_set(x_10, 3, x_393);
lean_ctor_set(x_10, 2, x_389);
lean_ctor_set(x_10, 1, x_388);
lean_ctor_set(x_10, 0, x_395);
return x_10;
}
}
else
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_323);
x_396 = lean_ctor_get(x_329, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_329, 1);
lean_inc(x_397);
lean_dec(x_329);
x_398 = lean_box(1);
x_399 = lean_unsigned_to_nat(1u);
x_400 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_396);
lean_ctor_set(x_400, 2, x_397);
lean_ctor_set(x_400, 3, x_398);
lean_ctor_set(x_400, 4, x_398);
x_401 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_327);
lean_ctor_set(x_10, 3, x_400);
lean_ctor_set(x_10, 2, x_325);
lean_ctor_set(x_10, 1, x_324);
lean_ctor_set(x_10, 0, x_401);
return x_10;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_402 = lean_ctor_get(x_329, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_329, 1);
lean_inc(x_403);
lean_dec(x_329);
x_404 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_404, 0, x_323);
lean_ctor_set(x_404, 1, x_324);
lean_ctor_set(x_404, 2, x_325);
lean_ctor_set(x_404, 3, x_327);
lean_ctor_set(x_404, 4, x_327);
x_405 = lean_box(1);
x_406 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_404);
lean_ctor_set(x_10, 3, x_405);
lean_ctor_set(x_10, 2, x_403);
lean_ctor_set(x_10, 1, x_402);
lean_ctor_set(x_10, 0, x_406);
return x_10;
}
}
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_323);
x_407 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_324, x_325, x_326, x_327, lean_box(0), lean_box(0), lean_box(0));
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_407, 2);
lean_inc(x_410);
lean_dec(x_407);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
x_411 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_411, 0, x_318);
lean_ctor_set(x_411, 1, x_319);
lean_ctor_set(x_411, 2, x_320);
lean_ctor_set(x_411, 3, x_321);
lean_ctor_set(x_411, 4, x_322);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_412 = lean_ctor_get(x_410, 0);
lean_inc(x_412);
x_413 = lean_unsigned_to_nat(3u);
x_414 = lean_nat_mul(x_413, x_412);
x_415 = lean_nat_dec_lt(x_414, x_318);
lean_dec(x_414);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_free_object(x_4);
x_416 = lean_unsigned_to_nat(1u);
x_417 = lean_nat_add(x_416, x_318);
lean_dec(x_318);
x_418 = lean_nat_add(x_417, x_412);
lean_dec(x_412);
lean_dec(x_417);
lean_ctor_set(x_10, 4, x_410);
lean_ctor_set(x_10, 3, x_411);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_418);
return x_10;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_dec(x_411);
x_419 = lean_ctor_get(x_321, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_322, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_322, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_322, 2);
lean_inc(x_422);
x_423 = lean_ctor_get(x_322, 3);
lean_inc(x_423);
x_424 = lean_ctor_get(x_322, 4);
lean_inc(x_424);
x_425 = lean_unsigned_to_nat(2u);
x_426 = lean_nat_mul(x_425, x_419);
x_427 = lean_nat_dec_lt(x_420, x_426);
lean_dec(x_426);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_420);
lean_free_object(x_10);
lean_free_object(x_4);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 lean_ctor_release(x_322, 4);
 x_428 = x_322;
} else {
 lean_dec_ref(x_322);
 x_428 = lean_box(0);
}
x_429 = lean_unsigned_to_nat(1u);
x_430 = lean_nat_add(x_429, x_318);
lean_dec(x_318);
x_431 = lean_nat_add(x_430, x_412);
lean_dec(x_430);
x_432 = lean_nat_add(x_429, x_419);
lean_dec(x_419);
x_433 = lean_nat_add(x_429, x_412);
lean_dec(x_412);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = lean_ctor_get(x_423, 0);
lean_inc(x_434);
x_435 = lean_nat_add(x_432, x_434);
lean_dec(x_434);
lean_dec(x_432);
lean_inc(x_321);
if (lean_is_scalar(x_428)) {
 x_436 = lean_alloc_ctor(0, 5, 0);
} else {
 x_436 = x_428;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_319);
lean_ctor_set(x_436, 2, x_320);
lean_ctor_set(x_436, 3, x_321);
lean_ctor_set(x_436, 4, x_423);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 x_437 = x_321;
} else {
 lean_dec_ref(x_321);
 x_437 = lean_box(0);
}
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_438 = lean_ctor_get(x_424, 0);
lean_inc(x_438);
x_439 = lean_nat_add(x_433, x_438);
lean_dec(x_438);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_437)) {
 x_440 = lean_alloc_ctor(0, 5, 0);
} else {
 x_440 = x_437;
}
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_408);
lean_ctor_set(x_440, 2, x_409);
lean_ctor_set(x_440, 3, x_424);
lean_ctor_set(x_440, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_441 = x_410;
} else {
 lean_dec_ref(x_410);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(0, 5, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_431);
lean_ctor_set(x_442, 1, x_421);
lean_ctor_set(x_442, 2, x_422);
lean_ctor_set(x_442, 3, x_436);
lean_ctor_set(x_442, 4, x_440);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_443 = lean_unsigned_to_nat(0u);
x_444 = lean_nat_add(x_433, x_443);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(0, 5, 0);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_408);
lean_ctor_set(x_445, 2, x_409);
lean_ctor_set(x_445, 3, x_424);
lean_ctor_set(x_445, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_446 = x_410;
} else {
 lean_dec_ref(x_410);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(0, 5, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_431);
lean_ctor_set(x_447, 1, x_421);
lean_ctor_set(x_447, 2, x_422);
lean_ctor_set(x_447, 3, x_436);
lean_ctor_set(x_447, 4, x_445);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_448 = lean_unsigned_to_nat(0u);
x_449 = lean_nat_add(x_432, x_448);
lean_dec(x_432);
lean_inc(x_321);
if (lean_is_scalar(x_428)) {
 x_450 = lean_alloc_ctor(0, 5, 0);
} else {
 x_450 = x_428;
}
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_319);
lean_ctor_set(x_450, 2, x_320);
lean_ctor_set(x_450, 3, x_321);
lean_ctor_set(x_450, 4, x_423);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 x_451 = x_321;
} else {
 lean_dec_ref(x_321);
 x_451 = lean_box(0);
}
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_452 = lean_ctor_get(x_424, 0);
lean_inc(x_452);
x_453 = lean_nat_add(x_433, x_452);
lean_dec(x_452);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_451)) {
 x_454 = lean_alloc_ctor(0, 5, 0);
} else {
 x_454 = x_451;
}
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_408);
lean_ctor_set(x_454, 2, x_409);
lean_ctor_set(x_454, 3, x_424);
lean_ctor_set(x_454, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_455 = x_410;
} else {
 lean_dec_ref(x_410);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(0, 5, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_431);
lean_ctor_set(x_456, 1, x_421);
lean_ctor_set(x_456, 2, x_422);
lean_ctor_set(x_456, 3, x_450);
lean_ctor_set(x_456, 4, x_454);
return x_456;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_457 = lean_nat_add(x_433, x_448);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_451)) {
 x_458 = lean_alloc_ctor(0, 5, 0);
} else {
 x_458 = x_451;
}
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_408);
lean_ctor_set(x_458, 2, x_409);
lean_ctor_set(x_458, 3, x_424);
lean_ctor_set(x_458, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_459 = x_410;
} else {
 lean_dec_ref(x_410);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(0, 5, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_431);
lean_ctor_set(x_460, 1, x_421);
lean_ctor_set(x_460, 2, x_422);
lean_ctor_set(x_460, 3, x_450);
lean_ctor_set(x_460, 4, x_458);
return x_460;
}
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_419);
x_461 = lean_unsigned_to_nat(1u);
x_462 = lean_nat_add(x_461, x_318);
lean_dec(x_318);
x_463 = lean_nat_add(x_462, x_412);
lean_dec(x_462);
x_464 = lean_nat_add(x_461, x_412);
lean_dec(x_412);
x_465 = lean_nat_add(x_464, x_420);
lean_dec(x_420);
lean_dec(x_464);
lean_ctor_set(x_10, 4, x_410);
lean_ctor_set(x_10, 3, x_322);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_465);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_463);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_321) == 0)
{
lean_dec(x_411);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_466 = lean_ctor_get(x_322, 0);
lean_inc(x_466);
x_467 = lean_unsigned_to_nat(1u);
x_468 = lean_nat_add(x_467, x_318);
lean_dec(x_318);
x_469 = lean_nat_add(x_467, x_466);
lean_dec(x_466);
x_470 = lean_box(1);
lean_ctor_set(x_10, 4, x_470);
lean_ctor_set(x_10, 3, x_322);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_469);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_468);
return x_4;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_318);
x_471 = lean_box(1);
x_472 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_10, 4, x_471);
lean_ctor_set(x_10, 3, x_471);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_472);
x_473 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_473);
return x_4;
}
}
else
{
lean_dec(x_318);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec(x_411);
x_474 = lean_ctor_get(x_322, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_322, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 lean_ctor_release(x_322, 4);
 x_476 = x_322;
} else {
 lean_dec_ref(x_322);
 x_476 = lean_box(0);
}
x_477 = lean_box(1);
x_478 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_476)) {
 x_479 = lean_alloc_ctor(0, 5, 0);
} else {
 x_479 = x_476;
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_319);
lean_ctor_set(x_479, 2, x_320);
lean_ctor_set(x_479, 3, x_477);
lean_ctor_set(x_479, 4, x_477);
lean_ctor_set(x_10, 4, x_477);
lean_ctor_set(x_10, 3, x_477);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_478);
x_480 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_479);
lean_ctor_set(x_4, 2, x_475);
lean_ctor_set(x_4, 1, x_474);
lean_ctor_set(x_4, 0, x_480);
return x_4;
}
else
{
lean_object* x_481; lean_object* x_482; 
lean_dec(x_320);
lean_dec(x_319);
lean_free_object(x_4);
x_481 = lean_box(1);
x_482 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_481);
lean_ctor_set(x_10, 3, x_411);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_482);
return x_10;
}
}
}
}
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; 
x_483 = lean_ctor_get(x_10, 0);
x_484 = lean_ctor_get(x_10, 1);
x_485 = lean_ctor_get(x_10, 2);
x_486 = lean_ctor_get(x_10, 3);
x_487 = lean_ctor_get(x_10, 4);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_10);
x_488 = lean_ctor_get(x_11, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_11, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_11, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_11, 3);
lean_inc(x_491);
x_492 = lean_ctor_get(x_11, 4);
lean_inc(x_492);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_493 = x_11;
} else {
 lean_dec_ref(x_11);
 x_493 = lean_box(0);
}
x_494 = lean_nat_dec_lt(x_483, x_488);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; 
lean_dec(x_483);
x_495 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_484, x_485, x_486, x_487, lean_box(0), lean_box(0), lean_box(0));
x_496 = lean_ctor_get(x_495, 2);
lean_inc(x_496);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_498);
lean_dec(x_495);
x_499 = lean_ctor_get(x_496, 0);
lean_inc(x_499);
lean_inc(x_492);
lean_inc(x_491);
lean_inc(x_490);
lean_inc(x_489);
lean_inc(x_488);
if (lean_is_scalar(x_493)) {
 x_500 = lean_alloc_ctor(0, 5, 0);
} else {
 x_500 = x_493;
}
lean_ctor_set(x_500, 0, x_488);
lean_ctor_set(x_500, 1, x_489);
lean_ctor_set(x_500, 2, x_490);
lean_ctor_set(x_500, 3, x_491);
lean_ctor_set(x_500, 4, x_492);
x_501 = lean_unsigned_to_nat(3u);
x_502 = lean_nat_mul(x_501, x_499);
x_503 = lean_nat_dec_lt(x_502, x_488);
lean_dec(x_502);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_492);
lean_dec(x_491);
lean_dec(x_490);
lean_dec(x_489);
lean_free_object(x_4);
x_504 = lean_unsigned_to_nat(1u);
x_505 = lean_nat_add(x_504, x_499);
lean_dec(x_499);
x_506 = lean_nat_add(x_505, x_488);
lean_dec(x_488);
lean_dec(x_505);
x_507 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_497);
lean_ctor_set(x_507, 2, x_498);
lean_ctor_set(x_507, 3, x_496);
lean_ctor_set(x_507, 4, x_500);
return x_507;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; 
lean_dec(x_500);
x_508 = lean_ctor_get(x_491, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_491, 1);
lean_inc(x_509);
x_510 = lean_ctor_get(x_491, 2);
lean_inc(x_510);
x_511 = lean_ctor_get(x_491, 3);
lean_inc(x_511);
x_512 = lean_ctor_get(x_491, 4);
lean_inc(x_512);
x_513 = lean_ctor_get(x_492, 0);
lean_inc(x_513);
x_514 = lean_unsigned_to_nat(2u);
x_515 = lean_nat_mul(x_514, x_513);
x_516 = lean_nat_dec_lt(x_508, x_515);
lean_dec(x_515);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_508);
lean_free_object(x_4);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 lean_ctor_release(x_491, 2);
 lean_ctor_release(x_491, 3);
 lean_ctor_release(x_491, 4);
 x_517 = x_491;
} else {
 lean_dec_ref(x_491);
 x_517 = lean_box(0);
}
x_518 = lean_unsigned_to_nat(1u);
x_519 = lean_nat_add(x_518, x_499);
lean_dec(x_499);
x_520 = lean_nat_add(x_519, x_488);
lean_dec(x_488);
x_521 = lean_nat_add(x_518, x_513);
lean_dec(x_513);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_522 = lean_ctor_get(x_511, 0);
lean_inc(x_522);
x_523 = lean_nat_add(x_519, x_522);
lean_dec(x_522);
lean_dec(x_519);
lean_inc(x_496);
if (lean_is_scalar(x_517)) {
 x_524 = lean_alloc_ctor(0, 5, 0);
} else {
 x_524 = x_517;
}
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_497);
lean_ctor_set(x_524, 2, x_498);
lean_ctor_set(x_524, 3, x_496);
lean_ctor_set(x_524, 4, x_511);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 lean_ctor_release(x_496, 2);
 lean_ctor_release(x_496, 3);
 lean_ctor_release(x_496, 4);
 x_525 = x_496;
} else {
 lean_dec_ref(x_496);
 x_525 = lean_box(0);
}
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_526 = lean_ctor_get(x_512, 0);
lean_inc(x_526);
x_527 = lean_nat_add(x_521, x_526);
lean_dec(x_526);
lean_dec(x_521);
if (lean_is_scalar(x_525)) {
 x_528 = lean_alloc_ctor(0, 5, 0);
} else {
 x_528 = x_525;
}
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_489);
lean_ctor_set(x_528, 2, x_490);
lean_ctor_set(x_528, 3, x_512);
lean_ctor_set(x_528, 4, x_492);
x_529 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_529, 0, x_520);
lean_ctor_set(x_529, 1, x_509);
lean_ctor_set(x_529, 2, x_510);
lean_ctor_set(x_529, 3, x_524);
lean_ctor_set(x_529, 4, x_528);
return x_529;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_530 = lean_unsigned_to_nat(0u);
x_531 = lean_nat_add(x_521, x_530);
lean_dec(x_521);
if (lean_is_scalar(x_525)) {
 x_532 = lean_alloc_ctor(0, 5, 0);
} else {
 x_532 = x_525;
}
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_489);
lean_ctor_set(x_532, 2, x_490);
lean_ctor_set(x_532, 3, x_512);
lean_ctor_set(x_532, 4, x_492);
x_533 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_533, 0, x_520);
lean_ctor_set(x_533, 1, x_509);
lean_ctor_set(x_533, 2, x_510);
lean_ctor_set(x_533, 3, x_524);
lean_ctor_set(x_533, 4, x_532);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_534 = lean_unsigned_to_nat(0u);
x_535 = lean_nat_add(x_519, x_534);
lean_dec(x_519);
lean_inc(x_496);
if (lean_is_scalar(x_517)) {
 x_536 = lean_alloc_ctor(0, 5, 0);
} else {
 x_536 = x_517;
}
lean_ctor_set(x_536, 0, x_535);
lean_ctor_set(x_536, 1, x_497);
lean_ctor_set(x_536, 2, x_498);
lean_ctor_set(x_536, 3, x_496);
lean_ctor_set(x_536, 4, x_511);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 lean_ctor_release(x_496, 2);
 lean_ctor_release(x_496, 3);
 lean_ctor_release(x_496, 4);
 x_537 = x_496;
} else {
 lean_dec_ref(x_496);
 x_537 = lean_box(0);
}
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_538 = lean_ctor_get(x_512, 0);
lean_inc(x_538);
x_539 = lean_nat_add(x_521, x_538);
lean_dec(x_538);
lean_dec(x_521);
if (lean_is_scalar(x_537)) {
 x_540 = lean_alloc_ctor(0, 5, 0);
} else {
 x_540 = x_537;
}
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_489);
lean_ctor_set(x_540, 2, x_490);
lean_ctor_set(x_540, 3, x_512);
lean_ctor_set(x_540, 4, x_492);
x_541 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_541, 0, x_520);
lean_ctor_set(x_541, 1, x_509);
lean_ctor_set(x_541, 2, x_510);
lean_ctor_set(x_541, 3, x_536);
lean_ctor_set(x_541, 4, x_540);
return x_541;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_nat_add(x_521, x_534);
lean_dec(x_521);
if (lean_is_scalar(x_537)) {
 x_543 = lean_alloc_ctor(0, 5, 0);
} else {
 x_543 = x_537;
}
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_489);
lean_ctor_set(x_543, 2, x_490);
lean_ctor_set(x_543, 3, x_512);
lean_ctor_set(x_543, 4, x_492);
x_544 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_544, 0, x_520);
lean_ctor_set(x_544, 1, x_509);
lean_ctor_set(x_544, 2, x_510);
lean_ctor_set(x_544, 3, x_536);
lean_ctor_set(x_544, 4, x_543);
return x_544;
}
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
x_545 = lean_unsigned_to_nat(1u);
x_546 = lean_nat_add(x_545, x_499);
lean_dec(x_499);
x_547 = lean_nat_add(x_546, x_488);
lean_dec(x_488);
x_548 = lean_nat_add(x_546, x_508);
lean_dec(x_508);
lean_dec(x_546);
x_549 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_497);
lean_ctor_set(x_549, 2, x_498);
lean_ctor_set(x_549, 3, x_496);
lean_ctor_set(x_549, 4, x_491);
lean_ctor_set(x_4, 4, x_492);
lean_ctor_set(x_4, 3, x_549);
lean_ctor_set(x_4, 2, x_490);
lean_ctor_set(x_4, 1, x_489);
lean_ctor_set(x_4, 0, x_547);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_491) == 0)
{
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_550 = lean_ctor_get(x_495, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_495, 1);
lean_inc(x_551);
lean_dec(x_495);
x_552 = lean_ctor_get(x_491, 0);
lean_inc(x_552);
x_553 = lean_unsigned_to_nat(1u);
x_554 = lean_nat_add(x_553, x_488);
lean_dec(x_488);
x_555 = lean_nat_add(x_553, x_552);
lean_dec(x_552);
x_556 = lean_box(1);
if (lean_is_scalar(x_493)) {
 x_557 = lean_alloc_ctor(0, 5, 0);
} else {
 x_557 = x_493;
}
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_550);
lean_ctor_set(x_557, 2, x_551);
lean_ctor_set(x_557, 3, x_556);
lean_ctor_set(x_557, 4, x_491);
x_558 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_558, 0, x_554);
lean_ctor_set(x_558, 1, x_489);
lean_ctor_set(x_558, 2, x_490);
lean_ctor_set(x_558, 3, x_557);
lean_ctor_set(x_558, 4, x_492);
return x_558;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_488);
x_559 = lean_ctor_get(x_495, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_495, 1);
lean_inc(x_560);
lean_dec(x_495);
x_561 = lean_ctor_get(x_491, 1);
lean_inc(x_561);
x_562 = lean_ctor_get(x_491, 2);
lean_inc(x_562);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 lean_ctor_release(x_491, 2);
 lean_ctor_release(x_491, 3);
 lean_ctor_release(x_491, 4);
 x_563 = x_491;
} else {
 lean_dec_ref(x_491);
 x_563 = lean_box(0);
}
x_564 = lean_box(1);
x_565 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_563)) {
 x_566 = lean_alloc_ctor(0, 5, 0);
} else {
 x_566 = x_563;
}
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_559);
lean_ctor_set(x_566, 2, x_560);
lean_ctor_set(x_566, 3, x_564);
lean_ctor_set(x_566, 4, x_564);
if (lean_is_scalar(x_493)) {
 x_567 = lean_alloc_ctor(0, 5, 0);
} else {
 x_567 = x_493;
}
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_489);
lean_ctor_set(x_567, 2, x_490);
lean_ctor_set(x_567, 3, x_564);
lean_ctor_set(x_567, 4, x_564);
x_568 = lean_unsigned_to_nat(3u);
x_569 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_561);
lean_ctor_set(x_569, 2, x_562);
lean_ctor_set(x_569, 3, x_566);
lean_ctor_set(x_569, 4, x_567);
return x_569;
}
}
else
{
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_488);
x_570 = lean_ctor_get(x_495, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_495, 1);
lean_inc(x_571);
lean_dec(x_495);
x_572 = lean_box(1);
x_573 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_493)) {
 x_574 = lean_alloc_ctor(0, 5, 0);
} else {
 x_574 = x_493;
}
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_570);
lean_ctor_set(x_574, 2, x_571);
lean_ctor_set(x_574, 3, x_572);
lean_ctor_set(x_574, 4, x_572);
x_575 = lean_unsigned_to_nat(3u);
x_576 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_489);
lean_ctor_set(x_576, 2, x_490);
lean_ctor_set(x_576, 3, x_574);
lean_ctor_set(x_576, 4, x_492);
return x_576;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_577 = lean_ctor_get(x_495, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_495, 1);
lean_inc(x_578);
lean_dec(x_495);
if (lean_is_scalar(x_493)) {
 x_579 = lean_alloc_ctor(0, 5, 0);
} else {
 x_579 = x_493;
}
lean_ctor_set(x_579, 0, x_488);
lean_ctor_set(x_579, 1, x_489);
lean_ctor_set(x_579, 2, x_490);
lean_ctor_set(x_579, 3, x_492);
lean_ctor_set(x_579, 4, x_492);
x_580 = lean_box(1);
x_581 = lean_unsigned_to_nat(2u);
x_582 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_577);
lean_ctor_set(x_582, 2, x_578);
lean_ctor_set(x_582, 3, x_580);
lean_ctor_set(x_582, 4, x_579);
return x_582;
}
}
}
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_488);
x_583 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_489, x_490, x_491, x_492, lean_box(0), lean_box(0), lean_box(0));
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
x_586 = lean_ctor_get(x_583, 2);
lean_inc(x_586);
lean_dec(x_583);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
if (lean_is_scalar(x_493)) {
 x_587 = lean_alloc_ctor(0, 5, 0);
} else {
 x_587 = x_493;
}
lean_ctor_set(x_587, 0, x_483);
lean_ctor_set(x_587, 1, x_484);
lean_ctor_set(x_587, 2, x_485);
lean_ctor_set(x_587, 3, x_486);
lean_ctor_set(x_587, 4, x_487);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; 
x_588 = lean_ctor_get(x_586, 0);
lean_inc(x_588);
x_589 = lean_unsigned_to_nat(3u);
x_590 = lean_nat_mul(x_589, x_588);
x_591 = lean_nat_dec_lt(x_590, x_483);
lean_dec(x_590);
if (x_591 == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_484);
lean_free_object(x_4);
x_592 = lean_unsigned_to_nat(1u);
x_593 = lean_nat_add(x_592, x_483);
lean_dec(x_483);
x_594 = lean_nat_add(x_593, x_588);
lean_dec(x_588);
lean_dec(x_593);
x_595 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_595, 0, x_594);
lean_ctor_set(x_595, 1, x_584);
lean_ctor_set(x_595, 2, x_585);
lean_ctor_set(x_595, 3, x_587);
lean_ctor_set(x_595, 4, x_586);
return x_595;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
lean_dec(x_587);
x_596 = lean_ctor_get(x_486, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_487, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_487, 1);
lean_inc(x_598);
x_599 = lean_ctor_get(x_487, 2);
lean_inc(x_599);
x_600 = lean_ctor_get(x_487, 3);
lean_inc(x_600);
x_601 = lean_ctor_get(x_487, 4);
lean_inc(x_601);
x_602 = lean_unsigned_to_nat(2u);
x_603 = lean_nat_mul(x_602, x_596);
x_604 = lean_nat_dec_lt(x_597, x_603);
lean_dec(x_603);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_597);
lean_free_object(x_4);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 lean_ctor_release(x_487, 4);
 x_605 = x_487;
} else {
 lean_dec_ref(x_487);
 x_605 = lean_box(0);
}
x_606 = lean_unsigned_to_nat(1u);
x_607 = lean_nat_add(x_606, x_483);
lean_dec(x_483);
x_608 = lean_nat_add(x_607, x_588);
lean_dec(x_607);
x_609 = lean_nat_add(x_606, x_596);
lean_dec(x_596);
x_610 = lean_nat_add(x_606, x_588);
lean_dec(x_588);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_611 = lean_ctor_get(x_600, 0);
lean_inc(x_611);
x_612 = lean_nat_add(x_609, x_611);
lean_dec(x_611);
lean_dec(x_609);
lean_inc(x_486);
if (lean_is_scalar(x_605)) {
 x_613 = lean_alloc_ctor(0, 5, 0);
} else {
 x_613 = x_605;
}
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_484);
lean_ctor_set(x_613, 2, x_485);
lean_ctor_set(x_613, 3, x_486);
lean_ctor_set(x_613, 4, x_600);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 lean_ctor_release(x_486, 2);
 lean_ctor_release(x_486, 3);
 lean_ctor_release(x_486, 4);
 x_614 = x_486;
} else {
 lean_dec_ref(x_486);
 x_614 = lean_box(0);
}
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_615 = lean_ctor_get(x_601, 0);
lean_inc(x_615);
x_616 = lean_nat_add(x_610, x_615);
lean_dec(x_615);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_614)) {
 x_617 = lean_alloc_ctor(0, 5, 0);
} else {
 x_617 = x_614;
}
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_584);
lean_ctor_set(x_617, 2, x_585);
lean_ctor_set(x_617, 3, x_601);
lean_ctor_set(x_617, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_618 = x_586;
} else {
 lean_dec_ref(x_586);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(0, 5, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_608);
lean_ctor_set(x_619, 1, x_598);
lean_ctor_set(x_619, 2, x_599);
lean_ctor_set(x_619, 3, x_613);
lean_ctor_set(x_619, 4, x_617);
return x_619;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_620 = lean_unsigned_to_nat(0u);
x_621 = lean_nat_add(x_610, x_620);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_614)) {
 x_622 = lean_alloc_ctor(0, 5, 0);
} else {
 x_622 = x_614;
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_584);
lean_ctor_set(x_622, 2, x_585);
lean_ctor_set(x_622, 3, x_601);
lean_ctor_set(x_622, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_623 = x_586;
} else {
 lean_dec_ref(x_586);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(0, 5, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_608);
lean_ctor_set(x_624, 1, x_598);
lean_ctor_set(x_624, 2, x_599);
lean_ctor_set(x_624, 3, x_613);
lean_ctor_set(x_624, 4, x_622);
return x_624;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_625 = lean_unsigned_to_nat(0u);
x_626 = lean_nat_add(x_609, x_625);
lean_dec(x_609);
lean_inc(x_486);
if (lean_is_scalar(x_605)) {
 x_627 = lean_alloc_ctor(0, 5, 0);
} else {
 x_627 = x_605;
}
lean_ctor_set(x_627, 0, x_626);
lean_ctor_set(x_627, 1, x_484);
lean_ctor_set(x_627, 2, x_485);
lean_ctor_set(x_627, 3, x_486);
lean_ctor_set(x_627, 4, x_600);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 lean_ctor_release(x_486, 2);
 lean_ctor_release(x_486, 3);
 lean_ctor_release(x_486, 4);
 x_628 = x_486;
} else {
 lean_dec_ref(x_486);
 x_628 = lean_box(0);
}
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_629 = lean_ctor_get(x_601, 0);
lean_inc(x_629);
x_630 = lean_nat_add(x_610, x_629);
lean_dec(x_629);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_628)) {
 x_631 = lean_alloc_ctor(0, 5, 0);
} else {
 x_631 = x_628;
}
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_584);
lean_ctor_set(x_631, 2, x_585);
lean_ctor_set(x_631, 3, x_601);
lean_ctor_set(x_631, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_632 = x_586;
} else {
 lean_dec_ref(x_586);
 x_632 = lean_box(0);
}
if (lean_is_scalar(x_632)) {
 x_633 = lean_alloc_ctor(0, 5, 0);
} else {
 x_633 = x_632;
}
lean_ctor_set(x_633, 0, x_608);
lean_ctor_set(x_633, 1, x_598);
lean_ctor_set(x_633, 2, x_599);
lean_ctor_set(x_633, 3, x_627);
lean_ctor_set(x_633, 4, x_631);
return x_633;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_634 = lean_nat_add(x_610, x_625);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_628)) {
 x_635 = lean_alloc_ctor(0, 5, 0);
} else {
 x_635 = x_628;
}
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_584);
lean_ctor_set(x_635, 2, x_585);
lean_ctor_set(x_635, 3, x_601);
lean_ctor_set(x_635, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_636 = x_586;
} else {
 lean_dec_ref(x_586);
 x_636 = lean_box(0);
}
if (lean_is_scalar(x_636)) {
 x_637 = lean_alloc_ctor(0, 5, 0);
} else {
 x_637 = x_636;
}
lean_ctor_set(x_637, 0, x_608);
lean_ctor_set(x_637, 1, x_598);
lean_ctor_set(x_637, 2, x_599);
lean_ctor_set(x_637, 3, x_627);
lean_ctor_set(x_637, 4, x_635);
return x_637;
}
}
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_596);
x_638 = lean_unsigned_to_nat(1u);
x_639 = lean_nat_add(x_638, x_483);
lean_dec(x_483);
x_640 = lean_nat_add(x_639, x_588);
lean_dec(x_639);
x_641 = lean_nat_add(x_638, x_588);
lean_dec(x_588);
x_642 = lean_nat_add(x_641, x_597);
lean_dec(x_597);
lean_dec(x_641);
x_643 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_584);
lean_ctor_set(x_643, 2, x_585);
lean_ctor_set(x_643, 3, x_487);
lean_ctor_set(x_643, 4, x_586);
lean_ctor_set(x_4, 4, x_643);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_640);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_486) == 0)
{
lean_dec(x_587);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_644 = lean_ctor_get(x_487, 0);
lean_inc(x_644);
x_645 = lean_unsigned_to_nat(1u);
x_646 = lean_nat_add(x_645, x_483);
lean_dec(x_483);
x_647 = lean_nat_add(x_645, x_644);
lean_dec(x_644);
x_648 = lean_box(1);
x_649 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_649, 0, x_647);
lean_ctor_set(x_649, 1, x_584);
lean_ctor_set(x_649, 2, x_585);
lean_ctor_set(x_649, 3, x_487);
lean_ctor_set(x_649, 4, x_648);
lean_ctor_set(x_4, 4, x_649);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_646);
return x_4;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_483);
x_650 = lean_box(1);
x_651 = lean_unsigned_to_nat(1u);
x_652 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_584);
lean_ctor_set(x_652, 2, x_585);
lean_ctor_set(x_652, 3, x_650);
lean_ctor_set(x_652, 4, x_650);
x_653 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_652);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_653);
return x_4;
}
}
else
{
lean_dec(x_483);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_587);
x_654 = lean_ctor_get(x_487, 1);
lean_inc(x_654);
x_655 = lean_ctor_get(x_487, 2);
lean_inc(x_655);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 lean_ctor_release(x_487, 4);
 x_656 = x_487;
} else {
 lean_dec_ref(x_487);
 x_656 = lean_box(0);
}
x_657 = lean_box(1);
x_658 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_656)) {
 x_659 = lean_alloc_ctor(0, 5, 0);
} else {
 x_659 = x_656;
}
lean_ctor_set(x_659, 0, x_658);
lean_ctor_set(x_659, 1, x_484);
lean_ctor_set(x_659, 2, x_485);
lean_ctor_set(x_659, 3, x_657);
lean_ctor_set(x_659, 4, x_657);
x_660 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_584);
lean_ctor_set(x_660, 2, x_585);
lean_ctor_set(x_660, 3, x_657);
lean_ctor_set(x_660, 4, x_657);
x_661 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_660);
lean_ctor_set(x_4, 3, x_659);
lean_ctor_set(x_4, 2, x_655);
lean_ctor_set(x_4, 1, x_654);
lean_ctor_set(x_4, 0, x_661);
return x_4;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_485);
lean_dec(x_484);
lean_free_object(x_4);
x_662 = lean_box(1);
x_663 = lean_unsigned_to_nat(2u);
x_664 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_584);
lean_ctor_set(x_664, 2, x_585);
lean_ctor_set(x_664, 3, x_587);
lean_ctor_set(x_664, 4, x_662);
return x_664;
}
}
}
}
}
}
else
{
lean_free_object(x_4);
return x_10;
}
}
else
{
lean_free_object(x_4);
return x_11;
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_17, 0);
lean_inc(x_665);
lean_dec(x_17);
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
lean_dec(x_665);
lean_ctor_set(x_4, 2, x_667);
lean_ctor_set(x_4, 1, x_666);
return x_4;
}
}
default: 
{
lean_object* x_668; lean_object* x_669; 
lean_free_object(x_4);
lean_dec(x_7);
x_668 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_alter_u2098___spec__1___rarg(x_1, x_2, x_3, x_11, lean_box(0));
x_669 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_8, x_9, x_10, x_668, lean_box(0), lean_box(0), lean_box(0));
return x_669;
}
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; 
x_670 = lean_ctor_get(x_4, 0);
x_671 = lean_ctor_get(x_4, 1);
x_672 = lean_ctor_get(x_4, 2);
x_673 = lean_ctor_get(x_4, 3);
x_674 = lean_ctor_get(x_4, 4);
lean_inc(x_674);
lean_inc(x_673);
lean_inc(x_672);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_671);
lean_inc(x_2);
x_675 = lean_apply_2(x_1, x_2, x_671);
x_676 = lean_unbox(x_675);
lean_dec(x_675);
switch (x_676) {
case 0:
{
lean_object* x_677; lean_object* x_678; 
lean_dec(x_670);
x_677 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_alter_u2098___spec__1___rarg(x_1, x_2, x_3, x_673, lean_box(0));
x_678 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_671, x_672, x_677, x_674, lean_box(0), lean_box(0), lean_box(0));
return x_678;
}
case 1:
{
lean_object* x_679; lean_object* x_680; 
lean_dec(x_2);
lean_dec(x_1);
x_679 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_671, x_672, lean_box(0));
x_680 = lean_apply_1(x_3, x_679);
if (lean_obj_tag(x_680) == 0)
{
lean_dec(x_670);
if (lean_obj_tag(x_673) == 0)
{
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; uint8_t x_693; 
x_681 = lean_ctor_get(x_673, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_673, 1);
lean_inc(x_682);
x_683 = lean_ctor_get(x_673, 2);
lean_inc(x_683);
x_684 = lean_ctor_get(x_673, 3);
lean_inc(x_684);
x_685 = lean_ctor_get(x_673, 4);
lean_inc(x_685);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 lean_ctor_release(x_673, 2);
 lean_ctor_release(x_673, 3);
 lean_ctor_release(x_673, 4);
 x_686 = x_673;
} else {
 lean_dec_ref(x_673);
 x_686 = lean_box(0);
}
x_687 = lean_ctor_get(x_674, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_674, 1);
lean_inc(x_688);
x_689 = lean_ctor_get(x_674, 2);
lean_inc(x_689);
x_690 = lean_ctor_get(x_674, 3);
lean_inc(x_690);
x_691 = lean_ctor_get(x_674, 4);
lean_inc(x_691);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 lean_ctor_release(x_674, 4);
 x_692 = x_674;
} else {
 lean_dec_ref(x_674);
 x_692 = lean_box(0);
}
x_693 = lean_nat_dec_lt(x_681, x_687);
if (x_693 == 0)
{
lean_object* x_694; lean_object* x_695; 
lean_dec(x_681);
x_694 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_682, x_683, x_684, x_685, lean_box(0), lean_box(0), lean_box(0));
x_695 = lean_ctor_get(x_694, 2);
lean_inc(x_695);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; 
x_696 = lean_ctor_get(x_694, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_694, 1);
lean_inc(x_697);
lean_dec(x_694);
x_698 = lean_ctor_get(x_695, 0);
lean_inc(x_698);
lean_inc(x_691);
lean_inc(x_690);
lean_inc(x_689);
lean_inc(x_688);
lean_inc(x_687);
if (lean_is_scalar(x_692)) {
 x_699 = lean_alloc_ctor(0, 5, 0);
} else {
 x_699 = x_692;
}
lean_ctor_set(x_699, 0, x_687);
lean_ctor_set(x_699, 1, x_688);
lean_ctor_set(x_699, 2, x_689);
lean_ctor_set(x_699, 3, x_690);
lean_ctor_set(x_699, 4, x_691);
x_700 = lean_unsigned_to_nat(3u);
x_701 = lean_nat_mul(x_700, x_698);
x_702 = lean_nat_dec_lt(x_701, x_687);
lean_dec(x_701);
if (x_702 == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_dec(x_691);
lean_dec(x_690);
lean_dec(x_689);
lean_dec(x_688);
x_703 = lean_unsigned_to_nat(1u);
x_704 = lean_nat_add(x_703, x_698);
lean_dec(x_698);
x_705 = lean_nat_add(x_704, x_687);
lean_dec(x_687);
lean_dec(x_704);
if (lean_is_scalar(x_686)) {
 x_706 = lean_alloc_ctor(0, 5, 0);
} else {
 x_706 = x_686;
}
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_696);
lean_ctor_set(x_706, 2, x_697);
lean_ctor_set(x_706, 3, x_695);
lean_ctor_set(x_706, 4, x_699);
return x_706;
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; 
lean_dec(x_699);
x_707 = lean_ctor_get(x_690, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_690, 1);
lean_inc(x_708);
x_709 = lean_ctor_get(x_690, 2);
lean_inc(x_709);
x_710 = lean_ctor_get(x_690, 3);
lean_inc(x_710);
x_711 = lean_ctor_get(x_690, 4);
lean_inc(x_711);
x_712 = lean_ctor_get(x_691, 0);
lean_inc(x_712);
x_713 = lean_unsigned_to_nat(2u);
x_714 = lean_nat_mul(x_713, x_712);
x_715 = lean_nat_dec_lt(x_707, x_714);
lean_dec(x_714);
if (x_715 == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_707);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 lean_ctor_release(x_690, 2);
 lean_ctor_release(x_690, 3);
 lean_ctor_release(x_690, 4);
 x_716 = x_690;
} else {
 lean_dec_ref(x_690);
 x_716 = lean_box(0);
}
x_717 = lean_unsigned_to_nat(1u);
x_718 = lean_nat_add(x_717, x_698);
lean_dec(x_698);
x_719 = lean_nat_add(x_718, x_687);
lean_dec(x_687);
x_720 = lean_nat_add(x_717, x_712);
lean_dec(x_712);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_721 = lean_ctor_get(x_710, 0);
lean_inc(x_721);
x_722 = lean_nat_add(x_718, x_721);
lean_dec(x_721);
lean_dec(x_718);
lean_inc(x_695);
if (lean_is_scalar(x_716)) {
 x_723 = lean_alloc_ctor(0, 5, 0);
} else {
 x_723 = x_716;
}
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_696);
lean_ctor_set(x_723, 2, x_697);
lean_ctor_set(x_723, 3, x_695);
lean_ctor_set(x_723, 4, x_710);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 lean_ctor_release(x_695, 2);
 lean_ctor_release(x_695, 3);
 lean_ctor_release(x_695, 4);
 x_724 = x_695;
} else {
 lean_dec_ref(x_695);
 x_724 = lean_box(0);
}
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_725 = lean_ctor_get(x_711, 0);
lean_inc(x_725);
x_726 = lean_nat_add(x_720, x_725);
lean_dec(x_725);
lean_dec(x_720);
if (lean_is_scalar(x_724)) {
 x_727 = lean_alloc_ctor(0, 5, 0);
} else {
 x_727 = x_724;
}
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_688);
lean_ctor_set(x_727, 2, x_689);
lean_ctor_set(x_727, 3, x_711);
lean_ctor_set(x_727, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_728 = lean_alloc_ctor(0, 5, 0);
} else {
 x_728 = x_686;
}
lean_ctor_set(x_728, 0, x_719);
lean_ctor_set(x_728, 1, x_708);
lean_ctor_set(x_728, 2, x_709);
lean_ctor_set(x_728, 3, x_723);
lean_ctor_set(x_728, 4, x_727);
return x_728;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_729 = lean_unsigned_to_nat(0u);
x_730 = lean_nat_add(x_720, x_729);
lean_dec(x_720);
if (lean_is_scalar(x_724)) {
 x_731 = lean_alloc_ctor(0, 5, 0);
} else {
 x_731 = x_724;
}
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_688);
lean_ctor_set(x_731, 2, x_689);
lean_ctor_set(x_731, 3, x_711);
lean_ctor_set(x_731, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_732 = lean_alloc_ctor(0, 5, 0);
} else {
 x_732 = x_686;
}
lean_ctor_set(x_732, 0, x_719);
lean_ctor_set(x_732, 1, x_708);
lean_ctor_set(x_732, 2, x_709);
lean_ctor_set(x_732, 3, x_723);
lean_ctor_set(x_732, 4, x_731);
return x_732;
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_733 = lean_unsigned_to_nat(0u);
x_734 = lean_nat_add(x_718, x_733);
lean_dec(x_718);
lean_inc(x_695);
if (lean_is_scalar(x_716)) {
 x_735 = lean_alloc_ctor(0, 5, 0);
} else {
 x_735 = x_716;
}
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_696);
lean_ctor_set(x_735, 2, x_697);
lean_ctor_set(x_735, 3, x_695);
lean_ctor_set(x_735, 4, x_710);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 lean_ctor_release(x_695, 2);
 lean_ctor_release(x_695, 3);
 lean_ctor_release(x_695, 4);
 x_736 = x_695;
} else {
 lean_dec_ref(x_695);
 x_736 = lean_box(0);
}
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_737 = lean_ctor_get(x_711, 0);
lean_inc(x_737);
x_738 = lean_nat_add(x_720, x_737);
lean_dec(x_737);
lean_dec(x_720);
if (lean_is_scalar(x_736)) {
 x_739 = lean_alloc_ctor(0, 5, 0);
} else {
 x_739 = x_736;
}
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_688);
lean_ctor_set(x_739, 2, x_689);
lean_ctor_set(x_739, 3, x_711);
lean_ctor_set(x_739, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_740 = lean_alloc_ctor(0, 5, 0);
} else {
 x_740 = x_686;
}
lean_ctor_set(x_740, 0, x_719);
lean_ctor_set(x_740, 1, x_708);
lean_ctor_set(x_740, 2, x_709);
lean_ctor_set(x_740, 3, x_735);
lean_ctor_set(x_740, 4, x_739);
return x_740;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_741 = lean_nat_add(x_720, x_733);
lean_dec(x_720);
if (lean_is_scalar(x_736)) {
 x_742 = lean_alloc_ctor(0, 5, 0);
} else {
 x_742 = x_736;
}
lean_ctor_set(x_742, 0, x_741);
lean_ctor_set(x_742, 1, x_688);
lean_ctor_set(x_742, 2, x_689);
lean_ctor_set(x_742, 3, x_711);
lean_ctor_set(x_742, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_743 = lean_alloc_ctor(0, 5, 0);
} else {
 x_743 = x_686;
}
lean_ctor_set(x_743, 0, x_719);
lean_ctor_set(x_743, 1, x_708);
lean_ctor_set(x_743, 2, x_709);
lean_ctor_set(x_743, 3, x_735);
lean_ctor_set(x_743, 4, x_742);
return x_743;
}
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_dec(x_712);
lean_dec(x_711);
lean_dec(x_710);
lean_dec(x_709);
lean_dec(x_708);
x_744 = lean_unsigned_to_nat(1u);
x_745 = lean_nat_add(x_744, x_698);
lean_dec(x_698);
x_746 = lean_nat_add(x_745, x_687);
lean_dec(x_687);
x_747 = lean_nat_add(x_745, x_707);
lean_dec(x_707);
lean_dec(x_745);
if (lean_is_scalar(x_686)) {
 x_748 = lean_alloc_ctor(0, 5, 0);
} else {
 x_748 = x_686;
}
lean_ctor_set(x_748, 0, x_747);
lean_ctor_set(x_748, 1, x_696);
lean_ctor_set(x_748, 2, x_697);
lean_ctor_set(x_748, 3, x_695);
lean_ctor_set(x_748, 4, x_690);
x_749 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_749, 0, x_746);
lean_ctor_set(x_749, 1, x_688);
lean_ctor_set(x_749, 2, x_689);
lean_ctor_set(x_749, 3, x_748);
lean_ctor_set(x_749, 4, x_691);
return x_749;
}
}
}
else
{
if (lean_obj_tag(x_690) == 0)
{
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_750 = lean_ctor_get(x_694, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_694, 1);
lean_inc(x_751);
lean_dec(x_694);
x_752 = lean_ctor_get(x_690, 0);
lean_inc(x_752);
x_753 = lean_unsigned_to_nat(1u);
x_754 = lean_nat_add(x_753, x_687);
lean_dec(x_687);
x_755 = lean_nat_add(x_753, x_752);
lean_dec(x_752);
x_756 = lean_box(1);
if (lean_is_scalar(x_692)) {
 x_757 = lean_alloc_ctor(0, 5, 0);
} else {
 x_757 = x_692;
}
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set(x_757, 1, x_750);
lean_ctor_set(x_757, 2, x_751);
lean_ctor_set(x_757, 3, x_756);
lean_ctor_set(x_757, 4, x_690);
if (lean_is_scalar(x_686)) {
 x_758 = lean_alloc_ctor(0, 5, 0);
} else {
 x_758 = x_686;
}
lean_ctor_set(x_758, 0, x_754);
lean_ctor_set(x_758, 1, x_688);
lean_ctor_set(x_758, 2, x_689);
lean_ctor_set(x_758, 3, x_757);
lean_ctor_set(x_758, 4, x_691);
return x_758;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_687);
x_759 = lean_ctor_get(x_694, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_694, 1);
lean_inc(x_760);
lean_dec(x_694);
x_761 = lean_ctor_get(x_690, 1);
lean_inc(x_761);
x_762 = lean_ctor_get(x_690, 2);
lean_inc(x_762);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 lean_ctor_release(x_690, 2);
 lean_ctor_release(x_690, 3);
 lean_ctor_release(x_690, 4);
 x_763 = x_690;
} else {
 lean_dec_ref(x_690);
 x_763 = lean_box(0);
}
x_764 = lean_box(1);
x_765 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_763)) {
 x_766 = lean_alloc_ctor(0, 5, 0);
} else {
 x_766 = x_763;
}
lean_ctor_set(x_766, 0, x_765);
lean_ctor_set(x_766, 1, x_759);
lean_ctor_set(x_766, 2, x_760);
lean_ctor_set(x_766, 3, x_764);
lean_ctor_set(x_766, 4, x_764);
if (lean_is_scalar(x_692)) {
 x_767 = lean_alloc_ctor(0, 5, 0);
} else {
 x_767 = x_692;
}
lean_ctor_set(x_767, 0, x_765);
lean_ctor_set(x_767, 1, x_688);
lean_ctor_set(x_767, 2, x_689);
lean_ctor_set(x_767, 3, x_764);
lean_ctor_set(x_767, 4, x_764);
x_768 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_686)) {
 x_769 = lean_alloc_ctor(0, 5, 0);
} else {
 x_769 = x_686;
}
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_761);
lean_ctor_set(x_769, 2, x_762);
lean_ctor_set(x_769, 3, x_766);
lean_ctor_set(x_769, 4, x_767);
return x_769;
}
}
else
{
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
lean_dec(x_687);
x_770 = lean_ctor_get(x_694, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_694, 1);
lean_inc(x_771);
lean_dec(x_694);
x_772 = lean_box(1);
x_773 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_692)) {
 x_774 = lean_alloc_ctor(0, 5, 0);
} else {
 x_774 = x_692;
}
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_770);
lean_ctor_set(x_774, 2, x_771);
lean_ctor_set(x_774, 3, x_772);
lean_ctor_set(x_774, 4, x_772);
x_775 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_686)) {
 x_776 = lean_alloc_ctor(0, 5, 0);
} else {
 x_776 = x_686;
}
lean_ctor_set(x_776, 0, x_775);
lean_ctor_set(x_776, 1, x_688);
lean_ctor_set(x_776, 2, x_689);
lean_ctor_set(x_776, 3, x_774);
lean_ctor_set(x_776, 4, x_691);
return x_776;
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_777 = lean_ctor_get(x_694, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_694, 1);
lean_inc(x_778);
lean_dec(x_694);
if (lean_is_scalar(x_692)) {
 x_779 = lean_alloc_ctor(0, 5, 0);
} else {
 x_779 = x_692;
}
lean_ctor_set(x_779, 0, x_687);
lean_ctor_set(x_779, 1, x_688);
lean_ctor_set(x_779, 2, x_689);
lean_ctor_set(x_779, 3, x_691);
lean_ctor_set(x_779, 4, x_691);
x_780 = lean_box(1);
x_781 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_686)) {
 x_782 = lean_alloc_ctor(0, 5, 0);
} else {
 x_782 = x_686;
}
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_777);
lean_ctor_set(x_782, 2, x_778);
lean_ctor_set(x_782, 3, x_780);
lean_ctor_set(x_782, 4, x_779);
return x_782;
}
}
}
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
lean_dec(x_687);
x_783 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_688, x_689, x_690, x_691, lean_box(0), lean_box(0), lean_box(0));
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
x_786 = lean_ctor_get(x_783, 2);
lean_inc(x_786);
lean_dec(x_783);
lean_inc(x_685);
lean_inc(x_684);
lean_inc(x_683);
lean_inc(x_682);
lean_inc(x_681);
if (lean_is_scalar(x_692)) {
 x_787 = lean_alloc_ctor(0, 5, 0);
} else {
 x_787 = x_692;
}
lean_ctor_set(x_787, 0, x_681);
lean_ctor_set(x_787, 1, x_682);
lean_ctor_set(x_787, 2, x_683);
lean_ctor_set(x_787, 3, x_684);
lean_ctor_set(x_787, 4, x_685);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; 
x_788 = lean_ctor_get(x_786, 0);
lean_inc(x_788);
x_789 = lean_unsigned_to_nat(3u);
x_790 = lean_nat_mul(x_789, x_788);
x_791 = lean_nat_dec_lt(x_790, x_681);
lean_dec(x_790);
if (x_791 == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_683);
lean_dec(x_682);
x_792 = lean_unsigned_to_nat(1u);
x_793 = lean_nat_add(x_792, x_681);
lean_dec(x_681);
x_794 = lean_nat_add(x_793, x_788);
lean_dec(x_788);
lean_dec(x_793);
if (lean_is_scalar(x_686)) {
 x_795 = lean_alloc_ctor(0, 5, 0);
} else {
 x_795 = x_686;
}
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_784);
lean_ctor_set(x_795, 2, x_785);
lean_ctor_set(x_795, 3, x_787);
lean_ctor_set(x_795, 4, x_786);
return x_795;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; uint8_t x_804; 
lean_dec(x_787);
x_796 = lean_ctor_get(x_684, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_685, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_685, 1);
lean_inc(x_798);
x_799 = lean_ctor_get(x_685, 2);
lean_inc(x_799);
x_800 = lean_ctor_get(x_685, 3);
lean_inc(x_800);
x_801 = lean_ctor_get(x_685, 4);
lean_inc(x_801);
x_802 = lean_unsigned_to_nat(2u);
x_803 = lean_nat_mul(x_802, x_796);
x_804 = lean_nat_dec_lt(x_797, x_803);
lean_dec(x_803);
if (x_804 == 0)
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_797);
lean_dec(x_686);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 lean_ctor_release(x_685, 2);
 lean_ctor_release(x_685, 3);
 lean_ctor_release(x_685, 4);
 x_805 = x_685;
} else {
 lean_dec_ref(x_685);
 x_805 = lean_box(0);
}
x_806 = lean_unsigned_to_nat(1u);
x_807 = lean_nat_add(x_806, x_681);
lean_dec(x_681);
x_808 = lean_nat_add(x_807, x_788);
lean_dec(x_807);
x_809 = lean_nat_add(x_806, x_796);
lean_dec(x_796);
x_810 = lean_nat_add(x_806, x_788);
lean_dec(x_788);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_811 = lean_ctor_get(x_800, 0);
lean_inc(x_811);
x_812 = lean_nat_add(x_809, x_811);
lean_dec(x_811);
lean_dec(x_809);
lean_inc(x_684);
if (lean_is_scalar(x_805)) {
 x_813 = lean_alloc_ctor(0, 5, 0);
} else {
 x_813 = x_805;
}
lean_ctor_set(x_813, 0, x_812);
lean_ctor_set(x_813, 1, x_682);
lean_ctor_set(x_813, 2, x_683);
lean_ctor_set(x_813, 3, x_684);
lean_ctor_set(x_813, 4, x_800);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 lean_ctor_release(x_684, 2);
 lean_ctor_release(x_684, 3);
 lean_ctor_release(x_684, 4);
 x_814 = x_684;
} else {
 lean_dec_ref(x_684);
 x_814 = lean_box(0);
}
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_815 = lean_ctor_get(x_801, 0);
lean_inc(x_815);
x_816 = lean_nat_add(x_810, x_815);
lean_dec(x_815);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_814)) {
 x_817 = lean_alloc_ctor(0, 5, 0);
} else {
 x_817 = x_814;
}
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_784);
lean_ctor_set(x_817, 2, x_785);
lean_ctor_set(x_817, 3, x_801);
lean_ctor_set(x_817, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_818 = x_786;
} else {
 lean_dec_ref(x_786);
 x_818 = lean_box(0);
}
if (lean_is_scalar(x_818)) {
 x_819 = lean_alloc_ctor(0, 5, 0);
} else {
 x_819 = x_818;
}
lean_ctor_set(x_819, 0, x_808);
lean_ctor_set(x_819, 1, x_798);
lean_ctor_set(x_819, 2, x_799);
lean_ctor_set(x_819, 3, x_813);
lean_ctor_set(x_819, 4, x_817);
return x_819;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_820 = lean_unsigned_to_nat(0u);
x_821 = lean_nat_add(x_810, x_820);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_814)) {
 x_822 = lean_alloc_ctor(0, 5, 0);
} else {
 x_822 = x_814;
}
lean_ctor_set(x_822, 0, x_821);
lean_ctor_set(x_822, 1, x_784);
lean_ctor_set(x_822, 2, x_785);
lean_ctor_set(x_822, 3, x_801);
lean_ctor_set(x_822, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_823 = x_786;
} else {
 lean_dec_ref(x_786);
 x_823 = lean_box(0);
}
if (lean_is_scalar(x_823)) {
 x_824 = lean_alloc_ctor(0, 5, 0);
} else {
 x_824 = x_823;
}
lean_ctor_set(x_824, 0, x_808);
lean_ctor_set(x_824, 1, x_798);
lean_ctor_set(x_824, 2, x_799);
lean_ctor_set(x_824, 3, x_813);
lean_ctor_set(x_824, 4, x_822);
return x_824;
}
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_825 = lean_unsigned_to_nat(0u);
x_826 = lean_nat_add(x_809, x_825);
lean_dec(x_809);
lean_inc(x_684);
if (lean_is_scalar(x_805)) {
 x_827 = lean_alloc_ctor(0, 5, 0);
} else {
 x_827 = x_805;
}
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_682);
lean_ctor_set(x_827, 2, x_683);
lean_ctor_set(x_827, 3, x_684);
lean_ctor_set(x_827, 4, x_800);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 lean_ctor_release(x_684, 2);
 lean_ctor_release(x_684, 3);
 lean_ctor_release(x_684, 4);
 x_828 = x_684;
} else {
 lean_dec_ref(x_684);
 x_828 = lean_box(0);
}
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_829 = lean_ctor_get(x_801, 0);
lean_inc(x_829);
x_830 = lean_nat_add(x_810, x_829);
lean_dec(x_829);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_828)) {
 x_831 = lean_alloc_ctor(0, 5, 0);
} else {
 x_831 = x_828;
}
lean_ctor_set(x_831, 0, x_830);
lean_ctor_set(x_831, 1, x_784);
lean_ctor_set(x_831, 2, x_785);
lean_ctor_set(x_831, 3, x_801);
lean_ctor_set(x_831, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_832 = x_786;
} else {
 lean_dec_ref(x_786);
 x_832 = lean_box(0);
}
if (lean_is_scalar(x_832)) {
 x_833 = lean_alloc_ctor(0, 5, 0);
} else {
 x_833 = x_832;
}
lean_ctor_set(x_833, 0, x_808);
lean_ctor_set(x_833, 1, x_798);
lean_ctor_set(x_833, 2, x_799);
lean_ctor_set(x_833, 3, x_827);
lean_ctor_set(x_833, 4, x_831);
return x_833;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_834 = lean_nat_add(x_810, x_825);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_828)) {
 x_835 = lean_alloc_ctor(0, 5, 0);
} else {
 x_835 = x_828;
}
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_784);
lean_ctor_set(x_835, 2, x_785);
lean_ctor_set(x_835, 3, x_801);
lean_ctor_set(x_835, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_836 = x_786;
} else {
 lean_dec_ref(x_786);
 x_836 = lean_box(0);
}
if (lean_is_scalar(x_836)) {
 x_837 = lean_alloc_ctor(0, 5, 0);
} else {
 x_837 = x_836;
}
lean_ctor_set(x_837, 0, x_808);
lean_ctor_set(x_837, 1, x_798);
lean_ctor_set(x_837, 2, x_799);
lean_ctor_set(x_837, 3, x_827);
lean_ctor_set(x_837, 4, x_835);
return x_837;
}
}
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
lean_dec(x_801);
lean_dec(x_800);
lean_dec(x_799);
lean_dec(x_798);
lean_dec(x_796);
x_838 = lean_unsigned_to_nat(1u);
x_839 = lean_nat_add(x_838, x_681);
lean_dec(x_681);
x_840 = lean_nat_add(x_839, x_788);
lean_dec(x_839);
x_841 = lean_nat_add(x_838, x_788);
lean_dec(x_788);
x_842 = lean_nat_add(x_841, x_797);
lean_dec(x_797);
lean_dec(x_841);
if (lean_is_scalar(x_686)) {
 x_843 = lean_alloc_ctor(0, 5, 0);
} else {
 x_843 = x_686;
}
lean_ctor_set(x_843, 0, x_842);
lean_ctor_set(x_843, 1, x_784);
lean_ctor_set(x_843, 2, x_785);
lean_ctor_set(x_843, 3, x_685);
lean_ctor_set(x_843, 4, x_786);
x_844 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_844, 0, x_840);
lean_ctor_set(x_844, 1, x_682);
lean_ctor_set(x_844, 2, x_683);
lean_ctor_set(x_844, 3, x_684);
lean_ctor_set(x_844, 4, x_843);
return x_844;
}
}
}
else
{
if (lean_obj_tag(x_684) == 0)
{
lean_dec(x_787);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_845 = lean_ctor_get(x_685, 0);
lean_inc(x_845);
x_846 = lean_unsigned_to_nat(1u);
x_847 = lean_nat_add(x_846, x_681);
lean_dec(x_681);
x_848 = lean_nat_add(x_846, x_845);
lean_dec(x_845);
x_849 = lean_box(1);
if (lean_is_scalar(x_686)) {
 x_850 = lean_alloc_ctor(0, 5, 0);
} else {
 x_850 = x_686;
}
lean_ctor_set(x_850, 0, x_848);
lean_ctor_set(x_850, 1, x_784);
lean_ctor_set(x_850, 2, x_785);
lean_ctor_set(x_850, 3, x_685);
lean_ctor_set(x_850, 4, x_849);
x_851 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_851, 0, x_847);
lean_ctor_set(x_851, 1, x_682);
lean_ctor_set(x_851, 2, x_683);
lean_ctor_set(x_851, 3, x_684);
lean_ctor_set(x_851, 4, x_850);
return x_851;
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_681);
x_852 = lean_box(1);
x_853 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_686)) {
 x_854 = lean_alloc_ctor(0, 5, 0);
} else {
 x_854 = x_686;
}
lean_ctor_set(x_854, 0, x_853);
lean_ctor_set(x_854, 1, x_784);
lean_ctor_set(x_854, 2, x_785);
lean_ctor_set(x_854, 3, x_852);
lean_ctor_set(x_854, 4, x_852);
x_855 = lean_unsigned_to_nat(3u);
x_856 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_682);
lean_ctor_set(x_856, 2, x_683);
lean_ctor_set(x_856, 3, x_684);
lean_ctor_set(x_856, 4, x_854);
return x_856;
}
}
else
{
lean_dec(x_681);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; 
lean_dec(x_787);
x_857 = lean_ctor_get(x_685, 1);
lean_inc(x_857);
x_858 = lean_ctor_get(x_685, 2);
lean_inc(x_858);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 lean_ctor_release(x_685, 2);
 lean_ctor_release(x_685, 3);
 lean_ctor_release(x_685, 4);
 x_859 = x_685;
} else {
 lean_dec_ref(x_685);
 x_859 = lean_box(0);
}
x_860 = lean_box(1);
x_861 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_859)) {
 x_862 = lean_alloc_ctor(0, 5, 0);
} else {
 x_862 = x_859;
}
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_862, 1, x_682);
lean_ctor_set(x_862, 2, x_683);
lean_ctor_set(x_862, 3, x_860);
lean_ctor_set(x_862, 4, x_860);
if (lean_is_scalar(x_686)) {
 x_863 = lean_alloc_ctor(0, 5, 0);
} else {
 x_863 = x_686;
}
lean_ctor_set(x_863, 0, x_861);
lean_ctor_set(x_863, 1, x_784);
lean_ctor_set(x_863, 2, x_785);
lean_ctor_set(x_863, 3, x_860);
lean_ctor_set(x_863, 4, x_860);
x_864 = lean_unsigned_to_nat(3u);
x_865 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_857);
lean_ctor_set(x_865, 2, x_858);
lean_ctor_set(x_865, 3, x_862);
lean_ctor_set(x_865, 4, x_863);
return x_865;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_683);
lean_dec(x_682);
x_866 = lean_box(1);
x_867 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_686)) {
 x_868 = lean_alloc_ctor(0, 5, 0);
} else {
 x_868 = x_686;
}
lean_ctor_set(x_868, 0, x_867);
lean_ctor_set(x_868, 1, x_784);
lean_ctor_set(x_868, 2, x_785);
lean_ctor_set(x_868, 3, x_787);
lean_ctor_set(x_868, 4, x_866);
return x_868;
}
}
}
}
}
else
{
return x_673;
}
}
else
{
return x_674;
}
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_869 = lean_ctor_get(x_680, 0);
lean_inc(x_869);
lean_dec(x_680);
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
x_872 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_872, 0, x_670);
lean_ctor_set(x_872, 1, x_870);
lean_ctor_set(x_872, 2, x_871);
lean_ctor_set(x_872, 3, x_673);
lean_ctor_set(x_872, 4, x_674);
return x_872;
}
}
default: 
{
lean_object* x_873; lean_object* x_874; 
lean_dec(x_670);
x_873 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_alter_u2098___spec__1___rarg(x_1, x_2, x_3, x_674, lean_box(0));
x_874 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_671, x_672, x_673, x_873, lean_box(0), lean_box(0), lean_box(0));
return x_874;
}
}
}
}
else
{
lean_object* x_875; lean_object* x_876; 
lean_dec(x_2);
lean_dec(x_1);
x_875 = lean_box(0);
x_876 = lean_apply_1(x_3, x_875);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; 
x_877 = lean_box(1);
return x_877;
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_878 = lean_ctor_get(x_876, 0);
lean_inc(x_878);
lean_dec(x_876);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_881 = lean_box(1);
x_882 = lean_unsigned_to_nat(1u);
x_883 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_883, 0, x_882);
lean_ctor_set(x_883, 1, x_879);
lean_ctor_set(x_883, 2, x_880);
lean_ctor_set(x_883, 3, x_881);
lean_ctor_set(x_883, 4, x_881);
return x_883;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_alter_u2098___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_alter_u2098___spec__1___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_alter_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_8 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Cell_alter___rarg), 3, 2);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_5);
x_9 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_alter_u2098___spec__1___rarg(x_1, x_4, x_8, x_6, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_alter_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_alter_u2098___rarg), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___rarg(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg___lambda__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg___closed__1;
x_5 = l_Std_DTreeMap_Internal_Impl_applyCell___rarg(x_1, x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg___closed__1;
x_6 = l_Std_DTreeMap_Internal_Impl_applyCell___rarg(x_1, x_3, x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_get_u2098___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg___closed__1;
x_6 = l_Std_DTreeMap_Internal_Impl_applyCell___rarg(x_1, x_3, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__4;
x_8 = l_panic___rarg(x_4, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg___closed__1;
x_6 = l_Std_DTreeMap_Internal_Impl_applyCell___rarg(x_1, x_3, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_Const_alter_u2098___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_4, 3);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_8);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
switch (x_13) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_4);
lean_dec(x_7);
x_14 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_Const_alter_u2098___spec__1___rarg(x_1, x_2, x_3, x_10, lean_box(0));
x_15 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_8, x_9, x_14, x_11, lean_box(0), lean_box(0), lean_box(0));
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_8, x_9, lean_box(0));
x_17 = lean_apply_1(x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_7);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_10, 2);
x_23 = lean_ctor_get(x_10, 3);
x_24 = lean_ctor_get(x_10, 4);
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
x_27 = lean_ctor_get(x_11, 2);
x_28 = lean_ctor_get(x_11, 3);
x_29 = lean_ctor_get(x_11, 4);
x_30 = lean_nat_dec_lt(x_20, x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_20);
x_31 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_21, x_22, x_23, x_24, lean_box(0), lean_box(0), lean_box(0));
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_mul(x_36, x_35);
x_38 = lean_nat_dec_lt(x_37, x_25);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_4);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_39, x_35);
lean_dec(x_35);
x_41 = lean_nat_add(x_40, x_25);
lean_dec(x_25);
lean_dec(x_40);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_32);
lean_ctor_set(x_10, 2, x_34);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_41);
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_11);
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_28, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_28, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_28, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_29, 0);
lean_inc(x_47);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_mul(x_48, x_47);
x_50 = lean_nat_dec_lt(x_42, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
uint8_t x_51; 
lean_dec(x_42);
lean_free_object(x_4);
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_28, 4);
lean_dec(x_52);
x_53 = lean_ctor_get(x_28, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_28, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_28, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_28, 0);
lean_dec(x_56);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_57, x_35);
lean_dec(x_35);
x_59 = lean_nat_add(x_58, x_25);
lean_dec(x_25);
x_60 = lean_nat_add(x_57, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
x_62 = lean_nat_add(x_58, x_61);
lean_dec(x_61);
lean_dec(x_58);
lean_inc(x_32);
lean_ctor_set(x_28, 4, x_45);
lean_ctor_set(x_28, 3, x_32);
lean_ctor_set(x_28, 2, x_34);
lean_ctor_set(x_28, 1, x_33);
lean_ctor_set(x_28, 0, x_62);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_32, 4);
lean_dec(x_64);
x_65 = lean_ctor_get(x_32, 3);
lean_dec(x_65);
x_66 = lean_ctor_get(x_32, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_32, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_32, 0);
lean_dec(x_68);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_46, 0);
lean_inc(x_69);
x_70 = lean_nat_add(x_60, x_69);
lean_dec(x_69);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_70);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_add(x_60, x_71);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_72);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
else
{
lean_dec(x_32);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_46, 0);
lean_inc(x_73);
x_74 = lean_nat_add(x_60, x_73);
lean_dec(x_73);
lean_dec(x_60);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_26);
lean_ctor_set(x_75, 2, x_27);
lean_ctor_set(x_75, 3, x_46);
lean_ctor_set(x_75, 4, x_29);
lean_ctor_set(x_10, 4, x_75);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_add(x_60, x_76);
lean_dec(x_60);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_26);
lean_ctor_set(x_78, 2, x_27);
lean_ctor_set(x_78, 3, x_46);
lean_ctor_set(x_78, 4, x_29);
lean_ctor_set(x_10, 4, x_78);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_add(x_58, x_79);
lean_dec(x_58);
lean_inc(x_32);
lean_ctor_set(x_28, 4, x_45);
lean_ctor_set(x_28, 3, x_32);
lean_ctor_set(x_28, 2, x_34);
lean_ctor_set(x_28, 1, x_33);
lean_ctor_set(x_28, 0, x_80);
x_81 = !lean_is_exclusive(x_32);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_32, 4);
lean_dec(x_82);
x_83 = lean_ctor_get(x_32, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_32, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_32, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_32, 0);
lean_dec(x_86);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_46, 0);
lean_inc(x_87);
x_88 = lean_nat_add(x_60, x_87);
lean_dec(x_87);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_88);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_89; 
x_89 = lean_nat_add(x_60, x_79);
lean_dec(x_60);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 0, x_89);
lean_ctor_set(x_10, 4, x_32);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
else
{
lean_dec(x_32);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_46, 0);
lean_inc(x_90);
x_91 = lean_nat_add(x_60, x_90);
lean_dec(x_90);
lean_dec(x_60);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_26);
lean_ctor_set(x_92, 2, x_27);
lean_ctor_set(x_92, 3, x_46);
lean_ctor_set(x_92, 4, x_29);
lean_ctor_set(x_10, 4, x_92);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_nat_add(x_60, x_79);
lean_dec(x_60);
x_94 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_26);
lean_ctor_set(x_94, 2, x_27);
lean_ctor_set(x_94, 3, x_46);
lean_ctor_set(x_94, 4, x_29);
lean_ctor_set(x_10, 4, x_94);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_28);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_95, x_35);
lean_dec(x_35);
x_97 = lean_nat_add(x_96, x_25);
lean_dec(x_25);
x_98 = lean_nat_add(x_95, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_45, 0);
lean_inc(x_99);
x_100 = lean_nat_add(x_96, x_99);
lean_dec(x_99);
lean_dec(x_96);
lean_inc(x_32);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_33);
lean_ctor_set(x_101, 2, x_34);
lean_ctor_set(x_101, 3, x_32);
lean_ctor_set(x_101, 4, x_45);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_102 = x_32;
} else {
 lean_dec_ref(x_32);
 x_102 = lean_box(0);
}
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_46, 0);
lean_inc(x_103);
x_104 = lean_nat_add(x_98, x_103);
lean_dec(x_103);
lean_dec(x_98);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 5, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_26);
lean_ctor_set(x_105, 2, x_27);
lean_ctor_set(x_105, 3, x_46);
lean_ctor_set(x_105, 4, x_29);
lean_ctor_set(x_10, 4, x_105);
lean_ctor_set(x_10, 3, x_101);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_nat_add(x_98, x_106);
lean_dec(x_98);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(0, 5, 0);
} else {
 x_108 = x_102;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_26);
lean_ctor_set(x_108, 2, x_27);
lean_ctor_set(x_108, 3, x_46);
lean_ctor_set(x_108, 4, x_29);
lean_ctor_set(x_10, 4, x_108);
lean_ctor_set(x_10, 3, x_101);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_nat_add(x_96, x_109);
lean_dec(x_96);
lean_inc(x_32);
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_33);
lean_ctor_set(x_111, 2, x_34);
lean_ctor_set(x_111, 3, x_32);
lean_ctor_set(x_111, 4, x_45);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_112 = x_32;
} else {
 lean_dec_ref(x_32);
 x_112 = lean_box(0);
}
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_46, 0);
lean_inc(x_113);
x_114 = lean_nat_add(x_98, x_113);
lean_dec(x_113);
lean_dec(x_98);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 5, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_26);
lean_ctor_set(x_115, 2, x_27);
lean_ctor_set(x_115, 3, x_46);
lean_ctor_set(x_115, 4, x_29);
lean_ctor_set(x_10, 4, x_115);
lean_ctor_set(x_10, 3, x_111);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_nat_add(x_98, x_109);
lean_dec(x_98);
if (lean_is_scalar(x_112)) {
 x_117 = lean_alloc_ctor(0, 5, 0);
} else {
 x_117 = x_112;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_26);
lean_ctor_set(x_117, 2, x_27);
lean_ctor_set(x_117, 3, x_46);
lean_ctor_set(x_117, 4, x_29);
lean_ctor_set(x_10, 4, x_117);
lean_ctor_set(x_10, 3, x_111);
lean_ctor_set(x_10, 2, x_44);
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_118, x_35);
lean_dec(x_35);
x_120 = lean_nat_add(x_119, x_25);
lean_dec(x_25);
x_121 = lean_nat_add(x_119, x_42);
lean_dec(x_42);
lean_dec(x_119);
lean_ctor_set(x_10, 4, x_28);
lean_ctor_set(x_10, 3, x_32);
lean_ctor_set(x_10, 2, x_34);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_121);
lean_ctor_set(x_4, 4, x_29);
lean_ctor_set(x_4, 2, x_27);
lean_ctor_set(x_4, 1, x_26);
lean_ctor_set(x_4, 0, x_120);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_28) == 0)
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_31, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_31, 1);
lean_inc(x_123);
lean_dec(x_31);
x_124 = lean_ctor_get(x_28, 0);
lean_inc(x_124);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_add(x_125, x_25);
lean_dec(x_25);
x_127 = lean_nat_add(x_125, x_124);
lean_dec(x_124);
x_128 = lean_box(1);
lean_ctor_set(x_11, 4, x_28);
lean_ctor_set(x_11, 3, x_128);
lean_ctor_set(x_11, 2, x_123);
lean_ctor_set(x_11, 1, x_122);
lean_ctor_set(x_11, 0, x_127);
lean_ctor_set(x_10, 4, x_29);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_27);
lean_ctor_set(x_10, 1, x_26);
lean_ctor_set(x_10, 0, x_126);
return x_10;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_25);
x_129 = lean_ctor_get(x_31, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_31, 1);
lean_inc(x_130);
lean_dec(x_31);
x_131 = !lean_is_exclusive(x_28);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_28, 1);
x_133 = lean_ctor_get(x_28, 2);
x_134 = lean_ctor_get(x_28, 4);
lean_dec(x_134);
x_135 = lean_ctor_get(x_28, 3);
lean_dec(x_135);
x_136 = lean_ctor_get(x_28, 0);
lean_dec(x_136);
x_137 = lean_box(1);
x_138 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_28, 4, x_137);
lean_ctor_set(x_28, 3, x_137);
lean_ctor_set(x_28, 2, x_130);
lean_ctor_set(x_28, 1, x_129);
lean_ctor_set(x_28, 0, x_138);
lean_ctor_set(x_11, 4, x_137);
lean_ctor_set(x_11, 3, x_137);
lean_ctor_set(x_11, 0, x_138);
x_139 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_28);
lean_ctor_set(x_10, 2, x_133);
lean_ctor_set(x_10, 1, x_132);
lean_ctor_set(x_10, 0, x_139);
return x_10;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_ctor_get(x_28, 1);
x_141 = lean_ctor_get(x_28, 2);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_28);
x_142 = lean_box(1);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_129);
lean_ctor_set(x_144, 2, x_130);
lean_ctor_set(x_144, 3, x_142);
lean_ctor_set(x_144, 4, x_142);
lean_ctor_set(x_11, 4, x_142);
lean_ctor_set(x_11, 3, x_142);
lean_ctor_set(x_11, 0, x_143);
x_145 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_144);
lean_ctor_set(x_10, 2, x_141);
lean_ctor_set(x_10, 1, x_140);
lean_ctor_set(x_10, 0, x_145);
return x_10;
}
}
}
else
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_25);
x_146 = lean_ctor_get(x_31, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_31, 1);
lean_inc(x_147);
lean_dec(x_31);
x_148 = lean_box(1);
x_149 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_11, 4, x_148);
lean_ctor_set(x_11, 3, x_148);
lean_ctor_set(x_11, 2, x_147);
lean_ctor_set(x_11, 1, x_146);
lean_ctor_set(x_11, 0, x_149);
x_150 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_29);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_27);
lean_ctor_set(x_10, 1, x_26);
lean_ctor_set(x_10, 0, x_150);
return x_10;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_31, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_31, 1);
lean_inc(x_152);
lean_dec(x_31);
lean_ctor_set(x_11, 3, x_29);
x_153 = lean_box(1);
x_154 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_11);
lean_ctor_set(x_10, 3, x_153);
lean_ctor_set(x_10, 2, x_152);
lean_ctor_set(x_10, 1, x_151);
lean_ctor_set(x_10, 0, x_154);
return x_10;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_25);
x_155 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_26, x_27, x_28, x_29, lean_box(0), lean_box(0), lean_box(0));
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 2);
lean_inc(x_158);
lean_dec(x_155);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_ctor_set(x_11, 4, x_24);
lean_ctor_set(x_11, 3, x_23);
lean_ctor_set(x_11, 2, x_22);
lean_ctor_set(x_11, 1, x_21);
lean_ctor_set(x_11, 0, x_20);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_unsigned_to_nat(3u);
x_161 = lean_nat_mul(x_160, x_159);
x_162 = lean_nat_dec_lt(x_161, x_20);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_4);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_nat_add(x_163, x_20);
lean_dec(x_20);
x_165 = lean_nat_add(x_164, x_159);
lean_dec(x_159);
lean_dec(x_164);
lean_ctor_set(x_10, 4, x_158);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_165);
return x_10;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_dec(x_11);
x_166 = lean_ctor_get(x_23, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_24, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_24, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_24, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_24, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_24, 4);
lean_inc(x_171);
x_172 = lean_unsigned_to_nat(2u);
x_173 = lean_nat_mul(x_172, x_166);
x_174 = lean_nat_dec_lt(x_167, x_173);
lean_dec(x_173);
if (x_174 == 0)
{
uint8_t x_175; 
lean_dec(x_167);
lean_free_object(x_10);
lean_free_object(x_4);
x_175 = !lean_is_exclusive(x_24);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_176 = lean_ctor_get(x_24, 4);
lean_dec(x_176);
x_177 = lean_ctor_get(x_24, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_24, 2);
lean_dec(x_178);
x_179 = lean_ctor_get(x_24, 1);
lean_dec(x_179);
x_180 = lean_ctor_get(x_24, 0);
lean_dec(x_180);
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_nat_add(x_181, x_20);
lean_dec(x_20);
x_183 = lean_nat_add(x_182, x_159);
lean_dec(x_182);
x_184 = lean_nat_add(x_181, x_166);
lean_dec(x_166);
x_185 = lean_nat_add(x_181, x_159);
lean_dec(x_159);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_170, 0);
lean_inc(x_186);
x_187 = lean_nat_add(x_184, x_186);
lean_dec(x_186);
lean_dec(x_184);
lean_inc(x_23);
lean_ctor_set(x_24, 4, x_170);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_187);
x_188 = !lean_is_exclusive(x_23);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_23, 4);
lean_dec(x_189);
x_190 = lean_ctor_get(x_23, 3);
lean_dec(x_190);
x_191 = lean_ctor_get(x_23, 2);
lean_dec(x_191);
x_192 = lean_ctor_get(x_23, 1);
lean_dec(x_192);
x_193 = lean_ctor_get(x_23, 0);
lean_dec(x_193);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_171, 0);
lean_inc(x_194);
x_195 = lean_nat_add(x_185, x_194);
lean_dec(x_194);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_195);
x_196 = !lean_is_exclusive(x_158);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_158, 4);
lean_dec(x_197);
x_198 = lean_ctor_get(x_158, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_158, 2);
lean_dec(x_199);
x_200 = lean_ctor_get(x_158, 1);
lean_dec(x_200);
x_201 = lean_ctor_get(x_158, 0);
lean_dec(x_201);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_202; 
lean_dec(x_158);
x_202 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_202, 0, x_183);
lean_ctor_set(x_202, 1, x_168);
lean_ctor_set(x_202, 2, x_169);
lean_ctor_set(x_202, 3, x_24);
lean_ctor_set(x_202, 4, x_23);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_203 = lean_unsigned_to_nat(0u);
x_204 = lean_nat_add(x_185, x_203);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_204);
x_205 = !lean_is_exclusive(x_158);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_158, 4);
lean_dec(x_206);
x_207 = lean_ctor_get(x_158, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_158, 2);
lean_dec(x_208);
x_209 = lean_ctor_get(x_158, 1);
lean_dec(x_209);
x_210 = lean_ctor_get(x_158, 0);
lean_dec(x_210);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_211; 
lean_dec(x_158);
x_211 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_211, 0, x_183);
lean_ctor_set(x_211, 1, x_168);
lean_ctor_set(x_211, 2, x_169);
lean_ctor_set(x_211, 3, x_24);
lean_ctor_set(x_211, 4, x_23);
return x_211;
}
}
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_ctor_get(x_171, 0);
lean_inc(x_212);
x_213 = lean_nat_add(x_185, x_212);
lean_dec(x_212);
lean_dec(x_185);
lean_inc(x_158);
x_214 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_156);
lean_ctor_set(x_214, 2, x_157);
lean_ctor_set(x_214, 3, x_171);
lean_ctor_set(x_214, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_215 = x_158;
} else {
 lean_dec_ref(x_158);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(0, 5, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_183);
lean_ctor_set(x_216, 1, x_168);
lean_ctor_set(x_216, 2, x_169);
lean_ctor_set(x_216, 3, x_24);
lean_ctor_set(x_216, 4, x_214);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_unsigned_to_nat(0u);
x_218 = lean_nat_add(x_185, x_217);
lean_dec(x_185);
lean_inc(x_158);
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_156);
lean_ctor_set(x_219, 2, x_157);
lean_ctor_set(x_219, 3, x_171);
lean_ctor_set(x_219, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_220 = x_158;
} else {
 lean_dec_ref(x_158);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 5, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_183);
lean_ctor_set(x_221, 1, x_168);
lean_ctor_set(x_221, 2, x_169);
lean_ctor_set(x_221, 3, x_24);
lean_ctor_set(x_221, 4, x_219);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_unsigned_to_nat(0u);
x_223 = lean_nat_add(x_184, x_222);
lean_dec(x_184);
lean_inc(x_23);
lean_ctor_set(x_24, 4, x_170);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_223);
x_224 = !lean_is_exclusive(x_23);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_23, 4);
lean_dec(x_225);
x_226 = lean_ctor_get(x_23, 3);
lean_dec(x_226);
x_227 = lean_ctor_get(x_23, 2);
lean_dec(x_227);
x_228 = lean_ctor_get(x_23, 1);
lean_dec(x_228);
x_229 = lean_ctor_get(x_23, 0);
lean_dec(x_229);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_230 = lean_ctor_get(x_171, 0);
lean_inc(x_230);
x_231 = lean_nat_add(x_185, x_230);
lean_dec(x_230);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_231);
x_232 = !lean_is_exclusive(x_158);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_158, 4);
lean_dec(x_233);
x_234 = lean_ctor_get(x_158, 3);
lean_dec(x_234);
x_235 = lean_ctor_get(x_158, 2);
lean_dec(x_235);
x_236 = lean_ctor_get(x_158, 1);
lean_dec(x_236);
x_237 = lean_ctor_get(x_158, 0);
lean_dec(x_237);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_238; 
lean_dec(x_158);
x_238 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_238, 0, x_183);
lean_ctor_set(x_238, 1, x_168);
lean_ctor_set(x_238, 2, x_169);
lean_ctor_set(x_238, 3, x_24);
lean_ctor_set(x_238, 4, x_23);
return x_238;
}
}
else
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_nat_add(x_185, x_222);
lean_dec(x_185);
lean_inc(x_158);
lean_ctor_set(x_23, 4, x_158);
lean_ctor_set(x_23, 3, x_171);
lean_ctor_set(x_23, 2, x_157);
lean_ctor_set(x_23, 1, x_156);
lean_ctor_set(x_23, 0, x_239);
x_240 = !lean_is_exclusive(x_158);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = lean_ctor_get(x_158, 4);
lean_dec(x_241);
x_242 = lean_ctor_get(x_158, 3);
lean_dec(x_242);
x_243 = lean_ctor_get(x_158, 2);
lean_dec(x_243);
x_244 = lean_ctor_get(x_158, 1);
lean_dec(x_244);
x_245 = lean_ctor_get(x_158, 0);
lean_dec(x_245);
lean_ctor_set(x_158, 4, x_23);
lean_ctor_set(x_158, 3, x_24);
lean_ctor_set(x_158, 2, x_169);
lean_ctor_set(x_158, 1, x_168);
lean_ctor_set(x_158, 0, x_183);
return x_158;
}
else
{
lean_object* x_246; 
lean_dec(x_158);
x_246 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_246, 0, x_183);
lean_ctor_set(x_246, 1, x_168);
lean_ctor_set(x_246, 2, x_169);
lean_ctor_set(x_246, 3, x_24);
lean_ctor_set(x_246, 4, x_23);
return x_246;
}
}
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = lean_ctor_get(x_171, 0);
lean_inc(x_247);
x_248 = lean_nat_add(x_185, x_247);
lean_dec(x_247);
lean_dec(x_185);
lean_inc(x_158);
x_249 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_156);
lean_ctor_set(x_249, 2, x_157);
lean_ctor_set(x_249, 3, x_171);
lean_ctor_set(x_249, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_250 = x_158;
} else {
 lean_dec_ref(x_158);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 5, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_183);
lean_ctor_set(x_251, 1, x_168);
lean_ctor_set(x_251, 2, x_169);
lean_ctor_set(x_251, 3, x_24);
lean_ctor_set(x_251, 4, x_249);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_nat_add(x_185, x_222);
lean_dec(x_185);
lean_inc(x_158);
x_253 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_156);
lean_ctor_set(x_253, 2, x_157);
lean_ctor_set(x_253, 3, x_171);
lean_ctor_set(x_253, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_254 = x_158;
} else {
 lean_dec_ref(x_158);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(0, 5, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_183);
lean_ctor_set(x_255, 1, x_168);
lean_ctor_set(x_255, 2, x_169);
lean_ctor_set(x_255, 3, x_24);
lean_ctor_set(x_255, 4, x_253);
return x_255;
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_24);
x_256 = lean_unsigned_to_nat(1u);
x_257 = lean_nat_add(x_256, x_20);
lean_dec(x_20);
x_258 = lean_nat_add(x_257, x_159);
lean_dec(x_257);
x_259 = lean_nat_add(x_256, x_166);
lean_dec(x_166);
x_260 = lean_nat_add(x_256, x_159);
lean_dec(x_159);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_170, 0);
lean_inc(x_261);
x_262 = lean_nat_add(x_259, x_261);
lean_dec(x_261);
lean_dec(x_259);
lean_inc(x_23);
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_21);
lean_ctor_set(x_263, 2, x_22);
lean_ctor_set(x_263, 3, x_23);
lean_ctor_set(x_263, 4, x_170);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 x_264 = x_23;
} else {
 lean_dec_ref(x_23);
 x_264 = lean_box(0);
}
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_265 = lean_ctor_get(x_171, 0);
lean_inc(x_265);
x_266 = lean_nat_add(x_260, x_265);
lean_dec(x_265);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_264)) {
 x_267 = lean_alloc_ctor(0, 5, 0);
} else {
 x_267 = x_264;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_156);
lean_ctor_set(x_267, 2, x_157);
lean_ctor_set(x_267, 3, x_171);
lean_ctor_set(x_267, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_268 = x_158;
} else {
 lean_dec_ref(x_158);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(0, 5, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_258);
lean_ctor_set(x_269, 1, x_168);
lean_ctor_set(x_269, 2, x_169);
lean_ctor_set(x_269, 3, x_263);
lean_ctor_set(x_269, 4, x_267);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_unsigned_to_nat(0u);
x_271 = lean_nat_add(x_260, x_270);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_264)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_264;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_156);
lean_ctor_set(x_272, 2, x_157);
lean_ctor_set(x_272, 3, x_171);
lean_ctor_set(x_272, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_273 = x_158;
} else {
 lean_dec_ref(x_158);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 5, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_258);
lean_ctor_set(x_274, 1, x_168);
lean_ctor_set(x_274, 2, x_169);
lean_ctor_set(x_274, 3, x_263);
lean_ctor_set(x_274, 4, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_unsigned_to_nat(0u);
x_276 = lean_nat_add(x_259, x_275);
lean_dec(x_259);
lean_inc(x_23);
x_277 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_21);
lean_ctor_set(x_277, 2, x_22);
lean_ctor_set(x_277, 3, x_23);
lean_ctor_set(x_277, 4, x_170);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 x_278 = x_23;
} else {
 lean_dec_ref(x_23);
 x_278 = lean_box(0);
}
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_ctor_get(x_171, 0);
lean_inc(x_279);
x_280 = lean_nat_add(x_260, x_279);
lean_dec(x_279);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_278)) {
 x_281 = lean_alloc_ctor(0, 5, 0);
} else {
 x_281 = x_278;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_156);
lean_ctor_set(x_281, 2, x_157);
lean_ctor_set(x_281, 3, x_171);
lean_ctor_set(x_281, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_282 = x_158;
} else {
 lean_dec_ref(x_158);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(0, 5, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_258);
lean_ctor_set(x_283, 1, x_168);
lean_ctor_set(x_283, 2, x_169);
lean_ctor_set(x_283, 3, x_277);
lean_ctor_set(x_283, 4, x_281);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_284 = lean_nat_add(x_260, x_275);
lean_dec(x_260);
lean_inc(x_158);
if (lean_is_scalar(x_278)) {
 x_285 = lean_alloc_ctor(0, 5, 0);
} else {
 x_285 = x_278;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_156);
lean_ctor_set(x_285, 2, x_157);
lean_ctor_set(x_285, 3, x_171);
lean_ctor_set(x_285, 4, x_158);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_286 = x_158;
} else {
 lean_dec_ref(x_158);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(0, 5, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_258);
lean_ctor_set(x_287, 1, x_168);
lean_ctor_set(x_287, 2, x_169);
lean_ctor_set(x_287, 3, x_277);
lean_ctor_set(x_287, 4, x_285);
return x_287;
}
}
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_166);
x_288 = lean_unsigned_to_nat(1u);
x_289 = lean_nat_add(x_288, x_20);
lean_dec(x_20);
x_290 = lean_nat_add(x_289, x_159);
lean_dec(x_289);
x_291 = lean_nat_add(x_288, x_159);
lean_dec(x_159);
x_292 = lean_nat_add(x_291, x_167);
lean_dec(x_167);
lean_dec(x_291);
lean_ctor_set(x_10, 4, x_158);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_292);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_290);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_24, 0);
lean_inc(x_293);
x_294 = lean_unsigned_to_nat(1u);
x_295 = lean_nat_add(x_294, x_20);
lean_dec(x_20);
x_296 = lean_nat_add(x_294, x_293);
lean_dec(x_293);
x_297 = lean_box(1);
lean_ctor_set(x_10, 4, x_297);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_296);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_295);
return x_4;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_20);
x_298 = lean_box(1);
x_299 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_10, 4, x_298);
lean_ctor_set(x_10, 3, x_298);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_299);
x_300 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_23);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_300);
return x_4;
}
}
else
{
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_301; 
lean_dec(x_11);
x_301 = !lean_is_exclusive(x_24);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_302 = lean_ctor_get(x_24, 1);
x_303 = lean_ctor_get(x_24, 2);
x_304 = lean_ctor_get(x_24, 4);
lean_dec(x_304);
x_305 = lean_ctor_get(x_24, 3);
lean_dec(x_305);
x_306 = lean_ctor_get(x_24, 0);
lean_dec(x_306);
x_307 = lean_box(1);
x_308 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_24, 4, x_307);
lean_ctor_set(x_24, 3, x_307);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_308);
lean_ctor_set(x_10, 4, x_307);
lean_ctor_set(x_10, 3, x_307);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_308);
x_309 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_24);
lean_ctor_set(x_4, 2, x_303);
lean_ctor_set(x_4, 1, x_302);
lean_ctor_set(x_4, 0, x_309);
return x_4;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_310 = lean_ctor_get(x_24, 1);
x_311 = lean_ctor_get(x_24, 2);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_24);
x_312 = lean_box(1);
x_313 = lean_unsigned_to_nat(1u);
x_314 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_21);
lean_ctor_set(x_314, 2, x_22);
lean_ctor_set(x_314, 3, x_312);
lean_ctor_set(x_314, 4, x_312);
lean_ctor_set(x_10, 4, x_312);
lean_ctor_set(x_10, 3, x_312);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_313);
x_315 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_314);
lean_ctor_set(x_4, 2, x_311);
lean_ctor_set(x_4, 1, x_310);
lean_ctor_set(x_4, 0, x_315);
return x_4;
}
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_4);
x_316 = lean_box(1);
x_317 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_316);
lean_ctor_set(x_10, 3, x_11);
lean_ctor_set(x_10, 2, x_157);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_317);
return x_10;
}
}
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_318 = lean_ctor_get(x_10, 0);
x_319 = lean_ctor_get(x_10, 1);
x_320 = lean_ctor_get(x_10, 2);
x_321 = lean_ctor_get(x_10, 3);
x_322 = lean_ctor_get(x_10, 4);
x_323 = lean_ctor_get(x_11, 0);
x_324 = lean_ctor_get(x_11, 1);
x_325 = lean_ctor_get(x_11, 2);
x_326 = lean_ctor_get(x_11, 3);
x_327 = lean_ctor_get(x_11, 4);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_11);
x_328 = lean_nat_dec_lt(x_318, x_323);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_318);
x_329 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_319, x_320, x_321, x_322, lean_box(0), lean_box(0), lean_box(0));
x_330 = lean_ctor_get(x_329, 2);
lean_inc(x_330);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_331 = lean_ctor_get(x_329, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_dec(x_329);
x_333 = lean_ctor_get(x_330, 0);
lean_inc(x_333);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
x_334 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_334, 0, x_323);
lean_ctor_set(x_334, 1, x_324);
lean_ctor_set(x_334, 2, x_325);
lean_ctor_set(x_334, 3, x_326);
lean_ctor_set(x_334, 4, x_327);
x_335 = lean_unsigned_to_nat(3u);
x_336 = lean_nat_mul(x_335, x_333);
x_337 = lean_nat_dec_lt(x_336, x_323);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_free_object(x_4);
x_338 = lean_unsigned_to_nat(1u);
x_339 = lean_nat_add(x_338, x_333);
lean_dec(x_333);
x_340 = lean_nat_add(x_339, x_323);
lean_dec(x_323);
lean_dec(x_339);
lean_ctor_set(x_10, 4, x_334);
lean_ctor_set(x_10, 3, x_330);
lean_ctor_set(x_10, 2, x_332);
lean_ctor_set(x_10, 1, x_331);
lean_ctor_set(x_10, 0, x_340);
return x_10;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
lean_dec(x_334);
x_341 = lean_ctor_get(x_326, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_326, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_326, 2);
lean_inc(x_343);
x_344 = lean_ctor_get(x_326, 3);
lean_inc(x_344);
x_345 = lean_ctor_get(x_326, 4);
lean_inc(x_345);
x_346 = lean_ctor_get(x_327, 0);
lean_inc(x_346);
x_347 = lean_unsigned_to_nat(2u);
x_348 = lean_nat_mul(x_347, x_346);
x_349 = lean_nat_dec_lt(x_341, x_348);
lean_dec(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_341);
lean_free_object(x_4);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 x_350 = x_326;
} else {
 lean_dec_ref(x_326);
 x_350 = lean_box(0);
}
x_351 = lean_unsigned_to_nat(1u);
x_352 = lean_nat_add(x_351, x_333);
lean_dec(x_333);
x_353 = lean_nat_add(x_352, x_323);
lean_dec(x_323);
x_354 = lean_nat_add(x_351, x_346);
lean_dec(x_346);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_355 = lean_ctor_get(x_344, 0);
lean_inc(x_355);
x_356 = lean_nat_add(x_352, x_355);
lean_dec(x_355);
lean_dec(x_352);
lean_inc(x_330);
if (lean_is_scalar(x_350)) {
 x_357 = lean_alloc_ctor(0, 5, 0);
} else {
 x_357 = x_350;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_331);
lean_ctor_set(x_357, 2, x_332);
lean_ctor_set(x_357, 3, x_330);
lean_ctor_set(x_357, 4, x_344);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 x_358 = x_330;
} else {
 lean_dec_ref(x_330);
 x_358 = lean_box(0);
}
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_345, 0);
lean_inc(x_359);
x_360 = lean_nat_add(x_354, x_359);
lean_dec(x_359);
lean_dec(x_354);
if (lean_is_scalar(x_358)) {
 x_361 = lean_alloc_ctor(0, 5, 0);
} else {
 x_361 = x_358;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_324);
lean_ctor_set(x_361, 2, x_325);
lean_ctor_set(x_361, 3, x_345);
lean_ctor_set(x_361, 4, x_327);
lean_ctor_set(x_10, 4, x_361);
lean_ctor_set(x_10, 3, x_357);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_unsigned_to_nat(0u);
x_363 = lean_nat_add(x_354, x_362);
lean_dec(x_354);
if (lean_is_scalar(x_358)) {
 x_364 = lean_alloc_ctor(0, 5, 0);
} else {
 x_364 = x_358;
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_324);
lean_ctor_set(x_364, 2, x_325);
lean_ctor_set(x_364, 3, x_345);
lean_ctor_set(x_364, 4, x_327);
lean_ctor_set(x_10, 4, x_364);
lean_ctor_set(x_10, 3, x_357);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = lean_unsigned_to_nat(0u);
x_366 = lean_nat_add(x_352, x_365);
lean_dec(x_352);
lean_inc(x_330);
if (lean_is_scalar(x_350)) {
 x_367 = lean_alloc_ctor(0, 5, 0);
} else {
 x_367 = x_350;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_331);
lean_ctor_set(x_367, 2, x_332);
lean_ctor_set(x_367, 3, x_330);
lean_ctor_set(x_367, 4, x_344);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 x_368 = x_330;
} else {
 lean_dec_ref(x_330);
 x_368 = lean_box(0);
}
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_345, 0);
lean_inc(x_369);
x_370 = lean_nat_add(x_354, x_369);
lean_dec(x_369);
lean_dec(x_354);
if (lean_is_scalar(x_368)) {
 x_371 = lean_alloc_ctor(0, 5, 0);
} else {
 x_371 = x_368;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_324);
lean_ctor_set(x_371, 2, x_325);
lean_ctor_set(x_371, 3, x_345);
lean_ctor_set(x_371, 4, x_327);
lean_ctor_set(x_10, 4, x_371);
lean_ctor_set(x_10, 3, x_367);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_nat_add(x_354, x_365);
lean_dec(x_354);
if (lean_is_scalar(x_368)) {
 x_373 = lean_alloc_ctor(0, 5, 0);
} else {
 x_373 = x_368;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_324);
lean_ctor_set(x_373, 2, x_325);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set(x_373, 4, x_327);
lean_ctor_set(x_10, 4, x_373);
lean_ctor_set(x_10, 3, x_367);
lean_ctor_set(x_10, 2, x_343);
lean_ctor_set(x_10, 1, x_342);
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
x_374 = lean_unsigned_to_nat(1u);
x_375 = lean_nat_add(x_374, x_333);
lean_dec(x_333);
x_376 = lean_nat_add(x_375, x_323);
lean_dec(x_323);
x_377 = lean_nat_add(x_375, x_341);
lean_dec(x_341);
lean_dec(x_375);
lean_ctor_set(x_10, 4, x_326);
lean_ctor_set(x_10, 3, x_330);
lean_ctor_set(x_10, 2, x_332);
lean_ctor_set(x_10, 1, x_331);
lean_ctor_set(x_10, 0, x_377);
lean_ctor_set(x_4, 4, x_327);
lean_ctor_set(x_4, 2, x_325);
lean_ctor_set(x_4, 1, x_324);
lean_ctor_set(x_4, 0, x_376);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_326) == 0)
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_378 = lean_ctor_get(x_329, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_329, 1);
lean_inc(x_379);
lean_dec(x_329);
x_380 = lean_ctor_get(x_326, 0);
lean_inc(x_380);
x_381 = lean_unsigned_to_nat(1u);
x_382 = lean_nat_add(x_381, x_323);
lean_dec(x_323);
x_383 = lean_nat_add(x_381, x_380);
lean_dec(x_380);
x_384 = lean_box(1);
x_385 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_378);
lean_ctor_set(x_385, 2, x_379);
lean_ctor_set(x_385, 3, x_384);
lean_ctor_set(x_385, 4, x_326);
lean_ctor_set(x_10, 4, x_327);
lean_ctor_set(x_10, 3, x_385);
lean_ctor_set(x_10, 2, x_325);
lean_ctor_set(x_10, 1, x_324);
lean_ctor_set(x_10, 0, x_382);
return x_10;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_323);
x_386 = lean_ctor_get(x_329, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_329, 1);
lean_inc(x_387);
lean_dec(x_329);
x_388 = lean_ctor_get(x_326, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_326, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 x_390 = x_326;
} else {
 lean_dec_ref(x_326);
 x_390 = lean_box(0);
}
x_391 = lean_box(1);
x_392 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_390)) {
 x_393 = lean_alloc_ctor(0, 5, 0);
} else {
 x_393 = x_390;
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_386);
lean_ctor_set(x_393, 2, x_387);
lean_ctor_set(x_393, 3, x_391);
lean_ctor_set(x_393, 4, x_391);
x_394 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_324);
lean_ctor_set(x_394, 2, x_325);
lean_ctor_set(x_394, 3, x_391);
lean_ctor_set(x_394, 4, x_391);
x_395 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_394);
lean_ctor_set(x_10, 3, x_393);
lean_ctor_set(x_10, 2, x_389);
lean_ctor_set(x_10, 1, x_388);
lean_ctor_set(x_10, 0, x_395);
return x_10;
}
}
else
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_323);
x_396 = lean_ctor_get(x_329, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_329, 1);
lean_inc(x_397);
lean_dec(x_329);
x_398 = lean_box(1);
x_399 = lean_unsigned_to_nat(1u);
x_400 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_396);
lean_ctor_set(x_400, 2, x_397);
lean_ctor_set(x_400, 3, x_398);
lean_ctor_set(x_400, 4, x_398);
x_401 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_10, 4, x_327);
lean_ctor_set(x_10, 3, x_400);
lean_ctor_set(x_10, 2, x_325);
lean_ctor_set(x_10, 1, x_324);
lean_ctor_set(x_10, 0, x_401);
return x_10;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_402 = lean_ctor_get(x_329, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_329, 1);
lean_inc(x_403);
lean_dec(x_329);
x_404 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_404, 0, x_323);
lean_ctor_set(x_404, 1, x_324);
lean_ctor_set(x_404, 2, x_325);
lean_ctor_set(x_404, 3, x_327);
lean_ctor_set(x_404, 4, x_327);
x_405 = lean_box(1);
x_406 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_404);
lean_ctor_set(x_10, 3, x_405);
lean_ctor_set(x_10, 2, x_403);
lean_ctor_set(x_10, 1, x_402);
lean_ctor_set(x_10, 0, x_406);
return x_10;
}
}
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_323);
x_407 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_324, x_325, x_326, x_327, lean_box(0), lean_box(0), lean_box(0));
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_407, 2);
lean_inc(x_410);
lean_dec(x_407);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
x_411 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_411, 0, x_318);
lean_ctor_set(x_411, 1, x_319);
lean_ctor_set(x_411, 2, x_320);
lean_ctor_set(x_411, 3, x_321);
lean_ctor_set(x_411, 4, x_322);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_412 = lean_ctor_get(x_410, 0);
lean_inc(x_412);
x_413 = lean_unsigned_to_nat(3u);
x_414 = lean_nat_mul(x_413, x_412);
x_415 = lean_nat_dec_lt(x_414, x_318);
lean_dec(x_414);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_free_object(x_4);
x_416 = lean_unsigned_to_nat(1u);
x_417 = lean_nat_add(x_416, x_318);
lean_dec(x_318);
x_418 = lean_nat_add(x_417, x_412);
lean_dec(x_412);
lean_dec(x_417);
lean_ctor_set(x_10, 4, x_410);
lean_ctor_set(x_10, 3, x_411);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_418);
return x_10;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_dec(x_411);
x_419 = lean_ctor_get(x_321, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_322, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_322, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_322, 2);
lean_inc(x_422);
x_423 = lean_ctor_get(x_322, 3);
lean_inc(x_423);
x_424 = lean_ctor_get(x_322, 4);
lean_inc(x_424);
x_425 = lean_unsigned_to_nat(2u);
x_426 = lean_nat_mul(x_425, x_419);
x_427 = lean_nat_dec_lt(x_420, x_426);
lean_dec(x_426);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_420);
lean_free_object(x_10);
lean_free_object(x_4);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 lean_ctor_release(x_322, 4);
 x_428 = x_322;
} else {
 lean_dec_ref(x_322);
 x_428 = lean_box(0);
}
x_429 = lean_unsigned_to_nat(1u);
x_430 = lean_nat_add(x_429, x_318);
lean_dec(x_318);
x_431 = lean_nat_add(x_430, x_412);
lean_dec(x_430);
x_432 = lean_nat_add(x_429, x_419);
lean_dec(x_419);
x_433 = lean_nat_add(x_429, x_412);
lean_dec(x_412);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = lean_ctor_get(x_423, 0);
lean_inc(x_434);
x_435 = lean_nat_add(x_432, x_434);
lean_dec(x_434);
lean_dec(x_432);
lean_inc(x_321);
if (lean_is_scalar(x_428)) {
 x_436 = lean_alloc_ctor(0, 5, 0);
} else {
 x_436 = x_428;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_319);
lean_ctor_set(x_436, 2, x_320);
lean_ctor_set(x_436, 3, x_321);
lean_ctor_set(x_436, 4, x_423);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 x_437 = x_321;
} else {
 lean_dec_ref(x_321);
 x_437 = lean_box(0);
}
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_438 = lean_ctor_get(x_424, 0);
lean_inc(x_438);
x_439 = lean_nat_add(x_433, x_438);
lean_dec(x_438);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_437)) {
 x_440 = lean_alloc_ctor(0, 5, 0);
} else {
 x_440 = x_437;
}
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_408);
lean_ctor_set(x_440, 2, x_409);
lean_ctor_set(x_440, 3, x_424);
lean_ctor_set(x_440, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_441 = x_410;
} else {
 lean_dec_ref(x_410);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(0, 5, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_431);
lean_ctor_set(x_442, 1, x_421);
lean_ctor_set(x_442, 2, x_422);
lean_ctor_set(x_442, 3, x_436);
lean_ctor_set(x_442, 4, x_440);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_443 = lean_unsigned_to_nat(0u);
x_444 = lean_nat_add(x_433, x_443);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(0, 5, 0);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_408);
lean_ctor_set(x_445, 2, x_409);
lean_ctor_set(x_445, 3, x_424);
lean_ctor_set(x_445, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_446 = x_410;
} else {
 lean_dec_ref(x_410);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(0, 5, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_431);
lean_ctor_set(x_447, 1, x_421);
lean_ctor_set(x_447, 2, x_422);
lean_ctor_set(x_447, 3, x_436);
lean_ctor_set(x_447, 4, x_445);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_448 = lean_unsigned_to_nat(0u);
x_449 = lean_nat_add(x_432, x_448);
lean_dec(x_432);
lean_inc(x_321);
if (lean_is_scalar(x_428)) {
 x_450 = lean_alloc_ctor(0, 5, 0);
} else {
 x_450 = x_428;
}
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_319);
lean_ctor_set(x_450, 2, x_320);
lean_ctor_set(x_450, 3, x_321);
lean_ctor_set(x_450, 4, x_423);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 x_451 = x_321;
} else {
 lean_dec_ref(x_321);
 x_451 = lean_box(0);
}
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_452 = lean_ctor_get(x_424, 0);
lean_inc(x_452);
x_453 = lean_nat_add(x_433, x_452);
lean_dec(x_452);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_451)) {
 x_454 = lean_alloc_ctor(0, 5, 0);
} else {
 x_454 = x_451;
}
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_408);
lean_ctor_set(x_454, 2, x_409);
lean_ctor_set(x_454, 3, x_424);
lean_ctor_set(x_454, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_455 = x_410;
} else {
 lean_dec_ref(x_410);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(0, 5, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_431);
lean_ctor_set(x_456, 1, x_421);
lean_ctor_set(x_456, 2, x_422);
lean_ctor_set(x_456, 3, x_450);
lean_ctor_set(x_456, 4, x_454);
return x_456;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_457 = lean_nat_add(x_433, x_448);
lean_dec(x_433);
lean_inc(x_410);
if (lean_is_scalar(x_451)) {
 x_458 = lean_alloc_ctor(0, 5, 0);
} else {
 x_458 = x_451;
}
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_408);
lean_ctor_set(x_458, 2, x_409);
lean_ctor_set(x_458, 3, x_424);
lean_ctor_set(x_458, 4, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_459 = x_410;
} else {
 lean_dec_ref(x_410);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(0, 5, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_431);
lean_ctor_set(x_460, 1, x_421);
lean_ctor_set(x_460, 2, x_422);
lean_ctor_set(x_460, 3, x_450);
lean_ctor_set(x_460, 4, x_458);
return x_460;
}
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_419);
x_461 = lean_unsigned_to_nat(1u);
x_462 = lean_nat_add(x_461, x_318);
lean_dec(x_318);
x_463 = lean_nat_add(x_462, x_412);
lean_dec(x_462);
x_464 = lean_nat_add(x_461, x_412);
lean_dec(x_412);
x_465 = lean_nat_add(x_464, x_420);
lean_dec(x_420);
lean_dec(x_464);
lean_ctor_set(x_10, 4, x_410);
lean_ctor_set(x_10, 3, x_322);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_465);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_463);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_321) == 0)
{
lean_dec(x_411);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_466 = lean_ctor_get(x_322, 0);
lean_inc(x_466);
x_467 = lean_unsigned_to_nat(1u);
x_468 = lean_nat_add(x_467, x_318);
lean_dec(x_318);
x_469 = lean_nat_add(x_467, x_466);
lean_dec(x_466);
x_470 = lean_box(1);
lean_ctor_set(x_10, 4, x_470);
lean_ctor_set(x_10, 3, x_322);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_469);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_468);
return x_4;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_318);
x_471 = lean_box(1);
x_472 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_10, 4, x_471);
lean_ctor_set(x_10, 3, x_471);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_472);
x_473 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_321);
lean_ctor_set(x_4, 2, x_320);
lean_ctor_set(x_4, 1, x_319);
lean_ctor_set(x_4, 0, x_473);
return x_4;
}
}
else
{
lean_dec(x_318);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec(x_411);
x_474 = lean_ctor_get(x_322, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_322, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 lean_ctor_release(x_322, 4);
 x_476 = x_322;
} else {
 lean_dec_ref(x_322);
 x_476 = lean_box(0);
}
x_477 = lean_box(1);
x_478 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_476)) {
 x_479 = lean_alloc_ctor(0, 5, 0);
} else {
 x_479 = x_476;
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_319);
lean_ctor_set(x_479, 2, x_320);
lean_ctor_set(x_479, 3, x_477);
lean_ctor_set(x_479, 4, x_477);
lean_ctor_set(x_10, 4, x_477);
lean_ctor_set(x_10, 3, x_477);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_478);
x_480 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_10);
lean_ctor_set(x_4, 3, x_479);
lean_ctor_set(x_4, 2, x_475);
lean_ctor_set(x_4, 1, x_474);
lean_ctor_set(x_4, 0, x_480);
return x_4;
}
else
{
lean_object* x_481; lean_object* x_482; 
lean_dec(x_320);
lean_dec(x_319);
lean_free_object(x_4);
x_481 = lean_box(1);
x_482 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_10, 4, x_481);
lean_ctor_set(x_10, 3, x_411);
lean_ctor_set(x_10, 2, x_409);
lean_ctor_set(x_10, 1, x_408);
lean_ctor_set(x_10, 0, x_482);
return x_10;
}
}
}
}
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; 
x_483 = lean_ctor_get(x_10, 0);
x_484 = lean_ctor_get(x_10, 1);
x_485 = lean_ctor_get(x_10, 2);
x_486 = lean_ctor_get(x_10, 3);
x_487 = lean_ctor_get(x_10, 4);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_10);
x_488 = lean_ctor_get(x_11, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_11, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_11, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_11, 3);
lean_inc(x_491);
x_492 = lean_ctor_get(x_11, 4);
lean_inc(x_492);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_493 = x_11;
} else {
 lean_dec_ref(x_11);
 x_493 = lean_box(0);
}
x_494 = lean_nat_dec_lt(x_483, x_488);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; 
lean_dec(x_483);
x_495 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_484, x_485, x_486, x_487, lean_box(0), lean_box(0), lean_box(0));
x_496 = lean_ctor_get(x_495, 2);
lean_inc(x_496);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_498);
lean_dec(x_495);
x_499 = lean_ctor_get(x_496, 0);
lean_inc(x_499);
lean_inc(x_492);
lean_inc(x_491);
lean_inc(x_490);
lean_inc(x_489);
lean_inc(x_488);
if (lean_is_scalar(x_493)) {
 x_500 = lean_alloc_ctor(0, 5, 0);
} else {
 x_500 = x_493;
}
lean_ctor_set(x_500, 0, x_488);
lean_ctor_set(x_500, 1, x_489);
lean_ctor_set(x_500, 2, x_490);
lean_ctor_set(x_500, 3, x_491);
lean_ctor_set(x_500, 4, x_492);
x_501 = lean_unsigned_to_nat(3u);
x_502 = lean_nat_mul(x_501, x_499);
x_503 = lean_nat_dec_lt(x_502, x_488);
lean_dec(x_502);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_492);
lean_dec(x_491);
lean_dec(x_490);
lean_dec(x_489);
lean_free_object(x_4);
x_504 = lean_unsigned_to_nat(1u);
x_505 = lean_nat_add(x_504, x_499);
lean_dec(x_499);
x_506 = lean_nat_add(x_505, x_488);
lean_dec(x_488);
lean_dec(x_505);
x_507 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_497);
lean_ctor_set(x_507, 2, x_498);
lean_ctor_set(x_507, 3, x_496);
lean_ctor_set(x_507, 4, x_500);
return x_507;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; 
lean_dec(x_500);
x_508 = lean_ctor_get(x_491, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_491, 1);
lean_inc(x_509);
x_510 = lean_ctor_get(x_491, 2);
lean_inc(x_510);
x_511 = lean_ctor_get(x_491, 3);
lean_inc(x_511);
x_512 = lean_ctor_get(x_491, 4);
lean_inc(x_512);
x_513 = lean_ctor_get(x_492, 0);
lean_inc(x_513);
x_514 = lean_unsigned_to_nat(2u);
x_515 = lean_nat_mul(x_514, x_513);
x_516 = lean_nat_dec_lt(x_508, x_515);
lean_dec(x_515);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_508);
lean_free_object(x_4);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 lean_ctor_release(x_491, 2);
 lean_ctor_release(x_491, 3);
 lean_ctor_release(x_491, 4);
 x_517 = x_491;
} else {
 lean_dec_ref(x_491);
 x_517 = lean_box(0);
}
x_518 = lean_unsigned_to_nat(1u);
x_519 = lean_nat_add(x_518, x_499);
lean_dec(x_499);
x_520 = lean_nat_add(x_519, x_488);
lean_dec(x_488);
x_521 = lean_nat_add(x_518, x_513);
lean_dec(x_513);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_522 = lean_ctor_get(x_511, 0);
lean_inc(x_522);
x_523 = lean_nat_add(x_519, x_522);
lean_dec(x_522);
lean_dec(x_519);
lean_inc(x_496);
if (lean_is_scalar(x_517)) {
 x_524 = lean_alloc_ctor(0, 5, 0);
} else {
 x_524 = x_517;
}
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_497);
lean_ctor_set(x_524, 2, x_498);
lean_ctor_set(x_524, 3, x_496);
lean_ctor_set(x_524, 4, x_511);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 lean_ctor_release(x_496, 2);
 lean_ctor_release(x_496, 3);
 lean_ctor_release(x_496, 4);
 x_525 = x_496;
} else {
 lean_dec_ref(x_496);
 x_525 = lean_box(0);
}
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_526 = lean_ctor_get(x_512, 0);
lean_inc(x_526);
x_527 = lean_nat_add(x_521, x_526);
lean_dec(x_526);
lean_dec(x_521);
if (lean_is_scalar(x_525)) {
 x_528 = lean_alloc_ctor(0, 5, 0);
} else {
 x_528 = x_525;
}
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_489);
lean_ctor_set(x_528, 2, x_490);
lean_ctor_set(x_528, 3, x_512);
lean_ctor_set(x_528, 4, x_492);
x_529 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_529, 0, x_520);
lean_ctor_set(x_529, 1, x_509);
lean_ctor_set(x_529, 2, x_510);
lean_ctor_set(x_529, 3, x_524);
lean_ctor_set(x_529, 4, x_528);
return x_529;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_530 = lean_unsigned_to_nat(0u);
x_531 = lean_nat_add(x_521, x_530);
lean_dec(x_521);
if (lean_is_scalar(x_525)) {
 x_532 = lean_alloc_ctor(0, 5, 0);
} else {
 x_532 = x_525;
}
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_489);
lean_ctor_set(x_532, 2, x_490);
lean_ctor_set(x_532, 3, x_512);
lean_ctor_set(x_532, 4, x_492);
x_533 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_533, 0, x_520);
lean_ctor_set(x_533, 1, x_509);
lean_ctor_set(x_533, 2, x_510);
lean_ctor_set(x_533, 3, x_524);
lean_ctor_set(x_533, 4, x_532);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_534 = lean_unsigned_to_nat(0u);
x_535 = lean_nat_add(x_519, x_534);
lean_dec(x_519);
lean_inc(x_496);
if (lean_is_scalar(x_517)) {
 x_536 = lean_alloc_ctor(0, 5, 0);
} else {
 x_536 = x_517;
}
lean_ctor_set(x_536, 0, x_535);
lean_ctor_set(x_536, 1, x_497);
lean_ctor_set(x_536, 2, x_498);
lean_ctor_set(x_536, 3, x_496);
lean_ctor_set(x_536, 4, x_511);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 lean_ctor_release(x_496, 2);
 lean_ctor_release(x_496, 3);
 lean_ctor_release(x_496, 4);
 x_537 = x_496;
} else {
 lean_dec_ref(x_496);
 x_537 = lean_box(0);
}
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_538 = lean_ctor_get(x_512, 0);
lean_inc(x_538);
x_539 = lean_nat_add(x_521, x_538);
lean_dec(x_538);
lean_dec(x_521);
if (lean_is_scalar(x_537)) {
 x_540 = lean_alloc_ctor(0, 5, 0);
} else {
 x_540 = x_537;
}
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_489);
lean_ctor_set(x_540, 2, x_490);
lean_ctor_set(x_540, 3, x_512);
lean_ctor_set(x_540, 4, x_492);
x_541 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_541, 0, x_520);
lean_ctor_set(x_541, 1, x_509);
lean_ctor_set(x_541, 2, x_510);
lean_ctor_set(x_541, 3, x_536);
lean_ctor_set(x_541, 4, x_540);
return x_541;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_nat_add(x_521, x_534);
lean_dec(x_521);
if (lean_is_scalar(x_537)) {
 x_543 = lean_alloc_ctor(0, 5, 0);
} else {
 x_543 = x_537;
}
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_489);
lean_ctor_set(x_543, 2, x_490);
lean_ctor_set(x_543, 3, x_512);
lean_ctor_set(x_543, 4, x_492);
x_544 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_544, 0, x_520);
lean_ctor_set(x_544, 1, x_509);
lean_ctor_set(x_544, 2, x_510);
lean_ctor_set(x_544, 3, x_536);
lean_ctor_set(x_544, 4, x_543);
return x_544;
}
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
x_545 = lean_unsigned_to_nat(1u);
x_546 = lean_nat_add(x_545, x_499);
lean_dec(x_499);
x_547 = lean_nat_add(x_546, x_488);
lean_dec(x_488);
x_548 = lean_nat_add(x_546, x_508);
lean_dec(x_508);
lean_dec(x_546);
x_549 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_497);
lean_ctor_set(x_549, 2, x_498);
lean_ctor_set(x_549, 3, x_496);
lean_ctor_set(x_549, 4, x_491);
lean_ctor_set(x_4, 4, x_492);
lean_ctor_set(x_4, 3, x_549);
lean_ctor_set(x_4, 2, x_490);
lean_ctor_set(x_4, 1, x_489);
lean_ctor_set(x_4, 0, x_547);
return x_4;
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_491) == 0)
{
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_550 = lean_ctor_get(x_495, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_495, 1);
lean_inc(x_551);
lean_dec(x_495);
x_552 = lean_ctor_get(x_491, 0);
lean_inc(x_552);
x_553 = lean_unsigned_to_nat(1u);
x_554 = lean_nat_add(x_553, x_488);
lean_dec(x_488);
x_555 = lean_nat_add(x_553, x_552);
lean_dec(x_552);
x_556 = lean_box(1);
if (lean_is_scalar(x_493)) {
 x_557 = lean_alloc_ctor(0, 5, 0);
} else {
 x_557 = x_493;
}
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_550);
lean_ctor_set(x_557, 2, x_551);
lean_ctor_set(x_557, 3, x_556);
lean_ctor_set(x_557, 4, x_491);
x_558 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_558, 0, x_554);
lean_ctor_set(x_558, 1, x_489);
lean_ctor_set(x_558, 2, x_490);
lean_ctor_set(x_558, 3, x_557);
lean_ctor_set(x_558, 4, x_492);
return x_558;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_488);
x_559 = lean_ctor_get(x_495, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_495, 1);
lean_inc(x_560);
lean_dec(x_495);
x_561 = lean_ctor_get(x_491, 1);
lean_inc(x_561);
x_562 = lean_ctor_get(x_491, 2);
lean_inc(x_562);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 lean_ctor_release(x_491, 2);
 lean_ctor_release(x_491, 3);
 lean_ctor_release(x_491, 4);
 x_563 = x_491;
} else {
 lean_dec_ref(x_491);
 x_563 = lean_box(0);
}
x_564 = lean_box(1);
x_565 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_563)) {
 x_566 = lean_alloc_ctor(0, 5, 0);
} else {
 x_566 = x_563;
}
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_559);
lean_ctor_set(x_566, 2, x_560);
lean_ctor_set(x_566, 3, x_564);
lean_ctor_set(x_566, 4, x_564);
if (lean_is_scalar(x_493)) {
 x_567 = lean_alloc_ctor(0, 5, 0);
} else {
 x_567 = x_493;
}
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_489);
lean_ctor_set(x_567, 2, x_490);
lean_ctor_set(x_567, 3, x_564);
lean_ctor_set(x_567, 4, x_564);
x_568 = lean_unsigned_to_nat(3u);
x_569 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_561);
lean_ctor_set(x_569, 2, x_562);
lean_ctor_set(x_569, 3, x_566);
lean_ctor_set(x_569, 4, x_567);
return x_569;
}
}
else
{
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_488);
x_570 = lean_ctor_get(x_495, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_495, 1);
lean_inc(x_571);
lean_dec(x_495);
x_572 = lean_box(1);
x_573 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_493)) {
 x_574 = lean_alloc_ctor(0, 5, 0);
} else {
 x_574 = x_493;
}
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_570);
lean_ctor_set(x_574, 2, x_571);
lean_ctor_set(x_574, 3, x_572);
lean_ctor_set(x_574, 4, x_572);
x_575 = lean_unsigned_to_nat(3u);
x_576 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_489);
lean_ctor_set(x_576, 2, x_490);
lean_ctor_set(x_576, 3, x_574);
lean_ctor_set(x_576, 4, x_492);
return x_576;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_577 = lean_ctor_get(x_495, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_495, 1);
lean_inc(x_578);
lean_dec(x_495);
if (lean_is_scalar(x_493)) {
 x_579 = lean_alloc_ctor(0, 5, 0);
} else {
 x_579 = x_493;
}
lean_ctor_set(x_579, 0, x_488);
lean_ctor_set(x_579, 1, x_489);
lean_ctor_set(x_579, 2, x_490);
lean_ctor_set(x_579, 3, x_492);
lean_ctor_set(x_579, 4, x_492);
x_580 = lean_box(1);
x_581 = lean_unsigned_to_nat(2u);
x_582 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_577);
lean_ctor_set(x_582, 2, x_578);
lean_ctor_set(x_582, 3, x_580);
lean_ctor_set(x_582, 4, x_579);
return x_582;
}
}
}
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_488);
x_583 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_489, x_490, x_491, x_492, lean_box(0), lean_box(0), lean_box(0));
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
x_586 = lean_ctor_get(x_583, 2);
lean_inc(x_586);
lean_dec(x_583);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
if (lean_is_scalar(x_493)) {
 x_587 = lean_alloc_ctor(0, 5, 0);
} else {
 x_587 = x_493;
}
lean_ctor_set(x_587, 0, x_483);
lean_ctor_set(x_587, 1, x_484);
lean_ctor_set(x_587, 2, x_485);
lean_ctor_set(x_587, 3, x_486);
lean_ctor_set(x_587, 4, x_487);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; 
x_588 = lean_ctor_get(x_586, 0);
lean_inc(x_588);
x_589 = lean_unsigned_to_nat(3u);
x_590 = lean_nat_mul(x_589, x_588);
x_591 = lean_nat_dec_lt(x_590, x_483);
lean_dec(x_590);
if (x_591 == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_484);
lean_free_object(x_4);
x_592 = lean_unsigned_to_nat(1u);
x_593 = lean_nat_add(x_592, x_483);
lean_dec(x_483);
x_594 = lean_nat_add(x_593, x_588);
lean_dec(x_588);
lean_dec(x_593);
x_595 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_595, 0, x_594);
lean_ctor_set(x_595, 1, x_584);
lean_ctor_set(x_595, 2, x_585);
lean_ctor_set(x_595, 3, x_587);
lean_ctor_set(x_595, 4, x_586);
return x_595;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
lean_dec(x_587);
x_596 = lean_ctor_get(x_486, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_487, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_487, 1);
lean_inc(x_598);
x_599 = lean_ctor_get(x_487, 2);
lean_inc(x_599);
x_600 = lean_ctor_get(x_487, 3);
lean_inc(x_600);
x_601 = lean_ctor_get(x_487, 4);
lean_inc(x_601);
x_602 = lean_unsigned_to_nat(2u);
x_603 = lean_nat_mul(x_602, x_596);
x_604 = lean_nat_dec_lt(x_597, x_603);
lean_dec(x_603);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_597);
lean_free_object(x_4);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 lean_ctor_release(x_487, 4);
 x_605 = x_487;
} else {
 lean_dec_ref(x_487);
 x_605 = lean_box(0);
}
x_606 = lean_unsigned_to_nat(1u);
x_607 = lean_nat_add(x_606, x_483);
lean_dec(x_483);
x_608 = lean_nat_add(x_607, x_588);
lean_dec(x_607);
x_609 = lean_nat_add(x_606, x_596);
lean_dec(x_596);
x_610 = lean_nat_add(x_606, x_588);
lean_dec(x_588);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_611 = lean_ctor_get(x_600, 0);
lean_inc(x_611);
x_612 = lean_nat_add(x_609, x_611);
lean_dec(x_611);
lean_dec(x_609);
lean_inc(x_486);
if (lean_is_scalar(x_605)) {
 x_613 = lean_alloc_ctor(0, 5, 0);
} else {
 x_613 = x_605;
}
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_484);
lean_ctor_set(x_613, 2, x_485);
lean_ctor_set(x_613, 3, x_486);
lean_ctor_set(x_613, 4, x_600);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 lean_ctor_release(x_486, 2);
 lean_ctor_release(x_486, 3);
 lean_ctor_release(x_486, 4);
 x_614 = x_486;
} else {
 lean_dec_ref(x_486);
 x_614 = lean_box(0);
}
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_615 = lean_ctor_get(x_601, 0);
lean_inc(x_615);
x_616 = lean_nat_add(x_610, x_615);
lean_dec(x_615);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_614)) {
 x_617 = lean_alloc_ctor(0, 5, 0);
} else {
 x_617 = x_614;
}
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_584);
lean_ctor_set(x_617, 2, x_585);
lean_ctor_set(x_617, 3, x_601);
lean_ctor_set(x_617, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_618 = x_586;
} else {
 lean_dec_ref(x_586);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(0, 5, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_608);
lean_ctor_set(x_619, 1, x_598);
lean_ctor_set(x_619, 2, x_599);
lean_ctor_set(x_619, 3, x_613);
lean_ctor_set(x_619, 4, x_617);
return x_619;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_620 = lean_unsigned_to_nat(0u);
x_621 = lean_nat_add(x_610, x_620);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_614)) {
 x_622 = lean_alloc_ctor(0, 5, 0);
} else {
 x_622 = x_614;
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_584);
lean_ctor_set(x_622, 2, x_585);
lean_ctor_set(x_622, 3, x_601);
lean_ctor_set(x_622, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_623 = x_586;
} else {
 lean_dec_ref(x_586);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(0, 5, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_608);
lean_ctor_set(x_624, 1, x_598);
lean_ctor_set(x_624, 2, x_599);
lean_ctor_set(x_624, 3, x_613);
lean_ctor_set(x_624, 4, x_622);
return x_624;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_625 = lean_unsigned_to_nat(0u);
x_626 = lean_nat_add(x_609, x_625);
lean_dec(x_609);
lean_inc(x_486);
if (lean_is_scalar(x_605)) {
 x_627 = lean_alloc_ctor(0, 5, 0);
} else {
 x_627 = x_605;
}
lean_ctor_set(x_627, 0, x_626);
lean_ctor_set(x_627, 1, x_484);
lean_ctor_set(x_627, 2, x_485);
lean_ctor_set(x_627, 3, x_486);
lean_ctor_set(x_627, 4, x_600);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 lean_ctor_release(x_486, 2);
 lean_ctor_release(x_486, 3);
 lean_ctor_release(x_486, 4);
 x_628 = x_486;
} else {
 lean_dec_ref(x_486);
 x_628 = lean_box(0);
}
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_629 = lean_ctor_get(x_601, 0);
lean_inc(x_629);
x_630 = lean_nat_add(x_610, x_629);
lean_dec(x_629);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_628)) {
 x_631 = lean_alloc_ctor(0, 5, 0);
} else {
 x_631 = x_628;
}
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_584);
lean_ctor_set(x_631, 2, x_585);
lean_ctor_set(x_631, 3, x_601);
lean_ctor_set(x_631, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_632 = x_586;
} else {
 lean_dec_ref(x_586);
 x_632 = lean_box(0);
}
if (lean_is_scalar(x_632)) {
 x_633 = lean_alloc_ctor(0, 5, 0);
} else {
 x_633 = x_632;
}
lean_ctor_set(x_633, 0, x_608);
lean_ctor_set(x_633, 1, x_598);
lean_ctor_set(x_633, 2, x_599);
lean_ctor_set(x_633, 3, x_627);
lean_ctor_set(x_633, 4, x_631);
return x_633;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_634 = lean_nat_add(x_610, x_625);
lean_dec(x_610);
lean_inc(x_586);
if (lean_is_scalar(x_628)) {
 x_635 = lean_alloc_ctor(0, 5, 0);
} else {
 x_635 = x_628;
}
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_584);
lean_ctor_set(x_635, 2, x_585);
lean_ctor_set(x_635, 3, x_601);
lean_ctor_set(x_635, 4, x_586);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 lean_ctor_release(x_586, 3);
 lean_ctor_release(x_586, 4);
 x_636 = x_586;
} else {
 lean_dec_ref(x_586);
 x_636 = lean_box(0);
}
if (lean_is_scalar(x_636)) {
 x_637 = lean_alloc_ctor(0, 5, 0);
} else {
 x_637 = x_636;
}
lean_ctor_set(x_637, 0, x_608);
lean_ctor_set(x_637, 1, x_598);
lean_ctor_set(x_637, 2, x_599);
lean_ctor_set(x_637, 3, x_627);
lean_ctor_set(x_637, 4, x_635);
return x_637;
}
}
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_596);
x_638 = lean_unsigned_to_nat(1u);
x_639 = lean_nat_add(x_638, x_483);
lean_dec(x_483);
x_640 = lean_nat_add(x_639, x_588);
lean_dec(x_639);
x_641 = lean_nat_add(x_638, x_588);
lean_dec(x_588);
x_642 = lean_nat_add(x_641, x_597);
lean_dec(x_597);
lean_dec(x_641);
x_643 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_584);
lean_ctor_set(x_643, 2, x_585);
lean_ctor_set(x_643, 3, x_487);
lean_ctor_set(x_643, 4, x_586);
lean_ctor_set(x_4, 4, x_643);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_640);
return x_4;
}
}
}
else
{
if (lean_obj_tag(x_486) == 0)
{
lean_dec(x_587);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_644 = lean_ctor_get(x_487, 0);
lean_inc(x_644);
x_645 = lean_unsigned_to_nat(1u);
x_646 = lean_nat_add(x_645, x_483);
lean_dec(x_483);
x_647 = lean_nat_add(x_645, x_644);
lean_dec(x_644);
x_648 = lean_box(1);
x_649 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_649, 0, x_647);
lean_ctor_set(x_649, 1, x_584);
lean_ctor_set(x_649, 2, x_585);
lean_ctor_set(x_649, 3, x_487);
lean_ctor_set(x_649, 4, x_648);
lean_ctor_set(x_4, 4, x_649);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_646);
return x_4;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_483);
x_650 = lean_box(1);
x_651 = lean_unsigned_to_nat(1u);
x_652 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_584);
lean_ctor_set(x_652, 2, x_585);
lean_ctor_set(x_652, 3, x_650);
lean_ctor_set(x_652, 4, x_650);
x_653 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_652);
lean_ctor_set(x_4, 3, x_486);
lean_ctor_set(x_4, 2, x_485);
lean_ctor_set(x_4, 1, x_484);
lean_ctor_set(x_4, 0, x_653);
return x_4;
}
}
else
{
lean_dec(x_483);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_587);
x_654 = lean_ctor_get(x_487, 1);
lean_inc(x_654);
x_655 = lean_ctor_get(x_487, 2);
lean_inc(x_655);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 lean_ctor_release(x_487, 4);
 x_656 = x_487;
} else {
 lean_dec_ref(x_487);
 x_656 = lean_box(0);
}
x_657 = lean_box(1);
x_658 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_656)) {
 x_659 = lean_alloc_ctor(0, 5, 0);
} else {
 x_659 = x_656;
}
lean_ctor_set(x_659, 0, x_658);
lean_ctor_set(x_659, 1, x_484);
lean_ctor_set(x_659, 2, x_485);
lean_ctor_set(x_659, 3, x_657);
lean_ctor_set(x_659, 4, x_657);
x_660 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_584);
lean_ctor_set(x_660, 2, x_585);
lean_ctor_set(x_660, 3, x_657);
lean_ctor_set(x_660, 4, x_657);
x_661 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_4, 4, x_660);
lean_ctor_set(x_4, 3, x_659);
lean_ctor_set(x_4, 2, x_655);
lean_ctor_set(x_4, 1, x_654);
lean_ctor_set(x_4, 0, x_661);
return x_4;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_485);
lean_dec(x_484);
lean_free_object(x_4);
x_662 = lean_box(1);
x_663 = lean_unsigned_to_nat(2u);
x_664 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_584);
lean_ctor_set(x_664, 2, x_585);
lean_ctor_set(x_664, 3, x_587);
lean_ctor_set(x_664, 4, x_662);
return x_664;
}
}
}
}
}
}
else
{
lean_free_object(x_4);
return x_10;
}
}
else
{
lean_free_object(x_4);
return x_11;
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_17, 0);
lean_inc(x_665);
lean_dec(x_17);
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
lean_dec(x_665);
lean_ctor_set(x_4, 2, x_667);
lean_ctor_set(x_4, 1, x_666);
return x_4;
}
}
default: 
{
lean_object* x_668; lean_object* x_669; 
lean_free_object(x_4);
lean_dec(x_7);
x_668 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_Const_alter_u2098___spec__1___rarg(x_1, x_2, x_3, x_11, lean_box(0));
x_669 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_8, x_9, x_10, x_668, lean_box(0), lean_box(0), lean_box(0));
return x_669;
}
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; 
x_670 = lean_ctor_get(x_4, 0);
x_671 = lean_ctor_get(x_4, 1);
x_672 = lean_ctor_get(x_4, 2);
x_673 = lean_ctor_get(x_4, 3);
x_674 = lean_ctor_get(x_4, 4);
lean_inc(x_674);
lean_inc(x_673);
lean_inc(x_672);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_671);
lean_inc(x_2);
x_675 = lean_apply_2(x_1, x_2, x_671);
x_676 = lean_unbox(x_675);
lean_dec(x_675);
switch (x_676) {
case 0:
{
lean_object* x_677; lean_object* x_678; 
lean_dec(x_670);
x_677 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_Const_alter_u2098___spec__1___rarg(x_1, x_2, x_3, x_673, lean_box(0));
x_678 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_671, x_672, x_677, x_674, lean_box(0), lean_box(0), lean_box(0));
return x_678;
}
case 1:
{
lean_object* x_679; lean_object* x_680; 
lean_dec(x_2);
lean_dec(x_1);
x_679 = l_Std_DTreeMap_Internal_Cell_ofEq___rarg(x_671, x_672, lean_box(0));
x_680 = lean_apply_1(x_3, x_679);
if (lean_obj_tag(x_680) == 0)
{
lean_dec(x_670);
if (lean_obj_tag(x_673) == 0)
{
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; uint8_t x_693; 
x_681 = lean_ctor_get(x_673, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_673, 1);
lean_inc(x_682);
x_683 = lean_ctor_get(x_673, 2);
lean_inc(x_683);
x_684 = lean_ctor_get(x_673, 3);
lean_inc(x_684);
x_685 = lean_ctor_get(x_673, 4);
lean_inc(x_685);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 lean_ctor_release(x_673, 2);
 lean_ctor_release(x_673, 3);
 lean_ctor_release(x_673, 4);
 x_686 = x_673;
} else {
 lean_dec_ref(x_673);
 x_686 = lean_box(0);
}
x_687 = lean_ctor_get(x_674, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_674, 1);
lean_inc(x_688);
x_689 = lean_ctor_get(x_674, 2);
lean_inc(x_689);
x_690 = lean_ctor_get(x_674, 3);
lean_inc(x_690);
x_691 = lean_ctor_get(x_674, 4);
lean_inc(x_691);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 lean_ctor_release(x_674, 4);
 x_692 = x_674;
} else {
 lean_dec_ref(x_674);
 x_692 = lean_box(0);
}
x_693 = lean_nat_dec_lt(x_681, x_687);
if (x_693 == 0)
{
lean_object* x_694; lean_object* x_695; 
lean_dec(x_681);
x_694 = l_Std_DTreeMap_Internal_Impl_maxView___rarg(x_682, x_683, x_684, x_685, lean_box(0), lean_box(0), lean_box(0));
x_695 = lean_ctor_get(x_694, 2);
lean_inc(x_695);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; 
x_696 = lean_ctor_get(x_694, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_694, 1);
lean_inc(x_697);
lean_dec(x_694);
x_698 = lean_ctor_get(x_695, 0);
lean_inc(x_698);
lean_inc(x_691);
lean_inc(x_690);
lean_inc(x_689);
lean_inc(x_688);
lean_inc(x_687);
if (lean_is_scalar(x_692)) {
 x_699 = lean_alloc_ctor(0, 5, 0);
} else {
 x_699 = x_692;
}
lean_ctor_set(x_699, 0, x_687);
lean_ctor_set(x_699, 1, x_688);
lean_ctor_set(x_699, 2, x_689);
lean_ctor_set(x_699, 3, x_690);
lean_ctor_set(x_699, 4, x_691);
x_700 = lean_unsigned_to_nat(3u);
x_701 = lean_nat_mul(x_700, x_698);
x_702 = lean_nat_dec_lt(x_701, x_687);
lean_dec(x_701);
if (x_702 == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_dec(x_691);
lean_dec(x_690);
lean_dec(x_689);
lean_dec(x_688);
x_703 = lean_unsigned_to_nat(1u);
x_704 = lean_nat_add(x_703, x_698);
lean_dec(x_698);
x_705 = lean_nat_add(x_704, x_687);
lean_dec(x_687);
lean_dec(x_704);
if (lean_is_scalar(x_686)) {
 x_706 = lean_alloc_ctor(0, 5, 0);
} else {
 x_706 = x_686;
}
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_696);
lean_ctor_set(x_706, 2, x_697);
lean_ctor_set(x_706, 3, x_695);
lean_ctor_set(x_706, 4, x_699);
return x_706;
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; 
lean_dec(x_699);
x_707 = lean_ctor_get(x_690, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_690, 1);
lean_inc(x_708);
x_709 = lean_ctor_get(x_690, 2);
lean_inc(x_709);
x_710 = lean_ctor_get(x_690, 3);
lean_inc(x_710);
x_711 = lean_ctor_get(x_690, 4);
lean_inc(x_711);
x_712 = lean_ctor_get(x_691, 0);
lean_inc(x_712);
x_713 = lean_unsigned_to_nat(2u);
x_714 = lean_nat_mul(x_713, x_712);
x_715 = lean_nat_dec_lt(x_707, x_714);
lean_dec(x_714);
if (x_715 == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_707);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 lean_ctor_release(x_690, 2);
 lean_ctor_release(x_690, 3);
 lean_ctor_release(x_690, 4);
 x_716 = x_690;
} else {
 lean_dec_ref(x_690);
 x_716 = lean_box(0);
}
x_717 = lean_unsigned_to_nat(1u);
x_718 = lean_nat_add(x_717, x_698);
lean_dec(x_698);
x_719 = lean_nat_add(x_718, x_687);
lean_dec(x_687);
x_720 = lean_nat_add(x_717, x_712);
lean_dec(x_712);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_721 = lean_ctor_get(x_710, 0);
lean_inc(x_721);
x_722 = lean_nat_add(x_718, x_721);
lean_dec(x_721);
lean_dec(x_718);
lean_inc(x_695);
if (lean_is_scalar(x_716)) {
 x_723 = lean_alloc_ctor(0, 5, 0);
} else {
 x_723 = x_716;
}
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_696);
lean_ctor_set(x_723, 2, x_697);
lean_ctor_set(x_723, 3, x_695);
lean_ctor_set(x_723, 4, x_710);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 lean_ctor_release(x_695, 2);
 lean_ctor_release(x_695, 3);
 lean_ctor_release(x_695, 4);
 x_724 = x_695;
} else {
 lean_dec_ref(x_695);
 x_724 = lean_box(0);
}
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_725 = lean_ctor_get(x_711, 0);
lean_inc(x_725);
x_726 = lean_nat_add(x_720, x_725);
lean_dec(x_725);
lean_dec(x_720);
if (lean_is_scalar(x_724)) {
 x_727 = lean_alloc_ctor(0, 5, 0);
} else {
 x_727 = x_724;
}
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_688);
lean_ctor_set(x_727, 2, x_689);
lean_ctor_set(x_727, 3, x_711);
lean_ctor_set(x_727, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_728 = lean_alloc_ctor(0, 5, 0);
} else {
 x_728 = x_686;
}
lean_ctor_set(x_728, 0, x_719);
lean_ctor_set(x_728, 1, x_708);
lean_ctor_set(x_728, 2, x_709);
lean_ctor_set(x_728, 3, x_723);
lean_ctor_set(x_728, 4, x_727);
return x_728;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_729 = lean_unsigned_to_nat(0u);
x_730 = lean_nat_add(x_720, x_729);
lean_dec(x_720);
if (lean_is_scalar(x_724)) {
 x_731 = lean_alloc_ctor(0, 5, 0);
} else {
 x_731 = x_724;
}
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_688);
lean_ctor_set(x_731, 2, x_689);
lean_ctor_set(x_731, 3, x_711);
lean_ctor_set(x_731, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_732 = lean_alloc_ctor(0, 5, 0);
} else {
 x_732 = x_686;
}
lean_ctor_set(x_732, 0, x_719);
lean_ctor_set(x_732, 1, x_708);
lean_ctor_set(x_732, 2, x_709);
lean_ctor_set(x_732, 3, x_723);
lean_ctor_set(x_732, 4, x_731);
return x_732;
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_733 = lean_unsigned_to_nat(0u);
x_734 = lean_nat_add(x_718, x_733);
lean_dec(x_718);
lean_inc(x_695);
if (lean_is_scalar(x_716)) {
 x_735 = lean_alloc_ctor(0, 5, 0);
} else {
 x_735 = x_716;
}
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_696);
lean_ctor_set(x_735, 2, x_697);
lean_ctor_set(x_735, 3, x_695);
lean_ctor_set(x_735, 4, x_710);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 lean_ctor_release(x_695, 2);
 lean_ctor_release(x_695, 3);
 lean_ctor_release(x_695, 4);
 x_736 = x_695;
} else {
 lean_dec_ref(x_695);
 x_736 = lean_box(0);
}
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_737 = lean_ctor_get(x_711, 0);
lean_inc(x_737);
x_738 = lean_nat_add(x_720, x_737);
lean_dec(x_737);
lean_dec(x_720);
if (lean_is_scalar(x_736)) {
 x_739 = lean_alloc_ctor(0, 5, 0);
} else {
 x_739 = x_736;
}
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_688);
lean_ctor_set(x_739, 2, x_689);
lean_ctor_set(x_739, 3, x_711);
lean_ctor_set(x_739, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_740 = lean_alloc_ctor(0, 5, 0);
} else {
 x_740 = x_686;
}
lean_ctor_set(x_740, 0, x_719);
lean_ctor_set(x_740, 1, x_708);
lean_ctor_set(x_740, 2, x_709);
lean_ctor_set(x_740, 3, x_735);
lean_ctor_set(x_740, 4, x_739);
return x_740;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_741 = lean_nat_add(x_720, x_733);
lean_dec(x_720);
if (lean_is_scalar(x_736)) {
 x_742 = lean_alloc_ctor(0, 5, 0);
} else {
 x_742 = x_736;
}
lean_ctor_set(x_742, 0, x_741);
lean_ctor_set(x_742, 1, x_688);
lean_ctor_set(x_742, 2, x_689);
lean_ctor_set(x_742, 3, x_711);
lean_ctor_set(x_742, 4, x_691);
if (lean_is_scalar(x_686)) {
 x_743 = lean_alloc_ctor(0, 5, 0);
} else {
 x_743 = x_686;
}
lean_ctor_set(x_743, 0, x_719);
lean_ctor_set(x_743, 1, x_708);
lean_ctor_set(x_743, 2, x_709);
lean_ctor_set(x_743, 3, x_735);
lean_ctor_set(x_743, 4, x_742);
return x_743;
}
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_dec(x_712);
lean_dec(x_711);
lean_dec(x_710);
lean_dec(x_709);
lean_dec(x_708);
x_744 = lean_unsigned_to_nat(1u);
x_745 = lean_nat_add(x_744, x_698);
lean_dec(x_698);
x_746 = lean_nat_add(x_745, x_687);
lean_dec(x_687);
x_747 = lean_nat_add(x_745, x_707);
lean_dec(x_707);
lean_dec(x_745);
if (lean_is_scalar(x_686)) {
 x_748 = lean_alloc_ctor(0, 5, 0);
} else {
 x_748 = x_686;
}
lean_ctor_set(x_748, 0, x_747);
lean_ctor_set(x_748, 1, x_696);
lean_ctor_set(x_748, 2, x_697);
lean_ctor_set(x_748, 3, x_695);
lean_ctor_set(x_748, 4, x_690);
x_749 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_749, 0, x_746);
lean_ctor_set(x_749, 1, x_688);
lean_ctor_set(x_749, 2, x_689);
lean_ctor_set(x_749, 3, x_748);
lean_ctor_set(x_749, 4, x_691);
return x_749;
}
}
}
else
{
if (lean_obj_tag(x_690) == 0)
{
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_750 = lean_ctor_get(x_694, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_694, 1);
lean_inc(x_751);
lean_dec(x_694);
x_752 = lean_ctor_get(x_690, 0);
lean_inc(x_752);
x_753 = lean_unsigned_to_nat(1u);
x_754 = lean_nat_add(x_753, x_687);
lean_dec(x_687);
x_755 = lean_nat_add(x_753, x_752);
lean_dec(x_752);
x_756 = lean_box(1);
if (lean_is_scalar(x_692)) {
 x_757 = lean_alloc_ctor(0, 5, 0);
} else {
 x_757 = x_692;
}
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set(x_757, 1, x_750);
lean_ctor_set(x_757, 2, x_751);
lean_ctor_set(x_757, 3, x_756);
lean_ctor_set(x_757, 4, x_690);
if (lean_is_scalar(x_686)) {
 x_758 = lean_alloc_ctor(0, 5, 0);
} else {
 x_758 = x_686;
}
lean_ctor_set(x_758, 0, x_754);
lean_ctor_set(x_758, 1, x_688);
lean_ctor_set(x_758, 2, x_689);
lean_ctor_set(x_758, 3, x_757);
lean_ctor_set(x_758, 4, x_691);
return x_758;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_687);
x_759 = lean_ctor_get(x_694, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_694, 1);
lean_inc(x_760);
lean_dec(x_694);
x_761 = lean_ctor_get(x_690, 1);
lean_inc(x_761);
x_762 = lean_ctor_get(x_690, 2);
lean_inc(x_762);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 lean_ctor_release(x_690, 2);
 lean_ctor_release(x_690, 3);
 lean_ctor_release(x_690, 4);
 x_763 = x_690;
} else {
 lean_dec_ref(x_690);
 x_763 = lean_box(0);
}
x_764 = lean_box(1);
x_765 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_763)) {
 x_766 = lean_alloc_ctor(0, 5, 0);
} else {
 x_766 = x_763;
}
lean_ctor_set(x_766, 0, x_765);
lean_ctor_set(x_766, 1, x_759);
lean_ctor_set(x_766, 2, x_760);
lean_ctor_set(x_766, 3, x_764);
lean_ctor_set(x_766, 4, x_764);
if (lean_is_scalar(x_692)) {
 x_767 = lean_alloc_ctor(0, 5, 0);
} else {
 x_767 = x_692;
}
lean_ctor_set(x_767, 0, x_765);
lean_ctor_set(x_767, 1, x_688);
lean_ctor_set(x_767, 2, x_689);
lean_ctor_set(x_767, 3, x_764);
lean_ctor_set(x_767, 4, x_764);
x_768 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_686)) {
 x_769 = lean_alloc_ctor(0, 5, 0);
} else {
 x_769 = x_686;
}
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_761);
lean_ctor_set(x_769, 2, x_762);
lean_ctor_set(x_769, 3, x_766);
lean_ctor_set(x_769, 4, x_767);
return x_769;
}
}
else
{
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
lean_dec(x_687);
x_770 = lean_ctor_get(x_694, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_694, 1);
lean_inc(x_771);
lean_dec(x_694);
x_772 = lean_box(1);
x_773 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_692)) {
 x_774 = lean_alloc_ctor(0, 5, 0);
} else {
 x_774 = x_692;
}
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_770);
lean_ctor_set(x_774, 2, x_771);
lean_ctor_set(x_774, 3, x_772);
lean_ctor_set(x_774, 4, x_772);
x_775 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_686)) {
 x_776 = lean_alloc_ctor(0, 5, 0);
} else {
 x_776 = x_686;
}
lean_ctor_set(x_776, 0, x_775);
lean_ctor_set(x_776, 1, x_688);
lean_ctor_set(x_776, 2, x_689);
lean_ctor_set(x_776, 3, x_774);
lean_ctor_set(x_776, 4, x_691);
return x_776;
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_777 = lean_ctor_get(x_694, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_694, 1);
lean_inc(x_778);
lean_dec(x_694);
if (lean_is_scalar(x_692)) {
 x_779 = lean_alloc_ctor(0, 5, 0);
} else {
 x_779 = x_692;
}
lean_ctor_set(x_779, 0, x_687);
lean_ctor_set(x_779, 1, x_688);
lean_ctor_set(x_779, 2, x_689);
lean_ctor_set(x_779, 3, x_691);
lean_ctor_set(x_779, 4, x_691);
x_780 = lean_box(1);
x_781 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_686)) {
 x_782 = lean_alloc_ctor(0, 5, 0);
} else {
 x_782 = x_686;
}
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_777);
lean_ctor_set(x_782, 2, x_778);
lean_ctor_set(x_782, 3, x_780);
lean_ctor_set(x_782, 4, x_779);
return x_782;
}
}
}
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
lean_dec(x_687);
x_783 = l_Std_DTreeMap_Internal_Impl_minView___rarg(x_688, x_689, x_690, x_691, lean_box(0), lean_box(0), lean_box(0));
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
x_786 = lean_ctor_get(x_783, 2);
lean_inc(x_786);
lean_dec(x_783);
lean_inc(x_685);
lean_inc(x_684);
lean_inc(x_683);
lean_inc(x_682);
lean_inc(x_681);
if (lean_is_scalar(x_692)) {
 x_787 = lean_alloc_ctor(0, 5, 0);
} else {
 x_787 = x_692;
}
lean_ctor_set(x_787, 0, x_681);
lean_ctor_set(x_787, 1, x_682);
lean_ctor_set(x_787, 2, x_683);
lean_ctor_set(x_787, 3, x_684);
lean_ctor_set(x_787, 4, x_685);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; 
x_788 = lean_ctor_get(x_786, 0);
lean_inc(x_788);
x_789 = lean_unsigned_to_nat(3u);
x_790 = lean_nat_mul(x_789, x_788);
x_791 = lean_nat_dec_lt(x_790, x_681);
lean_dec(x_790);
if (x_791 == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_683);
lean_dec(x_682);
x_792 = lean_unsigned_to_nat(1u);
x_793 = lean_nat_add(x_792, x_681);
lean_dec(x_681);
x_794 = lean_nat_add(x_793, x_788);
lean_dec(x_788);
lean_dec(x_793);
if (lean_is_scalar(x_686)) {
 x_795 = lean_alloc_ctor(0, 5, 0);
} else {
 x_795 = x_686;
}
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_784);
lean_ctor_set(x_795, 2, x_785);
lean_ctor_set(x_795, 3, x_787);
lean_ctor_set(x_795, 4, x_786);
return x_795;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; uint8_t x_804; 
lean_dec(x_787);
x_796 = lean_ctor_get(x_684, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_685, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_685, 1);
lean_inc(x_798);
x_799 = lean_ctor_get(x_685, 2);
lean_inc(x_799);
x_800 = lean_ctor_get(x_685, 3);
lean_inc(x_800);
x_801 = lean_ctor_get(x_685, 4);
lean_inc(x_801);
x_802 = lean_unsigned_to_nat(2u);
x_803 = lean_nat_mul(x_802, x_796);
x_804 = lean_nat_dec_lt(x_797, x_803);
lean_dec(x_803);
if (x_804 == 0)
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_797);
lean_dec(x_686);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 lean_ctor_release(x_685, 2);
 lean_ctor_release(x_685, 3);
 lean_ctor_release(x_685, 4);
 x_805 = x_685;
} else {
 lean_dec_ref(x_685);
 x_805 = lean_box(0);
}
x_806 = lean_unsigned_to_nat(1u);
x_807 = lean_nat_add(x_806, x_681);
lean_dec(x_681);
x_808 = lean_nat_add(x_807, x_788);
lean_dec(x_807);
x_809 = lean_nat_add(x_806, x_796);
lean_dec(x_796);
x_810 = lean_nat_add(x_806, x_788);
lean_dec(x_788);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_811 = lean_ctor_get(x_800, 0);
lean_inc(x_811);
x_812 = lean_nat_add(x_809, x_811);
lean_dec(x_811);
lean_dec(x_809);
lean_inc(x_684);
if (lean_is_scalar(x_805)) {
 x_813 = lean_alloc_ctor(0, 5, 0);
} else {
 x_813 = x_805;
}
lean_ctor_set(x_813, 0, x_812);
lean_ctor_set(x_813, 1, x_682);
lean_ctor_set(x_813, 2, x_683);
lean_ctor_set(x_813, 3, x_684);
lean_ctor_set(x_813, 4, x_800);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 lean_ctor_release(x_684, 2);
 lean_ctor_release(x_684, 3);
 lean_ctor_release(x_684, 4);
 x_814 = x_684;
} else {
 lean_dec_ref(x_684);
 x_814 = lean_box(0);
}
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_815 = lean_ctor_get(x_801, 0);
lean_inc(x_815);
x_816 = lean_nat_add(x_810, x_815);
lean_dec(x_815);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_814)) {
 x_817 = lean_alloc_ctor(0, 5, 0);
} else {
 x_817 = x_814;
}
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_784);
lean_ctor_set(x_817, 2, x_785);
lean_ctor_set(x_817, 3, x_801);
lean_ctor_set(x_817, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_818 = x_786;
} else {
 lean_dec_ref(x_786);
 x_818 = lean_box(0);
}
if (lean_is_scalar(x_818)) {
 x_819 = lean_alloc_ctor(0, 5, 0);
} else {
 x_819 = x_818;
}
lean_ctor_set(x_819, 0, x_808);
lean_ctor_set(x_819, 1, x_798);
lean_ctor_set(x_819, 2, x_799);
lean_ctor_set(x_819, 3, x_813);
lean_ctor_set(x_819, 4, x_817);
return x_819;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_820 = lean_unsigned_to_nat(0u);
x_821 = lean_nat_add(x_810, x_820);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_814)) {
 x_822 = lean_alloc_ctor(0, 5, 0);
} else {
 x_822 = x_814;
}
lean_ctor_set(x_822, 0, x_821);
lean_ctor_set(x_822, 1, x_784);
lean_ctor_set(x_822, 2, x_785);
lean_ctor_set(x_822, 3, x_801);
lean_ctor_set(x_822, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_823 = x_786;
} else {
 lean_dec_ref(x_786);
 x_823 = lean_box(0);
}
if (lean_is_scalar(x_823)) {
 x_824 = lean_alloc_ctor(0, 5, 0);
} else {
 x_824 = x_823;
}
lean_ctor_set(x_824, 0, x_808);
lean_ctor_set(x_824, 1, x_798);
lean_ctor_set(x_824, 2, x_799);
lean_ctor_set(x_824, 3, x_813);
lean_ctor_set(x_824, 4, x_822);
return x_824;
}
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_825 = lean_unsigned_to_nat(0u);
x_826 = lean_nat_add(x_809, x_825);
lean_dec(x_809);
lean_inc(x_684);
if (lean_is_scalar(x_805)) {
 x_827 = lean_alloc_ctor(0, 5, 0);
} else {
 x_827 = x_805;
}
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_682);
lean_ctor_set(x_827, 2, x_683);
lean_ctor_set(x_827, 3, x_684);
lean_ctor_set(x_827, 4, x_800);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 lean_ctor_release(x_684, 2);
 lean_ctor_release(x_684, 3);
 lean_ctor_release(x_684, 4);
 x_828 = x_684;
} else {
 lean_dec_ref(x_684);
 x_828 = lean_box(0);
}
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_829 = lean_ctor_get(x_801, 0);
lean_inc(x_829);
x_830 = lean_nat_add(x_810, x_829);
lean_dec(x_829);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_828)) {
 x_831 = lean_alloc_ctor(0, 5, 0);
} else {
 x_831 = x_828;
}
lean_ctor_set(x_831, 0, x_830);
lean_ctor_set(x_831, 1, x_784);
lean_ctor_set(x_831, 2, x_785);
lean_ctor_set(x_831, 3, x_801);
lean_ctor_set(x_831, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_832 = x_786;
} else {
 lean_dec_ref(x_786);
 x_832 = lean_box(0);
}
if (lean_is_scalar(x_832)) {
 x_833 = lean_alloc_ctor(0, 5, 0);
} else {
 x_833 = x_832;
}
lean_ctor_set(x_833, 0, x_808);
lean_ctor_set(x_833, 1, x_798);
lean_ctor_set(x_833, 2, x_799);
lean_ctor_set(x_833, 3, x_827);
lean_ctor_set(x_833, 4, x_831);
return x_833;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_834 = lean_nat_add(x_810, x_825);
lean_dec(x_810);
lean_inc(x_786);
if (lean_is_scalar(x_828)) {
 x_835 = lean_alloc_ctor(0, 5, 0);
} else {
 x_835 = x_828;
}
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_784);
lean_ctor_set(x_835, 2, x_785);
lean_ctor_set(x_835, 3, x_801);
lean_ctor_set(x_835, 4, x_786);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_836 = x_786;
} else {
 lean_dec_ref(x_786);
 x_836 = lean_box(0);
}
if (lean_is_scalar(x_836)) {
 x_837 = lean_alloc_ctor(0, 5, 0);
} else {
 x_837 = x_836;
}
lean_ctor_set(x_837, 0, x_808);
lean_ctor_set(x_837, 1, x_798);
lean_ctor_set(x_837, 2, x_799);
lean_ctor_set(x_837, 3, x_827);
lean_ctor_set(x_837, 4, x_835);
return x_837;
}
}
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
lean_dec(x_801);
lean_dec(x_800);
lean_dec(x_799);
lean_dec(x_798);
lean_dec(x_796);
x_838 = lean_unsigned_to_nat(1u);
x_839 = lean_nat_add(x_838, x_681);
lean_dec(x_681);
x_840 = lean_nat_add(x_839, x_788);
lean_dec(x_839);
x_841 = lean_nat_add(x_838, x_788);
lean_dec(x_788);
x_842 = lean_nat_add(x_841, x_797);
lean_dec(x_797);
lean_dec(x_841);
if (lean_is_scalar(x_686)) {
 x_843 = lean_alloc_ctor(0, 5, 0);
} else {
 x_843 = x_686;
}
lean_ctor_set(x_843, 0, x_842);
lean_ctor_set(x_843, 1, x_784);
lean_ctor_set(x_843, 2, x_785);
lean_ctor_set(x_843, 3, x_685);
lean_ctor_set(x_843, 4, x_786);
x_844 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_844, 0, x_840);
lean_ctor_set(x_844, 1, x_682);
lean_ctor_set(x_844, 2, x_683);
lean_ctor_set(x_844, 3, x_684);
lean_ctor_set(x_844, 4, x_843);
return x_844;
}
}
}
else
{
if (lean_obj_tag(x_684) == 0)
{
lean_dec(x_787);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_845 = lean_ctor_get(x_685, 0);
lean_inc(x_845);
x_846 = lean_unsigned_to_nat(1u);
x_847 = lean_nat_add(x_846, x_681);
lean_dec(x_681);
x_848 = lean_nat_add(x_846, x_845);
lean_dec(x_845);
x_849 = lean_box(1);
if (lean_is_scalar(x_686)) {
 x_850 = lean_alloc_ctor(0, 5, 0);
} else {
 x_850 = x_686;
}
lean_ctor_set(x_850, 0, x_848);
lean_ctor_set(x_850, 1, x_784);
lean_ctor_set(x_850, 2, x_785);
lean_ctor_set(x_850, 3, x_685);
lean_ctor_set(x_850, 4, x_849);
x_851 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_851, 0, x_847);
lean_ctor_set(x_851, 1, x_682);
lean_ctor_set(x_851, 2, x_683);
lean_ctor_set(x_851, 3, x_684);
lean_ctor_set(x_851, 4, x_850);
return x_851;
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_681);
x_852 = lean_box(1);
x_853 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_686)) {
 x_854 = lean_alloc_ctor(0, 5, 0);
} else {
 x_854 = x_686;
}
lean_ctor_set(x_854, 0, x_853);
lean_ctor_set(x_854, 1, x_784);
lean_ctor_set(x_854, 2, x_785);
lean_ctor_set(x_854, 3, x_852);
lean_ctor_set(x_854, 4, x_852);
x_855 = lean_unsigned_to_nat(3u);
x_856 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_682);
lean_ctor_set(x_856, 2, x_683);
lean_ctor_set(x_856, 3, x_684);
lean_ctor_set(x_856, 4, x_854);
return x_856;
}
}
else
{
lean_dec(x_681);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; 
lean_dec(x_787);
x_857 = lean_ctor_get(x_685, 1);
lean_inc(x_857);
x_858 = lean_ctor_get(x_685, 2);
lean_inc(x_858);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 lean_ctor_release(x_685, 2);
 lean_ctor_release(x_685, 3);
 lean_ctor_release(x_685, 4);
 x_859 = x_685;
} else {
 lean_dec_ref(x_685);
 x_859 = lean_box(0);
}
x_860 = lean_box(1);
x_861 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_859)) {
 x_862 = lean_alloc_ctor(0, 5, 0);
} else {
 x_862 = x_859;
}
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_862, 1, x_682);
lean_ctor_set(x_862, 2, x_683);
lean_ctor_set(x_862, 3, x_860);
lean_ctor_set(x_862, 4, x_860);
if (lean_is_scalar(x_686)) {
 x_863 = lean_alloc_ctor(0, 5, 0);
} else {
 x_863 = x_686;
}
lean_ctor_set(x_863, 0, x_861);
lean_ctor_set(x_863, 1, x_784);
lean_ctor_set(x_863, 2, x_785);
lean_ctor_set(x_863, 3, x_860);
lean_ctor_set(x_863, 4, x_860);
x_864 = lean_unsigned_to_nat(3u);
x_865 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_857);
lean_ctor_set(x_865, 2, x_858);
lean_ctor_set(x_865, 3, x_862);
lean_ctor_set(x_865, 4, x_863);
return x_865;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_683);
lean_dec(x_682);
x_866 = lean_box(1);
x_867 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_686)) {
 x_868 = lean_alloc_ctor(0, 5, 0);
} else {
 x_868 = x_686;
}
lean_ctor_set(x_868, 0, x_867);
lean_ctor_set(x_868, 1, x_784);
lean_ctor_set(x_868, 2, x_785);
lean_ctor_set(x_868, 3, x_787);
lean_ctor_set(x_868, 4, x_866);
return x_868;
}
}
}
}
}
else
{
return x_673;
}
}
else
{
return x_674;
}
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_869 = lean_ctor_get(x_680, 0);
lean_inc(x_869);
lean_dec(x_680);
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
x_872 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_872, 0, x_670);
lean_ctor_set(x_872, 1, x_870);
lean_ctor_set(x_872, 2, x_871);
lean_ctor_set(x_872, 3, x_673);
lean_ctor_set(x_872, 4, x_674);
return x_872;
}
}
default: 
{
lean_object* x_873; lean_object* x_874; 
lean_dec(x_670);
x_873 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_Const_alter_u2098___spec__1___rarg(x_1, x_2, x_3, x_674, lean_box(0));
x_874 = l_Std_DTreeMap_Internal_Impl_balance___rarg(x_671, x_672, x_673, x_873, lean_box(0), lean_box(0), lean_box(0));
return x_874;
}
}
}
}
else
{
lean_object* x_875; lean_object* x_876; 
lean_dec(x_2);
lean_dec(x_1);
x_875 = lean_box(0);
x_876 = lean_apply_1(x_3, x_875);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; 
x_877 = lean_box(1);
return x_877;
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_878 = lean_ctor_get(x_876, 0);
lean_inc(x_878);
lean_dec(x_876);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_881 = lean_box(1);
x_882 = lean_unsigned_to_nat(1u);
x_883 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_883, 0, x_882);
lean_ctor_set(x_883, 1, x_879);
lean_ctor_set(x_883, 2, x_880);
lean_ctor_set(x_883, 3, x_881);
lean_ctor_set(x_883, 4, x_881);
return x_883;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_Const_alter_u2098___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_Const_alter_u2098___spec__1___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter_u2098___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
x_7 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Cell_Const_alter___rarg), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_4);
x_8 = l_Std_DTreeMap_Internal_Impl_updateCell___at_Std_DTreeMap_Internal_Impl_Const_alter_u2098___spec__1___rarg(x_1, x_3, x_7, x_5, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter_u2098(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_alter_u2098___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = lean_apply_6(x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___rarg), 3, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getKey_x3f_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__2_splitter___rarg), 5, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__2_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__2_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___rarg), 2, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___rarg), 5, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___rarg), 5, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__2_splitter___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__2_splitter___rarg(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_4(x_2, x_1, lean_box(0), lean_box(0), lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___rarg), 2, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_4(x_2, x_1, lean_box(0), lean_box(0), lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___rarg), 2, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = lean_apply_6(x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___rarg), 3, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Std_Data_DTreeMap_Internal_WF_Defs(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_DTreeMap_Internal_Cell(uint8_t builtin, lean_object*);
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
l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_contains_u2098___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__2);
l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__3 = _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__3();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__3);
l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__4 = _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__4();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___rarg___closed__4);
l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_erase_u2098___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
