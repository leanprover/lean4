// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Model
// Imports: public import Std.Data.DTreeMap.Internal.WF.Defs public import Std.Data.DTreeMap.Internal.Cell import Init.Data.Nat.Internal.Linear import Init.Omega
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
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_toListModel___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_ofEq___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t l_Std_DTreeMap_Internal_Cell_contains___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0_value;
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(lean_object* v_k_1_, lean_object* v_l_2_){
_start:
{
if (lean_obj_tag(v_l_2_) == 0)
{
lean_object* v_k_3_; lean_object* v_l_4_; lean_object* v_r_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v_k_3_ = lean_ctor_get(v_l_2_, 1);
lean_inc(v_k_3_);
v_l_4_ = lean_ctor_get(v_l_2_, 3);
lean_inc(v_l_4_);
v_r_5_ = lean_ctor_get(v_l_2_, 4);
lean_inc(v_r_5_);
lean_dec_ref_known(v_l_2_, 5);
lean_inc_ref(v_k_1_);
v___x_6_ = lean_apply_1(v_k_1_, v_k_3_);
v___x_7_ = lean_unbox(v___x_6_);
switch(v___x_7_)
{
case 0:
{
lean_dec(v_r_5_);
v_l_2_ = v_l_4_;
goto _start;
}
case 1:
{
uint8_t v___x_9_; 
lean_dec(v_r_5_);
lean_dec(v_l_4_);
lean_dec_ref(v_k_1_);
v___x_9_ = 1;
return v___x_9_;
}
default: 
{
lean_dec(v_l_4_);
v_l_2_ = v_r_5_;
goto _start;
}
}
}
else
{
uint8_t v___x_11_; 
lean_dec_ref(v_k_1_);
v___x_11_ = 0;
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_x27___redArg___boxed(lean_object* v_k_12_, lean_object* v_l_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(v_k_12_, v_l_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_x27(lean_object* v_00_u03b1_16_, lean_object* v_00_u03b2_17_, lean_object* v_inst_18_, lean_object* v_k_19_, lean_object* v_l_20_){
_start:
{
uint8_t v___x_21_; 
v___x_21_ = l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(v_k_19_, v_l_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_x27___boxed(lean_object* v_00_u03b1_22_, lean_object* v_00_u03b2_23_, lean_object* v_inst_24_, lean_object* v_k_25_, lean_object* v_l_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Std_DTreeMap_Internal_Impl_contains_x27(v_00_u03b1_22_, v_00_u03b2_23_, v_inst_24_, v_k_25_, v_l_26_);
lean_dec_ref(v_inst_24_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___redArg(lean_object* v_l_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_){
_start:
{
if (lean_obj_tag(v_l_29_) == 0)
{
lean_object* v_size_32_; lean_object* v_k_33_; lean_object* v_v_34_; lean_object* v_l_35_; lean_object* v_r_36_; lean_object* v___x_37_; 
lean_dec(v_h__1_30_);
v_size_32_ = lean_ctor_get(v_l_29_, 0);
lean_inc(v_size_32_);
v_k_33_ = lean_ctor_get(v_l_29_, 1);
lean_inc(v_k_33_);
v_v_34_ = lean_ctor_get(v_l_29_, 2);
lean_inc(v_v_34_);
v_l_35_ = lean_ctor_get(v_l_29_, 3);
lean_inc(v_l_35_);
v_r_36_ = lean_ctor_get(v_l_29_, 4);
lean_inc(v_r_36_);
lean_dec_ref_known(v_l_29_, 5);
v___x_37_ = lean_apply_5(v_h__2_31_, v_size_32_, v_k_33_, v_v_34_, v_l_35_, v_r_36_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_h__2_31_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_apply_1(v_h__1_30_, v___x_38_);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter(lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_, lean_object* v_motive_42_, lean_object* v_l_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_){
_start:
{
if (lean_obj_tag(v_l_43_) == 0)
{
lean_object* v_size_46_; lean_object* v_k_47_; lean_object* v_v_48_; lean_object* v_l_49_; lean_object* v_r_50_; lean_object* v___x_51_; 
lean_dec(v_h__1_44_);
v_size_46_ = lean_ctor_get(v_l_43_, 0);
lean_inc(v_size_46_);
v_k_47_ = lean_ctor_get(v_l_43_, 1);
lean_inc(v_k_47_);
v_v_48_ = lean_ctor_get(v_l_43_, 2);
lean_inc(v_v_48_);
v_l_49_ = lean_ctor_get(v_l_43_, 3);
lean_inc(v_l_49_);
v_r_50_ = lean_ctor_get(v_l_43_, 4);
lean_inc(v_r_50_);
lean_dec_ref_known(v_l_43_, 5);
v___x_51_ = lean_apply_5(v_h__2_45_, v_size_46_, v_k_47_, v_v_48_, v_l_49_, v_r_50_);
return v___x_51_;
}
else
{
lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec(v_h__2_45_);
v___x_52_ = lean_box(0);
v___x_53_ = lean_apply_1(v_h__1_44_, v___x_52_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(uint8_t v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_, lean_object* v_h__3_57_){
_start:
{
switch(v_x_54_)
{
case 0:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec(v_h__3_57_);
lean_dec(v_h__2_56_);
v___x_58_ = lean_box(0);
v___x_59_ = lean_apply_1(v_h__1_55_, v___x_58_);
return v___x_59_;
}
case 1:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
lean_dec(v_h__2_56_);
lean_dec(v_h__1_55_);
v___x_60_ = lean_box(0);
v___x_61_ = lean_apply_1(v_h__3_57_, v___x_60_);
return v___x_61_;
}
default: 
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_h__3_57_);
lean_dec(v_h__1_55_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_1(v_h__2_56_, v___x_62_);
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(lean_object* v_x_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_, lean_object* v_h__3_67_){
_start:
{
uint8_t v_x_33__boxed_68_; lean_object* v_res_69_; 
v_x_33__boxed_68_ = lean_unbox(v_x_64_);
v_res_69_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_33__boxed_68_, v_h__1_65_, v_h__2_66_, v_h__3_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object* v_motive_70_, uint8_t v_x_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_, lean_object* v_h__3_74_){
_start:
{
switch(v_x_71_)
{
case 0:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_h__3_74_);
lean_dec(v_h__2_73_);
v___x_75_ = lean_box(0);
v___x_76_ = lean_apply_1(v_h__1_72_, v___x_75_);
return v___x_76_;
}
case 1:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v_h__2_73_);
lean_dec(v_h__1_72_);
v___x_77_ = lean_box(0);
v___x_78_ = lean_apply_1(v_h__3_74_, v___x_77_);
return v___x_78_;
}
default: 
{
lean_object* v___x_79_; lean_object* v___x_80_; 
lean_dec(v_h__3_74_);
lean_dec(v_h__1_72_);
v___x_79_ = lean_box(0);
v___x_80_ = lean_apply_1(v_h__2_73_, v___x_79_);
return v___x_80_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(lean_object* v_motive_81_, lean_object* v_x_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_, lean_object* v_h__3_85_){
_start:
{
uint8_t v_x_48__boxed_86_; lean_object* v_res_87_; 
v_x_48__boxed_86_ = lean_unbox(v_x_82_);
v_res_87_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_81_, v_x_48__boxed_86_, v_h__1_83_, v_h__2_84_, v_h__3_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(uint8_t v_x_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_, lean_object* v_h__3_91_){
_start:
{
switch(v_x_88_)
{
case 0:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v_h__3_91_);
lean_dec(v_h__2_90_);
v___x_92_ = lean_box(0);
v___x_93_ = lean_apply_1(v_h__1_89_, v___x_92_);
return v___x_93_;
}
case 1:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_h__2_90_);
lean_dec(v_h__1_89_);
v___x_94_ = lean_box(0);
v___x_95_ = lean_apply_1(v_h__3_91_, v___x_94_);
return v___x_95_;
}
default: 
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v_h__3_91_);
lean_dec(v_h__1_89_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_apply_1(v_h__2_90_, v___x_96_);
return v___x_97_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(lean_object* v_x_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_, lean_object* v_h__3_101_){
_start:
{
uint8_t v_x_33__boxed_102_; lean_object* v_res_103_; 
v_x_33__boxed_102_ = lean_unbox(v_x_98_);
v_res_103_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_33__boxed_102_, v_h__1_99_, v_h__2_100_, v_h__3_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object* v_motive_104_, uint8_t v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_, lean_object* v_h__3_108_){
_start:
{
switch(v_x_105_)
{
case 0:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_h__3_108_);
lean_dec(v_h__2_107_);
v___x_109_ = lean_box(0);
v___x_110_ = lean_apply_1(v_h__1_106_, v___x_109_);
return v___x_110_;
}
case 1:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec(v_h__2_107_);
lean_dec(v_h__1_106_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_apply_1(v_h__3_108_, v___x_111_);
return v___x_112_;
}
default: 
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v_h__3_108_);
lean_dec(v_h__1_106_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_apply_1(v_h__2_107_, v___x_113_);
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(lean_object* v_motive_115_, lean_object* v_x_116_, lean_object* v_h__1_117_, lean_object* v_h__2_118_, lean_object* v_h__3_119_){
_start:
{
uint8_t v_x_48__boxed_120_; lean_object* v_res_121_; 
v_x_48__boxed_120_ = lean_unbox(v_x_116_);
v_res_121_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_115_, v_x_48__boxed_120_, v_h__1_117_, v_h__2_118_, v_h__3_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(lean_object* v_k_122_, lean_object* v_f_123_, lean_object* v_ll_124_, lean_object* v_m_125_, lean_object* v_rr_126_){
_start:
{
if (lean_obj_tag(v_m_125_) == 0)
{
lean_object* v_k_127_; lean_object* v_v_128_; lean_object* v_l_129_; lean_object* v_r_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v_k_127_ = lean_ctor_get(v_m_125_, 1);
lean_inc_n(v_k_127_, 2);
v_v_128_ = lean_ctor_get(v_m_125_, 2);
lean_inc(v_v_128_);
v_l_129_ = lean_ctor_get(v_m_125_, 3);
lean_inc(v_l_129_);
v_r_130_ = lean_ctor_get(v_m_125_, 4);
lean_inc(v_r_130_);
lean_dec_ref_known(v_m_125_, 5);
lean_inc_ref(v_k_122_);
v___x_131_ = lean_apply_1(v_k_122_, v_k_127_);
v___x_132_ = lean_unbox(v___x_131_);
switch(v___x_132_)
{
case 0:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v_k_127_);
lean_ctor_set(v___x_133_, 1, v_v_128_);
v___x_134_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_130_);
lean_dec(v_r_130_);
v___x_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = l_List_appendTR___redArg(v___x_135_, v_rr_126_);
v_m_125_ = v_l_129_;
v_rr_126_ = v___x_136_;
goto _start;
}
case 1:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec_ref(v_k_122_);
v___x_138_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_129_);
lean_dec(v_l_129_);
v___x_139_ = l_List_appendTR___redArg(v_ll_124_, v___x_138_);
v___x_140_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_127_, v_v_128_);
v___x_141_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_130_);
lean_dec(v_r_130_);
v___x_142_ = l_List_appendTR___redArg(v___x_141_, v_rr_126_);
v___x_143_ = lean_apply_4(v_f_123_, v___x_139_, v___x_140_, lean_box(0), v___x_142_);
return v___x_143_;
}
default: 
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_144_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_129_);
lean_dec(v_l_129_);
v___x_145_ = l_List_appendTR___redArg(v_ll_124_, v___x_144_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v_k_127_);
lean_ctor_set(v___x_146_, 1, v_v_128_);
v___x_147_ = lean_box(0);
v___x_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = l_List_appendTR___redArg(v___x_145_, v___x_148_);
v_ll_124_ = v___x_149_;
v_m_125_ = v_r_130_;
goto _start;
}
}
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec_ref(v_k_122_);
v___x_151_ = lean_box(0);
v___x_152_ = lean_apply_4(v_f_123_, v_ll_124_, v___x_151_, lean_box(0), v_rr_126_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go(lean_object* v_00_u03b1_153_, lean_object* v_00_u03b2_154_, lean_object* v_00_u03b4_155_, lean_object* v_inst_156_, lean_object* v_k_157_, lean_object* v_l_158_, lean_object* v_f_159_, lean_object* v_ll_160_, lean_object* v_m_161_, lean_object* v_hm_162_, lean_object* v_rr_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(v_k_157_, v_f_159_, v_ll_160_, v_m_161_, v_rr_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___boxed(lean_object* v_00_u03b1_165_, lean_object* v_00_u03b2_166_, lean_object* v_00_u03b4_167_, lean_object* v_inst_168_, lean_object* v_k_169_, lean_object* v_l_170_, lean_object* v_f_171_, lean_object* v_ll_172_, lean_object* v_m_173_, lean_object* v_hm_174_, lean_object* v_rr_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go(v_00_u03b1_165_, v_00_u03b2_166_, v_00_u03b4_167_, v_inst_168_, v_k_169_, v_l_170_, v_f_171_, v_ll_172_, v_m_173_, v_hm_174_, v_rr_175_);
lean_dec(v_l_170_);
lean_dec_ref(v_inst_168_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(lean_object* v_k_177_, lean_object* v_l_178_, lean_object* v_f_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_box(0);
v___x_181_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(v_k_177_, v_f_179_, v___x_180_, v_l_178_, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition(lean_object* v_00_u03b1_182_, lean_object* v_00_u03b2_183_, lean_object* v_00_u03b4_184_, lean_object* v_inst_185_, lean_object* v_k_186_, lean_object* v_l_187_, lean_object* v_f_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v_k_186_, v_l_187_, v_f_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___boxed(lean_object* v_00_u03b1_190_, lean_object* v_00_u03b2_191_, lean_object* v_00_u03b4_192_, lean_object* v_inst_193_, lean_object* v_k_194_, lean_object* v_l_195_, lean_object* v_f_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Std_DTreeMap_Internal_Impl_applyPartition(v_00_u03b1_190_, v_00_u03b2_191_, v_00_u03b4_192_, v_inst_193_, v_k_194_, v_l_195_, v_f_196_);
lean_dec_ref(v_inst_193_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0(lean_object* v_f_198_, lean_object* v_c_199_, lean_object* v_h_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_apply_2(v_f_198_, v_c_199_, lean_box(0));
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___redArg(lean_object* v_inst_202_, lean_object* v_k_203_, lean_object* v_l_204_, lean_object* v_f_205_){
_start:
{
if (lean_obj_tag(v_l_204_) == 0)
{
lean_object* v_k_206_; lean_object* v_v_207_; lean_object* v_l_208_; lean_object* v_r_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_k_206_ = lean_ctor_get(v_l_204_, 1);
lean_inc_n(v_k_206_, 2);
v_v_207_ = lean_ctor_get(v_l_204_, 2);
lean_inc(v_v_207_);
v_l_208_ = lean_ctor_get(v_l_204_, 3);
lean_inc(v_l_208_);
v_r_209_ = lean_ctor_get(v_l_204_, 4);
lean_inc(v_r_209_);
lean_dec_ref_known(v_l_204_, 5);
lean_inc_ref(v_inst_202_);
lean_inc(v_k_203_);
v___x_210_ = lean_apply_2(v_inst_202_, v_k_203_, v_k_206_);
v___x_211_ = lean_unbox(v___x_210_);
switch(v___x_211_)
{
case 0:
{
lean_object* v___f_212_; 
lean_dec(v_r_209_);
lean_dec(v_v_207_);
lean_dec(v_k_206_);
v___f_212_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0), 3, 1);
lean_closure_set(v___f_212_, 0, v_f_205_);
v_l_204_ = v_l_208_;
v_f_205_ = v___f_212_;
goto _start;
}
case 1:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v_r_209_);
lean_dec(v_l_208_);
lean_dec(v_k_203_);
lean_dec_ref(v_inst_202_);
v___x_214_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_206_, v_v_207_);
v___x_215_ = lean_apply_2(v_f_205_, v___x_214_, lean_box(0));
return v___x_215_;
}
default: 
{
lean_object* v___f_216_; 
lean_dec(v_l_208_);
lean_dec(v_v_207_);
lean_dec(v_k_206_);
v___f_216_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0), 3, 1);
lean_closure_set(v___f_216_, 0, v_f_205_);
v_l_204_ = v_r_209_;
v_f_205_ = v___f_216_;
goto _start;
}
}
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v_k_203_);
lean_dec_ref(v_inst_202_);
v___x_218_ = lean_box(0);
v___x_219_ = lean_apply_2(v_f_205_, v___x_218_, lean_box(0));
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell(lean_object* v_00_u03b1_220_, lean_object* v_00_u03b2_221_, lean_object* v_00_u03b4_222_, lean_object* v_inst_223_, lean_object* v_k_224_, lean_object* v_l_225_, lean_object* v_f_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_223_, v_k_224_, v_l_225_, v_f_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___redArg(lean_object* v_l_228_, lean_object* v_f_229_, lean_object* v_h__1_230_, lean_object* v_h__2_231_){
_start:
{
if (lean_obj_tag(v_l_228_) == 0)
{
lean_object* v_size_232_; lean_object* v_k_233_; lean_object* v_v_234_; lean_object* v_l_235_; lean_object* v_r_236_; lean_object* v___x_237_; 
lean_dec(v_h__1_230_);
v_size_232_ = lean_ctor_get(v_l_228_, 0);
lean_inc(v_size_232_);
v_k_233_ = lean_ctor_get(v_l_228_, 1);
lean_inc(v_k_233_);
v_v_234_ = lean_ctor_get(v_l_228_, 2);
lean_inc(v_v_234_);
v_l_235_ = lean_ctor_get(v_l_228_, 3);
lean_inc(v_l_235_);
v_r_236_ = lean_ctor_get(v_l_228_, 4);
lean_inc(v_r_236_);
lean_dec_ref_known(v_l_228_, 5);
v___x_237_ = lean_apply_6(v_h__2_231_, v_size_232_, v_k_233_, v_v_234_, v_l_235_, v_r_236_, v_f_229_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; 
lean_dec(v_h__2_231_);
v___x_238_ = lean_apply_1(v_h__1_230_, v_f_229_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(lean_object* v_00_u03b1_239_, lean_object* v_00_u03b2_240_, lean_object* v_00_u03b4_241_, lean_object* v_inst_242_, lean_object* v_k_243_, lean_object* v_motive_244_, lean_object* v_l_245_, lean_object* v_f_246_, lean_object* v_h__1_247_, lean_object* v_h__2_248_){
_start:
{
if (lean_obj_tag(v_l_245_) == 0)
{
lean_object* v_size_249_; lean_object* v_k_250_; lean_object* v_v_251_; lean_object* v_l_252_; lean_object* v_r_253_; lean_object* v___x_254_; 
lean_dec(v_h__1_247_);
v_size_249_ = lean_ctor_get(v_l_245_, 0);
lean_inc(v_size_249_);
v_k_250_ = lean_ctor_get(v_l_245_, 1);
lean_inc(v_k_250_);
v_v_251_ = lean_ctor_get(v_l_245_, 2);
lean_inc(v_v_251_);
v_l_252_ = lean_ctor_get(v_l_245_, 3);
lean_inc(v_l_252_);
v_r_253_ = lean_ctor_get(v_l_245_, 4);
lean_inc(v_r_253_);
lean_dec_ref_known(v_l_245_, 5);
v___x_254_ = lean_apply_6(v_h__2_248_, v_size_249_, v_k_250_, v_v_251_, v_l_252_, v_r_253_, v_f_246_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; 
lean_dec(v_h__2_248_);
v___x_255_ = lean_apply_1(v_h__1_247_, v_f_246_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___boxed(lean_object* v_00_u03b1_256_, lean_object* v_00_u03b2_257_, lean_object* v_00_u03b4_258_, lean_object* v_inst_259_, lean_object* v_k_260_, lean_object* v_motive_261_, lean_object* v_l_262_, lean_object* v_f_263_, lean_object* v_h__1_264_, lean_object* v_h__2_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(v_00_u03b1_256_, v_00_u03b2_257_, v_00_u03b4_258_, v_inst_259_, v_k_260_, v_motive_261_, v_l_262_, v_f_263_, v_h__1_264_, v_h__2_265_);
lean_dec(v_k_260_);
lean_dec_ref(v_inst_259_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(uint8_t v_x_267_, lean_object* v_h__1_268_, lean_object* v_h__2_269_, lean_object* v_h__3_270_){
_start:
{
switch(v_x_267_)
{
case 0:
{
lean_object* v___x_271_; 
lean_dec(v_h__3_270_);
lean_dec(v_h__2_269_);
v___x_271_ = lean_apply_1(v_h__1_268_, lean_box(0));
return v___x_271_;
}
case 1:
{
lean_object* v___x_272_; 
lean_dec(v_h__3_270_);
lean_dec(v_h__1_268_);
v___x_272_ = lean_apply_1(v_h__2_269_, lean_box(0));
return v___x_272_;
}
default: 
{
lean_object* v___x_273_; 
lean_dec(v_h__2_269_);
lean_dec(v_h__1_268_);
v___x_273_ = lean_apply_1(v_h__3_270_, lean_box(0));
return v___x_273_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(lean_object* v_x_274_, lean_object* v_h__1_275_, lean_object* v_h__2_276_, lean_object* v_h__3_277_){
_start:
{
uint8_t v_x_33__boxed_278_; lean_object* v_res_279_; 
v_x_33__boxed_278_ = lean_unbox(v_x_274_);
v_res_279_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_33__boxed_278_, v_h__1_275_, v_h__2_276_, v_h__3_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object* v_motive_280_, uint8_t v_x_281_, lean_object* v_h__1_282_, lean_object* v_h__2_283_, lean_object* v_h__3_284_){
_start:
{
switch(v_x_281_)
{
case 0:
{
lean_object* v___x_285_; 
lean_dec(v_h__3_284_);
lean_dec(v_h__2_283_);
v___x_285_ = lean_apply_1(v_h__1_282_, lean_box(0));
return v___x_285_;
}
case 1:
{
lean_object* v___x_286_; 
lean_dec(v_h__3_284_);
lean_dec(v_h__1_282_);
v___x_286_ = lean_apply_1(v_h__2_283_, lean_box(0));
return v___x_286_;
}
default: 
{
lean_object* v___x_287_; 
lean_dec(v_h__2_283_);
lean_dec(v_h__1_282_);
v___x_287_ = lean_apply_1(v_h__3_284_, lean_box(0));
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(lean_object* v_motive_288_, lean_object* v_x_289_, lean_object* v_h__1_290_, lean_object* v_h__2_291_, lean_object* v_h__3_292_){
_start:
{
uint8_t v_x_42__boxed_293_; lean_object* v_res_294_; 
v_x_42__boxed_293_ = lean_unbox(v_x_289_);
v_res_294_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(v_motive_288_, v_x_42__boxed_293_, v_h__1_290_, v_h__2_291_, v_h__3_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___redArg(lean_object* v_m_295_, lean_object* v_h__1_296_, lean_object* v_h__2_297_){
_start:
{
if (lean_obj_tag(v_m_295_) == 0)
{
lean_object* v_size_298_; lean_object* v_k_299_; lean_object* v_v_300_; lean_object* v_l_301_; lean_object* v_r_302_; lean_object* v___x_303_; 
lean_dec(v_h__1_296_);
v_size_298_ = lean_ctor_get(v_m_295_, 0);
lean_inc(v_size_298_);
v_k_299_ = lean_ctor_get(v_m_295_, 1);
lean_inc(v_k_299_);
v_v_300_ = lean_ctor_get(v_m_295_, 2);
lean_inc(v_v_300_);
v_l_301_ = lean_ctor_get(v_m_295_, 3);
lean_inc(v_l_301_);
v_r_302_ = lean_ctor_get(v_m_295_, 4);
lean_inc(v_r_302_);
lean_dec_ref_known(v_m_295_, 5);
v___x_303_ = lean_apply_6(v_h__2_297_, v_size_298_, v_k_299_, v_v_300_, v_l_301_, v_r_302_, lean_box(0));
return v___x_303_;
}
else
{
lean_object* v___x_304_; 
lean_dec(v_h__2_297_);
v___x_304_ = lean_apply_1(v_h__1_296_, lean_box(0));
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(lean_object* v_00_u03b1_305_, lean_object* v_00_u03b2_306_, lean_object* v_inst_307_, lean_object* v_k_308_, lean_object* v_l_309_, lean_object* v_motive_310_, lean_object* v_m_311_, lean_object* v_hm_312_, lean_object* v_h__1_313_, lean_object* v_h__2_314_){
_start:
{
if (lean_obj_tag(v_m_311_) == 0)
{
lean_object* v_size_315_; lean_object* v_k_316_; lean_object* v_v_317_; lean_object* v_l_318_; lean_object* v_r_319_; lean_object* v___x_320_; 
lean_dec(v_h__1_313_);
v_size_315_ = lean_ctor_get(v_m_311_, 0);
lean_inc(v_size_315_);
v_k_316_ = lean_ctor_get(v_m_311_, 1);
lean_inc(v_k_316_);
v_v_317_ = lean_ctor_get(v_m_311_, 2);
lean_inc(v_v_317_);
v_l_318_ = lean_ctor_get(v_m_311_, 3);
lean_inc(v_l_318_);
v_r_319_ = lean_ctor_get(v_m_311_, 4);
lean_inc(v_r_319_);
lean_dec_ref_known(v_m_311_, 5);
v___x_320_ = lean_apply_6(v_h__2_314_, v_size_315_, v_k_316_, v_v_317_, v_l_318_, v_r_319_, lean_box(0));
return v___x_320_;
}
else
{
lean_object* v___x_321_; 
lean_dec(v_h__2_314_);
v___x_321_ = lean_apply_1(v_h__1_313_, lean_box(0));
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___boxed(lean_object* v_00_u03b1_322_, lean_object* v_00_u03b2_323_, lean_object* v_inst_324_, lean_object* v_k_325_, lean_object* v_l_326_, lean_object* v_motive_327_, lean_object* v_m_328_, lean_object* v_hm_329_, lean_object* v_h__1_330_, lean_object* v_h__2_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(v_00_u03b1_322_, v_00_u03b2_323_, v_inst_324_, v_k_325_, v_l_326_, v_motive_327_, v_m_328_, v_hm_329_, v_h__1_330_, v_h__2_331_);
lean_dec(v_l_326_);
lean_dec_ref(v_k_325_);
lean_dec_ref(v_inst_324_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___redArg(lean_object* v_x_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_obj_tag_nat(v_x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___redArg___boxed(lean_object* v_x_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___redArg(v_x_335_);
lean_dec_ref(v_x_335_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl(lean_object* v_00_u03b1_337_, lean_object* v_00_u03b2_338_, lean_object* v_inst_339_, lean_object* v_k_340_, lean_object* v_x_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = lean_obj_tag_nat(v_x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___boxed(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_inst_345_, lean_object* v_k_346_, lean_object* v_x_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl(v_00_u03b1_343_, v_00_u03b2_344_, v_inst_345_, v_k_346_, v_x_347_);
lean_dec_ref(v_x_347_);
lean_dec_ref(v_k_346_);
lean_dec_ref(v_inst_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(lean_object* v_t_349_, lean_object* v_k_350_){
_start:
{
switch(lean_obj_tag(v_t_349_))
{
case 0:
{
lean_object* v_a_351_; lean_object* v_a_352_; lean_object* v_a_353_; lean_object* v___x_354_; 
v_a_351_ = lean_ctor_get(v_t_349_, 0);
lean_inc(v_a_351_);
v_a_352_ = lean_ctor_get(v_t_349_, 1);
lean_inc(v_a_352_);
v_a_353_ = lean_ctor_get(v_t_349_, 2);
lean_inc(v_a_353_);
lean_dec_ref_known(v_t_349_, 3);
v___x_354_ = lean_apply_4(v_k_350_, v_a_351_, lean_box(0), v_a_352_, v_a_353_);
return v___x_354_;
}
case 1:
{
lean_object* v_a_355_; lean_object* v_a_356_; lean_object* v_a_357_; lean_object* v___x_358_; 
v_a_355_ = lean_ctor_get(v_t_349_, 0);
lean_inc(v_a_355_);
v_a_356_ = lean_ctor_get(v_t_349_, 1);
lean_inc(v_a_356_);
v_a_357_ = lean_ctor_get(v_t_349_, 2);
lean_inc(v_a_357_);
lean_dec_ref_known(v_t_349_, 3);
v___x_358_ = lean_apply_3(v_k_350_, v_a_355_, v_a_356_, v_a_357_);
return v___x_358_;
}
default: 
{
lean_object* v_a_359_; lean_object* v_a_360_; lean_object* v_a_361_; lean_object* v___x_362_; 
v_a_359_ = lean_ctor_get(v_t_349_, 0);
lean_inc(v_a_359_);
v_a_360_ = lean_ctor_get(v_t_349_, 1);
lean_inc(v_a_360_);
v_a_361_ = lean_ctor_get(v_t_349_, 2);
lean_inc(v_a_361_);
lean_dec_ref_known(v_t_349_, 3);
v___x_362_ = lean_apply_4(v_k_350_, v_a_359_, v_a_360_, lean_box(0), v_a_361_);
return v___x_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim(lean_object* v_00_u03b1_363_, lean_object* v_00_u03b2_364_, lean_object* v_inst_365_, lean_object* v_k_366_, lean_object* v_motive_367_, lean_object* v_ctorIdx_368_, lean_object* v_t_369_, lean_object* v_h_370_, lean_object* v_k_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_369_, v_k_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___boxed(lean_object* v_00_u03b1_373_, lean_object* v_00_u03b2_374_, lean_object* v_inst_375_, lean_object* v_k_376_, lean_object* v_motive_377_, lean_object* v_ctorIdx_378_, lean_object* v_t_379_, lean_object* v_h_380_, lean_object* v_k_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim(v_00_u03b1_373_, v_00_u03b2_374_, v_inst_375_, v_k_376_, v_motive_377_, v_ctorIdx_378_, v_t_379_, v_h_380_, v_k_381_);
lean_dec(v_ctorIdx_378_);
lean_dec_ref(v_k_376_);
lean_dec_ref(v_inst_375_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___redArg(lean_object* v_t_383_, lean_object* v_lt_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_383_, v_lt_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim(lean_object* v_00_u03b1_386_, lean_object* v_00_u03b2_387_, lean_object* v_inst_388_, lean_object* v_k_389_, lean_object* v_motive_390_, lean_object* v_t_391_, lean_object* v_h_392_, lean_object* v_lt_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_391_, v_lt_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___boxed(lean_object* v_00_u03b1_395_, lean_object* v_00_u03b2_396_, lean_object* v_inst_397_, lean_object* v_k_398_, lean_object* v_motive_399_, lean_object* v_t_400_, lean_object* v_h_401_, lean_object* v_lt_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim(v_00_u03b1_395_, v_00_u03b2_396_, v_inst_397_, v_k_398_, v_motive_399_, v_t_400_, v_h_401_, v_lt_402_);
lean_dec_ref(v_k_398_);
lean_dec_ref(v_inst_397_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___redArg(lean_object* v_t_404_, lean_object* v_eq_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_404_, v_eq_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim(lean_object* v_00_u03b1_407_, lean_object* v_00_u03b2_408_, lean_object* v_inst_409_, lean_object* v_k_410_, lean_object* v_motive_411_, lean_object* v_t_412_, lean_object* v_h_413_, lean_object* v_eq_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_412_, v_eq_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___boxed(lean_object* v_00_u03b1_416_, lean_object* v_00_u03b2_417_, lean_object* v_inst_418_, lean_object* v_k_419_, lean_object* v_motive_420_, lean_object* v_t_421_, lean_object* v_h_422_, lean_object* v_eq_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim(v_00_u03b1_416_, v_00_u03b2_417_, v_inst_418_, v_k_419_, v_motive_420_, v_t_421_, v_h_422_, v_eq_423_);
lean_dec_ref(v_k_419_);
lean_dec_ref(v_inst_418_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___redArg(lean_object* v_t_425_, lean_object* v_gt_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_425_, v_gt_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim(lean_object* v_00_u03b1_428_, lean_object* v_00_u03b2_429_, lean_object* v_inst_430_, lean_object* v_k_431_, lean_object* v_motive_432_, lean_object* v_t_433_, lean_object* v_h_434_, lean_object* v_gt_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_433_, v_gt_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___boxed(lean_object* v_00_u03b1_437_, lean_object* v_00_u03b2_438_, lean_object* v_inst_439_, lean_object* v_k_440_, lean_object* v_motive_441_, lean_object* v_t_442_, lean_object* v_h_443_, lean_object* v_gt_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim(v_00_u03b1_437_, v_00_u03b2_438_, v_inst_439_, v_k_440_, v_motive_441_, v_t_442_, v_h_443_, v_gt_444_);
lean_dec_ref(v_k_440_);
lean_dec_ref(v_inst_439_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___redArg(lean_object* v_k_449_, lean_object* v_init_450_, lean_object* v_inner_451_, lean_object* v_l_452_){
_start:
{
if (lean_obj_tag(v_l_452_) == 0)
{
lean_object* v_k_453_; lean_object* v_v_454_; lean_object* v_l_455_; lean_object* v_r_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_k_453_ = lean_ctor_get(v_l_452_, 1);
lean_inc_n(v_k_453_, 2);
v_v_454_ = lean_ctor_get(v_l_452_, 2);
lean_inc(v_v_454_);
v_l_455_ = lean_ctor_get(v_l_452_, 3);
lean_inc(v_l_455_);
v_r_456_ = lean_ctor_get(v_l_452_, 4);
lean_inc(v_r_456_);
lean_dec_ref_known(v_l_452_, 5);
lean_inc_ref(v_k_449_);
v___x_457_ = lean_apply_1(v_k_449_, v_k_453_);
v___x_458_ = lean_unbox(v___x_457_);
switch(v___x_458_)
{
case 0:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_456_);
lean_dec(v_r_456_);
v___x_460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_460_, 0, v_k_453_);
lean_ctor_set(v___x_460_, 1, v_v_454_);
lean_ctor_set(v___x_460_, 2, v___x_459_);
lean_inc(v_inner_451_);
v___x_461_ = lean_apply_2(v_inner_451_, v_init_450_, v___x_460_);
v_init_450_ = v___x_461_;
v_l_452_ = v_l_455_;
goto _start;
}
case 1:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec_ref(v_k_449_);
v___x_463_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_455_);
lean_dec(v_l_455_);
v___x_464_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_453_, v_v_454_);
v___x_465_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_456_);
lean_dec(v_r_456_);
v___x_466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_466_, 0, v___x_463_);
lean_ctor_set(v___x_466_, 1, v___x_464_);
lean_ctor_set(v___x_466_, 2, v___x_465_);
v___x_467_ = lean_apply_2(v_inner_451_, v_init_450_, v___x_466_);
return v___x_467_;
}
default: 
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_455_);
lean_dec(v_l_455_);
v___x_469_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v_k_453_);
lean_ctor_set(v___x_469_, 2, v_v_454_);
lean_inc(v_inner_451_);
v___x_470_ = lean_apply_2(v_inner_451_, v_init_450_, v___x_469_);
v_init_450_ = v___x_470_;
v_l_452_ = v_r_456_;
goto _start;
}
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec_ref(v_k_449_);
v___x_472_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0));
v___x_473_ = lean_apply_2(v_inner_451_, v_init_450_, v___x_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_00_u03b3_476_, lean_object* v_inst_477_, lean_object* v_k_478_, lean_object* v_init_479_, lean_object* v_inner_480_, lean_object* v_l_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v_k_478_, v_init_479_, v_inner_480_, v_l_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___boxed(lean_object* v_00_u03b1_483_, lean_object* v_00_u03b2_484_, lean_object* v_00_u03b3_485_, lean_object* v_inst_486_, lean_object* v_k_487_, lean_object* v_init_488_, lean_object* v_inner_489_, lean_object* v_l_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_DTreeMap_Internal_Impl_explore(v_00_u03b1_483_, v_00_u03b2_484_, v_00_u03b3_485_, v_inst_486_, v_k_487_, v_init_488_, v_inner_489_, v_l_490_);
lean_dec_ref(v_inst_486_);
return v_res_491_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(lean_object* v_c_492_, lean_object* v_x_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_492_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0___boxed(lean_object* v_c_495_, lean_object* v_x_496_){
_start:
{
uint8_t v_res_497_; lean_object* v_r_498_; 
v_res_497_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(v_c_495_, v_x_496_);
lean_dec(v_c_495_);
v_r_498_ = lean_box(v_res_497_);
return v_r_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(lean_object* v_inst_500_, lean_object* v_l_501_, lean_object* v_k_502_){
_start:
{
lean_object* v___f_503_; lean_object* v___x_504_; 
v___f_503_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0));
v___x_504_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_500_, v_k_502_, v_l_501_, v___f_503_);
return v___x_504_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098(lean_object* v_00_u03b1_505_, lean_object* v_00_u03b2_506_, lean_object* v_inst_507_, lean_object* v_l_508_, lean_object* v_k_509_){
_start:
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(v_inst_507_, v_l_508_, v_k_509_);
v___x_511_ = lean_unbox(v___x_510_);
lean_dec(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___boxed(lean_object* v_00_u03b1_512_, lean_object* v_00_u03b2_513_, lean_object* v_inst_514_, lean_object* v_l_515_, lean_object* v_k_516_){
_start:
{
uint8_t v_res_517_; lean_object* v_r_518_; 
v_res_517_ = l_Std_DTreeMap_Internal_Impl_contains_u2098(v_00_u03b1_512_, v_00_u03b2_513_, v_inst_514_, v_l_515_, v_k_516_);
v_r_518_ = lean_box(v_res_517_);
return v_r_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0(lean_object* v_c_519_, lean_object* v_x_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(v_c_519_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(lean_object* v_inst_523_, lean_object* v_l_524_, lean_object* v_k_525_){
_start:
{
lean_object* v___f_526_; lean_object* v___x_527_; 
v___f_526_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0));
v___x_527_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_523_, v_k_525_, v_l_524_, v___f_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098(lean_object* v_00_u03b1_528_, lean_object* v_00_u03b2_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_l_533_, lean_object* v_k_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_530_, v_l_533_, v_k_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(lean_object* v_inst_536_, lean_object* v_l_537_, lean_object* v_k_538_){
_start:
{
lean_object* v___x_539_; lean_object* v_val_540_; 
v___x_539_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_536_, v_l_537_, v_k_538_);
v_val_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_val_540_);
lean_dec(v___x_539_);
return v_val_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098(lean_object* v_00_u03b1_541_, lean_object* v_00_u03b2_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_l_546_, lean_object* v_k_547_, lean_object* v_h_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(v_inst_543_, v_l_546_, v_k_547_);
return v___x_549_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_553_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2));
v___x_554_ = lean_unsigned_to_nat(14u);
v___x_555_ = lean_unsigned_to_nat(22u);
v___x_556_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1));
v___x_557_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0));
v___x_558_ = l_mkPanicMessageWithDecl(v___x_557_, v___x_556_, v___x_555_, v___x_554_, v___x_553_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(lean_object* v_inst_559_, lean_object* v_l_560_, lean_object* v_k_561_, lean_object* v_inst_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_559_, v_l_560_, v_k_561_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_565_ = l_panic___redArg(v_inst_562_, v___x_564_);
return v___x_565_;
}
else
{
lean_object* v_val_566_; 
v_val_566_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_val_566_);
lean_dec_ref_known(v___x_563_, 1);
return v_val_566_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___boxed(lean_object* v_inst_567_, lean_object* v_l_568_, lean_object* v_k_569_, lean_object* v_inst_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(v_inst_567_, v_l_568_, v_k_569_, v_inst_570_);
lean_dec(v_inst_570_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098(lean_object* v_00_u03b1_572_, lean_object* v_00_u03b2_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_l_577_, lean_object* v_k_578_, lean_object* v_inst_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(v_inst_574_, v_l_577_, v_k_578_, v_inst_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___boxed(lean_object* v_00_u03b1_581_, lean_object* v_00_u03b2_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_l_586_, lean_object* v_k_587_, lean_object* v_inst_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098(v_00_u03b1_581_, v_00_u03b2_582_, v_inst_583_, v_inst_584_, v_inst_585_, v_l_586_, v_k_587_, v_inst_588_);
lean_dec(v_inst_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(lean_object* v_inst_590_, lean_object* v_k_591_, lean_object* v_l_592_, lean_object* v_fallback_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_590_, v_l_592_, v_k_591_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_inc(v_fallback_593_);
return v_fallback_593_;
}
else
{
lean_object* v_val_595_; 
v_val_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_val_595_);
lean_dec_ref_known(v___x_594_, 1);
return v_val_595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg___boxed(lean_object* v_inst_596_, lean_object* v_k_597_, lean_object* v_l_598_, lean_object* v_fallback_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(v_inst_596_, v_k_597_, v_l_598_, v_fallback_599_);
lean_dec(v_fallback_599_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098(lean_object* v_00_u03b1_601_, lean_object* v_00_u03b2_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_k_606_, lean_object* v_l_607_, lean_object* v_fallback_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(v_inst_603_, v_k_606_, v_l_607_, v_fallback_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___boxed(lean_object* v_00_u03b1_610_, lean_object* v_00_u03b2_611_, lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_k_615_, lean_object* v_l_616_, lean_object* v_fallback_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Std_DTreeMap_Internal_Impl_getD_u2098(v_00_u03b1_610_, v_00_u03b2_611_, v_inst_612_, v_inst_613_, v_inst_614_, v_k_615_, v_l_616_, v_fallback_617_);
lean_dec(v_fallback_617_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___lam__0(lean_object* v_c_619_, lean_object* v_x_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(v_c_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(lean_object* v_inst_623_, lean_object* v_l_624_, lean_object* v_k_625_){
_start:
{
lean_object* v___f_626_; lean_object* v___x_627_; 
v___f_626_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0));
v___x_627_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_623_, v_k_625_, v_l_624_, v___f_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098(lean_object* v_00_u03b1_628_, lean_object* v_00_u03b2_629_, lean_object* v_inst_630_, lean_object* v_l_631_, lean_object* v_k_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_630_, v_l_631_, v_k_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(lean_object* v_inst_634_, lean_object* v_l_635_, lean_object* v_k_636_){
_start:
{
lean_object* v___x_637_; lean_object* v_val_638_; 
v___x_637_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_634_, v_l_635_, v_k_636_);
v_val_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_638_);
lean_dec(v___x_637_);
return v_val_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098(lean_object* v_00_u03b1_639_, lean_object* v_00_u03b2_640_, lean_object* v_inst_641_, lean_object* v_l_642_, lean_object* v_k_643_, lean_object* v_h_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(v_inst_641_, v_l_642_, v_k_643_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_l_648_, lean_object* v_k_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_646_, v_l_648_, v_k_649_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_652_ = l_panic___redArg(v_inst_647_, v___x_651_);
return v___x_652_;
}
else
{
lean_object* v_val_653_; 
v_val_653_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_653_);
lean_dec_ref_known(v___x_650_, 1);
return v_val_653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg___boxed(lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_l_656_, lean_object* v_k_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(v_inst_654_, v_inst_655_, v_l_656_, v_k_657_);
lean_dec_ref(v_inst_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(lean_object* v_00_u03b1_659_, lean_object* v_00_u03b2_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_l_663_, lean_object* v_k_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(v_inst_661_, v_inst_662_, v_l_663_, v_k_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___boxed(lean_object* v_00_u03b1_666_, lean_object* v_00_u03b2_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_l_670_, lean_object* v_k_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(v_00_u03b1_666_, v_00_u03b2_667_, v_inst_668_, v_inst_669_, v_l_670_, v_k_671_);
lean_dec_ref(v_inst_669_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(lean_object* v_inst_673_, lean_object* v_k_674_, lean_object* v_l_675_, lean_object* v_fallback_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_673_, v_l_675_, v_k_674_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_inc_ref(v_fallback_676_);
return v_fallback_676_;
}
else
{
lean_object* v_val_678_; 
v_val_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_val_678_);
lean_dec_ref_known(v___x_677_, 1);
return v_val_678_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg___boxed(lean_object* v_inst_679_, lean_object* v_k_680_, lean_object* v_l_681_, lean_object* v_fallback_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(v_inst_679_, v_k_680_, v_l_681_, v_fallback_682_);
lean_dec_ref(v_fallback_682_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(lean_object* v_00_u03b1_684_, lean_object* v_00_u03b2_685_, lean_object* v_inst_686_, lean_object* v_k_687_, lean_object* v_l_688_, lean_object* v_fallback_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(v_inst_686_, v_k_687_, v_l_688_, v_fallback_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___boxed(lean_object* v_00_u03b1_691_, lean_object* v_00_u03b2_692_, lean_object* v_inst_693_, lean_object* v_k_694_, lean_object* v_l_695_, lean_object* v_fallback_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(v_00_u03b1_691_, v_00_u03b2_692_, v_inst_693_, v_k_694_, v_l_695_, v_fallback_696_);
lean_dec_ref(v_fallback_696_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0(lean_object* v_c_698_, lean_object* v_x_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(v_c_698_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(lean_object* v_inst_702_, lean_object* v_l_703_, lean_object* v_k_704_){
_start:
{
lean_object* v___f_705_; lean_object* v___x_706_; 
v___f_705_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0));
v___x_706_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_702_, v_k_704_, v_l_703_, v___f_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098(lean_object* v_00_u03b1_707_, lean_object* v_00_u03b2_708_, lean_object* v_inst_709_, lean_object* v_l_710_, lean_object* v_k_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_709_, v_l_710_, v_k_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(lean_object* v_inst_713_, lean_object* v_l_714_, lean_object* v_k_715_){
_start:
{
lean_object* v___x_716_; lean_object* v_val_717_; 
v___x_716_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_713_, v_l_714_, v_k_715_);
v_val_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_val_717_);
lean_dec(v___x_716_);
return v_val_717_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098(lean_object* v_00_u03b1_718_, lean_object* v_00_u03b2_719_, lean_object* v_inst_720_, lean_object* v_l_721_, lean_object* v_k_722_, lean_object* v_h_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(v_inst_720_, v_l_721_, v_k_722_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(lean_object* v_inst_725_, lean_object* v_l_726_, lean_object* v_k_727_, lean_object* v_inst_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_725_, v_l_726_, v_k_727_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_731_ = l_panic___redArg(v_inst_728_, v___x_730_);
return v___x_731_;
}
else
{
lean_object* v_val_732_; 
v_val_732_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_val_732_);
lean_dec_ref_known(v___x_729_, 1);
return v_val_732_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg___boxed(lean_object* v_inst_733_, lean_object* v_l_734_, lean_object* v_k_735_, lean_object* v_inst_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(v_inst_733_, v_l_734_, v_k_735_, v_inst_736_);
lean_dec(v_inst_736_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(lean_object* v_00_u03b1_738_, lean_object* v_00_u03b2_739_, lean_object* v_inst_740_, lean_object* v_l_741_, lean_object* v_k_742_, lean_object* v_inst_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(v_inst_740_, v_l_741_, v_k_742_, v_inst_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___boxed(lean_object* v_00_u03b1_745_, lean_object* v_00_u03b2_746_, lean_object* v_inst_747_, lean_object* v_l_748_, lean_object* v_k_749_, lean_object* v_inst_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(v_00_u03b1_745_, v_00_u03b2_746_, v_inst_747_, v_l_748_, v_k_749_, v_inst_750_);
lean_dec(v_inst_750_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(lean_object* v_inst_752_, lean_object* v_k_753_, lean_object* v_l_754_, lean_object* v_fallback_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_752_, v_l_754_, v_k_753_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_inc(v_fallback_755_);
return v_fallback_755_;
}
else
{
lean_object* v_val_757_; 
v_val_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_val_757_);
lean_dec_ref_known(v___x_756_, 1);
return v_val_757_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg___boxed(lean_object* v_inst_758_, lean_object* v_k_759_, lean_object* v_l_760_, lean_object* v_fallback_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(v_inst_758_, v_k_759_, v_l_760_, v_fallback_761_);
lean_dec(v_fallback_761_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(lean_object* v_00_u03b1_763_, lean_object* v_00_u03b2_764_, lean_object* v_inst_765_, lean_object* v_k_766_, lean_object* v_l_767_, lean_object* v_fallback_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(v_inst_765_, v_k_766_, v_l_767_, v_fallback_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___boxed(lean_object* v_00_u03b1_770_, lean_object* v_00_u03b2_771_, lean_object* v_inst_772_, lean_object* v_k_773_, lean_object* v_l_774_, lean_object* v_fallback_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(v_00_u03b1_770_, v_00_u03b2_771_, v_inst_772_, v_k_773_, v_l_774_, v_fallback_775_);
lean_dec(v_fallback_775_);
return v_res_776_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(lean_object* v_x_777_){
_start:
{
uint8_t v___x_778_; 
v___x_778_ = 0;
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* v_x_779_){
_start:
{
uint8_t v_res_780_; lean_object* v_r_781_; 
v_res_780_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(v_x_779_);
lean_dec(v_x_779_);
v_r_781_ = lean_box(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(lean_object* v_sofar_782_, lean_object* v_step_783_){
_start:
{
if (lean_obj_tag(v_step_783_) == 0)
{
lean_object* v_a_784_; lean_object* v_a_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_a_784_ = lean_ctor_get(v_step_783_, 0);
v_a_785_ = lean_ctor_get(v_step_783_, 1);
lean_inc(v_a_785_);
lean_inc(v_a_784_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v_a_784_);
lean_ctor_set(v___x_786_, 1, v_a_785_);
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
return v___x_787_;
}
else
{
lean_object* v_a_788_; lean_object* v___x_789_; 
v_a_788_ = lean_ctor_get(v_step_783_, 2);
v___x_789_ = l_List_head_x3f___redArg(v_a_788_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_inc(v_sofar_782_);
return v_sofar_782_;
}
else
{
return v___x_789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* v_sofar_790_, lean_object* v_step_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(v_sofar_790_, v_step_791_);
lean_dec_ref(v_step_791_);
lean_dec(v_sofar_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(lean_object* v_l_795_){
_start:
{
lean_object* v___f_796_; lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___f_796_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0));
v___f_797_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1));
v___x_798_ = lean_box(0);
v___x_799_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___f_796_, v___x_798_, v___f_797_, v_l_795_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(lean_object* v_00_u03b1_800_, lean_object* v_00_u03b2_801_, lean_object* v_inst_802_, lean_object* v_l_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(v_l_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___boxed(lean_object* v_00_u03b1_805_, lean_object* v_00_u03b2_806_, lean_object* v_inst_807_, lean_object* v_l_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(v_00_u03b1_805_, v_00_u03b2_806_, v_inst_807_, v_l_808_);
lean_dec_ref(v_inst_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_r_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_List_head_x3f___redArg(v_r_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed(lean_object* v_x_815_, lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v_r_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(v_x_815_, v_x_816_, v_x_817_, v_r_818_);
lean_dec(v_r_818_);
lean_dec(v_x_816_);
lean_dec(v_x_815_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(lean_object* v_l_821_){
_start:
{
lean_object* v___f_822_; lean_object* v___f_823_; lean_object* v___x_824_; 
v___f_822_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0));
v___f_823_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0));
v___x_824_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_822_, v_l_821_, v___f_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_inst_827_, lean_object* v_l_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(v_l_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___boxed(lean_object* v_00_u03b1_830_, lean_object* v_00_u03b2_831_, lean_object* v_inst_832_, lean_object* v_l_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(v_00_u03b1_830_, v_00_u03b2_831_, v_inst_832_, v_l_833_);
lean_dec_ref(v_inst_832_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse___redArg(lean_object* v_x_835_){
_start:
{
if (lean_obj_tag(v_x_835_) == 0)
{
lean_object* v_size_836_; lean_object* v_k_837_; lean_object* v_v_838_; lean_object* v_l_839_; lean_object* v_r_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_849_; 
v_size_836_ = lean_ctor_get(v_x_835_, 0);
v_k_837_ = lean_ctor_get(v_x_835_, 1);
v_v_838_ = lean_ctor_get(v_x_835_, 2);
v_l_839_ = lean_ctor_get(v_x_835_, 3);
v_r_840_ = lean_ctor_get(v_x_835_, 4);
v_isSharedCheck_849_ = !lean_is_exclusive(v_x_835_);
if (v_isSharedCheck_849_ == 0)
{
v___x_842_ = v_x_835_;
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_r_840_);
lean_inc(v_l_839_);
lean_inc(v_v_838_);
lean_inc(v_k_837_);
lean_inc(v_size_836_);
lean_dec(v_x_835_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_844_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_r_840_);
v___x_845_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_l_839_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 4, v___x_845_);
lean_ctor_set(v___x_842_, 3, v___x_844_);
v___x_847_ = v___x_842_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_size_836_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_k_837_);
lean_ctor_set(v_reuseFailAlloc_848_, 2, v_v_838_);
lean_ctor_set(v_reuseFailAlloc_848_, 3, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_848_, 4, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
return v_x_835_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse(lean_object* v_00_u03b1_850_, lean_object* v_00_u03b2_851_, lean_object* v_x_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0(lean_object* v_c_854_, lean_object* v_x_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(v_c_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(lean_object* v_inst_858_, lean_object* v_l_859_, lean_object* v_k_860_){
_start:
{
lean_object* v___f_861_; lean_object* v___x_862_; 
v___f_861_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0));
v___x_862_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_858_, v_k_860_, v_l_859_, v___f_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098(lean_object* v_00_u03b1_863_, lean_object* v_00_u03b2_864_, lean_object* v_inst_865_, lean_object* v_l_866_, lean_object* v_k_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_865_, v_l_866_, v_k_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(lean_object* v_inst_869_, lean_object* v_l_870_, lean_object* v_k_871_){
_start:
{
lean_object* v___x_872_; lean_object* v_val_873_; 
v___x_872_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_869_, v_l_870_, v_k_871_);
v_val_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_val_873_);
lean_dec(v___x_872_);
return v_val_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098(lean_object* v_00_u03b1_874_, lean_object* v_00_u03b2_875_, lean_object* v_inst_876_, lean_object* v_l_877_, lean_object* v_k_878_, lean_object* v_h_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(v_inst_876_, v_l_877_, v_k_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(lean_object* v_inst_881_, lean_object* v_l_882_, lean_object* v_k_883_, lean_object* v_inst_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_881_, v_l_882_, v_k_883_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_887_ = l_panic___redArg(v_inst_884_, v___x_886_);
return v___x_887_;
}
else
{
lean_object* v_val_888_; 
v_val_888_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_val_888_);
lean_dec_ref_known(v___x_885_, 1);
return v_val_888_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg___boxed(lean_object* v_inst_889_, lean_object* v_l_890_, lean_object* v_k_891_, lean_object* v_inst_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(v_inst_889_, v_l_890_, v_k_891_, v_inst_892_);
lean_dec(v_inst_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(lean_object* v_00_u03b1_894_, lean_object* v_00_u03b2_895_, lean_object* v_inst_896_, lean_object* v_l_897_, lean_object* v_k_898_, lean_object* v_inst_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(v_inst_896_, v_l_897_, v_k_898_, v_inst_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___boxed(lean_object* v_00_u03b1_901_, lean_object* v_00_u03b2_902_, lean_object* v_inst_903_, lean_object* v_l_904_, lean_object* v_k_905_, lean_object* v_inst_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(v_00_u03b1_901_, v_00_u03b2_902_, v_inst_903_, v_l_904_, v_k_905_, v_inst_906_);
lean_dec(v_inst_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(lean_object* v_inst_908_, lean_object* v_l_909_, lean_object* v_k_910_, lean_object* v_fallback_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_908_, v_l_909_, v_k_910_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_inc(v_fallback_911_);
return v_fallback_911_;
}
else
{
lean_object* v_val_913_; 
v_val_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_val_913_);
lean_dec_ref_known(v___x_912_, 1);
return v_val_913_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg___boxed(lean_object* v_inst_914_, lean_object* v_l_915_, lean_object* v_k_916_, lean_object* v_fallback_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(v_inst_914_, v_l_915_, v_k_916_, v_fallback_917_);
lean_dec(v_fallback_917_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(lean_object* v_00_u03b1_919_, lean_object* v_00_u03b2_920_, lean_object* v_inst_921_, lean_object* v_l_922_, lean_object* v_k_923_, lean_object* v_fallback_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(v_inst_921_, v_l_922_, v_k_923_, v_fallback_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___boxed(lean_object* v_00_u03b1_926_, lean_object* v_00_u03b2_927_, lean_object* v_inst_928_, lean_object* v_l_929_, lean_object* v_k_930_, lean_object* v_fallback_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(v_00_u03b1_926_, v_00_u03b2_927_, v_inst_928_, v_l_929_, v_k_930_, v_fallback_931_);
lean_dec(v_fallback_931_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object* v_t_933_, lean_object* v_h__1_934_, lean_object* v_h__2_935_){
_start:
{
if (lean_obj_tag(v_t_933_) == 0)
{
lean_object* v_size_936_; lean_object* v_k_937_; lean_object* v_v_938_; lean_object* v_l_939_; lean_object* v_r_940_; lean_object* v___x_941_; 
lean_dec(v_h__1_934_);
v_size_936_ = lean_ctor_get(v_t_933_, 0);
lean_inc(v_size_936_);
v_k_937_ = lean_ctor_get(v_t_933_, 1);
lean_inc(v_k_937_);
v_v_938_ = lean_ctor_get(v_t_933_, 2);
lean_inc(v_v_938_);
v_l_939_ = lean_ctor_get(v_t_933_, 3);
lean_inc(v_l_939_);
v_r_940_ = lean_ctor_get(v_t_933_, 4);
lean_inc(v_r_940_);
lean_dec_ref_known(v_t_933_, 5);
v___x_941_ = lean_apply_5(v_h__2_935_, v_size_936_, v_k_937_, v_v_938_, v_l_939_, v_r_940_);
return v___x_941_;
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v_h__2_935_);
v___x_942_ = lean_box(0);
v___x_943_ = lean_apply_1(v_h__1_934_, v___x_942_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object* v_00_u03b1_944_, lean_object* v_00_u03b2_945_, lean_object* v_motive_946_, lean_object* v_t_947_, lean_object* v_h__1_948_, lean_object* v_h__2_949_){
_start:
{
if (lean_obj_tag(v_t_947_) == 0)
{
lean_object* v_size_950_; lean_object* v_k_951_; lean_object* v_v_952_; lean_object* v_l_953_; lean_object* v_r_954_; lean_object* v___x_955_; 
lean_dec(v_h__1_948_);
v_size_950_ = lean_ctor_get(v_t_947_, 0);
lean_inc(v_size_950_);
v_k_951_ = lean_ctor_get(v_t_947_, 1);
lean_inc(v_k_951_);
v_v_952_ = lean_ctor_get(v_t_947_, 2);
lean_inc(v_v_952_);
v_l_953_ = lean_ctor_get(v_t_947_, 3);
lean_inc(v_l_953_);
v_r_954_ = lean_ctor_get(v_t_947_, 4);
lean_inc(v_r_954_);
lean_dec_ref_known(v_t_947_, 5);
v___x_955_ = lean_apply_5(v_h__2_949_, v_size_950_, v_k_951_, v_v_952_, v_l_953_, v_r_954_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec(v_h__2_949_);
v___x_956_ = lean_box(0);
v___x_957_ = lean_apply_1(v_h__1_948_, v___x_956_);
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(uint8_t v_x_958_, lean_object* v_h__1_959_, lean_object* v_h__2_960_, lean_object* v_h__3_961_){
_start:
{
switch(v_x_958_)
{
case 0:
{
lean_object* v___x_962_; 
lean_dec(v_h__3_961_);
lean_dec(v_h__2_960_);
v___x_962_ = lean_apply_1(v_h__1_959_, lean_box(0));
return v___x_962_;
}
case 1:
{
lean_object* v___x_963_; 
lean_dec(v_h__2_960_);
lean_dec(v_h__1_959_);
v___x_963_ = lean_apply_1(v_h__3_961_, lean_box(0));
return v___x_963_;
}
default: 
{
lean_object* v___x_964_; 
lean_dec(v_h__3_961_);
lean_dec(v_h__1_959_);
v___x_964_ = lean_apply_1(v_h__2_960_, lean_box(0));
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_965_, lean_object* v_h__1_966_, lean_object* v_h__2_967_, lean_object* v_h__3_968_){
_start:
{
uint8_t v_x_33__boxed_969_; lean_object* v_res_970_; 
v_x_33__boxed_969_ = lean_unbox(v_x_965_);
v_res_970_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(v_x_33__boxed_969_, v_h__1_966_, v_h__2_967_, v_h__3_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(lean_object* v_motive_971_, uint8_t v_x_972_, lean_object* v_h__1_973_, lean_object* v_h__2_974_, lean_object* v_h__3_975_){
_start:
{
switch(v_x_972_)
{
case 0:
{
lean_object* v___x_976_; 
lean_dec(v_h__3_975_);
lean_dec(v_h__2_974_);
v___x_976_ = lean_apply_1(v_h__1_973_, lean_box(0));
return v___x_976_;
}
case 1:
{
lean_object* v___x_977_; 
lean_dec(v_h__2_974_);
lean_dec(v_h__1_973_);
v___x_977_ = lean_apply_1(v_h__3_975_, lean_box(0));
return v___x_977_;
}
default: 
{
lean_object* v___x_978_; 
lean_dec(v_h__3_975_);
lean_dec(v_h__1_973_);
v___x_978_ = lean_apply_1(v_h__2_974_, lean_box(0));
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___boxed(lean_object* v_motive_979_, lean_object* v_x_980_, lean_object* v_h__1_981_, lean_object* v_h__2_982_, lean_object* v_h__3_983_){
_start:
{
uint8_t v_x_42__boxed_984_; lean_object* v_res_985_; 
v_x_42__boxed_984_ = lean_unbox(v_x_980_);
v_res_985_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(v_motive_979_, v_x_42__boxed_984_, v_h__1_981_, v_h__2_982_, v_h__3_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object* v_x_986_, lean_object* v_h__1_987_, lean_object* v_h__2_988_){
_start:
{
if (lean_obj_tag(v_x_986_) == 0)
{
lean_object* v___x_989_; 
lean_dec(v_h__2_988_);
v___x_989_ = lean_apply_1(v_h__1_987_, lean_box(0));
return v___x_989_;
}
else
{
lean_object* v_val_990_; lean_object* v___x_991_; 
lean_dec(v_h__1_987_);
v_val_990_ = lean_ctor_get(v_x_986_, 0);
lean_inc(v_val_990_);
lean_dec_ref_known(v_x_986_, 1);
v___x_991_ = lean_apply_2(v_h__2_988_, v_val_990_, lean_box(0));
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object* v_00_u03b1_992_, lean_object* v_00_u03b2_993_, lean_object* v_motive_994_, lean_object* v_x_995_, lean_object* v_h__1_996_, lean_object* v_h__2_997_){
_start:
{
if (lean_obj_tag(v_x_995_) == 0)
{
lean_object* v___x_998_; 
lean_dec(v_h__2_997_);
v___x_998_ = lean_apply_1(v_h__1_996_, lean_box(0));
return v___x_998_;
}
else
{
lean_object* v_val_999_; lean_object* v___x_1000_; 
lean_dec(v_h__1_996_);
v_val_999_ = lean_ctor_get(v_x_995_, 0);
lean_inc(v_val_999_);
lean_dec_ref_known(v_x_995_, 1);
v___x_1000_ = lean_apply_2(v_h__2_997_, v_val_999_, lean_box(0));
return v___x_1000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___redArg(lean_object* v_t_1001_, lean_object* v_h__1_1002_){
_start:
{
lean_object* v_size_1003_; lean_object* v_k_1004_; lean_object* v_v_1005_; lean_object* v_l_1006_; lean_object* v_r_1007_; lean_object* v___x_1008_; 
v_size_1003_ = lean_ctor_get(v_t_1001_, 0);
lean_inc(v_size_1003_);
v_k_1004_ = lean_ctor_get(v_t_1001_, 1);
lean_inc(v_k_1004_);
v_v_1005_ = lean_ctor_get(v_t_1001_, 2);
lean_inc(v_v_1005_);
v_l_1006_ = lean_ctor_get(v_t_1001_, 3);
lean_inc(v_l_1006_);
v_r_1007_ = lean_ctor_get(v_t_1001_, 4);
lean_inc(v_r_1007_);
lean_dec(v_t_1001_);
v___x_1008_ = lean_apply_6(v_h__1_1002_, v_size_1003_, v_k_1004_, v_v_1005_, v_l_1006_, v_r_1007_, lean_box(0));
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(lean_object* v_00_u03b1_1009_, lean_object* v_00_u03b2_1010_, lean_object* v_inst_1011_, lean_object* v_k_1012_, lean_object* v_motive_1013_, lean_object* v_t_1014_, lean_object* v_hlk_1015_, lean_object* v_h__1_1016_){
_start:
{
lean_object* v_size_1017_; lean_object* v_k_1018_; lean_object* v_v_1019_; lean_object* v_l_1020_; lean_object* v_r_1021_; lean_object* v___x_1022_; 
v_size_1017_ = lean_ctor_get(v_t_1014_, 0);
lean_inc(v_size_1017_);
v_k_1018_ = lean_ctor_get(v_t_1014_, 1);
lean_inc(v_k_1018_);
v_v_1019_ = lean_ctor_get(v_t_1014_, 2);
lean_inc(v_v_1019_);
v_l_1020_ = lean_ctor_get(v_t_1014_, 3);
lean_inc(v_l_1020_);
v_r_1021_ = lean_ctor_get(v_t_1014_, 4);
lean_inc(v_r_1021_);
lean_dec(v_t_1014_);
v___x_1022_ = lean_apply_6(v_h__1_1016_, v_size_1017_, v_k_1018_, v_v_1019_, v_l_1020_, v_r_1021_, lean_box(0));
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___boxed(lean_object* v_00_u03b1_1023_, lean_object* v_00_u03b2_1024_, lean_object* v_inst_1025_, lean_object* v_k_1026_, lean_object* v_motive_1027_, lean_object* v_t_1028_, lean_object* v_hlk_1029_, lean_object* v_h__1_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(v_00_u03b1_1023_, v_00_u03b2_1024_, v_inst_1025_, v_k_1026_, v_motive_1027_, v_t_1028_, v_hlk_1029_, v_h__1_1030_);
lean_dec(v_k_1026_);
lean_dec_ref(v_inst_1025_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1032_, lean_object* v_h__1_1033_, lean_object* v_h__2_1034_){
_start:
{
if (lean_obj_tag(v_x_1032_) == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
lean_dec(v_h__2_1034_);
v___x_1035_ = lean_box(0);
v___x_1036_ = lean_apply_1(v_h__1_1033_, v___x_1035_);
return v___x_1036_;
}
else
{
lean_object* v_val_1037_; lean_object* v___x_1038_; 
lean_dec(v_h__1_1033_);
v_val_1037_ = lean_ctor_get(v_x_1032_, 0);
lean_inc(v_val_1037_);
lean_dec_ref_known(v_x_1032_, 1);
v___x_1038_ = lean_apply_1(v_h__2_1034_, v_val_1037_);
return v___x_1038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1039_, lean_object* v_00_u03b2_1040_, lean_object* v_motive_1041_, lean_object* v_x_1042_, lean_object* v_h__1_1043_, lean_object* v_h__2_1044_){
_start:
{
if (lean_obj_tag(v_x_1042_) == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec(v_h__2_1044_);
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_apply_1(v_h__1_1043_, v___x_1045_);
return v___x_1046_;
}
else
{
lean_object* v_val_1047_; lean_object* v___x_1048_; 
lean_dec(v_h__1_1043_);
v_val_1047_ = lean_ctor_get(v_x_1042_, 0);
lean_inc(v_val_1047_);
lean_dec_ref_known(v_x_1042_, 1);
v___x_1048_ = lean_apply_1(v_h__2_1044_, v_val_1047_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___redArg(lean_object* v_t_1049_, lean_object* v_h__1_1050_){
_start:
{
lean_object* v_size_1051_; lean_object* v_k_1052_; lean_object* v_v_1053_; lean_object* v_l_1054_; lean_object* v_r_1055_; lean_object* v___x_1056_; 
v_size_1051_ = lean_ctor_get(v_t_1049_, 0);
lean_inc(v_size_1051_);
v_k_1052_ = lean_ctor_get(v_t_1049_, 1);
lean_inc(v_k_1052_);
v_v_1053_ = lean_ctor_get(v_t_1049_, 2);
lean_inc(v_v_1053_);
v_l_1054_ = lean_ctor_get(v_t_1049_, 3);
lean_inc(v_l_1054_);
v_r_1055_ = lean_ctor_get(v_t_1049_, 4);
lean_inc(v_r_1055_);
lean_dec(v_t_1049_);
v___x_1056_ = lean_apply_6(v_h__1_1050_, v_size_1051_, v_k_1052_, v_v_1053_, v_l_1054_, v_r_1055_, lean_box(0));
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(lean_object* v_00_u03b1_1057_, lean_object* v_00_u03b2_1058_, lean_object* v_inst_1059_, lean_object* v_k_1060_, lean_object* v_motive_1061_, lean_object* v_t_1062_, lean_object* v_hlk_1063_, lean_object* v_h__1_1064_){
_start:
{
lean_object* v_size_1065_; lean_object* v_k_1066_; lean_object* v_v_1067_; lean_object* v_l_1068_; lean_object* v_r_1069_; lean_object* v___x_1070_; 
v_size_1065_ = lean_ctor_get(v_t_1062_, 0);
lean_inc(v_size_1065_);
v_k_1066_ = lean_ctor_get(v_t_1062_, 1);
lean_inc(v_k_1066_);
v_v_1067_ = lean_ctor_get(v_t_1062_, 2);
lean_inc(v_v_1067_);
v_l_1068_ = lean_ctor_get(v_t_1062_, 3);
lean_inc(v_l_1068_);
v_r_1069_ = lean_ctor_get(v_t_1062_, 4);
lean_inc(v_r_1069_);
lean_dec(v_t_1062_);
v___x_1070_ = lean_apply_6(v_h__1_1064_, v_size_1065_, v_k_1066_, v_v_1067_, v_l_1068_, v_r_1069_, lean_box(0));
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___boxed(lean_object* v_00_u03b1_1071_, lean_object* v_00_u03b2_1072_, lean_object* v_inst_1073_, lean_object* v_k_1074_, lean_object* v_motive_1075_, lean_object* v_t_1076_, lean_object* v_hlk_1077_, lean_object* v_h__1_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(v_00_u03b1_1071_, v_00_u03b2_1072_, v_inst_1073_, v_k_1074_, v_motive_1075_, v_t_1076_, v_hlk_1077_, v_h__1_1078_);
lean_dec(v_k_1074_);
lean_dec_ref(v_inst_1073_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1080_, lean_object* v_h__1_1081_, lean_object* v_h__2_1082_, lean_object* v_h__3_1083_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
lean_object* v_l_1084_; 
lean_dec(v_h__1_1081_);
v_l_1084_ = lean_ctor_get(v_x_1080_, 3);
if (lean_obj_tag(v_l_1084_) == 0)
{
lean_object* v_size_1085_; lean_object* v_k_1086_; lean_object* v_v_1087_; lean_object* v_r_1088_; lean_object* v_size_1089_; lean_object* v_k_1090_; lean_object* v_v_1091_; lean_object* v_l_1092_; lean_object* v_r_1093_; lean_object* v___x_1094_; 
lean_inc_ref(v_l_1084_);
lean_dec(v_h__2_1082_);
v_size_1085_ = lean_ctor_get(v_x_1080_, 0);
lean_inc(v_size_1085_);
v_k_1086_ = lean_ctor_get(v_x_1080_, 1);
lean_inc(v_k_1086_);
v_v_1087_ = lean_ctor_get(v_x_1080_, 2);
lean_inc(v_v_1087_);
v_r_1088_ = lean_ctor_get(v_x_1080_, 4);
lean_inc(v_r_1088_);
lean_dec_ref_known(v_x_1080_, 5);
v_size_1089_ = lean_ctor_get(v_l_1084_, 0);
lean_inc(v_size_1089_);
v_k_1090_ = lean_ctor_get(v_l_1084_, 1);
lean_inc(v_k_1090_);
v_v_1091_ = lean_ctor_get(v_l_1084_, 2);
lean_inc(v_v_1091_);
v_l_1092_ = lean_ctor_get(v_l_1084_, 3);
lean_inc(v_l_1092_);
v_r_1093_ = lean_ctor_get(v_l_1084_, 4);
lean_inc(v_r_1093_);
lean_dec_ref_known(v_l_1084_, 5);
v___x_1094_ = lean_apply_9(v_h__3_1083_, v_size_1085_, v_k_1086_, v_v_1087_, v_size_1089_, v_k_1090_, v_v_1091_, v_l_1092_, v_r_1093_, v_r_1088_);
return v___x_1094_;
}
else
{
lean_object* v_size_1095_; lean_object* v_k_1096_; lean_object* v_v_1097_; lean_object* v_r_1098_; lean_object* v___x_1099_; 
lean_dec(v_h__3_1083_);
v_size_1095_ = lean_ctor_get(v_x_1080_, 0);
lean_inc(v_size_1095_);
v_k_1096_ = lean_ctor_get(v_x_1080_, 1);
lean_inc(v_k_1096_);
v_v_1097_ = lean_ctor_get(v_x_1080_, 2);
lean_inc(v_v_1097_);
v_r_1098_ = lean_ctor_get(v_x_1080_, 4);
lean_inc(v_r_1098_);
lean_dec_ref_known(v_x_1080_, 5);
v___x_1099_ = lean_apply_4(v_h__2_1082_, v_size_1095_, v_k_1096_, v_v_1097_, v_r_1098_);
return v___x_1099_;
}
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_h__3_1083_);
lean_dec(v_h__2_1082_);
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_apply_1(v_h__1_1081_, v___x_1100_);
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1102_, lean_object* v_00_u03b2_1103_, lean_object* v_motive_1104_, lean_object* v_x_1105_, lean_object* v_h__1_1106_, lean_object* v_h__2_1107_, lean_object* v_h__3_1108_){
_start:
{
if (lean_obj_tag(v_x_1105_) == 0)
{
lean_object* v_l_1109_; 
lean_dec(v_h__1_1106_);
v_l_1109_ = lean_ctor_get(v_x_1105_, 3);
if (lean_obj_tag(v_l_1109_) == 0)
{
lean_object* v_size_1110_; lean_object* v_k_1111_; lean_object* v_v_1112_; lean_object* v_r_1113_; lean_object* v_size_1114_; lean_object* v_k_1115_; lean_object* v_v_1116_; lean_object* v_l_1117_; lean_object* v_r_1118_; lean_object* v___x_1119_; 
lean_inc_ref(v_l_1109_);
lean_dec(v_h__2_1107_);
v_size_1110_ = lean_ctor_get(v_x_1105_, 0);
lean_inc(v_size_1110_);
v_k_1111_ = lean_ctor_get(v_x_1105_, 1);
lean_inc(v_k_1111_);
v_v_1112_ = lean_ctor_get(v_x_1105_, 2);
lean_inc(v_v_1112_);
v_r_1113_ = lean_ctor_get(v_x_1105_, 4);
lean_inc(v_r_1113_);
lean_dec_ref_known(v_x_1105_, 5);
v_size_1114_ = lean_ctor_get(v_l_1109_, 0);
lean_inc(v_size_1114_);
v_k_1115_ = lean_ctor_get(v_l_1109_, 1);
lean_inc(v_k_1115_);
v_v_1116_ = lean_ctor_get(v_l_1109_, 2);
lean_inc(v_v_1116_);
v_l_1117_ = lean_ctor_get(v_l_1109_, 3);
lean_inc(v_l_1117_);
v_r_1118_ = lean_ctor_get(v_l_1109_, 4);
lean_inc(v_r_1118_);
lean_dec_ref_known(v_l_1109_, 5);
v___x_1119_ = lean_apply_9(v_h__3_1108_, v_size_1110_, v_k_1111_, v_v_1112_, v_size_1114_, v_k_1115_, v_v_1116_, v_l_1117_, v_r_1118_, v_r_1113_);
return v___x_1119_;
}
else
{
lean_object* v_size_1120_; lean_object* v_k_1121_; lean_object* v_v_1122_; lean_object* v_r_1123_; lean_object* v___x_1124_; 
lean_dec(v_h__3_1108_);
v_size_1120_ = lean_ctor_get(v_x_1105_, 0);
lean_inc(v_size_1120_);
v_k_1121_ = lean_ctor_get(v_x_1105_, 1);
lean_inc(v_k_1121_);
v_v_1122_ = lean_ctor_get(v_x_1105_, 2);
lean_inc(v_v_1122_);
v_r_1123_ = lean_ctor_get(v_x_1105_, 4);
lean_inc(v_r_1123_);
lean_dec_ref_known(v_x_1105_, 5);
v___x_1124_ = lean_apply_4(v_h__2_1107_, v_size_1120_, v_k_1121_, v_v_1122_, v_r_1123_);
return v___x_1124_;
}
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec(v_h__3_1108_);
lean_dec(v_h__2_1107_);
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_apply_1(v_h__1_1106_, v___x_1125_);
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_step_1127_, lean_object* v_h__1_1128_, lean_object* v_h__2_1129_){
_start:
{
if (lean_obj_tag(v_step_1127_) == 0)
{
lean_object* v_a_1130_; lean_object* v_a_1131_; lean_object* v_a_1132_; lean_object* v___x_1133_; 
lean_dec(v_h__2_1129_);
v_a_1130_ = lean_ctor_get(v_step_1127_, 0);
lean_inc(v_a_1130_);
v_a_1131_ = lean_ctor_get(v_step_1127_, 1);
lean_inc(v_a_1131_);
v_a_1132_ = lean_ctor_get(v_step_1127_, 2);
lean_inc(v_a_1132_);
lean_dec_ref_known(v_step_1127_, 3);
v___x_1133_ = lean_apply_4(v_h__1_1128_, v_a_1130_, lean_box(0), v_a_1131_, v_a_1132_);
return v___x_1133_;
}
else
{
lean_object* v_a_1134_; lean_object* v_a_1135_; lean_object* v_a_1136_; lean_object* v___x_1137_; 
lean_dec(v_h__1_1128_);
v_a_1134_ = lean_ctor_get(v_step_1127_, 0);
lean_inc(v_a_1134_);
v_a_1135_ = lean_ctor_get(v_step_1127_, 1);
lean_inc(v_a_1135_);
v_a_1136_ = lean_ctor_get(v_step_1127_, 2);
lean_inc(v_a_1136_);
lean_dec_ref_known(v_step_1127_, 3);
v___x_1137_ = lean_apply_3(v_h__2_1129_, v_a_1134_, v_a_1135_, v_a_1136_);
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_1138_, lean_object* v_00_u03b2_1139_, lean_object* v_inst_1140_, lean_object* v_motive_1141_, lean_object* v_step_1142_, lean_object* v_h__1_1143_, lean_object* v_h__2_1144_){
_start:
{
if (lean_obj_tag(v_step_1142_) == 0)
{
lean_object* v_a_1145_; lean_object* v_a_1146_; lean_object* v_a_1147_; lean_object* v___x_1148_; 
lean_dec(v_h__2_1144_);
v_a_1145_ = lean_ctor_get(v_step_1142_, 0);
lean_inc(v_a_1145_);
v_a_1146_ = lean_ctor_get(v_step_1142_, 1);
lean_inc(v_a_1146_);
v_a_1147_ = lean_ctor_get(v_step_1142_, 2);
lean_inc(v_a_1147_);
lean_dec_ref_known(v_step_1142_, 3);
v___x_1148_ = lean_apply_4(v_h__1_1143_, v_a_1145_, lean_box(0), v_a_1146_, v_a_1147_);
return v___x_1148_;
}
else
{
lean_object* v_a_1149_; lean_object* v_a_1150_; lean_object* v_a_1151_; lean_object* v___x_1152_; 
lean_dec(v_h__1_1143_);
v_a_1149_ = lean_ctor_get(v_step_1142_, 0);
lean_inc(v_a_1149_);
v_a_1150_ = lean_ctor_get(v_step_1142_, 1);
lean_inc(v_a_1150_);
v_a_1151_ = lean_ctor_get(v_step_1142_, 2);
lean_inc(v_a_1151_);
lean_dec_ref_known(v_step_1142_, 3);
v___x_1152_ = lean_apply_3(v_h__2_1144_, v_a_1149_, v_a_1150_, v_a_1151_);
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_1153_, lean_object* v_00_u03b2_1154_, lean_object* v_inst_1155_, lean_object* v_motive_1156_, lean_object* v_step_1157_, lean_object* v_h__1_1158_, lean_object* v_h__2_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(v_00_u03b1_1153_, v_00_u03b2_1154_, v_inst_1155_, v_motive_1156_, v_step_1157_, v_h__1_1158_, v_h__2_1159_);
lean_dec_ref(v_inst_1155_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object* v_x_1161_, lean_object* v_x_1162_, lean_object* v_h__1_1163_, lean_object* v_h__2_1164_, lean_object* v_h__3_1165_){
_start:
{
if (lean_obj_tag(v_x_1161_) == 0)
{
lean_object* v_l_1166_; 
lean_dec(v_h__1_1163_);
v_l_1166_ = lean_ctor_get(v_x_1161_, 3);
if (lean_obj_tag(v_l_1166_) == 0)
{
lean_object* v_size_1167_; lean_object* v_k_1168_; lean_object* v_v_1169_; lean_object* v_r_1170_; lean_object* v_size_1171_; lean_object* v_k_1172_; lean_object* v_v_1173_; lean_object* v_l_1174_; lean_object* v_r_1175_; lean_object* v___x_1176_; 
lean_inc_ref(v_l_1166_);
lean_dec(v_h__2_1164_);
v_size_1167_ = lean_ctor_get(v_x_1161_, 0);
lean_inc(v_size_1167_);
v_k_1168_ = lean_ctor_get(v_x_1161_, 1);
lean_inc(v_k_1168_);
v_v_1169_ = lean_ctor_get(v_x_1161_, 2);
lean_inc(v_v_1169_);
v_r_1170_ = lean_ctor_get(v_x_1161_, 4);
lean_inc(v_r_1170_);
lean_dec_ref_known(v_x_1161_, 5);
v_size_1171_ = lean_ctor_get(v_l_1166_, 0);
lean_inc(v_size_1171_);
v_k_1172_ = lean_ctor_get(v_l_1166_, 1);
lean_inc(v_k_1172_);
v_v_1173_ = lean_ctor_get(v_l_1166_, 2);
lean_inc(v_v_1173_);
v_l_1174_ = lean_ctor_get(v_l_1166_, 3);
lean_inc(v_l_1174_);
v_r_1175_ = lean_ctor_get(v_l_1166_, 4);
lean_inc(v_r_1175_);
lean_dec_ref_known(v_l_1166_, 5);
v___x_1176_ = lean_apply_10(v_h__3_1165_, v_size_1167_, v_k_1168_, v_v_1169_, v_size_1171_, v_k_1172_, v_v_1173_, v_l_1174_, v_r_1175_, v_r_1170_, v_x_1162_);
return v___x_1176_;
}
else
{
lean_object* v_size_1177_; lean_object* v_k_1178_; lean_object* v_v_1179_; lean_object* v_r_1180_; lean_object* v___x_1181_; 
lean_dec(v_h__3_1165_);
v_size_1177_ = lean_ctor_get(v_x_1161_, 0);
lean_inc(v_size_1177_);
v_k_1178_ = lean_ctor_get(v_x_1161_, 1);
lean_inc(v_k_1178_);
v_v_1179_ = lean_ctor_get(v_x_1161_, 2);
lean_inc(v_v_1179_);
v_r_1180_ = lean_ctor_get(v_x_1161_, 4);
lean_inc(v_r_1180_);
lean_dec_ref_known(v_x_1161_, 5);
v___x_1181_ = lean_apply_5(v_h__2_1164_, v_size_1177_, v_k_1178_, v_v_1179_, v_r_1180_, v_x_1162_);
return v___x_1181_;
}
}
else
{
lean_object* v___x_1182_; 
lean_dec(v_h__3_1165_);
lean_dec(v_h__2_1164_);
v___x_1182_ = lean_apply_1(v_h__1_1163_, v_x_1162_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1183_, lean_object* v_00_u03b2_1184_, lean_object* v_motive_1185_, lean_object* v_x_1186_, lean_object* v_x_1187_, lean_object* v_h__1_1188_, lean_object* v_h__2_1189_, lean_object* v_h__3_1190_){
_start:
{
if (lean_obj_tag(v_x_1186_) == 0)
{
lean_object* v_l_1191_; 
lean_dec(v_h__1_1188_);
v_l_1191_ = lean_ctor_get(v_x_1186_, 3);
if (lean_obj_tag(v_l_1191_) == 0)
{
lean_object* v_size_1192_; lean_object* v_k_1193_; lean_object* v_v_1194_; lean_object* v_r_1195_; lean_object* v_size_1196_; lean_object* v_k_1197_; lean_object* v_v_1198_; lean_object* v_l_1199_; lean_object* v_r_1200_; lean_object* v___x_1201_; 
lean_inc_ref(v_l_1191_);
lean_dec(v_h__2_1189_);
v_size_1192_ = lean_ctor_get(v_x_1186_, 0);
lean_inc(v_size_1192_);
v_k_1193_ = lean_ctor_get(v_x_1186_, 1);
lean_inc(v_k_1193_);
v_v_1194_ = lean_ctor_get(v_x_1186_, 2);
lean_inc(v_v_1194_);
v_r_1195_ = lean_ctor_get(v_x_1186_, 4);
lean_inc(v_r_1195_);
lean_dec_ref_known(v_x_1186_, 5);
v_size_1196_ = lean_ctor_get(v_l_1191_, 0);
lean_inc(v_size_1196_);
v_k_1197_ = lean_ctor_get(v_l_1191_, 1);
lean_inc(v_k_1197_);
v_v_1198_ = lean_ctor_get(v_l_1191_, 2);
lean_inc(v_v_1198_);
v_l_1199_ = lean_ctor_get(v_l_1191_, 3);
lean_inc(v_l_1199_);
v_r_1200_ = lean_ctor_get(v_l_1191_, 4);
lean_inc(v_r_1200_);
lean_dec_ref_known(v_l_1191_, 5);
v___x_1201_ = lean_apply_10(v_h__3_1190_, v_size_1192_, v_k_1193_, v_v_1194_, v_size_1196_, v_k_1197_, v_v_1198_, v_l_1199_, v_r_1200_, v_r_1195_, v_x_1187_);
return v___x_1201_;
}
else
{
lean_object* v_size_1202_; lean_object* v_k_1203_; lean_object* v_v_1204_; lean_object* v_r_1205_; lean_object* v___x_1206_; 
lean_dec(v_h__3_1190_);
v_size_1202_ = lean_ctor_get(v_x_1186_, 0);
lean_inc(v_size_1202_);
v_k_1203_ = lean_ctor_get(v_x_1186_, 1);
lean_inc(v_k_1203_);
v_v_1204_ = lean_ctor_get(v_x_1186_, 2);
lean_inc(v_v_1204_);
v_r_1205_ = lean_ctor_get(v_x_1186_, 4);
lean_inc(v_r_1205_);
lean_dec_ref_known(v_x_1186_, 5);
v___x_1206_ = lean_apply_5(v_h__2_1189_, v_size_1202_, v_k_1203_, v_v_1204_, v_r_1205_, v_x_1187_);
return v___x_1206_;
}
}
else
{
lean_object* v___x_1207_; 
lean_dec(v_h__3_1190_);
lean_dec(v_h__2_1189_);
v___x_1207_ = lean_apply_1(v_h__1_1188_, v_x_1187_);
return v___x_1207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object* v_x_1208_, lean_object* v_h__1_1209_, lean_object* v_h__2_1210_){
_start:
{
lean_object* v_l_1211_; 
v_l_1211_ = lean_ctor_get(v_x_1208_, 3);
if (lean_obj_tag(v_l_1211_) == 0)
{
lean_object* v_size_1212_; lean_object* v_k_1213_; lean_object* v_v_1214_; lean_object* v_r_1215_; lean_object* v_size_1216_; lean_object* v_k_1217_; lean_object* v_v_1218_; lean_object* v_l_1219_; lean_object* v_r_1220_; lean_object* v___x_1221_; 
lean_inc_ref(v_l_1211_);
lean_dec(v_h__1_1209_);
v_size_1212_ = lean_ctor_get(v_x_1208_, 0);
lean_inc(v_size_1212_);
v_k_1213_ = lean_ctor_get(v_x_1208_, 1);
lean_inc(v_k_1213_);
v_v_1214_ = lean_ctor_get(v_x_1208_, 2);
lean_inc(v_v_1214_);
v_r_1215_ = lean_ctor_get(v_x_1208_, 4);
lean_inc(v_r_1215_);
lean_dec(v_x_1208_);
v_size_1216_ = lean_ctor_get(v_l_1211_, 0);
lean_inc(v_size_1216_);
v_k_1217_ = lean_ctor_get(v_l_1211_, 1);
lean_inc(v_k_1217_);
v_v_1218_ = lean_ctor_get(v_l_1211_, 2);
lean_inc(v_v_1218_);
v_l_1219_ = lean_ctor_get(v_l_1211_, 3);
lean_inc(v_l_1219_);
v_r_1220_ = lean_ctor_get(v_l_1211_, 4);
lean_inc(v_r_1220_);
lean_dec_ref_known(v_l_1211_, 5);
v___x_1221_ = lean_apply_10(v_h__2_1210_, v_size_1212_, v_k_1213_, v_v_1214_, v_size_1216_, v_k_1217_, v_v_1218_, v_l_1219_, v_r_1220_, v_r_1215_, lean_box(0));
return v___x_1221_;
}
else
{
lean_object* v_size_1222_; lean_object* v_k_1223_; lean_object* v_v_1224_; lean_object* v_r_1225_; lean_object* v___x_1226_; 
lean_dec(v_h__2_1210_);
v_size_1222_ = lean_ctor_get(v_x_1208_, 0);
lean_inc(v_size_1222_);
v_k_1223_ = lean_ctor_get(v_x_1208_, 1);
lean_inc(v_k_1223_);
v_v_1224_ = lean_ctor_get(v_x_1208_, 2);
lean_inc(v_v_1224_);
v_r_1225_ = lean_ctor_get(v_x_1208_, 4);
lean_inc(v_r_1225_);
lean_dec(v_x_1208_);
v___x_1226_ = lean_apply_5(v_h__1_1209_, v_size_1222_, v_k_1223_, v_v_1224_, v_r_1225_, lean_box(0));
return v___x_1226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* v_00_u03b1_1227_, lean_object* v_00_u03b2_1228_, lean_object* v_motive_1229_, lean_object* v_x_1230_, lean_object* v_x_1231_, lean_object* v_h__1_1232_, lean_object* v_h__2_1233_){
_start:
{
lean_object* v_l_1234_; 
v_l_1234_ = lean_ctor_get(v_x_1230_, 3);
if (lean_obj_tag(v_l_1234_) == 0)
{
lean_object* v_size_1235_; lean_object* v_k_1236_; lean_object* v_v_1237_; lean_object* v_r_1238_; lean_object* v_size_1239_; lean_object* v_k_1240_; lean_object* v_v_1241_; lean_object* v_l_1242_; lean_object* v_r_1243_; lean_object* v___x_1244_; 
lean_inc_ref(v_l_1234_);
lean_dec(v_h__1_1232_);
v_size_1235_ = lean_ctor_get(v_x_1230_, 0);
lean_inc(v_size_1235_);
v_k_1236_ = lean_ctor_get(v_x_1230_, 1);
lean_inc(v_k_1236_);
v_v_1237_ = lean_ctor_get(v_x_1230_, 2);
lean_inc(v_v_1237_);
v_r_1238_ = lean_ctor_get(v_x_1230_, 4);
lean_inc(v_r_1238_);
lean_dec(v_x_1230_);
v_size_1239_ = lean_ctor_get(v_l_1234_, 0);
lean_inc(v_size_1239_);
v_k_1240_ = lean_ctor_get(v_l_1234_, 1);
lean_inc(v_k_1240_);
v_v_1241_ = lean_ctor_get(v_l_1234_, 2);
lean_inc(v_v_1241_);
v_l_1242_ = lean_ctor_get(v_l_1234_, 3);
lean_inc(v_l_1242_);
v_r_1243_ = lean_ctor_get(v_l_1234_, 4);
lean_inc(v_r_1243_);
lean_dec_ref_known(v_l_1234_, 5);
v___x_1244_ = lean_apply_10(v_h__2_1233_, v_size_1235_, v_k_1236_, v_v_1237_, v_size_1239_, v_k_1240_, v_v_1241_, v_l_1242_, v_r_1243_, v_r_1238_, lean_box(0));
return v___x_1244_;
}
else
{
lean_object* v_size_1245_; lean_object* v_k_1246_; lean_object* v_v_1247_; lean_object* v_r_1248_; lean_object* v___x_1249_; 
lean_dec(v_h__2_1233_);
v_size_1245_ = lean_ctor_get(v_x_1230_, 0);
lean_inc(v_size_1245_);
v_k_1246_ = lean_ctor_get(v_x_1230_, 1);
lean_inc(v_k_1246_);
v_v_1247_ = lean_ctor_get(v_x_1230_, 2);
lean_inc(v_v_1247_);
v_r_1248_ = lean_ctor_get(v_x_1230_, 4);
lean_inc(v_r_1248_);
lean_dec(v_x_1230_);
v___x_1249_ = lean_apply_5(v_h__1_1232_, v_size_1245_, v_k_1246_, v_v_1247_, v_r_1248_, lean_box(0));
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1250_, lean_object* v_h__1_1251_, lean_object* v_h__2_1252_, lean_object* v_h__3_1253_){
_start:
{
if (lean_obj_tag(v_x_1250_) == 0)
{
lean_object* v_r_1254_; 
lean_dec(v_h__1_1251_);
v_r_1254_ = lean_ctor_get(v_x_1250_, 4);
if (lean_obj_tag(v_r_1254_) == 0)
{
lean_object* v_size_1255_; lean_object* v_k_1256_; lean_object* v_v_1257_; lean_object* v_l_1258_; lean_object* v_size_1259_; lean_object* v_k_1260_; lean_object* v_v_1261_; lean_object* v_l_1262_; lean_object* v_r_1263_; lean_object* v___x_1264_; 
lean_inc_ref(v_r_1254_);
lean_dec(v_h__2_1252_);
v_size_1255_ = lean_ctor_get(v_x_1250_, 0);
lean_inc(v_size_1255_);
v_k_1256_ = lean_ctor_get(v_x_1250_, 1);
lean_inc(v_k_1256_);
v_v_1257_ = lean_ctor_get(v_x_1250_, 2);
lean_inc(v_v_1257_);
v_l_1258_ = lean_ctor_get(v_x_1250_, 3);
lean_inc(v_l_1258_);
lean_dec_ref_known(v_x_1250_, 5);
v_size_1259_ = lean_ctor_get(v_r_1254_, 0);
lean_inc(v_size_1259_);
v_k_1260_ = lean_ctor_get(v_r_1254_, 1);
lean_inc(v_k_1260_);
v_v_1261_ = lean_ctor_get(v_r_1254_, 2);
lean_inc(v_v_1261_);
v_l_1262_ = lean_ctor_get(v_r_1254_, 3);
lean_inc(v_l_1262_);
v_r_1263_ = lean_ctor_get(v_r_1254_, 4);
lean_inc(v_r_1263_);
lean_dec_ref_known(v_r_1254_, 5);
v___x_1264_ = lean_apply_9(v_h__3_1253_, v_size_1255_, v_k_1256_, v_v_1257_, v_l_1258_, v_size_1259_, v_k_1260_, v_v_1261_, v_l_1262_, v_r_1263_);
return v___x_1264_;
}
else
{
lean_object* v_size_1265_; lean_object* v_k_1266_; lean_object* v_v_1267_; lean_object* v_l_1268_; lean_object* v___x_1269_; 
lean_dec(v_h__3_1253_);
v_size_1265_ = lean_ctor_get(v_x_1250_, 0);
lean_inc(v_size_1265_);
v_k_1266_ = lean_ctor_get(v_x_1250_, 1);
lean_inc(v_k_1266_);
v_v_1267_ = lean_ctor_get(v_x_1250_, 2);
lean_inc(v_v_1267_);
v_l_1268_ = lean_ctor_get(v_x_1250_, 3);
lean_inc(v_l_1268_);
lean_dec_ref_known(v_x_1250_, 5);
v___x_1269_ = lean_apply_4(v_h__2_1252_, v_size_1265_, v_k_1266_, v_v_1267_, v_l_1268_);
return v___x_1269_;
}
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec(v_h__3_1253_);
lean_dec(v_h__2_1252_);
v___x_1270_ = lean_box(0);
v___x_1271_ = lean_apply_1(v_h__1_1251_, v___x_1270_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1272_, lean_object* v_00_u03b2_1273_, lean_object* v_motive_1274_, lean_object* v_x_1275_, lean_object* v_h__1_1276_, lean_object* v_h__2_1277_, lean_object* v_h__3_1278_){
_start:
{
if (lean_obj_tag(v_x_1275_) == 0)
{
lean_object* v_r_1279_; 
lean_dec(v_h__1_1276_);
v_r_1279_ = lean_ctor_get(v_x_1275_, 4);
if (lean_obj_tag(v_r_1279_) == 0)
{
lean_object* v_size_1280_; lean_object* v_k_1281_; lean_object* v_v_1282_; lean_object* v_l_1283_; lean_object* v_size_1284_; lean_object* v_k_1285_; lean_object* v_v_1286_; lean_object* v_l_1287_; lean_object* v_r_1288_; lean_object* v___x_1289_; 
lean_inc_ref(v_r_1279_);
lean_dec(v_h__2_1277_);
v_size_1280_ = lean_ctor_get(v_x_1275_, 0);
lean_inc(v_size_1280_);
v_k_1281_ = lean_ctor_get(v_x_1275_, 1);
lean_inc(v_k_1281_);
v_v_1282_ = lean_ctor_get(v_x_1275_, 2);
lean_inc(v_v_1282_);
v_l_1283_ = lean_ctor_get(v_x_1275_, 3);
lean_inc(v_l_1283_);
lean_dec_ref_known(v_x_1275_, 5);
v_size_1284_ = lean_ctor_get(v_r_1279_, 0);
lean_inc(v_size_1284_);
v_k_1285_ = lean_ctor_get(v_r_1279_, 1);
lean_inc(v_k_1285_);
v_v_1286_ = lean_ctor_get(v_r_1279_, 2);
lean_inc(v_v_1286_);
v_l_1287_ = lean_ctor_get(v_r_1279_, 3);
lean_inc(v_l_1287_);
v_r_1288_ = lean_ctor_get(v_r_1279_, 4);
lean_inc(v_r_1288_);
lean_dec_ref_known(v_r_1279_, 5);
v___x_1289_ = lean_apply_9(v_h__3_1278_, v_size_1280_, v_k_1281_, v_v_1282_, v_l_1283_, v_size_1284_, v_k_1285_, v_v_1286_, v_l_1287_, v_r_1288_);
return v___x_1289_;
}
else
{
lean_object* v_size_1290_; lean_object* v_k_1291_; lean_object* v_v_1292_; lean_object* v_l_1293_; lean_object* v___x_1294_; 
lean_dec(v_h__3_1278_);
v_size_1290_ = lean_ctor_get(v_x_1275_, 0);
lean_inc(v_size_1290_);
v_k_1291_ = lean_ctor_get(v_x_1275_, 1);
lean_inc(v_k_1291_);
v_v_1292_ = lean_ctor_get(v_x_1275_, 2);
lean_inc(v_v_1292_);
v_l_1293_ = lean_ctor_get(v_x_1275_, 3);
lean_inc(v_l_1293_);
lean_dec_ref_known(v_x_1275_, 5);
v___x_1294_ = lean_apply_4(v_h__2_1277_, v_size_1290_, v_k_1291_, v_v_1292_, v_l_1293_);
return v___x_1294_;
}
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec(v_h__3_1278_);
lean_dec(v_h__2_1277_);
v___x_1295_ = lean_box(0);
v___x_1296_ = lean_apply_1(v_h__1_1276_, v___x_1295_);
return v___x_1296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1297_, lean_object* v_x_1298_, lean_object* v_h__1_1299_, lean_object* v_h__2_1300_, lean_object* v_h__3_1301_){
_start:
{
if (lean_obj_tag(v_x_1297_) == 0)
{
lean_object* v_r_1302_; 
lean_dec(v_h__1_1299_);
v_r_1302_ = lean_ctor_get(v_x_1297_, 4);
if (lean_obj_tag(v_r_1302_) == 0)
{
lean_object* v_size_1303_; lean_object* v_k_1304_; lean_object* v_v_1305_; lean_object* v_l_1306_; lean_object* v_size_1307_; lean_object* v_k_1308_; lean_object* v_v_1309_; lean_object* v_l_1310_; lean_object* v_r_1311_; lean_object* v___x_1312_; 
lean_inc_ref(v_r_1302_);
lean_dec(v_h__2_1300_);
v_size_1303_ = lean_ctor_get(v_x_1297_, 0);
lean_inc(v_size_1303_);
v_k_1304_ = lean_ctor_get(v_x_1297_, 1);
lean_inc(v_k_1304_);
v_v_1305_ = lean_ctor_get(v_x_1297_, 2);
lean_inc(v_v_1305_);
v_l_1306_ = lean_ctor_get(v_x_1297_, 3);
lean_inc(v_l_1306_);
lean_dec_ref_known(v_x_1297_, 5);
v_size_1307_ = lean_ctor_get(v_r_1302_, 0);
lean_inc(v_size_1307_);
v_k_1308_ = lean_ctor_get(v_r_1302_, 1);
lean_inc(v_k_1308_);
v_v_1309_ = lean_ctor_get(v_r_1302_, 2);
lean_inc(v_v_1309_);
v_l_1310_ = lean_ctor_get(v_r_1302_, 3);
lean_inc(v_l_1310_);
v_r_1311_ = lean_ctor_get(v_r_1302_, 4);
lean_inc(v_r_1311_);
lean_dec_ref_known(v_r_1302_, 5);
v___x_1312_ = lean_apply_10(v_h__3_1301_, v_size_1303_, v_k_1304_, v_v_1305_, v_l_1306_, v_size_1307_, v_k_1308_, v_v_1309_, v_l_1310_, v_r_1311_, v_x_1298_);
return v___x_1312_;
}
else
{
lean_object* v_size_1313_; lean_object* v_k_1314_; lean_object* v_v_1315_; lean_object* v_l_1316_; lean_object* v___x_1317_; 
lean_dec(v_h__3_1301_);
v_size_1313_ = lean_ctor_get(v_x_1297_, 0);
lean_inc(v_size_1313_);
v_k_1314_ = lean_ctor_get(v_x_1297_, 1);
lean_inc(v_k_1314_);
v_v_1315_ = lean_ctor_get(v_x_1297_, 2);
lean_inc(v_v_1315_);
v_l_1316_ = lean_ctor_get(v_x_1297_, 3);
lean_inc(v_l_1316_);
lean_dec_ref_known(v_x_1297_, 5);
v___x_1317_ = lean_apply_5(v_h__2_1300_, v_size_1313_, v_k_1314_, v_v_1315_, v_l_1316_, v_x_1298_);
return v___x_1317_;
}
}
else
{
lean_object* v___x_1318_; 
lean_dec(v_h__3_1301_);
lean_dec(v_h__2_1300_);
v___x_1318_ = lean_apply_1(v_h__1_1299_, v_x_1298_);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1319_, lean_object* v_00_u03b2_1320_, lean_object* v_motive_1321_, lean_object* v_x_1322_, lean_object* v_x_1323_, lean_object* v_h__1_1324_, lean_object* v_h__2_1325_, lean_object* v_h__3_1326_){
_start:
{
if (lean_obj_tag(v_x_1322_) == 0)
{
lean_object* v_r_1327_; 
lean_dec(v_h__1_1324_);
v_r_1327_ = lean_ctor_get(v_x_1322_, 4);
if (lean_obj_tag(v_r_1327_) == 0)
{
lean_object* v_size_1328_; lean_object* v_k_1329_; lean_object* v_v_1330_; lean_object* v_l_1331_; lean_object* v_size_1332_; lean_object* v_k_1333_; lean_object* v_v_1334_; lean_object* v_l_1335_; lean_object* v_r_1336_; lean_object* v___x_1337_; 
lean_inc_ref(v_r_1327_);
lean_dec(v_h__2_1325_);
v_size_1328_ = lean_ctor_get(v_x_1322_, 0);
lean_inc(v_size_1328_);
v_k_1329_ = lean_ctor_get(v_x_1322_, 1);
lean_inc(v_k_1329_);
v_v_1330_ = lean_ctor_get(v_x_1322_, 2);
lean_inc(v_v_1330_);
v_l_1331_ = lean_ctor_get(v_x_1322_, 3);
lean_inc(v_l_1331_);
lean_dec_ref_known(v_x_1322_, 5);
v_size_1332_ = lean_ctor_get(v_r_1327_, 0);
lean_inc(v_size_1332_);
v_k_1333_ = lean_ctor_get(v_r_1327_, 1);
lean_inc(v_k_1333_);
v_v_1334_ = lean_ctor_get(v_r_1327_, 2);
lean_inc(v_v_1334_);
v_l_1335_ = lean_ctor_get(v_r_1327_, 3);
lean_inc(v_l_1335_);
v_r_1336_ = lean_ctor_get(v_r_1327_, 4);
lean_inc(v_r_1336_);
lean_dec_ref_known(v_r_1327_, 5);
v___x_1337_ = lean_apply_10(v_h__3_1326_, v_size_1328_, v_k_1329_, v_v_1330_, v_l_1331_, v_size_1332_, v_k_1333_, v_v_1334_, v_l_1335_, v_r_1336_, v_x_1323_);
return v___x_1337_;
}
else
{
lean_object* v_size_1338_; lean_object* v_k_1339_; lean_object* v_v_1340_; lean_object* v_l_1341_; lean_object* v___x_1342_; 
lean_dec(v_h__3_1326_);
v_size_1338_ = lean_ctor_get(v_x_1322_, 0);
lean_inc(v_size_1338_);
v_k_1339_ = lean_ctor_get(v_x_1322_, 1);
lean_inc(v_k_1339_);
v_v_1340_ = lean_ctor_get(v_x_1322_, 2);
lean_inc(v_v_1340_);
v_l_1341_ = lean_ctor_get(v_x_1322_, 3);
lean_inc(v_l_1341_);
lean_dec_ref_known(v_x_1322_, 5);
v___x_1342_ = lean_apply_5(v_h__2_1325_, v_size_1338_, v_k_1339_, v_v_1340_, v_l_1341_, v_x_1323_);
return v___x_1342_;
}
}
else
{
lean_object* v___x_1343_; 
lean_dec(v_h__3_1326_);
lean_dec(v_h__2_1325_);
v___x_1343_ = lean_apply_1(v_h__1_1324_, v_x_1323_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object* v_x_1344_, lean_object* v_h__1_1345_, lean_object* v_h__2_1346_){
_start:
{
lean_object* v_r_1347_; 
v_r_1347_ = lean_ctor_get(v_x_1344_, 4);
if (lean_obj_tag(v_r_1347_) == 0)
{
lean_object* v_size_1348_; lean_object* v_k_1349_; lean_object* v_v_1350_; lean_object* v_l_1351_; lean_object* v_size_1352_; lean_object* v_k_1353_; lean_object* v_v_1354_; lean_object* v_l_1355_; lean_object* v_r_1356_; lean_object* v___x_1357_; 
lean_inc_ref(v_r_1347_);
lean_dec(v_h__1_1345_);
v_size_1348_ = lean_ctor_get(v_x_1344_, 0);
lean_inc(v_size_1348_);
v_k_1349_ = lean_ctor_get(v_x_1344_, 1);
lean_inc(v_k_1349_);
v_v_1350_ = lean_ctor_get(v_x_1344_, 2);
lean_inc(v_v_1350_);
v_l_1351_ = lean_ctor_get(v_x_1344_, 3);
lean_inc(v_l_1351_);
lean_dec(v_x_1344_);
v_size_1352_ = lean_ctor_get(v_r_1347_, 0);
lean_inc(v_size_1352_);
v_k_1353_ = lean_ctor_get(v_r_1347_, 1);
lean_inc(v_k_1353_);
v_v_1354_ = lean_ctor_get(v_r_1347_, 2);
lean_inc(v_v_1354_);
v_l_1355_ = lean_ctor_get(v_r_1347_, 3);
lean_inc(v_l_1355_);
v_r_1356_ = lean_ctor_get(v_r_1347_, 4);
lean_inc(v_r_1356_);
lean_dec_ref_known(v_r_1347_, 5);
v___x_1357_ = lean_apply_10(v_h__2_1346_, v_size_1348_, v_k_1349_, v_v_1350_, v_l_1351_, v_size_1352_, v_k_1353_, v_v_1354_, v_l_1355_, v_r_1356_, lean_box(0));
return v___x_1357_;
}
else
{
lean_object* v_size_1358_; lean_object* v_k_1359_; lean_object* v_v_1360_; lean_object* v_l_1361_; lean_object* v___x_1362_; 
lean_dec(v_h__2_1346_);
v_size_1358_ = lean_ctor_get(v_x_1344_, 0);
lean_inc(v_size_1358_);
v_k_1359_ = lean_ctor_get(v_x_1344_, 1);
lean_inc(v_k_1359_);
v_v_1360_ = lean_ctor_get(v_x_1344_, 2);
lean_inc(v_v_1360_);
v_l_1361_ = lean_ctor_get(v_x_1344_, 3);
lean_inc(v_l_1361_);
lean_dec(v_x_1344_);
v___x_1362_ = lean_apply_5(v_h__1_1345_, v_size_1358_, v_k_1359_, v_v_1360_, v_l_1361_, lean_box(0));
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1363_, lean_object* v_00_u03b2_1364_, lean_object* v_motive_1365_, lean_object* v_x_1366_, lean_object* v_x_1367_, lean_object* v_h__1_1368_, lean_object* v_h__2_1369_){
_start:
{
lean_object* v_r_1370_; 
v_r_1370_ = lean_ctor_get(v_x_1366_, 4);
if (lean_obj_tag(v_r_1370_) == 0)
{
lean_object* v_size_1371_; lean_object* v_k_1372_; lean_object* v_v_1373_; lean_object* v_l_1374_; lean_object* v_size_1375_; lean_object* v_k_1376_; lean_object* v_v_1377_; lean_object* v_l_1378_; lean_object* v_r_1379_; lean_object* v___x_1380_; 
lean_inc_ref(v_r_1370_);
lean_dec(v_h__1_1368_);
v_size_1371_ = lean_ctor_get(v_x_1366_, 0);
lean_inc(v_size_1371_);
v_k_1372_ = lean_ctor_get(v_x_1366_, 1);
lean_inc(v_k_1372_);
v_v_1373_ = lean_ctor_get(v_x_1366_, 2);
lean_inc(v_v_1373_);
v_l_1374_ = lean_ctor_get(v_x_1366_, 3);
lean_inc(v_l_1374_);
lean_dec(v_x_1366_);
v_size_1375_ = lean_ctor_get(v_r_1370_, 0);
lean_inc(v_size_1375_);
v_k_1376_ = lean_ctor_get(v_r_1370_, 1);
lean_inc(v_k_1376_);
v_v_1377_ = lean_ctor_get(v_r_1370_, 2);
lean_inc(v_v_1377_);
v_l_1378_ = lean_ctor_get(v_r_1370_, 3);
lean_inc(v_l_1378_);
v_r_1379_ = lean_ctor_get(v_r_1370_, 4);
lean_inc(v_r_1379_);
lean_dec_ref_known(v_r_1370_, 5);
v___x_1380_ = lean_apply_10(v_h__2_1369_, v_size_1371_, v_k_1372_, v_v_1373_, v_l_1374_, v_size_1375_, v_k_1376_, v_v_1377_, v_l_1378_, v_r_1379_, lean_box(0));
return v___x_1380_;
}
else
{
lean_object* v_size_1381_; lean_object* v_k_1382_; lean_object* v_v_1383_; lean_object* v_l_1384_; lean_object* v___x_1385_; 
lean_dec(v_h__2_1369_);
v_size_1381_ = lean_ctor_get(v_x_1366_, 0);
lean_inc(v_size_1381_);
v_k_1382_ = lean_ctor_get(v_x_1366_, 1);
lean_inc(v_k_1382_);
v_v_1383_ = lean_ctor_get(v_x_1366_, 2);
lean_inc(v_v_1383_);
v_l_1384_ = lean_ctor_get(v_x_1366_, 3);
lean_inc(v_l_1384_);
lean_dec(v_x_1366_);
v___x_1385_ = lean_apply_5(v_h__1_1368_, v_size_1381_, v_k_1382_, v_v_1383_, v_l_1384_, lean_box(0));
return v___x_1385_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object* v_x_1386_, lean_object* v_x_1387_, lean_object* v_h__1_1388_, lean_object* v_h__2_1389_, lean_object* v_h__3_1390_){
_start:
{
if (lean_obj_tag(v_x_1386_) == 0)
{
lean_object* v_l_1391_; 
lean_dec(v_h__1_1388_);
v_l_1391_ = lean_ctor_get(v_x_1386_, 3);
if (lean_obj_tag(v_l_1391_) == 0)
{
lean_object* v_size_1392_; lean_object* v_k_1393_; lean_object* v_v_1394_; lean_object* v_r_1395_; lean_object* v_size_1396_; lean_object* v_k_1397_; lean_object* v_v_1398_; lean_object* v_l_1399_; lean_object* v_r_1400_; lean_object* v___x_1401_; 
lean_inc_ref(v_l_1391_);
lean_dec(v_h__2_1389_);
v_size_1392_ = lean_ctor_get(v_x_1386_, 0);
lean_inc(v_size_1392_);
v_k_1393_ = lean_ctor_get(v_x_1386_, 1);
lean_inc(v_k_1393_);
v_v_1394_ = lean_ctor_get(v_x_1386_, 2);
lean_inc(v_v_1394_);
v_r_1395_ = lean_ctor_get(v_x_1386_, 4);
lean_inc(v_r_1395_);
lean_dec_ref_known(v_x_1386_, 5);
v_size_1396_ = lean_ctor_get(v_l_1391_, 0);
lean_inc(v_size_1396_);
v_k_1397_ = lean_ctor_get(v_l_1391_, 1);
lean_inc(v_k_1397_);
v_v_1398_ = lean_ctor_get(v_l_1391_, 2);
lean_inc(v_v_1398_);
v_l_1399_ = lean_ctor_get(v_l_1391_, 3);
lean_inc(v_l_1399_);
v_r_1400_ = lean_ctor_get(v_l_1391_, 4);
lean_inc(v_r_1400_);
lean_dec_ref_known(v_l_1391_, 5);
v___x_1401_ = lean_apply_10(v_h__3_1390_, v_size_1392_, v_k_1393_, v_v_1394_, v_size_1396_, v_k_1397_, v_v_1398_, v_l_1399_, v_r_1400_, v_r_1395_, v_x_1387_);
return v___x_1401_;
}
else
{
lean_object* v_size_1402_; lean_object* v_k_1403_; lean_object* v_v_1404_; lean_object* v_r_1405_; lean_object* v___x_1406_; 
lean_dec(v_h__3_1390_);
v_size_1402_ = lean_ctor_get(v_x_1386_, 0);
lean_inc(v_size_1402_);
v_k_1403_ = lean_ctor_get(v_x_1386_, 1);
lean_inc(v_k_1403_);
v_v_1404_ = lean_ctor_get(v_x_1386_, 2);
lean_inc(v_v_1404_);
v_r_1405_ = lean_ctor_get(v_x_1386_, 4);
lean_inc(v_r_1405_);
lean_dec_ref_known(v_x_1386_, 5);
v___x_1406_ = lean_apply_5(v_h__2_1389_, v_size_1402_, v_k_1403_, v_v_1404_, v_r_1405_, v_x_1387_);
return v___x_1406_;
}
}
else
{
lean_object* v___x_1407_; 
lean_dec(v_h__3_1390_);
lean_dec(v_h__2_1389_);
v___x_1407_ = lean_apply_1(v_h__1_1388_, v_x_1387_);
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* v_00_u03b1_1408_, lean_object* v_00_u03b2_1409_, lean_object* v_motive_1410_, lean_object* v_x_1411_, lean_object* v_x_1412_, lean_object* v_h__1_1413_, lean_object* v_h__2_1414_, lean_object* v_h__3_1415_){
_start:
{
if (lean_obj_tag(v_x_1411_) == 0)
{
lean_object* v_l_1416_; 
lean_dec(v_h__1_1413_);
v_l_1416_ = lean_ctor_get(v_x_1411_, 3);
if (lean_obj_tag(v_l_1416_) == 0)
{
lean_object* v_size_1417_; lean_object* v_k_1418_; lean_object* v_v_1419_; lean_object* v_r_1420_; lean_object* v_size_1421_; lean_object* v_k_1422_; lean_object* v_v_1423_; lean_object* v_l_1424_; lean_object* v_r_1425_; lean_object* v___x_1426_; 
lean_inc_ref(v_l_1416_);
lean_dec(v_h__2_1414_);
v_size_1417_ = lean_ctor_get(v_x_1411_, 0);
lean_inc(v_size_1417_);
v_k_1418_ = lean_ctor_get(v_x_1411_, 1);
lean_inc(v_k_1418_);
v_v_1419_ = lean_ctor_get(v_x_1411_, 2);
lean_inc(v_v_1419_);
v_r_1420_ = lean_ctor_get(v_x_1411_, 4);
lean_inc(v_r_1420_);
lean_dec_ref_known(v_x_1411_, 5);
v_size_1421_ = lean_ctor_get(v_l_1416_, 0);
lean_inc(v_size_1421_);
v_k_1422_ = lean_ctor_get(v_l_1416_, 1);
lean_inc(v_k_1422_);
v_v_1423_ = lean_ctor_get(v_l_1416_, 2);
lean_inc(v_v_1423_);
v_l_1424_ = lean_ctor_get(v_l_1416_, 3);
lean_inc(v_l_1424_);
v_r_1425_ = lean_ctor_get(v_l_1416_, 4);
lean_inc(v_r_1425_);
lean_dec_ref_known(v_l_1416_, 5);
v___x_1426_ = lean_apply_10(v_h__3_1415_, v_size_1417_, v_k_1418_, v_v_1419_, v_size_1421_, v_k_1422_, v_v_1423_, v_l_1424_, v_r_1425_, v_r_1420_, v_x_1412_);
return v___x_1426_;
}
else
{
lean_object* v_size_1427_; lean_object* v_k_1428_; lean_object* v_v_1429_; lean_object* v_r_1430_; lean_object* v___x_1431_; 
lean_dec(v_h__3_1415_);
v_size_1427_ = lean_ctor_get(v_x_1411_, 0);
lean_inc(v_size_1427_);
v_k_1428_ = lean_ctor_get(v_x_1411_, 1);
lean_inc(v_k_1428_);
v_v_1429_ = lean_ctor_get(v_x_1411_, 2);
lean_inc(v_v_1429_);
v_r_1430_ = lean_ctor_get(v_x_1411_, 4);
lean_inc(v_r_1430_);
lean_dec_ref_known(v_x_1411_, 5);
v___x_1431_ = lean_apply_5(v_h__2_1414_, v_size_1427_, v_k_1428_, v_v_1429_, v_r_1430_, v_x_1412_);
return v___x_1431_;
}
}
else
{
lean_object* v___x_1432_; 
lean_dec(v_h__3_1415_);
lean_dec(v_h__2_1414_);
v___x_1432_ = lean_apply_1(v_h__1_1413_, v_x_1412_);
return v___x_1432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object* v_x_1433_, lean_object* v_x_1434_, lean_object* v_h__1_1435_, lean_object* v_h__2_1436_, lean_object* v_h__3_1437_){
_start:
{
if (lean_obj_tag(v_x_1433_) == 0)
{
lean_object* v_r_1438_; 
lean_dec(v_h__1_1435_);
v_r_1438_ = lean_ctor_get(v_x_1433_, 4);
if (lean_obj_tag(v_r_1438_) == 0)
{
lean_object* v_size_1439_; lean_object* v_k_1440_; lean_object* v_v_1441_; lean_object* v_l_1442_; lean_object* v_size_1443_; lean_object* v_k_1444_; lean_object* v_v_1445_; lean_object* v_l_1446_; lean_object* v_r_1447_; lean_object* v___x_1448_; 
lean_inc_ref(v_r_1438_);
lean_dec(v_h__2_1436_);
v_size_1439_ = lean_ctor_get(v_x_1433_, 0);
lean_inc(v_size_1439_);
v_k_1440_ = lean_ctor_get(v_x_1433_, 1);
lean_inc(v_k_1440_);
v_v_1441_ = lean_ctor_get(v_x_1433_, 2);
lean_inc(v_v_1441_);
v_l_1442_ = lean_ctor_get(v_x_1433_, 3);
lean_inc(v_l_1442_);
lean_dec_ref_known(v_x_1433_, 5);
v_size_1443_ = lean_ctor_get(v_r_1438_, 0);
lean_inc(v_size_1443_);
v_k_1444_ = lean_ctor_get(v_r_1438_, 1);
lean_inc(v_k_1444_);
v_v_1445_ = lean_ctor_get(v_r_1438_, 2);
lean_inc(v_v_1445_);
v_l_1446_ = lean_ctor_get(v_r_1438_, 3);
lean_inc(v_l_1446_);
v_r_1447_ = lean_ctor_get(v_r_1438_, 4);
lean_inc(v_r_1447_);
lean_dec_ref_known(v_r_1438_, 5);
v___x_1448_ = lean_apply_10(v_h__3_1437_, v_size_1439_, v_k_1440_, v_v_1441_, v_l_1442_, v_size_1443_, v_k_1444_, v_v_1445_, v_l_1446_, v_r_1447_, v_x_1434_);
return v___x_1448_;
}
else
{
lean_object* v_size_1449_; lean_object* v_k_1450_; lean_object* v_v_1451_; lean_object* v_l_1452_; lean_object* v___x_1453_; 
lean_dec(v_h__3_1437_);
v_size_1449_ = lean_ctor_get(v_x_1433_, 0);
lean_inc(v_size_1449_);
v_k_1450_ = lean_ctor_get(v_x_1433_, 1);
lean_inc(v_k_1450_);
v_v_1451_ = lean_ctor_get(v_x_1433_, 2);
lean_inc(v_v_1451_);
v_l_1452_ = lean_ctor_get(v_x_1433_, 3);
lean_inc(v_l_1452_);
lean_dec_ref_known(v_x_1433_, 5);
v___x_1453_ = lean_apply_5(v_h__2_1436_, v_size_1449_, v_k_1450_, v_v_1451_, v_l_1452_, v_x_1434_);
return v___x_1453_;
}
}
else
{
lean_object* v___x_1454_; 
lean_dec(v_h__3_1437_);
lean_dec(v_h__2_1436_);
v___x_1454_ = lean_apply_1(v_h__1_1435_, v_x_1434_);
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object* v_00_u03b1_1455_, lean_object* v_00_u03b2_1456_, lean_object* v_motive_1457_, lean_object* v_x_1458_, lean_object* v_x_1459_, lean_object* v_h__1_1460_, lean_object* v_h__2_1461_, lean_object* v_h__3_1462_){
_start:
{
if (lean_obj_tag(v_x_1458_) == 0)
{
lean_object* v_r_1463_; 
lean_dec(v_h__1_1460_);
v_r_1463_ = lean_ctor_get(v_x_1458_, 4);
if (lean_obj_tag(v_r_1463_) == 0)
{
lean_object* v_size_1464_; lean_object* v_k_1465_; lean_object* v_v_1466_; lean_object* v_l_1467_; lean_object* v_size_1468_; lean_object* v_k_1469_; lean_object* v_v_1470_; lean_object* v_l_1471_; lean_object* v_r_1472_; lean_object* v___x_1473_; 
lean_inc_ref(v_r_1463_);
lean_dec(v_h__2_1461_);
v_size_1464_ = lean_ctor_get(v_x_1458_, 0);
lean_inc(v_size_1464_);
v_k_1465_ = lean_ctor_get(v_x_1458_, 1);
lean_inc(v_k_1465_);
v_v_1466_ = lean_ctor_get(v_x_1458_, 2);
lean_inc(v_v_1466_);
v_l_1467_ = lean_ctor_get(v_x_1458_, 3);
lean_inc(v_l_1467_);
lean_dec_ref_known(v_x_1458_, 5);
v_size_1468_ = lean_ctor_get(v_r_1463_, 0);
lean_inc(v_size_1468_);
v_k_1469_ = lean_ctor_get(v_r_1463_, 1);
lean_inc(v_k_1469_);
v_v_1470_ = lean_ctor_get(v_r_1463_, 2);
lean_inc(v_v_1470_);
v_l_1471_ = lean_ctor_get(v_r_1463_, 3);
lean_inc(v_l_1471_);
v_r_1472_ = lean_ctor_get(v_r_1463_, 4);
lean_inc(v_r_1472_);
lean_dec_ref_known(v_r_1463_, 5);
v___x_1473_ = lean_apply_10(v_h__3_1462_, v_size_1464_, v_k_1465_, v_v_1466_, v_l_1467_, v_size_1468_, v_k_1469_, v_v_1470_, v_l_1471_, v_r_1472_, v_x_1459_);
return v___x_1473_;
}
else
{
lean_object* v_size_1474_; lean_object* v_k_1475_; lean_object* v_v_1476_; lean_object* v_l_1477_; lean_object* v___x_1478_; 
lean_dec(v_h__3_1462_);
v_size_1474_ = lean_ctor_get(v_x_1458_, 0);
lean_inc(v_size_1474_);
v_k_1475_ = lean_ctor_get(v_x_1458_, 1);
lean_inc(v_k_1475_);
v_v_1476_ = lean_ctor_get(v_x_1458_, 2);
lean_inc(v_v_1476_);
v_l_1477_ = lean_ctor_get(v_x_1458_, 3);
lean_inc(v_l_1477_);
lean_dec_ref_known(v_x_1458_, 5);
v___x_1478_ = lean_apply_5(v_h__2_1461_, v_size_1474_, v_k_1475_, v_v_1476_, v_l_1477_, v_x_1459_);
return v___x_1478_;
}
}
else
{
lean_object* v___x_1479_; 
lean_dec(v_h__3_1462_);
lean_dec(v_h__2_1461_);
v___x_1479_ = lean_apply_1(v_h__1_1460_, v_x_1459_);
return v___x_1479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1480_, lean_object* v_h__1_1481_, lean_object* v_h__2_1482_, lean_object* v_h__3_1483_){
_start:
{
if (lean_obj_tag(v_x_1480_) == 0)
{
lean_object* v_l_1484_; 
lean_dec(v_h__1_1481_);
v_l_1484_ = lean_ctor_get(v_x_1480_, 3);
if (lean_obj_tag(v_l_1484_) == 0)
{
lean_object* v_size_1485_; lean_object* v_k_1486_; lean_object* v_v_1487_; lean_object* v_r_1488_; lean_object* v_size_1489_; lean_object* v_k_1490_; lean_object* v_v_1491_; lean_object* v_l_1492_; lean_object* v_r_1493_; lean_object* v___x_1494_; 
lean_inc_ref(v_l_1484_);
lean_dec(v_h__2_1482_);
v_size_1485_ = lean_ctor_get(v_x_1480_, 0);
lean_inc(v_size_1485_);
v_k_1486_ = lean_ctor_get(v_x_1480_, 1);
lean_inc(v_k_1486_);
v_v_1487_ = lean_ctor_get(v_x_1480_, 2);
lean_inc(v_v_1487_);
v_r_1488_ = lean_ctor_get(v_x_1480_, 4);
lean_inc(v_r_1488_);
lean_dec_ref_known(v_x_1480_, 5);
v_size_1489_ = lean_ctor_get(v_l_1484_, 0);
lean_inc(v_size_1489_);
v_k_1490_ = lean_ctor_get(v_l_1484_, 1);
lean_inc(v_k_1490_);
v_v_1491_ = lean_ctor_get(v_l_1484_, 2);
lean_inc(v_v_1491_);
v_l_1492_ = lean_ctor_get(v_l_1484_, 3);
lean_inc(v_l_1492_);
v_r_1493_ = lean_ctor_get(v_l_1484_, 4);
lean_inc(v_r_1493_);
lean_dec_ref_known(v_l_1484_, 5);
v___x_1494_ = lean_apply_9(v_h__3_1483_, v_size_1485_, v_k_1486_, v_v_1487_, v_size_1489_, v_k_1490_, v_v_1491_, v_l_1492_, v_r_1493_, v_r_1488_);
return v___x_1494_;
}
else
{
lean_object* v_size_1495_; lean_object* v_k_1496_; lean_object* v_v_1497_; lean_object* v_r_1498_; lean_object* v___x_1499_; 
lean_dec(v_h__3_1483_);
v_size_1495_ = lean_ctor_get(v_x_1480_, 0);
lean_inc(v_size_1495_);
v_k_1496_ = lean_ctor_get(v_x_1480_, 1);
lean_inc(v_k_1496_);
v_v_1497_ = lean_ctor_get(v_x_1480_, 2);
lean_inc(v_v_1497_);
v_r_1498_ = lean_ctor_get(v_x_1480_, 4);
lean_inc(v_r_1498_);
lean_dec_ref_known(v_x_1480_, 5);
v___x_1499_ = lean_apply_4(v_h__2_1482_, v_size_1495_, v_k_1496_, v_v_1497_, v_r_1498_);
return v___x_1499_;
}
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_dec(v_h__3_1483_);
lean_dec(v_h__2_1482_);
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_apply_1(v_h__1_1481_, v___x_1500_);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1502_, lean_object* v_00_u03b2_1503_, lean_object* v_motive_1504_, lean_object* v_x_1505_, lean_object* v_h__1_1506_, lean_object* v_h__2_1507_, lean_object* v_h__3_1508_){
_start:
{
if (lean_obj_tag(v_x_1505_) == 0)
{
lean_object* v_l_1509_; 
lean_dec(v_h__1_1506_);
v_l_1509_ = lean_ctor_get(v_x_1505_, 3);
if (lean_obj_tag(v_l_1509_) == 0)
{
lean_object* v_size_1510_; lean_object* v_k_1511_; lean_object* v_v_1512_; lean_object* v_r_1513_; lean_object* v_size_1514_; lean_object* v_k_1515_; lean_object* v_v_1516_; lean_object* v_l_1517_; lean_object* v_r_1518_; lean_object* v___x_1519_; 
lean_inc_ref(v_l_1509_);
lean_dec(v_h__2_1507_);
v_size_1510_ = lean_ctor_get(v_x_1505_, 0);
lean_inc(v_size_1510_);
v_k_1511_ = lean_ctor_get(v_x_1505_, 1);
lean_inc(v_k_1511_);
v_v_1512_ = lean_ctor_get(v_x_1505_, 2);
lean_inc(v_v_1512_);
v_r_1513_ = lean_ctor_get(v_x_1505_, 4);
lean_inc(v_r_1513_);
lean_dec_ref_known(v_x_1505_, 5);
v_size_1514_ = lean_ctor_get(v_l_1509_, 0);
lean_inc(v_size_1514_);
v_k_1515_ = lean_ctor_get(v_l_1509_, 1);
lean_inc(v_k_1515_);
v_v_1516_ = lean_ctor_get(v_l_1509_, 2);
lean_inc(v_v_1516_);
v_l_1517_ = lean_ctor_get(v_l_1509_, 3);
lean_inc(v_l_1517_);
v_r_1518_ = lean_ctor_get(v_l_1509_, 4);
lean_inc(v_r_1518_);
lean_dec_ref_known(v_l_1509_, 5);
v___x_1519_ = lean_apply_9(v_h__3_1508_, v_size_1510_, v_k_1511_, v_v_1512_, v_size_1514_, v_k_1515_, v_v_1516_, v_l_1517_, v_r_1518_, v_r_1513_);
return v___x_1519_;
}
else
{
lean_object* v_size_1520_; lean_object* v_k_1521_; lean_object* v_v_1522_; lean_object* v_r_1523_; lean_object* v___x_1524_; 
lean_dec(v_h__3_1508_);
v_size_1520_ = lean_ctor_get(v_x_1505_, 0);
lean_inc(v_size_1520_);
v_k_1521_ = lean_ctor_get(v_x_1505_, 1);
lean_inc(v_k_1521_);
v_v_1522_ = lean_ctor_get(v_x_1505_, 2);
lean_inc(v_v_1522_);
v_r_1523_ = lean_ctor_get(v_x_1505_, 4);
lean_inc(v_r_1523_);
lean_dec_ref_known(v_x_1505_, 5);
v___x_1524_ = lean_apply_4(v_h__2_1507_, v_size_1520_, v_k_1521_, v_v_1522_, v_r_1523_);
return v___x_1524_;
}
}
else
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec(v_h__3_1508_);
lean_dec(v_h__2_1507_);
v___x_1525_ = lean_box(0);
v___x_1526_ = lean_apply_1(v_h__1_1506_, v___x_1525_);
return v___x_1526_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object* v_x_1527_, lean_object* v_x_1528_, lean_object* v_h__1_1529_, lean_object* v_h__2_1530_, lean_object* v_h__3_1531_){
_start:
{
if (lean_obj_tag(v_x_1527_) == 0)
{
lean_object* v_l_1532_; 
lean_dec(v_h__1_1529_);
v_l_1532_ = lean_ctor_get(v_x_1527_, 3);
if (lean_obj_tag(v_l_1532_) == 0)
{
lean_object* v_size_1533_; lean_object* v_k_1534_; lean_object* v_v_1535_; lean_object* v_r_1536_; lean_object* v_size_1537_; lean_object* v_k_1538_; lean_object* v_v_1539_; lean_object* v_l_1540_; lean_object* v_r_1541_; lean_object* v___x_1542_; 
lean_inc_ref(v_l_1532_);
lean_dec(v_h__2_1530_);
v_size_1533_ = lean_ctor_get(v_x_1527_, 0);
lean_inc(v_size_1533_);
v_k_1534_ = lean_ctor_get(v_x_1527_, 1);
lean_inc(v_k_1534_);
v_v_1535_ = lean_ctor_get(v_x_1527_, 2);
lean_inc(v_v_1535_);
v_r_1536_ = lean_ctor_get(v_x_1527_, 4);
lean_inc(v_r_1536_);
lean_dec_ref_known(v_x_1527_, 5);
v_size_1537_ = lean_ctor_get(v_l_1532_, 0);
lean_inc(v_size_1537_);
v_k_1538_ = lean_ctor_get(v_l_1532_, 1);
lean_inc(v_k_1538_);
v_v_1539_ = lean_ctor_get(v_l_1532_, 2);
lean_inc(v_v_1539_);
v_l_1540_ = lean_ctor_get(v_l_1532_, 3);
lean_inc(v_l_1540_);
v_r_1541_ = lean_ctor_get(v_l_1532_, 4);
lean_inc(v_r_1541_);
lean_dec_ref_known(v_l_1532_, 5);
v___x_1542_ = lean_apply_10(v_h__3_1531_, v_size_1533_, v_k_1534_, v_v_1535_, v_size_1537_, v_k_1538_, v_v_1539_, v_l_1540_, v_r_1541_, v_r_1536_, v_x_1528_);
return v___x_1542_;
}
else
{
lean_object* v_size_1543_; lean_object* v_k_1544_; lean_object* v_v_1545_; lean_object* v_r_1546_; lean_object* v___x_1547_; 
lean_dec(v_h__3_1531_);
v_size_1543_ = lean_ctor_get(v_x_1527_, 0);
lean_inc(v_size_1543_);
v_k_1544_ = lean_ctor_get(v_x_1527_, 1);
lean_inc(v_k_1544_);
v_v_1545_ = lean_ctor_get(v_x_1527_, 2);
lean_inc(v_v_1545_);
v_r_1546_ = lean_ctor_get(v_x_1527_, 4);
lean_inc(v_r_1546_);
lean_dec_ref_known(v_x_1527_, 5);
v___x_1547_ = lean_apply_5(v_h__2_1530_, v_size_1543_, v_k_1544_, v_v_1545_, v_r_1546_, v_x_1528_);
return v___x_1547_;
}
}
else
{
lean_object* v___x_1548_; 
lean_dec(v_h__3_1531_);
lean_dec(v_h__2_1530_);
v___x_1548_ = lean_apply_1(v_h__1_1529_, v_x_1528_);
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1549_, lean_object* v_00_u03b2_1550_, lean_object* v_motive_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_, lean_object* v_h__1_1554_, lean_object* v_h__2_1555_, lean_object* v_h__3_1556_){
_start:
{
if (lean_obj_tag(v_x_1552_) == 0)
{
lean_object* v_l_1557_; 
lean_dec(v_h__1_1554_);
v_l_1557_ = lean_ctor_get(v_x_1552_, 3);
if (lean_obj_tag(v_l_1557_) == 0)
{
lean_object* v_size_1558_; lean_object* v_k_1559_; lean_object* v_v_1560_; lean_object* v_r_1561_; lean_object* v_size_1562_; lean_object* v_k_1563_; lean_object* v_v_1564_; lean_object* v_l_1565_; lean_object* v_r_1566_; lean_object* v___x_1567_; 
lean_inc_ref(v_l_1557_);
lean_dec(v_h__2_1555_);
v_size_1558_ = lean_ctor_get(v_x_1552_, 0);
lean_inc(v_size_1558_);
v_k_1559_ = lean_ctor_get(v_x_1552_, 1);
lean_inc(v_k_1559_);
v_v_1560_ = lean_ctor_get(v_x_1552_, 2);
lean_inc(v_v_1560_);
v_r_1561_ = lean_ctor_get(v_x_1552_, 4);
lean_inc(v_r_1561_);
lean_dec_ref_known(v_x_1552_, 5);
v_size_1562_ = lean_ctor_get(v_l_1557_, 0);
lean_inc(v_size_1562_);
v_k_1563_ = lean_ctor_get(v_l_1557_, 1);
lean_inc(v_k_1563_);
v_v_1564_ = lean_ctor_get(v_l_1557_, 2);
lean_inc(v_v_1564_);
v_l_1565_ = lean_ctor_get(v_l_1557_, 3);
lean_inc(v_l_1565_);
v_r_1566_ = lean_ctor_get(v_l_1557_, 4);
lean_inc(v_r_1566_);
lean_dec_ref_known(v_l_1557_, 5);
v___x_1567_ = lean_apply_10(v_h__3_1556_, v_size_1558_, v_k_1559_, v_v_1560_, v_size_1562_, v_k_1563_, v_v_1564_, v_l_1565_, v_r_1566_, v_r_1561_, v_x_1553_);
return v___x_1567_;
}
else
{
lean_object* v_size_1568_; lean_object* v_k_1569_; lean_object* v_v_1570_; lean_object* v_r_1571_; lean_object* v___x_1572_; 
lean_dec(v_h__3_1556_);
v_size_1568_ = lean_ctor_get(v_x_1552_, 0);
lean_inc(v_size_1568_);
v_k_1569_ = lean_ctor_get(v_x_1552_, 1);
lean_inc(v_k_1569_);
v_v_1570_ = lean_ctor_get(v_x_1552_, 2);
lean_inc(v_v_1570_);
v_r_1571_ = lean_ctor_get(v_x_1552_, 4);
lean_inc(v_r_1571_);
lean_dec_ref_known(v_x_1552_, 5);
v___x_1572_ = lean_apply_5(v_h__2_1555_, v_size_1568_, v_k_1569_, v_v_1570_, v_r_1571_, v_x_1553_);
return v___x_1572_;
}
}
else
{
lean_object* v___x_1573_; 
lean_dec(v_h__3_1556_);
lean_dec(v_h__2_1555_);
v___x_1573_ = lean_apply_1(v_h__1_1554_, v_x_1553_);
return v___x_1573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* v_x_1574_, lean_object* v_h__1_1575_, lean_object* v_h__2_1576_){
_start:
{
lean_object* v_l_1577_; 
v_l_1577_ = lean_ctor_get(v_x_1574_, 3);
if (lean_obj_tag(v_l_1577_) == 0)
{
lean_object* v_size_1578_; lean_object* v_k_1579_; lean_object* v_v_1580_; lean_object* v_r_1581_; lean_object* v_size_1582_; lean_object* v_k_1583_; lean_object* v_v_1584_; lean_object* v_l_1585_; lean_object* v_r_1586_; lean_object* v___x_1587_; 
lean_inc_ref(v_l_1577_);
lean_dec(v_h__1_1575_);
v_size_1578_ = lean_ctor_get(v_x_1574_, 0);
lean_inc(v_size_1578_);
v_k_1579_ = lean_ctor_get(v_x_1574_, 1);
lean_inc(v_k_1579_);
v_v_1580_ = lean_ctor_get(v_x_1574_, 2);
lean_inc(v_v_1580_);
v_r_1581_ = lean_ctor_get(v_x_1574_, 4);
lean_inc(v_r_1581_);
lean_dec(v_x_1574_);
v_size_1582_ = lean_ctor_get(v_l_1577_, 0);
lean_inc(v_size_1582_);
v_k_1583_ = lean_ctor_get(v_l_1577_, 1);
lean_inc(v_k_1583_);
v_v_1584_ = lean_ctor_get(v_l_1577_, 2);
lean_inc(v_v_1584_);
v_l_1585_ = lean_ctor_get(v_l_1577_, 3);
lean_inc(v_l_1585_);
v_r_1586_ = lean_ctor_get(v_l_1577_, 4);
lean_inc(v_r_1586_);
lean_dec_ref_known(v_l_1577_, 5);
v___x_1587_ = lean_apply_10(v_h__2_1576_, v_size_1578_, v_k_1579_, v_v_1580_, v_size_1582_, v_k_1583_, v_v_1584_, v_l_1585_, v_r_1586_, v_r_1581_, lean_box(0));
return v___x_1587_;
}
else
{
lean_object* v_size_1588_; lean_object* v_k_1589_; lean_object* v_v_1590_; lean_object* v_r_1591_; lean_object* v___x_1592_; 
lean_dec(v_h__2_1576_);
v_size_1588_ = lean_ctor_get(v_x_1574_, 0);
lean_inc(v_size_1588_);
v_k_1589_ = lean_ctor_get(v_x_1574_, 1);
lean_inc(v_k_1589_);
v_v_1590_ = lean_ctor_get(v_x_1574_, 2);
lean_inc(v_v_1590_);
v_r_1591_ = lean_ctor_get(v_x_1574_, 4);
lean_inc(v_r_1591_);
lean_dec(v_x_1574_);
v___x_1592_ = lean_apply_5(v_h__1_1575_, v_size_1588_, v_k_1589_, v_v_1590_, v_r_1591_, lean_box(0));
return v___x_1592_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* v_00_u03b1_1593_, lean_object* v_00_u03b2_1594_, lean_object* v_motive_1595_, lean_object* v_x_1596_, lean_object* v_x_1597_, lean_object* v_h__1_1598_, lean_object* v_h__2_1599_){
_start:
{
lean_object* v_l_1600_; 
v_l_1600_ = lean_ctor_get(v_x_1596_, 3);
if (lean_obj_tag(v_l_1600_) == 0)
{
lean_object* v_size_1601_; lean_object* v_k_1602_; lean_object* v_v_1603_; lean_object* v_r_1604_; lean_object* v_size_1605_; lean_object* v_k_1606_; lean_object* v_v_1607_; lean_object* v_l_1608_; lean_object* v_r_1609_; lean_object* v___x_1610_; 
lean_inc_ref(v_l_1600_);
lean_dec(v_h__1_1598_);
v_size_1601_ = lean_ctor_get(v_x_1596_, 0);
lean_inc(v_size_1601_);
v_k_1602_ = lean_ctor_get(v_x_1596_, 1);
lean_inc(v_k_1602_);
v_v_1603_ = lean_ctor_get(v_x_1596_, 2);
lean_inc(v_v_1603_);
v_r_1604_ = lean_ctor_get(v_x_1596_, 4);
lean_inc(v_r_1604_);
lean_dec(v_x_1596_);
v_size_1605_ = lean_ctor_get(v_l_1600_, 0);
lean_inc(v_size_1605_);
v_k_1606_ = lean_ctor_get(v_l_1600_, 1);
lean_inc(v_k_1606_);
v_v_1607_ = lean_ctor_get(v_l_1600_, 2);
lean_inc(v_v_1607_);
v_l_1608_ = lean_ctor_get(v_l_1600_, 3);
lean_inc(v_l_1608_);
v_r_1609_ = lean_ctor_get(v_l_1600_, 4);
lean_inc(v_r_1609_);
lean_dec_ref_known(v_l_1600_, 5);
v___x_1610_ = lean_apply_10(v_h__2_1599_, v_size_1601_, v_k_1602_, v_v_1603_, v_size_1605_, v_k_1606_, v_v_1607_, v_l_1608_, v_r_1609_, v_r_1604_, lean_box(0));
return v___x_1610_;
}
else
{
lean_object* v_size_1611_; lean_object* v_k_1612_; lean_object* v_v_1613_; lean_object* v_r_1614_; lean_object* v___x_1615_; 
lean_dec(v_h__2_1599_);
v_size_1611_ = lean_ctor_get(v_x_1596_, 0);
lean_inc(v_size_1611_);
v_k_1612_ = lean_ctor_get(v_x_1596_, 1);
lean_inc(v_k_1612_);
v_v_1613_ = lean_ctor_get(v_x_1596_, 2);
lean_inc(v_v_1613_);
v_r_1614_ = lean_ctor_get(v_x_1596_, 4);
lean_inc(v_r_1614_);
lean_dec(v_x_1596_);
v___x_1615_ = lean_apply_5(v_h__1_1598_, v_size_1611_, v_k_1612_, v_v_1613_, v_r_1614_, lean_box(0));
return v___x_1615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1616_, lean_object* v_h__1_1617_, lean_object* v_h__2_1618_, lean_object* v_h__3_1619_){
_start:
{
if (lean_obj_tag(v_x_1616_) == 0)
{
lean_object* v_r_1620_; 
lean_dec(v_h__1_1617_);
v_r_1620_ = lean_ctor_get(v_x_1616_, 4);
if (lean_obj_tag(v_r_1620_) == 0)
{
lean_object* v_size_1621_; lean_object* v_k_1622_; lean_object* v_v_1623_; lean_object* v_l_1624_; lean_object* v_size_1625_; lean_object* v_k_1626_; lean_object* v_v_1627_; lean_object* v_l_1628_; lean_object* v_r_1629_; lean_object* v___x_1630_; 
lean_inc_ref(v_r_1620_);
lean_dec(v_h__2_1618_);
v_size_1621_ = lean_ctor_get(v_x_1616_, 0);
lean_inc(v_size_1621_);
v_k_1622_ = lean_ctor_get(v_x_1616_, 1);
lean_inc(v_k_1622_);
v_v_1623_ = lean_ctor_get(v_x_1616_, 2);
lean_inc(v_v_1623_);
v_l_1624_ = lean_ctor_get(v_x_1616_, 3);
lean_inc(v_l_1624_);
lean_dec_ref_known(v_x_1616_, 5);
v_size_1625_ = lean_ctor_get(v_r_1620_, 0);
lean_inc(v_size_1625_);
v_k_1626_ = lean_ctor_get(v_r_1620_, 1);
lean_inc(v_k_1626_);
v_v_1627_ = lean_ctor_get(v_r_1620_, 2);
lean_inc(v_v_1627_);
v_l_1628_ = lean_ctor_get(v_r_1620_, 3);
lean_inc(v_l_1628_);
v_r_1629_ = lean_ctor_get(v_r_1620_, 4);
lean_inc(v_r_1629_);
lean_dec_ref_known(v_r_1620_, 5);
v___x_1630_ = lean_apply_9(v_h__3_1619_, v_size_1621_, v_k_1622_, v_v_1623_, v_l_1624_, v_size_1625_, v_k_1626_, v_v_1627_, v_l_1628_, v_r_1629_);
return v___x_1630_;
}
else
{
lean_object* v_size_1631_; lean_object* v_k_1632_; lean_object* v_v_1633_; lean_object* v_l_1634_; lean_object* v___x_1635_; 
lean_dec(v_h__3_1619_);
v_size_1631_ = lean_ctor_get(v_x_1616_, 0);
lean_inc(v_size_1631_);
v_k_1632_ = lean_ctor_get(v_x_1616_, 1);
lean_inc(v_k_1632_);
v_v_1633_ = lean_ctor_get(v_x_1616_, 2);
lean_inc(v_v_1633_);
v_l_1634_ = lean_ctor_get(v_x_1616_, 3);
lean_inc(v_l_1634_);
lean_dec_ref_known(v_x_1616_, 5);
v___x_1635_ = lean_apply_4(v_h__2_1618_, v_size_1631_, v_k_1632_, v_v_1633_, v_l_1634_);
return v___x_1635_;
}
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec(v_h__3_1619_);
lean_dec(v_h__2_1618_);
v___x_1636_ = lean_box(0);
v___x_1637_ = lean_apply_1(v_h__1_1617_, v___x_1636_);
return v___x_1637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1638_, lean_object* v_00_u03b2_1639_, lean_object* v_motive_1640_, lean_object* v_x_1641_, lean_object* v_h__1_1642_, lean_object* v_h__2_1643_, lean_object* v_h__3_1644_){
_start:
{
if (lean_obj_tag(v_x_1641_) == 0)
{
lean_object* v_r_1645_; 
lean_dec(v_h__1_1642_);
v_r_1645_ = lean_ctor_get(v_x_1641_, 4);
if (lean_obj_tag(v_r_1645_) == 0)
{
lean_object* v_size_1646_; lean_object* v_k_1647_; lean_object* v_v_1648_; lean_object* v_l_1649_; lean_object* v_size_1650_; lean_object* v_k_1651_; lean_object* v_v_1652_; lean_object* v_l_1653_; lean_object* v_r_1654_; lean_object* v___x_1655_; 
lean_inc_ref(v_r_1645_);
lean_dec(v_h__2_1643_);
v_size_1646_ = lean_ctor_get(v_x_1641_, 0);
lean_inc(v_size_1646_);
v_k_1647_ = lean_ctor_get(v_x_1641_, 1);
lean_inc(v_k_1647_);
v_v_1648_ = lean_ctor_get(v_x_1641_, 2);
lean_inc(v_v_1648_);
v_l_1649_ = lean_ctor_get(v_x_1641_, 3);
lean_inc(v_l_1649_);
lean_dec_ref_known(v_x_1641_, 5);
v_size_1650_ = lean_ctor_get(v_r_1645_, 0);
lean_inc(v_size_1650_);
v_k_1651_ = lean_ctor_get(v_r_1645_, 1);
lean_inc(v_k_1651_);
v_v_1652_ = lean_ctor_get(v_r_1645_, 2);
lean_inc(v_v_1652_);
v_l_1653_ = lean_ctor_get(v_r_1645_, 3);
lean_inc(v_l_1653_);
v_r_1654_ = lean_ctor_get(v_r_1645_, 4);
lean_inc(v_r_1654_);
lean_dec_ref_known(v_r_1645_, 5);
v___x_1655_ = lean_apply_9(v_h__3_1644_, v_size_1646_, v_k_1647_, v_v_1648_, v_l_1649_, v_size_1650_, v_k_1651_, v_v_1652_, v_l_1653_, v_r_1654_);
return v___x_1655_;
}
else
{
lean_object* v_size_1656_; lean_object* v_k_1657_; lean_object* v_v_1658_; lean_object* v_l_1659_; lean_object* v___x_1660_; 
lean_dec(v_h__3_1644_);
v_size_1656_ = lean_ctor_get(v_x_1641_, 0);
lean_inc(v_size_1656_);
v_k_1657_ = lean_ctor_get(v_x_1641_, 1);
lean_inc(v_k_1657_);
v_v_1658_ = lean_ctor_get(v_x_1641_, 2);
lean_inc(v_v_1658_);
v_l_1659_ = lean_ctor_get(v_x_1641_, 3);
lean_inc(v_l_1659_);
lean_dec_ref_known(v_x_1641_, 5);
v___x_1660_ = lean_apply_4(v_h__2_1643_, v_size_1656_, v_k_1657_, v_v_1658_, v_l_1659_);
return v___x_1660_;
}
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_dec(v_h__3_1644_);
lean_dec(v_h__2_1643_);
v___x_1661_ = lean_box(0);
v___x_1662_ = lean_apply_1(v_h__1_1642_, v___x_1661_);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1663_, lean_object* v_x_1664_, lean_object* v_h__1_1665_, lean_object* v_h__2_1666_, lean_object* v_h__3_1667_){
_start:
{
if (lean_obj_tag(v_x_1663_) == 0)
{
lean_object* v_r_1668_; 
lean_dec(v_h__1_1665_);
v_r_1668_ = lean_ctor_get(v_x_1663_, 4);
if (lean_obj_tag(v_r_1668_) == 0)
{
lean_object* v_size_1669_; lean_object* v_k_1670_; lean_object* v_v_1671_; lean_object* v_l_1672_; lean_object* v_size_1673_; lean_object* v_k_1674_; lean_object* v_v_1675_; lean_object* v_l_1676_; lean_object* v_r_1677_; lean_object* v___x_1678_; 
lean_inc_ref(v_r_1668_);
lean_dec(v_h__2_1666_);
v_size_1669_ = lean_ctor_get(v_x_1663_, 0);
lean_inc(v_size_1669_);
v_k_1670_ = lean_ctor_get(v_x_1663_, 1);
lean_inc(v_k_1670_);
v_v_1671_ = lean_ctor_get(v_x_1663_, 2);
lean_inc(v_v_1671_);
v_l_1672_ = lean_ctor_get(v_x_1663_, 3);
lean_inc(v_l_1672_);
lean_dec_ref_known(v_x_1663_, 5);
v_size_1673_ = lean_ctor_get(v_r_1668_, 0);
lean_inc(v_size_1673_);
v_k_1674_ = lean_ctor_get(v_r_1668_, 1);
lean_inc(v_k_1674_);
v_v_1675_ = lean_ctor_get(v_r_1668_, 2);
lean_inc(v_v_1675_);
v_l_1676_ = lean_ctor_get(v_r_1668_, 3);
lean_inc(v_l_1676_);
v_r_1677_ = lean_ctor_get(v_r_1668_, 4);
lean_inc(v_r_1677_);
lean_dec_ref_known(v_r_1668_, 5);
v___x_1678_ = lean_apply_10(v_h__3_1667_, v_size_1669_, v_k_1670_, v_v_1671_, v_l_1672_, v_size_1673_, v_k_1674_, v_v_1675_, v_l_1676_, v_r_1677_, v_x_1664_);
return v___x_1678_;
}
else
{
lean_object* v_size_1679_; lean_object* v_k_1680_; lean_object* v_v_1681_; lean_object* v_l_1682_; lean_object* v___x_1683_; 
lean_dec(v_h__3_1667_);
v_size_1679_ = lean_ctor_get(v_x_1663_, 0);
lean_inc(v_size_1679_);
v_k_1680_ = lean_ctor_get(v_x_1663_, 1);
lean_inc(v_k_1680_);
v_v_1681_ = lean_ctor_get(v_x_1663_, 2);
lean_inc(v_v_1681_);
v_l_1682_ = lean_ctor_get(v_x_1663_, 3);
lean_inc(v_l_1682_);
lean_dec_ref_known(v_x_1663_, 5);
v___x_1683_ = lean_apply_5(v_h__2_1666_, v_size_1679_, v_k_1680_, v_v_1681_, v_l_1682_, v_x_1664_);
return v___x_1683_;
}
}
else
{
lean_object* v___x_1684_; 
lean_dec(v_h__3_1667_);
lean_dec(v_h__2_1666_);
v___x_1684_ = lean_apply_1(v_h__1_1665_, v_x_1664_);
return v___x_1684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1685_, lean_object* v_00_u03b2_1686_, lean_object* v_motive_1687_, lean_object* v_x_1688_, lean_object* v_x_1689_, lean_object* v_h__1_1690_, lean_object* v_h__2_1691_, lean_object* v_h__3_1692_){
_start:
{
if (lean_obj_tag(v_x_1688_) == 0)
{
lean_object* v_r_1693_; 
lean_dec(v_h__1_1690_);
v_r_1693_ = lean_ctor_get(v_x_1688_, 4);
if (lean_obj_tag(v_r_1693_) == 0)
{
lean_object* v_size_1694_; lean_object* v_k_1695_; lean_object* v_v_1696_; lean_object* v_l_1697_; lean_object* v_size_1698_; lean_object* v_k_1699_; lean_object* v_v_1700_; lean_object* v_l_1701_; lean_object* v_r_1702_; lean_object* v___x_1703_; 
lean_inc_ref(v_r_1693_);
lean_dec(v_h__2_1691_);
v_size_1694_ = lean_ctor_get(v_x_1688_, 0);
lean_inc(v_size_1694_);
v_k_1695_ = lean_ctor_get(v_x_1688_, 1);
lean_inc(v_k_1695_);
v_v_1696_ = lean_ctor_get(v_x_1688_, 2);
lean_inc(v_v_1696_);
v_l_1697_ = lean_ctor_get(v_x_1688_, 3);
lean_inc(v_l_1697_);
lean_dec_ref_known(v_x_1688_, 5);
v_size_1698_ = lean_ctor_get(v_r_1693_, 0);
lean_inc(v_size_1698_);
v_k_1699_ = lean_ctor_get(v_r_1693_, 1);
lean_inc(v_k_1699_);
v_v_1700_ = lean_ctor_get(v_r_1693_, 2);
lean_inc(v_v_1700_);
v_l_1701_ = lean_ctor_get(v_r_1693_, 3);
lean_inc(v_l_1701_);
v_r_1702_ = lean_ctor_get(v_r_1693_, 4);
lean_inc(v_r_1702_);
lean_dec_ref_known(v_r_1693_, 5);
v___x_1703_ = lean_apply_10(v_h__3_1692_, v_size_1694_, v_k_1695_, v_v_1696_, v_l_1697_, v_size_1698_, v_k_1699_, v_v_1700_, v_l_1701_, v_r_1702_, v_x_1689_);
return v___x_1703_;
}
else
{
lean_object* v_size_1704_; lean_object* v_k_1705_; lean_object* v_v_1706_; lean_object* v_l_1707_; lean_object* v___x_1708_; 
lean_dec(v_h__3_1692_);
v_size_1704_ = lean_ctor_get(v_x_1688_, 0);
lean_inc(v_size_1704_);
v_k_1705_ = lean_ctor_get(v_x_1688_, 1);
lean_inc(v_k_1705_);
v_v_1706_ = lean_ctor_get(v_x_1688_, 2);
lean_inc(v_v_1706_);
v_l_1707_ = lean_ctor_get(v_x_1688_, 3);
lean_inc(v_l_1707_);
lean_dec_ref_known(v_x_1688_, 5);
v___x_1708_ = lean_apply_5(v_h__2_1691_, v_size_1704_, v_k_1705_, v_v_1706_, v_l_1707_, v_x_1689_);
return v___x_1708_;
}
}
else
{
lean_object* v___x_1709_; 
lean_dec(v_h__3_1692_);
lean_dec(v_h__2_1691_);
v___x_1709_ = lean_apply_1(v_h__1_1690_, v_x_1689_);
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* v_x_1710_, lean_object* v_h__1_1711_, lean_object* v_h__2_1712_){
_start:
{
lean_object* v_r_1713_; 
v_r_1713_ = lean_ctor_get(v_x_1710_, 4);
if (lean_obj_tag(v_r_1713_) == 0)
{
lean_object* v_size_1714_; lean_object* v_k_1715_; lean_object* v_v_1716_; lean_object* v_l_1717_; lean_object* v_size_1718_; lean_object* v_k_1719_; lean_object* v_v_1720_; lean_object* v_l_1721_; lean_object* v_r_1722_; lean_object* v___x_1723_; 
lean_inc_ref(v_r_1713_);
lean_dec(v_h__1_1711_);
v_size_1714_ = lean_ctor_get(v_x_1710_, 0);
lean_inc(v_size_1714_);
v_k_1715_ = lean_ctor_get(v_x_1710_, 1);
lean_inc(v_k_1715_);
v_v_1716_ = lean_ctor_get(v_x_1710_, 2);
lean_inc(v_v_1716_);
v_l_1717_ = lean_ctor_get(v_x_1710_, 3);
lean_inc(v_l_1717_);
lean_dec(v_x_1710_);
v_size_1718_ = lean_ctor_get(v_r_1713_, 0);
lean_inc(v_size_1718_);
v_k_1719_ = lean_ctor_get(v_r_1713_, 1);
lean_inc(v_k_1719_);
v_v_1720_ = lean_ctor_get(v_r_1713_, 2);
lean_inc(v_v_1720_);
v_l_1721_ = lean_ctor_get(v_r_1713_, 3);
lean_inc(v_l_1721_);
v_r_1722_ = lean_ctor_get(v_r_1713_, 4);
lean_inc(v_r_1722_);
lean_dec_ref_known(v_r_1713_, 5);
v___x_1723_ = lean_apply_10(v_h__2_1712_, v_size_1714_, v_k_1715_, v_v_1716_, v_l_1717_, v_size_1718_, v_k_1719_, v_v_1720_, v_l_1721_, v_r_1722_, lean_box(0));
return v___x_1723_;
}
else
{
lean_object* v_size_1724_; lean_object* v_k_1725_; lean_object* v_v_1726_; lean_object* v_l_1727_; lean_object* v___x_1728_; 
lean_dec(v_h__2_1712_);
v_size_1724_ = lean_ctor_get(v_x_1710_, 0);
lean_inc(v_size_1724_);
v_k_1725_ = lean_ctor_get(v_x_1710_, 1);
lean_inc(v_k_1725_);
v_v_1726_ = lean_ctor_get(v_x_1710_, 2);
lean_inc(v_v_1726_);
v_l_1727_ = lean_ctor_get(v_x_1710_, 3);
lean_inc(v_l_1727_);
lean_dec(v_x_1710_);
v___x_1728_ = lean_apply_5(v_h__1_1711_, v_size_1724_, v_k_1725_, v_v_1726_, v_l_1727_, lean_box(0));
return v___x_1728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1729_, lean_object* v_00_u03b2_1730_, lean_object* v_motive_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_, lean_object* v_h__1_1734_, lean_object* v_h__2_1735_){
_start:
{
lean_object* v_r_1736_; 
v_r_1736_ = lean_ctor_get(v_x_1732_, 4);
if (lean_obj_tag(v_r_1736_) == 0)
{
lean_object* v_size_1737_; lean_object* v_k_1738_; lean_object* v_v_1739_; lean_object* v_l_1740_; lean_object* v_size_1741_; lean_object* v_k_1742_; lean_object* v_v_1743_; lean_object* v_l_1744_; lean_object* v_r_1745_; lean_object* v___x_1746_; 
lean_inc_ref(v_r_1736_);
lean_dec(v_h__1_1734_);
v_size_1737_ = lean_ctor_get(v_x_1732_, 0);
lean_inc(v_size_1737_);
v_k_1738_ = lean_ctor_get(v_x_1732_, 1);
lean_inc(v_k_1738_);
v_v_1739_ = lean_ctor_get(v_x_1732_, 2);
lean_inc(v_v_1739_);
v_l_1740_ = lean_ctor_get(v_x_1732_, 3);
lean_inc(v_l_1740_);
lean_dec(v_x_1732_);
v_size_1741_ = lean_ctor_get(v_r_1736_, 0);
lean_inc(v_size_1741_);
v_k_1742_ = lean_ctor_get(v_r_1736_, 1);
lean_inc(v_k_1742_);
v_v_1743_ = lean_ctor_get(v_r_1736_, 2);
lean_inc(v_v_1743_);
v_l_1744_ = lean_ctor_get(v_r_1736_, 3);
lean_inc(v_l_1744_);
v_r_1745_ = lean_ctor_get(v_r_1736_, 4);
lean_inc(v_r_1745_);
lean_dec_ref_known(v_r_1736_, 5);
v___x_1746_ = lean_apply_10(v_h__2_1735_, v_size_1737_, v_k_1738_, v_v_1739_, v_l_1740_, v_size_1741_, v_k_1742_, v_v_1743_, v_l_1744_, v_r_1745_, lean_box(0));
return v___x_1746_;
}
else
{
lean_object* v_size_1747_; lean_object* v_k_1748_; lean_object* v_v_1749_; lean_object* v_l_1750_; lean_object* v___x_1751_; 
lean_dec(v_h__2_1735_);
v_size_1747_ = lean_ctor_get(v_x_1732_, 0);
lean_inc(v_size_1747_);
v_k_1748_ = lean_ctor_get(v_x_1732_, 1);
lean_inc(v_k_1748_);
v_v_1749_ = lean_ctor_get(v_x_1732_, 2);
lean_inc(v_v_1749_);
v_l_1750_ = lean_ctor_get(v_x_1732_, 3);
lean_inc(v_l_1750_);
lean_dec(v_x_1732_);
v___x_1751_ = lean_apply_5(v_h__1_1734_, v_size_1747_, v_k_1748_, v_v_1749_, v_l_1750_, lean_box(0));
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object* v_l_1752_, lean_object* v_h__1_1753_, lean_object* v_h__2_1754_){
_start:
{
if (lean_obj_tag(v_l_1752_) == 0)
{
lean_object* v_size_1755_; lean_object* v_k_1756_; lean_object* v_v_1757_; lean_object* v_l_1758_; lean_object* v_r_1759_; lean_object* v___x_1760_; 
lean_dec(v_h__1_1753_);
v_size_1755_ = lean_ctor_get(v_l_1752_, 0);
lean_inc(v_size_1755_);
v_k_1756_ = lean_ctor_get(v_l_1752_, 1);
lean_inc(v_k_1756_);
v_v_1757_ = lean_ctor_get(v_l_1752_, 2);
lean_inc(v_v_1757_);
v_l_1758_ = lean_ctor_get(v_l_1752_, 3);
lean_inc(v_l_1758_);
v_r_1759_ = lean_ctor_get(v_l_1752_, 4);
lean_inc(v_r_1759_);
lean_dec_ref_known(v_l_1752_, 5);
v___x_1760_ = lean_apply_7(v_h__2_1754_, v_size_1755_, v_k_1756_, v_v_1757_, v_l_1758_, v_r_1759_, lean_box(0), lean_box(0));
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; 
lean_dec(v_h__2_1754_);
v___x_1761_ = lean_apply_2(v_h__1_1753_, lean_box(0), lean_box(0));
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object* v_00_u03b1_1762_, lean_object* v_00_u03b2_1763_, lean_object* v_r_1764_, lean_object* v_motive_1765_, lean_object* v_l_1766_, lean_object* v_hl_1767_, lean_object* v_hlr_1768_, lean_object* v_h__1_1769_, lean_object* v_h__2_1770_){
_start:
{
if (lean_obj_tag(v_l_1766_) == 0)
{
lean_object* v_size_1771_; lean_object* v_k_1772_; lean_object* v_v_1773_; lean_object* v_l_1774_; lean_object* v_r_1775_; lean_object* v___x_1776_; 
lean_dec(v_h__1_1769_);
v_size_1771_ = lean_ctor_get(v_l_1766_, 0);
lean_inc(v_size_1771_);
v_k_1772_ = lean_ctor_get(v_l_1766_, 1);
lean_inc(v_k_1772_);
v_v_1773_ = lean_ctor_get(v_l_1766_, 2);
lean_inc(v_v_1773_);
v_l_1774_ = lean_ctor_get(v_l_1766_, 3);
lean_inc(v_l_1774_);
v_r_1775_ = lean_ctor_get(v_l_1766_, 4);
lean_inc(v_r_1775_);
lean_dec_ref_known(v_l_1766_, 5);
v___x_1776_ = lean_apply_7(v_h__2_1770_, v_size_1771_, v_k_1772_, v_v_1773_, v_l_1774_, v_r_1775_, lean_box(0), lean_box(0));
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; 
lean_dec(v_h__2_1770_);
v___x_1777_ = lean_apply_2(v_h__1_1769_, lean_box(0), lean_box(0));
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object* v_00_u03b1_1778_, lean_object* v_00_u03b2_1779_, lean_object* v_r_1780_, lean_object* v_motive_1781_, lean_object* v_l_1782_, lean_object* v_hl_1783_, lean_object* v_hlr_1784_, lean_object* v_h__1_1785_, lean_object* v_h__2_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(v_00_u03b1_1778_, v_00_u03b2_1779_, v_r_1780_, v_motive_1781_, v_l_1782_, v_hl_1783_, v_hlr_1784_, v_h__1_1785_, v_h__2_1786_);
lean_dec(v_r_1780_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(lean_object* v_x_1788_, lean_object* v_h__1_1789_){
_start:
{
lean_object* v_k_1790_; lean_object* v_v_1791_; lean_object* v_tree_1792_; lean_object* v___x_1793_; 
v_k_1790_ = lean_ctor_get(v_x_1788_, 0);
lean_inc(v_k_1790_);
v_v_1791_ = lean_ctor_get(v_x_1788_, 1);
lean_inc(v_v_1791_);
v_tree_1792_ = lean_ctor_get(v_x_1788_, 2);
lean_inc(v_tree_1792_);
lean_dec_ref(v_x_1788_);
v___x_1793_ = lean_apply_5(v_h__1_1789_, v_k_1790_, v_v_1791_, v_tree_1792_, lean_box(0), lean_box(0));
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object* v_00_u03b1_1794_, lean_object* v_00_u03b2_1795_, lean_object* v_l_x27_1796_, lean_object* v_r_x27_1797_, lean_object* v_motive_1798_, lean_object* v_x_1799_, lean_object* v_h__1_1800_){
_start:
{
lean_object* v_k_1801_; lean_object* v_v_1802_; lean_object* v_tree_1803_; lean_object* v___x_1804_; 
v_k_1801_ = lean_ctor_get(v_x_1799_, 0);
lean_inc(v_k_1801_);
v_v_1802_ = lean_ctor_get(v_x_1799_, 1);
lean_inc(v_v_1802_);
v_tree_1803_ = lean_ctor_get(v_x_1799_, 2);
lean_inc(v_tree_1803_);
lean_dec_ref(v_x_1799_);
v___x_1804_ = lean_apply_5(v_h__1_1800_, v_k_1801_, v_v_1802_, v_tree_1803_, lean_box(0), lean_box(0));
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object* v_00_u03b1_1805_, lean_object* v_00_u03b2_1806_, lean_object* v_l_x27_1807_, lean_object* v_r_x27_1808_, lean_object* v_motive_1809_, lean_object* v_x_1810_, lean_object* v_h__1_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(v_00_u03b1_1805_, v_00_u03b2_1806_, v_l_x27_1807_, v_r_x27_1808_, v_motive_1809_, v_x_1810_, v_h__1_1811_);
lean_dec(v_r_x27_1808_);
lean_dec(v_l_x27_1807_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object* v_l_1813_, lean_object* v_h__1_1814_, lean_object* v_h__2_1815_){
_start:
{
if (lean_obj_tag(v_l_1813_) == 0)
{
lean_object* v_size_1816_; lean_object* v_k_1817_; lean_object* v_v_1818_; lean_object* v_l_1819_; lean_object* v_r_1820_; lean_object* v___x_1821_; 
lean_dec(v_h__1_1814_);
v_size_1816_ = lean_ctor_get(v_l_1813_, 0);
lean_inc(v_size_1816_);
v_k_1817_ = lean_ctor_get(v_l_1813_, 1);
lean_inc(v_k_1817_);
v_v_1818_ = lean_ctor_get(v_l_1813_, 2);
lean_inc(v_v_1818_);
v_l_1819_ = lean_ctor_get(v_l_1813_, 3);
lean_inc(v_l_1819_);
v_r_1820_ = lean_ctor_get(v_l_1813_, 4);
lean_inc(v_r_1820_);
lean_dec_ref_known(v_l_1813_, 5);
v___x_1821_ = lean_apply_5(v_h__2_1815_, v_size_1816_, v_k_1817_, v_v_1818_, v_l_1819_, v_r_1820_);
return v___x_1821_;
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec(v_h__2_1815_);
v___x_1822_ = lean_box(0);
v___x_1823_ = lean_apply_1(v_h__1_1814_, v___x_1822_);
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object* v_00_u03b1_1824_, lean_object* v_00_u03b2_1825_, lean_object* v_motive_1826_, lean_object* v_l_1827_, lean_object* v_h__1_1828_, lean_object* v_h__2_1829_){
_start:
{
if (lean_obj_tag(v_l_1827_) == 0)
{
lean_object* v_size_1830_; lean_object* v_k_1831_; lean_object* v_v_1832_; lean_object* v_l_1833_; lean_object* v_r_1834_; lean_object* v___x_1835_; 
lean_dec(v_h__1_1828_);
v_size_1830_ = lean_ctor_get(v_l_1827_, 0);
lean_inc(v_size_1830_);
v_k_1831_ = lean_ctor_get(v_l_1827_, 1);
lean_inc(v_k_1831_);
v_v_1832_ = lean_ctor_get(v_l_1827_, 2);
lean_inc(v_v_1832_);
v_l_1833_ = lean_ctor_get(v_l_1827_, 3);
lean_inc(v_l_1833_);
v_r_1834_ = lean_ctor_get(v_l_1827_, 4);
lean_inc(v_r_1834_);
lean_dec_ref_known(v_l_1827_, 5);
v___x_1835_ = lean_apply_5(v_h__2_1829_, v_size_1830_, v_k_1831_, v_v_1832_, v_l_1833_, v_r_1834_);
return v___x_1835_;
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_dec(v_h__2_1829_);
v___x_1836_ = lean_box(0);
v___x_1837_ = lean_apply_1(v_h__1_1828_, v___x_1836_);
return v___x_1837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(lean_object* v_r_1838_, lean_object* v_h__1_1839_, lean_object* v_h__2_1840_){
_start:
{
if (lean_obj_tag(v_r_1838_) == 0)
{
lean_object* v_size_1841_; lean_object* v_k_1842_; lean_object* v_v_1843_; lean_object* v_l_1844_; lean_object* v_r_1845_; lean_object* v___x_1846_; 
lean_dec(v_h__1_1839_);
v_size_1841_ = lean_ctor_get(v_r_1838_, 0);
lean_inc(v_size_1841_);
v_k_1842_ = lean_ctor_get(v_r_1838_, 1);
lean_inc(v_k_1842_);
v_v_1843_ = lean_ctor_get(v_r_1838_, 2);
lean_inc(v_v_1843_);
v_l_1844_ = lean_ctor_get(v_r_1838_, 3);
lean_inc(v_l_1844_);
v_r_1845_ = lean_ctor_get(v_r_1838_, 4);
lean_inc(v_r_1845_);
lean_dec_ref_known(v_r_1838_, 5);
v___x_1846_ = lean_apply_7(v_h__2_1840_, v_size_1841_, v_k_1842_, v_v_1843_, v_l_1844_, v_r_1845_, lean_box(0), lean_box(0));
return v___x_1846_;
}
else
{
lean_object* v___x_1847_; 
lean_dec(v_h__2_1840_);
v___x_1847_ = lean_apply_2(v_h__1_1839_, lean_box(0), lean_box(0));
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object* v_00_u03b1_1848_, lean_object* v_00_u03b2_1849_, lean_object* v_l_1850_, lean_object* v_motive_1851_, lean_object* v_r_1852_, lean_object* v_hr_1853_, lean_object* v_hlr_1854_, lean_object* v_h__1_1855_, lean_object* v_h__2_1856_){
_start:
{
if (lean_obj_tag(v_r_1852_) == 0)
{
lean_object* v_size_1857_; lean_object* v_k_1858_; lean_object* v_v_1859_; lean_object* v_l_1860_; lean_object* v_r_1861_; lean_object* v___x_1862_; 
lean_dec(v_h__1_1855_);
v_size_1857_ = lean_ctor_get(v_r_1852_, 0);
lean_inc(v_size_1857_);
v_k_1858_ = lean_ctor_get(v_r_1852_, 1);
lean_inc(v_k_1858_);
v_v_1859_ = lean_ctor_get(v_r_1852_, 2);
lean_inc(v_v_1859_);
v_l_1860_ = lean_ctor_get(v_r_1852_, 3);
lean_inc(v_l_1860_);
v_r_1861_ = lean_ctor_get(v_r_1852_, 4);
lean_inc(v_r_1861_);
lean_dec_ref_known(v_r_1852_, 5);
v___x_1862_ = lean_apply_7(v_h__2_1856_, v_size_1857_, v_k_1858_, v_v_1859_, v_l_1860_, v_r_1861_, lean_box(0), lean_box(0));
return v___x_1862_;
}
else
{
lean_object* v___x_1863_; 
lean_dec(v_h__2_1856_);
v___x_1863_ = lean_apply_2(v_h__1_1855_, lean_box(0), lean_box(0));
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object* v_00_u03b1_1864_, lean_object* v_00_u03b2_1865_, lean_object* v_l_1866_, lean_object* v_motive_1867_, lean_object* v_r_1868_, lean_object* v_hr_1869_, lean_object* v_hlr_1870_, lean_object* v_h__1_1871_, lean_object* v_h__2_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(v_00_u03b1_1864_, v_00_u03b2_1865_, v_l_1866_, v_motive_1867_, v_r_1868_, v_hr_1869_, v_hlr_1870_, v_h__1_1871_, v_h__2_1872_);
lean_dec(v_l_1866_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(lean_object* v_r_1874_, lean_object* v_h__1_1875_, lean_object* v_h__2_1876_){
_start:
{
if (lean_obj_tag(v_r_1874_) == 0)
{
lean_object* v_size_1877_; lean_object* v_k_1878_; lean_object* v_v_1879_; lean_object* v_l_1880_; lean_object* v_r_1881_; lean_object* v___x_1882_; 
lean_dec(v_h__1_1875_);
v_size_1877_ = lean_ctor_get(v_r_1874_, 0);
lean_inc(v_size_1877_);
v_k_1878_ = lean_ctor_get(v_r_1874_, 1);
lean_inc(v_k_1878_);
v_v_1879_ = lean_ctor_get(v_r_1874_, 2);
lean_inc(v_v_1879_);
v_l_1880_ = lean_ctor_get(v_r_1874_, 3);
lean_inc(v_l_1880_);
v_r_1881_ = lean_ctor_get(v_r_1874_, 4);
lean_inc(v_r_1881_);
lean_dec_ref_known(v_r_1874_, 5);
v___x_1882_ = lean_apply_7(v_h__2_1876_, v_size_1877_, v_k_1878_, v_v_1879_, v_l_1880_, v_r_1881_, lean_box(0), lean_box(0));
return v___x_1882_;
}
else
{
lean_object* v___x_1883_; 
lean_dec(v_h__2_1876_);
v___x_1883_ = lean_apply_2(v_h__1_1875_, lean_box(0), lean_box(0));
return v___x_1883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object* v_00_u03b1_1884_, lean_object* v_00_u03b2_1885_, lean_object* v_sz_1886_, lean_object* v_k_1887_, lean_object* v_v_1888_, lean_object* v_l_x27_1889_, lean_object* v_r_x27_1890_, lean_object* v_motive_1891_, lean_object* v_r_1892_, lean_object* v_hr_1893_, lean_object* v_hlr_1894_, lean_object* v_h__1_1895_, lean_object* v_h__2_1896_){
_start:
{
if (lean_obj_tag(v_r_1892_) == 0)
{
lean_object* v_size_1897_; lean_object* v_k_1898_; lean_object* v_v_1899_; lean_object* v_l_1900_; lean_object* v_r_1901_; lean_object* v___x_1902_; 
lean_dec(v_h__1_1895_);
v_size_1897_ = lean_ctor_get(v_r_1892_, 0);
lean_inc(v_size_1897_);
v_k_1898_ = lean_ctor_get(v_r_1892_, 1);
lean_inc(v_k_1898_);
v_v_1899_ = lean_ctor_get(v_r_1892_, 2);
lean_inc(v_v_1899_);
v_l_1900_ = lean_ctor_get(v_r_1892_, 3);
lean_inc(v_l_1900_);
v_r_1901_ = lean_ctor_get(v_r_1892_, 4);
lean_inc(v_r_1901_);
lean_dec_ref_known(v_r_1892_, 5);
v___x_1902_ = lean_apply_7(v_h__2_1896_, v_size_1897_, v_k_1898_, v_v_1899_, v_l_1900_, v_r_1901_, lean_box(0), lean_box(0));
return v___x_1902_;
}
else
{
lean_object* v___x_1903_; 
lean_dec(v_h__2_1896_);
v___x_1903_ = lean_apply_2(v_h__1_1895_, lean_box(0), lean_box(0));
return v___x_1903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object* v_00_u03b1_1904_, lean_object* v_00_u03b2_1905_, lean_object* v_sz_1906_, lean_object* v_k_1907_, lean_object* v_v_1908_, lean_object* v_l_x27_1909_, lean_object* v_r_x27_1910_, lean_object* v_motive_1911_, lean_object* v_r_1912_, lean_object* v_hr_1913_, lean_object* v_hlr_1914_, lean_object* v_h__1_1915_, lean_object* v_h__2_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(v_00_u03b1_1904_, v_00_u03b2_1905_, v_sz_1906_, v_k_1907_, v_v_1908_, v_l_x27_1909_, v_r_x27_1910_, v_motive_1911_, v_r_1912_, v_hr_1913_, v_hlr_1914_, v_h__1_1915_, v_h__2_1916_);
lean_dec(v_r_x27_1910_);
lean_dec(v_l_x27_1909_);
lean_dec(v_v_1908_);
lean_dec(v_k_1907_);
lean_dec(v_sz_1906_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object* v_t_1918_, lean_object* v_h__1_1919_, lean_object* v_h__2_1920_){
_start:
{
if (lean_obj_tag(v_t_1918_) == 0)
{
lean_object* v_size_1921_; lean_object* v_k_1922_; lean_object* v_v_1923_; lean_object* v_l_1924_; lean_object* v_r_1925_; lean_object* v___x_1926_; 
lean_dec(v_h__1_1919_);
v_size_1921_ = lean_ctor_get(v_t_1918_, 0);
lean_inc(v_size_1921_);
v_k_1922_ = lean_ctor_get(v_t_1918_, 1);
lean_inc(v_k_1922_);
v_v_1923_ = lean_ctor_get(v_t_1918_, 2);
lean_inc(v_v_1923_);
v_l_1924_ = lean_ctor_get(v_t_1918_, 3);
lean_inc(v_l_1924_);
v_r_1925_ = lean_ctor_get(v_t_1918_, 4);
lean_inc(v_r_1925_);
lean_dec_ref_known(v_t_1918_, 5);
v___x_1926_ = lean_apply_6(v_h__2_1920_, v_size_1921_, v_k_1922_, v_v_1923_, v_l_1924_, v_r_1925_, lean_box(0));
return v___x_1926_;
}
else
{
lean_object* v___x_1927_; 
lean_dec(v_h__2_1920_);
v___x_1927_ = lean_apply_1(v_h__1_1919_, lean_box(0));
return v___x_1927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object* v_00_u03b1_1928_, lean_object* v_00_u03b2_1929_, lean_object* v_motive_1930_, lean_object* v_t_1931_, lean_object* v_hr_1932_, lean_object* v_h__1_1933_, lean_object* v_h__2_1934_){
_start:
{
if (lean_obj_tag(v_t_1931_) == 0)
{
lean_object* v_size_1935_; lean_object* v_k_1936_; lean_object* v_v_1937_; lean_object* v_l_1938_; lean_object* v_r_1939_; lean_object* v___x_1940_; 
lean_dec(v_h__1_1933_);
v_size_1935_ = lean_ctor_get(v_t_1931_, 0);
lean_inc(v_size_1935_);
v_k_1936_ = lean_ctor_get(v_t_1931_, 1);
lean_inc(v_k_1936_);
v_v_1937_ = lean_ctor_get(v_t_1931_, 2);
lean_inc(v_v_1937_);
v_l_1938_ = lean_ctor_get(v_t_1931_, 3);
lean_inc(v_l_1938_);
v_r_1939_ = lean_ctor_get(v_t_1931_, 4);
lean_inc(v_r_1939_);
lean_dec_ref_known(v_t_1931_, 5);
v___x_1940_ = lean_apply_6(v_h__2_1934_, v_size_1935_, v_k_1936_, v_v_1937_, v_l_1938_, v_r_1939_, lean_box(0));
return v___x_1940_;
}
else
{
lean_object* v___x_1941_; 
lean_dec(v_h__2_1934_);
v___x_1941_ = lean_apply_1(v_h__1_1933_, lean_box(0));
return v___x_1941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t v_x_1942_, lean_object* v_h__1_1943_, lean_object* v_h__2_1944_, lean_object* v_h__3_1945_){
_start:
{
switch(v_x_1942_)
{
case 0:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
lean_dec(v_h__3_1945_);
lean_dec(v_h__2_1944_);
v___x_1946_ = lean_box(0);
v___x_1947_ = lean_apply_1(v_h__1_1943_, v___x_1946_);
return v___x_1947_;
}
case 1:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec(v_h__2_1944_);
lean_dec(v_h__1_1943_);
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_apply_1(v_h__3_1945_, v___x_1948_);
return v___x_1949_;
}
default: 
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_dec(v_h__3_1945_);
lean_dec(v_h__1_1943_);
v___x_1950_ = lean_box(0);
v___x_1951_ = lean_apply_1(v_h__2_1944_, v___x_1950_);
return v___x_1951_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object* v_x_1952_, lean_object* v_h__1_1953_, lean_object* v_h__2_1954_, lean_object* v_h__3_1955_){
_start:
{
uint8_t v_x_33__boxed_1956_; lean_object* v_res_1957_; 
v_x_33__boxed_1956_ = lean_unbox(v_x_1952_);
v_res_1957_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_33__boxed_1956_, v_h__1_1953_, v_h__2_1954_, v_h__3_1955_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object* v_motive_1958_, uint8_t v_x_1959_, lean_object* v_h__1_1960_, lean_object* v_h__2_1961_, lean_object* v_h__3_1962_){
_start:
{
switch(v_x_1959_)
{
case 0:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec(v_h__3_1962_);
lean_dec(v_h__2_1961_);
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_apply_1(v_h__1_1960_, v___x_1963_);
return v___x_1964_;
}
case 1:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_dec(v_h__2_1961_);
lean_dec(v_h__1_1960_);
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_apply_1(v_h__3_1962_, v___x_1965_);
return v___x_1966_;
}
default: 
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_dec(v_h__3_1962_);
lean_dec(v_h__1_1960_);
v___x_1967_ = lean_box(0);
v___x_1968_ = lean_apply_1(v_h__2_1961_, v___x_1967_);
return v___x_1968_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object* v_motive_1969_, lean_object* v_x_1970_, lean_object* v_h__1_1971_, lean_object* v_h__2_1972_, lean_object* v_h__3_1973_){
_start:
{
uint8_t v_x_48__boxed_1974_; lean_object* v_res_1975_; 
v_x_48__boxed_1974_ = lean_unbox(v_x_1970_);
v_res_1975_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_1969_, v_x_48__boxed_1974_, v_h__1_1971_, v_h__2_1972_, v_h__3_1973_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___redArg(lean_object* v_x_1976_, lean_object* v_h__1_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_apply_4(v_h__1_1977_, v_x_1976_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(lean_object* v_00_u03b1_1979_, lean_object* v_00_u03b2_1980_, lean_object* v_l_x27_1981_, lean_object* v_motive_1982_, lean_object* v_x_1983_, lean_object* v_h__1_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_apply_4(v_h__1_1984_, v_x_1983_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___boxed(lean_object* v_00_u03b1_1986_, lean_object* v_00_u03b2_1987_, lean_object* v_l_x27_1988_, lean_object* v_motive_1989_, lean_object* v_x_1990_, lean_object* v_h__1_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(v_00_u03b1_1986_, v_00_u03b2_1987_, v_l_x27_1988_, v_motive_1989_, v_x_1990_, v_h__1_1991_);
lean_dec(v_l_x27_1988_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(lean_object* v_l_1993_, lean_object* v_h__1_1994_, lean_object* v_h__2_1995_){
_start:
{
if (lean_obj_tag(v_l_1993_) == 0)
{
lean_object* v_size_1996_; lean_object* v_k_1997_; lean_object* v_v_1998_; lean_object* v_l_1999_; lean_object* v_r_2000_; lean_object* v___x_2001_; 
lean_dec(v_h__1_1994_);
v_size_1996_ = lean_ctor_get(v_l_1993_, 0);
lean_inc(v_size_1996_);
v_k_1997_ = lean_ctor_get(v_l_1993_, 1);
lean_inc(v_k_1997_);
v_v_1998_ = lean_ctor_get(v_l_1993_, 2);
lean_inc(v_v_1998_);
v_l_1999_ = lean_ctor_get(v_l_1993_, 3);
lean_inc(v_l_1999_);
v_r_2000_ = lean_ctor_get(v_l_1993_, 4);
lean_inc(v_r_2000_);
lean_dec_ref_known(v_l_1993_, 5);
v___x_2001_ = lean_apply_6(v_h__2_1995_, v_size_1996_, v_k_1997_, v_v_1998_, v_l_1999_, v_r_2000_, lean_box(0));
return v___x_2001_;
}
else
{
lean_object* v___x_2002_; 
lean_dec(v_h__2_1995_);
v___x_2002_ = lean_apply_1(v_h__1_1994_, lean_box(0));
return v___x_2002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(lean_object* v_00_u03b1_2003_, lean_object* v_00_u03b2_2004_, lean_object* v_motive_2005_, lean_object* v_l_2006_, lean_object* v_hl_2007_, lean_object* v_h__1_2008_, lean_object* v_h__2_2009_){
_start:
{
if (lean_obj_tag(v_l_2006_) == 0)
{
lean_object* v_size_2010_; lean_object* v_k_2011_; lean_object* v_v_2012_; lean_object* v_l_2013_; lean_object* v_r_2014_; lean_object* v___x_2015_; 
lean_dec(v_h__1_2008_);
v_size_2010_ = lean_ctor_get(v_l_2006_, 0);
lean_inc(v_size_2010_);
v_k_2011_ = lean_ctor_get(v_l_2006_, 1);
lean_inc(v_k_2011_);
v_v_2012_ = lean_ctor_get(v_l_2006_, 2);
lean_inc(v_v_2012_);
v_l_2013_ = lean_ctor_get(v_l_2006_, 3);
lean_inc(v_l_2013_);
v_r_2014_ = lean_ctor_get(v_l_2006_, 4);
lean_inc(v_r_2014_);
lean_dec_ref_known(v_l_2006_, 5);
v___x_2015_ = lean_apply_6(v_h__2_2009_, v_size_2010_, v_k_2011_, v_v_2012_, v_l_2013_, v_r_2014_, lean_box(0));
return v___x_2015_;
}
else
{
lean_object* v___x_2016_; 
lean_dec(v_h__2_2009_);
v___x_2016_ = lean_apply_1(v_h__1_2008_, lean_box(0));
return v___x_2016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object* v_x_2017_, lean_object* v_h__1_2018_, lean_object* v_h__2_2019_){
_start:
{
if (lean_obj_tag(v_x_2017_) == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_dec(v_h__2_2019_);
v___x_2020_ = lean_box(0);
v___x_2021_ = lean_apply_1(v_h__1_2018_, v___x_2020_);
return v___x_2021_;
}
else
{
lean_object* v_val_2022_; lean_object* v_fst_2023_; lean_object* v_snd_2024_; lean_object* v___x_2025_; 
lean_dec(v_h__1_2018_);
v_val_2022_ = lean_ctor_get(v_x_2017_, 0);
lean_inc(v_val_2022_);
lean_dec_ref_known(v_x_2017_, 1);
v_fst_2023_ = lean_ctor_get(v_val_2022_, 0);
lean_inc(v_fst_2023_);
v_snd_2024_ = lean_ctor_get(v_val_2022_, 1);
lean_inc(v_snd_2024_);
lean_dec(v_val_2022_);
v___x_2025_ = lean_apply_2(v_h__2_2019_, v_fst_2023_, v_snd_2024_);
return v___x_2025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* v_00_u03b1_2026_, lean_object* v_00_u03b2_2027_, lean_object* v_motive_2028_, lean_object* v_x_2029_, lean_object* v_h__1_2030_, lean_object* v_h__2_2031_){
_start:
{
if (lean_obj_tag(v_x_2029_) == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_dec(v_h__2_2031_);
v___x_2032_ = lean_box(0);
v___x_2033_ = lean_apply_1(v_h__1_2030_, v___x_2032_);
return v___x_2033_;
}
else
{
lean_object* v_val_2034_; lean_object* v_fst_2035_; lean_object* v_snd_2036_; lean_object* v___x_2037_; 
lean_dec(v_h__1_2030_);
v_val_2034_ = lean_ctor_get(v_x_2029_, 0);
lean_inc(v_val_2034_);
lean_dec_ref_known(v_x_2029_, 1);
v_fst_2035_ = lean_ctor_get(v_val_2034_, 0);
lean_inc(v_fst_2035_);
v_snd_2036_ = lean_ctor_get(v_val_2034_, 1);
lean_inc(v_snd_2036_);
lean_dec(v_val_2034_);
v___x_2037_ = lean_apply_2(v_h__2_2031_, v_fst_2035_, v_snd_2036_);
return v___x_2037_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(lean_object* v_x_2038_, lean_object* v_h__1_2039_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_apply_4(v_h__1_2039_, v_x_2038_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object* v_00_u03b1_2041_, lean_object* v_00_u03b2_2042_, lean_object* v_l_2043_, lean_object* v_motive_2044_, lean_object* v_x_2045_, lean_object* v_h__1_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_apply_4(v_h__1_2046_, v_x_2045_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(lean_object* v_00_u03b1_2048_, lean_object* v_00_u03b2_2049_, lean_object* v_l_2050_, lean_object* v_motive_2051_, lean_object* v_x_2052_, lean_object* v_h__1_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_2048_, v_00_u03b2_2049_, v_l_2050_, v_motive_2051_, v_x_2052_, v_h__1_2053_);
lean_dec(v_l_2050_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___redArg(lean_object* v_x_2055_, lean_object* v_h__1_2056_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_apply_4(v_h__1_2056_, v_x_2055_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(lean_object* v_00_u03b1_2058_, lean_object* v_00_u03b2_2059_, lean_object* v_l_2060_, lean_object* v_motive_2061_, lean_object* v_x_2062_, lean_object* v_h__1_2063_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_apply_4(v_h__1_2063_, v_x_2062_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_2065_, lean_object* v_00_u03b2_2066_, lean_object* v_l_2067_, lean_object* v_motive_2068_, lean_object* v_x_2069_, lean_object* v_h__1_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(v_00_u03b1_2065_, v_00_u03b2_2066_, v_l_2067_, v_motive_2068_, v_x_2069_, v_h__1_2070_);
lean_dec(v_l_2067_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___redArg(lean_object* v_x_2072_, lean_object* v_h__1_2073_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_apply_3(v_h__1_2073_, v_x_2072_, lean_box(0), lean_box(0));
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(lean_object* v_00_u03b1_2075_, lean_object* v_00_u03b2_2076_, lean_object* v_l_x27_2077_, lean_object* v_motive_2078_, lean_object* v_x_2079_, lean_object* v_h__1_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_apply_3(v_h__1_2080_, v_x_2079_, lean_box(0), lean_box(0));
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___boxed(lean_object* v_00_u03b1_2082_, lean_object* v_00_u03b2_2083_, lean_object* v_l_x27_2084_, lean_object* v_motive_2085_, lean_object* v_x_2086_, lean_object* v_h__1_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(v_00_u03b1_2082_, v_00_u03b2_2083_, v_l_x27_2084_, v_motive_2085_, v_x_2086_, v_h__1_2087_);
lean_dec(v_l_x27_2084_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___redArg(lean_object* v_x_2089_, lean_object* v_h__1_2090_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_apply_3(v_h__1_2090_, v_x_2089_, lean_box(0), lean_box(0));
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(lean_object* v_00_u03b1_2092_, lean_object* v_00_u03b2_2093_, lean_object* v_r_x27_2094_, lean_object* v_motive_2095_, lean_object* v_x_2096_, lean_object* v_h__1_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_apply_3(v_h__1_2097_, v_x_2096_, lean_box(0), lean_box(0));
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___boxed(lean_object* v_00_u03b1_2099_, lean_object* v_00_u03b2_2100_, lean_object* v_r_x27_2101_, lean_object* v_motive_2102_, lean_object* v_x_2103_, lean_object* v_h__1_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(v_00_u03b1_2099_, v_00_u03b2_2100_, v_r_x27_2101_, v_motive_2102_, v_x_2103_, v_h__1_2104_);
lean_dec(v_r_x27_2101_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(lean_object* v_r_2106_, lean_object* v_h__1_2107_, lean_object* v_h__2_2108_){
_start:
{
if (lean_obj_tag(v_r_2106_) == 0)
{
lean_object* v_size_2109_; lean_object* v_k_2110_; lean_object* v_v_2111_; lean_object* v_l_2112_; lean_object* v_r_2113_; lean_object* v___x_2114_; 
lean_dec(v_h__1_2107_);
v_size_2109_ = lean_ctor_get(v_r_2106_, 0);
lean_inc(v_size_2109_);
v_k_2110_ = lean_ctor_get(v_r_2106_, 1);
lean_inc(v_k_2110_);
v_v_2111_ = lean_ctor_get(v_r_2106_, 2);
lean_inc(v_v_2111_);
v_l_2112_ = lean_ctor_get(v_r_2106_, 3);
lean_inc(v_l_2112_);
v_r_2113_ = lean_ctor_get(v_r_2106_, 4);
lean_inc(v_r_2113_);
lean_dec_ref_known(v_r_2106_, 5);
v___x_2114_ = lean_apply_5(v_h__2_2108_, v_size_2109_, v_k_2110_, v_v_2111_, v_l_2112_, v_r_2113_);
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec(v_h__2_2108_);
v___x_2115_ = lean_box(0);
v___x_2116_ = lean_apply_1(v_h__1_2107_, v___x_2115_);
return v___x_2116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object* v_00_u03b1_2117_, lean_object* v_00_u03b2_2118_, lean_object* v_motive_2119_, lean_object* v_r_2120_, lean_object* v_h__1_2121_, lean_object* v_h__2_2122_){
_start:
{
if (lean_obj_tag(v_r_2120_) == 0)
{
lean_object* v_size_2123_; lean_object* v_k_2124_; lean_object* v_v_2125_; lean_object* v_l_2126_; lean_object* v_r_2127_; lean_object* v___x_2128_; 
lean_dec(v_h__1_2121_);
v_size_2123_ = lean_ctor_get(v_r_2120_, 0);
lean_inc(v_size_2123_);
v_k_2124_ = lean_ctor_get(v_r_2120_, 1);
lean_inc(v_k_2124_);
v_v_2125_ = lean_ctor_get(v_r_2120_, 2);
lean_inc(v_v_2125_);
v_l_2126_ = lean_ctor_get(v_r_2120_, 3);
lean_inc(v_l_2126_);
v_r_2127_ = lean_ctor_get(v_r_2120_, 4);
lean_inc(v_r_2127_);
lean_dec_ref_known(v_r_2120_, 5);
v___x_2128_ = lean_apply_5(v_h__2_2122_, v_size_2123_, v_k_2124_, v_v_2125_, v_l_2126_, v_r_2127_);
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
lean_dec(v_h__2_2122_);
v___x_2129_ = lean_box(0);
v___x_2130_ = lean_apply_1(v_h__1_2121_, v___x_2129_);
return v___x_2130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(lean_object* v_x_2131_, lean_object* v_h__1_2132_, lean_object* v_h__2_2133_){
_start:
{
if (lean_obj_tag(v_x_2131_) == 0)
{
lean_object* v_size_2134_; lean_object* v_k_2135_; lean_object* v_v_2136_; lean_object* v_l_2137_; lean_object* v_r_2138_; lean_object* v___x_2139_; 
lean_dec(v_h__2_2133_);
v_size_2134_ = lean_ctor_get(v_x_2131_, 0);
lean_inc(v_size_2134_);
v_k_2135_ = lean_ctor_get(v_x_2131_, 1);
lean_inc(v_k_2135_);
v_v_2136_ = lean_ctor_get(v_x_2131_, 2);
lean_inc(v_v_2136_);
v_l_2137_ = lean_ctor_get(v_x_2131_, 3);
lean_inc(v_l_2137_);
v_r_2138_ = lean_ctor_get(v_x_2131_, 4);
lean_inc(v_r_2138_);
lean_dec_ref_known(v_x_2131_, 5);
v___x_2139_ = lean_apply_5(v_h__1_2132_, v_size_2134_, v_k_2135_, v_v_2136_, v_l_2137_, v_r_2138_);
return v___x_2139_;
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_dec(v_h__1_2132_);
v___x_2140_ = lean_box(0);
v___x_2141_ = lean_apply_1(v_h__2_2133_, v___x_2140_);
return v___x_2141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(lean_object* v_00_u03b1_2142_, lean_object* v_00_u03b2_2143_, lean_object* v_motive_2144_, lean_object* v_x_2145_, lean_object* v_h__1_2146_, lean_object* v_h__2_2147_){
_start:
{
if (lean_obj_tag(v_x_2145_) == 0)
{
lean_object* v_size_2148_; lean_object* v_k_2149_; lean_object* v_v_2150_; lean_object* v_l_2151_; lean_object* v_r_2152_; lean_object* v___x_2153_; 
lean_dec(v_h__2_2147_);
v_size_2148_ = lean_ctor_get(v_x_2145_, 0);
lean_inc(v_size_2148_);
v_k_2149_ = lean_ctor_get(v_x_2145_, 1);
lean_inc(v_k_2149_);
v_v_2150_ = lean_ctor_get(v_x_2145_, 2);
lean_inc(v_v_2150_);
v_l_2151_ = lean_ctor_get(v_x_2145_, 3);
lean_inc(v_l_2151_);
v_r_2152_ = lean_ctor_get(v_x_2145_, 4);
lean_inc(v_r_2152_);
lean_dec_ref_known(v_x_2145_, 5);
v___x_2153_ = lean_apply_5(v_h__1_2146_, v_size_2148_, v_k_2149_, v_v_2150_, v_l_2151_, v_r_2152_);
return v___x_2153_;
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec(v_h__1_2146_);
v___x_2154_ = lean_box(0);
v___x_2155_ = lean_apply_1(v_h__2_2147_, v___x_2154_);
return v___x_2155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object* v_r_2156_, lean_object* v_h__1_2157_, lean_object* v_h__2_2158_){
_start:
{
if (lean_obj_tag(v_r_2156_) == 0)
{
lean_object* v_size_2159_; lean_object* v_k_2160_; lean_object* v_v_2161_; lean_object* v_l_2162_; lean_object* v_r_2163_; lean_object* v___x_2164_; 
lean_dec(v_h__1_2157_);
v_size_2159_ = lean_ctor_get(v_r_2156_, 0);
lean_inc(v_size_2159_);
v_k_2160_ = lean_ctor_get(v_r_2156_, 1);
lean_inc(v_k_2160_);
v_v_2161_ = lean_ctor_get(v_r_2156_, 2);
lean_inc(v_v_2161_);
v_l_2162_ = lean_ctor_get(v_r_2156_, 3);
lean_inc(v_l_2162_);
v_r_2163_ = lean_ctor_get(v_r_2156_, 4);
lean_inc(v_r_2163_);
lean_dec_ref_known(v_r_2156_, 5);
v___x_2164_ = lean_apply_7(v_h__2_2158_, v_size_2159_, v_k_2160_, v_v_2161_, v_l_2162_, v_r_2163_, lean_box(0), lean_box(0));
return v___x_2164_;
}
else
{
lean_object* v___x_2165_; 
lean_dec(v_h__2_2158_);
v___x_2165_ = lean_apply_2(v_h__1_2157_, lean_box(0), lean_box(0));
return v___x_2165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object* v_00_u03b1_2166_, lean_object* v_00_u03b2_2167_, lean_object* v_motive_2168_, lean_object* v_r_2169_, lean_object* v_hr_2170_, lean_object* v_h__1_2171_, lean_object* v_h__2_2172_){
_start:
{
if (lean_obj_tag(v_r_2169_) == 0)
{
lean_object* v_size_2173_; lean_object* v_k_2174_; lean_object* v_v_2175_; lean_object* v_l_2176_; lean_object* v_r_2177_; lean_object* v___x_2178_; 
lean_dec(v_h__1_2171_);
v_size_2173_ = lean_ctor_get(v_r_2169_, 0);
lean_inc(v_size_2173_);
v_k_2174_ = lean_ctor_get(v_r_2169_, 1);
lean_inc(v_k_2174_);
v_v_2175_ = lean_ctor_get(v_r_2169_, 2);
lean_inc(v_v_2175_);
v_l_2176_ = lean_ctor_get(v_r_2169_, 3);
lean_inc(v_l_2176_);
v_r_2177_ = lean_ctor_get(v_r_2169_, 4);
lean_inc(v_r_2177_);
lean_dec_ref_known(v_r_2169_, 5);
v___x_2178_ = lean_apply_7(v_h__2_2172_, v_size_2173_, v_k_2174_, v_v_2175_, v_l_2176_, v_r_2177_, lean_box(0), lean_box(0));
return v___x_2178_;
}
else
{
lean_object* v___x_2179_; 
lean_dec(v_h__2_2172_);
v___x_2179_ = lean_apply_2(v_h__1_2171_, lean_box(0), lean_box(0));
return v___x_2179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg(lean_object* v_t_2180_, lean_object* v_h__1_2181_, lean_object* v_h__2_2182_){
_start:
{
if (lean_obj_tag(v_t_2180_) == 0)
{
lean_object* v_size_2183_; lean_object* v_k_2184_; lean_object* v_v_2185_; lean_object* v_l_2186_; lean_object* v_r_2187_; lean_object* v___x_2188_; 
lean_dec(v_h__1_2181_);
v_size_2183_ = lean_ctor_get(v_t_2180_, 0);
lean_inc(v_size_2183_);
v_k_2184_ = lean_ctor_get(v_t_2180_, 1);
lean_inc(v_k_2184_);
v_v_2185_ = lean_ctor_get(v_t_2180_, 2);
lean_inc(v_v_2185_);
v_l_2186_ = lean_ctor_get(v_t_2180_, 3);
lean_inc(v_l_2186_);
v_r_2187_ = lean_ctor_get(v_t_2180_, 4);
lean_inc(v_r_2187_);
lean_dec_ref_known(v_t_2180_, 5);
v___x_2188_ = lean_apply_5(v_h__2_2182_, v_size_2183_, v_k_2184_, v_v_2185_, v_l_2186_, v_r_2187_);
return v___x_2188_;
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec(v_h__2_2182_);
v___x_2189_ = lean_box(0);
v___x_2190_ = lean_apply_1(v_h__1_2181_, v___x_2189_);
return v___x_2190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_2191_, lean_object* v_00_u03b4_2192_, lean_object* v_motive_2193_, lean_object* v_t_2194_, lean_object* v_h__1_2195_, lean_object* v_h__2_2196_){
_start:
{
if (lean_obj_tag(v_t_2194_) == 0)
{
lean_object* v_size_2197_; lean_object* v_k_2198_; lean_object* v_v_2199_; lean_object* v_l_2200_; lean_object* v_r_2201_; lean_object* v___x_2202_; 
lean_dec(v_h__1_2195_);
v_size_2197_ = lean_ctor_get(v_t_2194_, 0);
lean_inc(v_size_2197_);
v_k_2198_ = lean_ctor_get(v_t_2194_, 1);
lean_inc(v_k_2198_);
v_v_2199_ = lean_ctor_get(v_t_2194_, 2);
lean_inc(v_v_2199_);
v_l_2200_ = lean_ctor_get(v_t_2194_, 3);
lean_inc(v_l_2200_);
v_r_2201_ = lean_ctor_get(v_t_2194_, 4);
lean_inc(v_r_2201_);
lean_dec_ref_known(v_t_2194_, 5);
v___x_2202_ = lean_apply_5(v_h__2_2196_, v_size_2197_, v_k_2198_, v_v_2199_, v_l_2200_, v_r_2201_);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec(v_h__2_2196_);
v___x_2203_ = lean_box(0);
v___x_2204_ = lean_apply_1(v_h__1_2195_, v___x_2203_);
return v___x_2204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object* v_x_2205_, lean_object* v_h__1_2206_, lean_object* v_h__2_2207_){
_start:
{
if (lean_obj_tag(v_x_2205_) == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec(v_h__2_2207_);
v___x_2208_ = lean_box(0);
v___x_2209_ = lean_apply_1(v_h__1_2206_, v___x_2208_);
return v___x_2209_;
}
else
{
lean_object* v_val_2210_; lean_object* v___x_2211_; 
lean_dec(v_h__1_2206_);
v_val_2210_ = lean_ctor_get(v_x_2205_, 0);
lean_inc(v_val_2210_);
lean_dec_ref_known(v_x_2205_, 1);
v___x_2211_ = lean_apply_1(v_h__2_2207_, v_val_2210_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_2212_, lean_object* v_00_u03b2_2213_, lean_object* v_motive_2214_, lean_object* v_x_2215_, lean_object* v_h__1_2216_, lean_object* v_h__2_2217_){
_start:
{
if (lean_obj_tag(v_x_2215_) == 0)
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_dec(v_h__2_2217_);
v___x_2218_ = lean_box(0);
v___x_2219_ = lean_apply_1(v_h__1_2216_, v___x_2218_);
return v___x_2219_;
}
else
{
lean_object* v_val_2220_; lean_object* v___x_2221_; 
lean_dec(v_h__1_2216_);
v_val_2220_ = lean_ctor_get(v_x_2215_, 0);
lean_inc(v_val_2220_);
lean_dec_ref_known(v_x_2215_, 1);
v___x_2221_ = lean_apply_1(v_h__2_2217_, v_val_2220_);
return v___x_2221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___redArg(lean_object* v_t_2222_, lean_object* v_h__1_2223_){
_start:
{
lean_object* v_size_2224_; lean_object* v_k_2225_; lean_object* v_v_2226_; lean_object* v_l_2227_; lean_object* v_r_2228_; lean_object* v___x_2229_; 
v_size_2224_ = lean_ctor_get(v_t_2222_, 0);
lean_inc(v_size_2224_);
v_k_2225_ = lean_ctor_get(v_t_2222_, 1);
lean_inc(v_k_2225_);
v_v_2226_ = lean_ctor_get(v_t_2222_, 2);
lean_inc(v_v_2226_);
v_l_2227_ = lean_ctor_get(v_t_2222_, 3);
lean_inc(v_l_2227_);
v_r_2228_ = lean_ctor_get(v_t_2222_, 4);
lean_inc(v_r_2228_);
lean_dec(v_t_2222_);
v___x_2229_ = lean_apply_6(v_h__1_2223_, v_size_2224_, v_k_2225_, v_v_2226_, v_l_2227_, v_r_2228_, lean_box(0));
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(lean_object* v_00_u03b1_2230_, lean_object* v_00_u03b4_2231_, lean_object* v_inst_2232_, lean_object* v_k_2233_, lean_object* v_motive_2234_, lean_object* v_t_2235_, lean_object* v_hlk_2236_, lean_object* v_h__1_2237_){
_start:
{
lean_object* v_size_2238_; lean_object* v_k_2239_; lean_object* v_v_2240_; lean_object* v_l_2241_; lean_object* v_r_2242_; lean_object* v___x_2243_; 
v_size_2238_ = lean_ctor_get(v_t_2235_, 0);
lean_inc(v_size_2238_);
v_k_2239_ = lean_ctor_get(v_t_2235_, 1);
lean_inc(v_k_2239_);
v_v_2240_ = lean_ctor_get(v_t_2235_, 2);
lean_inc(v_v_2240_);
v_l_2241_ = lean_ctor_get(v_t_2235_, 3);
lean_inc(v_l_2241_);
v_r_2242_ = lean_ctor_get(v_t_2235_, 4);
lean_inc(v_r_2242_);
lean_dec(v_t_2235_);
v___x_2243_ = lean_apply_6(v_h__1_2237_, v_size_2238_, v_k_2239_, v_v_2240_, v_l_2241_, v_r_2242_, lean_box(0));
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___boxed(lean_object* v_00_u03b1_2244_, lean_object* v_00_u03b4_2245_, lean_object* v_inst_2246_, lean_object* v_k_2247_, lean_object* v_motive_2248_, lean_object* v_t_2249_, lean_object* v_hlk_2250_, lean_object* v_h__1_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(v_00_u03b1_2244_, v_00_u03b4_2245_, v_inst_2246_, v_k_2247_, v_motive_2248_, v_t_2249_, v_hlk_2250_, v_h__1_2251_);
lean_dec(v_k_2247_);
lean_dec_ref(v_inst_2246_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(lean_object* v_x_2253_, lean_object* v_x_2254_, lean_object* v_h__1_2255_){
_start:
{
lean_object* v_size_2256_; lean_object* v_k_2257_; lean_object* v_v_2258_; lean_object* v_l_2259_; lean_object* v_r_2260_; lean_object* v___x_2261_; 
v_size_2256_ = lean_ctor_get(v_x_2253_, 0);
lean_inc(v_size_2256_);
v_k_2257_ = lean_ctor_get(v_x_2253_, 1);
lean_inc(v_k_2257_);
v_v_2258_ = lean_ctor_get(v_x_2253_, 2);
lean_inc(v_v_2258_);
v_l_2259_ = lean_ctor_get(v_x_2253_, 3);
lean_inc(v_l_2259_);
v_r_2260_ = lean_ctor_get(v_x_2253_, 4);
lean_inc(v_r_2260_);
lean_dec(v_x_2253_);
v___x_2261_ = lean_apply_8(v_h__1_2255_, v_size_2256_, v_k_2257_, v_v_2258_, v_l_2259_, v_r_2260_, lean_box(0), v_x_2254_, lean_box(0));
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter(lean_object* v_00_u03b1_2262_, lean_object* v_00_u03b2_2263_, lean_object* v_motive_2264_, lean_object* v_x_2265_, lean_object* v_x_2266_, lean_object* v_x_2267_, lean_object* v_x_2268_, lean_object* v_h__1_2269_){
_start:
{
lean_object* v_size_2270_; lean_object* v_k_2271_; lean_object* v_v_2272_; lean_object* v_l_2273_; lean_object* v_r_2274_; lean_object* v___x_2275_; 
v_size_2270_ = lean_ctor_get(v_x_2265_, 0);
lean_inc(v_size_2270_);
v_k_2271_ = lean_ctor_get(v_x_2265_, 1);
lean_inc(v_k_2271_);
v_v_2272_ = lean_ctor_get(v_x_2265_, 2);
lean_inc(v_v_2272_);
v_l_2273_ = lean_ctor_get(v_x_2265_, 3);
lean_inc(v_l_2273_);
v_r_2274_ = lean_ctor_get(v_x_2265_, 4);
lean_inc(v_r_2274_);
lean_dec(v_x_2265_);
v___x_2275_ = lean_apply_8(v_h__1_2269_, v_size_2270_, v_k_2271_, v_v_2272_, v_l_2273_, v_r_2274_, lean_box(0), v_x_2267_, lean_box(0));
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(uint8_t v_x_2276_, lean_object* v_h__1_2277_, lean_object* v_h__2_2278_, lean_object* v_h__3_2279_){
_start:
{
switch(v_x_2276_)
{
case 0:
{
lean_object* v___x_2280_; 
lean_dec(v_h__3_2279_);
lean_dec(v_h__2_2278_);
v___x_2280_ = lean_apply_1(v_h__1_2277_, lean_box(0));
return v___x_2280_;
}
case 1:
{
lean_object* v___x_2281_; 
lean_dec(v_h__3_2279_);
lean_dec(v_h__1_2277_);
v___x_2281_ = lean_apply_1(v_h__2_2278_, lean_box(0));
return v___x_2281_;
}
default: 
{
lean_object* v___x_2282_; 
lean_dec(v_h__2_2278_);
lean_dec(v_h__1_2277_);
v___x_2282_ = lean_apply_1(v_h__3_2279_, lean_box(0));
return v___x_2282_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg___boxed(lean_object* v_x_2283_, lean_object* v_h__1_2284_, lean_object* v_h__2_2285_, lean_object* v_h__3_2286_){
_start:
{
uint8_t v_x_33__boxed_2287_; lean_object* v_res_2288_; 
v_x_33__boxed_2287_ = lean_unbox(v_x_2283_);
v_res_2288_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(v_x_33__boxed_2287_, v_h__1_2284_, v_h__2_2285_, v_h__3_2286_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(lean_object* v_motive_2289_, uint8_t v_x_2290_, lean_object* v_h__1_2291_, lean_object* v_h__2_2292_, lean_object* v_h__3_2293_){
_start:
{
switch(v_x_2290_)
{
case 0:
{
lean_object* v___x_2294_; 
lean_dec(v_h__3_2293_);
lean_dec(v_h__2_2292_);
v___x_2294_ = lean_apply_1(v_h__1_2291_, lean_box(0));
return v___x_2294_;
}
case 1:
{
lean_object* v___x_2295_; 
lean_dec(v_h__3_2293_);
lean_dec(v_h__1_2291_);
v___x_2295_ = lean_apply_1(v_h__2_2292_, lean_box(0));
return v___x_2295_;
}
default: 
{
lean_object* v___x_2296_; 
lean_dec(v_h__2_2292_);
lean_dec(v_h__1_2291_);
v___x_2296_ = lean_apply_1(v_h__3_2293_, lean_box(0));
return v___x_2296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___boxed(lean_object* v_motive_2297_, lean_object* v_x_2298_, lean_object* v_h__1_2299_, lean_object* v_h__2_2300_, lean_object* v_h__3_2301_){
_start:
{
uint8_t v_x_42__boxed_2302_; lean_object* v_res_2303_; 
v_x_42__boxed_2302_ = lean_unbox(v_x_2298_);
v_res_2303_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(v_motive_2297_, v_x_42__boxed_2302_, v_h__1_2299_, v_h__2_2300_, v_h__3_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object* v_x_2304_, lean_object* v_x_2305_, lean_object* v_h__1_2306_, lean_object* v_h__2_2307_){
_start:
{
if (lean_obj_tag(v_x_2304_) == 0)
{
lean_object* v_size_2308_; lean_object* v_k_2309_; lean_object* v_v_2310_; lean_object* v_l_2311_; lean_object* v_r_2312_; lean_object* v___x_2313_; 
lean_dec(v_h__1_2306_);
v_size_2308_ = lean_ctor_get(v_x_2304_, 0);
lean_inc(v_size_2308_);
v_k_2309_ = lean_ctor_get(v_x_2304_, 1);
lean_inc(v_k_2309_);
v_v_2310_ = lean_ctor_get(v_x_2304_, 2);
lean_inc(v_v_2310_);
v_l_2311_ = lean_ctor_get(v_x_2304_, 3);
lean_inc(v_l_2311_);
v_r_2312_ = lean_ctor_get(v_x_2304_, 4);
lean_inc(v_r_2312_);
lean_dec_ref_known(v_x_2304_, 5);
v___x_2313_ = lean_apply_6(v_h__2_2307_, v_size_2308_, v_k_2309_, v_v_2310_, v_l_2311_, v_r_2312_, v_x_2305_);
return v___x_2313_;
}
else
{
lean_object* v___x_2314_; 
lean_dec(v_h__2_2307_);
v___x_2314_ = lean_apply_1(v_h__1_2306_, v_x_2305_);
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object* v_00_u03b1_2315_, lean_object* v_00_u03b2_2316_, lean_object* v_motive_2317_, lean_object* v_x_2318_, lean_object* v_x_2319_, lean_object* v_h__1_2320_, lean_object* v_h__2_2321_){
_start:
{
if (lean_obj_tag(v_x_2318_) == 0)
{
lean_object* v_size_2322_; lean_object* v_k_2323_; lean_object* v_v_2324_; lean_object* v_l_2325_; lean_object* v_r_2326_; lean_object* v___x_2327_; 
lean_dec(v_h__1_2320_);
v_size_2322_ = lean_ctor_get(v_x_2318_, 0);
lean_inc(v_size_2322_);
v_k_2323_ = lean_ctor_get(v_x_2318_, 1);
lean_inc(v_k_2323_);
v_v_2324_ = lean_ctor_get(v_x_2318_, 2);
lean_inc(v_v_2324_);
v_l_2325_ = lean_ctor_get(v_x_2318_, 3);
lean_inc(v_l_2325_);
v_r_2326_ = lean_ctor_get(v_x_2318_, 4);
lean_inc(v_r_2326_);
lean_dec_ref_known(v_x_2318_, 5);
v___x_2327_ = lean_apply_6(v_h__2_2321_, v_size_2322_, v_k_2323_, v_v_2324_, v_l_2325_, v_r_2326_, v_x_2319_);
return v___x_2327_;
}
else
{
lean_object* v___x_2328_; 
lean_dec(v_h__2_2321_);
v___x_2328_ = lean_apply_1(v_h__1_2320_, v_x_2319_);
return v___x_2328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t v_x_2329_, lean_object* v_h__1_2330_, lean_object* v_h__2_2331_, lean_object* v_h__3_2332_){
_start:
{
switch(v_x_2329_)
{
case 0:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_dec(v_h__3_2332_);
lean_dec(v_h__2_2331_);
v___x_2333_ = lean_box(0);
v___x_2334_ = lean_apply_1(v_h__1_2330_, v___x_2333_);
return v___x_2334_;
}
case 1:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_dec(v_h__3_2332_);
lean_dec(v_h__1_2330_);
v___x_2335_ = lean_box(0);
v___x_2336_ = lean_apply_1(v_h__2_2331_, v___x_2335_);
return v___x_2336_;
}
default: 
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec(v_h__2_2331_);
lean_dec(v_h__1_2330_);
v___x_2337_ = lean_box(0);
v___x_2338_ = lean_apply_1(v_h__3_2332_, v___x_2337_);
return v___x_2338_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_2339_, lean_object* v_h__1_2340_, lean_object* v_h__2_2341_, lean_object* v_h__3_2342_){
_start:
{
uint8_t v_x_33__boxed_2343_; lean_object* v_res_2344_; 
v_x_33__boxed_2343_ = lean_unbox(v_x_2339_);
v_res_2344_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_33__boxed_2343_, v_h__1_2340_, v_h__2_2341_, v_h__3_2342_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object* v_motive_2345_, uint8_t v_x_2346_, lean_object* v_h__1_2347_, lean_object* v_h__2_2348_, lean_object* v_h__3_2349_){
_start:
{
switch(v_x_2346_)
{
case 0:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
lean_dec(v_h__3_2349_);
lean_dec(v_h__2_2348_);
v___x_2350_ = lean_box(0);
v___x_2351_ = lean_apply_1(v_h__1_2347_, v___x_2350_);
return v___x_2351_;
}
case 1:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_dec(v_h__3_2349_);
lean_dec(v_h__1_2347_);
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_apply_1(v_h__2_2348_, v___x_2352_);
return v___x_2353_;
}
default: 
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
lean_dec(v_h__2_2348_);
lean_dec(v_h__1_2347_);
v___x_2354_ = lean_box(0);
v___x_2355_ = lean_apply_1(v_h__3_2349_, v___x_2354_);
return v___x_2355_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object* v_motive_2356_, lean_object* v_x_2357_, lean_object* v_h__1_2358_, lean_object* v_h__2_2359_, lean_object* v_h__3_2360_){
_start:
{
uint8_t v_x_48__boxed_2361_; lean_object* v_res_2362_; 
v_x_48__boxed_2361_ = lean_unbox(v_x_2357_);
v_res_2362_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(v_motive_2356_, v_x_48__boxed_2361_, v_h__1_2358_, v_h__2_2359_, v_h__3_2360_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter___redArg(lean_object* v_x_2363_, lean_object* v_x_2364_, lean_object* v_x_2365_, lean_object* v_h__1_2366_, lean_object* v_h__2_2367_){
_start:
{
if (lean_obj_tag(v_x_2363_) == 0)
{
lean_object* v_size_2368_; lean_object* v_k_2369_; lean_object* v_v_2370_; lean_object* v_l_2371_; lean_object* v_r_2372_; lean_object* v___x_2373_; 
lean_dec(v_h__1_2366_);
v_size_2368_ = lean_ctor_get(v_x_2363_, 0);
lean_inc(v_size_2368_);
v_k_2369_ = lean_ctor_get(v_x_2363_, 1);
lean_inc(v_k_2369_);
v_v_2370_ = lean_ctor_get(v_x_2363_, 2);
lean_inc(v_v_2370_);
v_l_2371_ = lean_ctor_get(v_x_2363_, 3);
lean_inc(v_l_2371_);
v_r_2372_ = lean_ctor_get(v_x_2363_, 4);
lean_inc(v_r_2372_);
lean_dec_ref_known(v_x_2363_, 5);
v___x_2373_ = lean_apply_7(v_h__2_2367_, v_size_2368_, v_k_2369_, v_v_2370_, v_l_2371_, v_r_2372_, v_x_2364_, v_x_2365_);
return v___x_2373_;
}
else
{
lean_object* v___x_2374_; 
lean_dec(v_h__2_2367_);
v___x_2374_ = lean_apply_2(v_h__1_2366_, v_x_2364_, v_x_2365_);
return v___x_2374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2375_, lean_object* v_00_u03b2_2376_, lean_object* v_motive_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_, lean_object* v_x_2380_, lean_object* v_h__1_2381_, lean_object* v_h__2_2382_){
_start:
{
if (lean_obj_tag(v_x_2378_) == 0)
{
lean_object* v_size_2383_; lean_object* v_k_2384_; lean_object* v_v_2385_; lean_object* v_l_2386_; lean_object* v_r_2387_; lean_object* v___x_2388_; 
lean_dec(v_h__1_2381_);
v_size_2383_ = lean_ctor_get(v_x_2378_, 0);
lean_inc(v_size_2383_);
v_k_2384_ = lean_ctor_get(v_x_2378_, 1);
lean_inc(v_k_2384_);
v_v_2385_ = lean_ctor_get(v_x_2378_, 2);
lean_inc(v_v_2385_);
v_l_2386_ = lean_ctor_get(v_x_2378_, 3);
lean_inc(v_l_2386_);
v_r_2387_ = lean_ctor_get(v_x_2378_, 4);
lean_inc(v_r_2387_);
lean_dec_ref_known(v_x_2378_, 5);
v___x_2388_ = lean_apply_7(v_h__2_2382_, v_size_2383_, v_k_2384_, v_v_2385_, v_l_2386_, v_r_2387_, v_x_2379_, v_x_2380_);
return v___x_2388_;
}
else
{
lean_object* v___x_2389_; 
lean_dec(v_h__2_2382_);
v___x_2389_ = lean_apply_2(v_h__1_2381_, v_x_2379_, v_x_2380_);
return v___x_2389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter___redArg(lean_object* v_x_2390_, lean_object* v_x_2391_, lean_object* v_x_2392_, lean_object* v_h__1_2393_, lean_object* v_h__2_2394_){
_start:
{
if (lean_obj_tag(v_x_2390_) == 0)
{
lean_object* v_size_2395_; lean_object* v_k_2396_; lean_object* v_v_2397_; lean_object* v_l_2398_; lean_object* v_r_2399_; lean_object* v___x_2400_; 
lean_dec(v_h__1_2393_);
v_size_2395_ = lean_ctor_get(v_x_2390_, 0);
lean_inc(v_size_2395_);
v_k_2396_ = lean_ctor_get(v_x_2390_, 1);
lean_inc(v_k_2396_);
v_v_2397_ = lean_ctor_get(v_x_2390_, 2);
lean_inc(v_v_2397_);
v_l_2398_ = lean_ctor_get(v_x_2390_, 3);
lean_inc(v_l_2398_);
v_r_2399_ = lean_ctor_get(v_x_2390_, 4);
lean_inc(v_r_2399_);
lean_dec_ref_known(v_x_2390_, 5);
v___x_2400_ = lean_apply_7(v_h__2_2394_, v_size_2395_, v_k_2396_, v_v_2397_, v_l_2398_, v_r_2399_, v_x_2391_, v_x_2392_);
return v___x_2400_;
}
else
{
lean_object* v___x_2401_; 
lean_dec(v_h__2_2394_);
v___x_2401_ = lean_apply_2(v_h__1_2393_, v_x_2391_, v_x_2392_);
return v___x_2401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2402_, lean_object* v_00_u03b2_2403_, lean_object* v_motive_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_, lean_object* v_h__1_2408_, lean_object* v_h__2_2409_){
_start:
{
if (lean_obj_tag(v_x_2405_) == 0)
{
lean_object* v_size_2410_; lean_object* v_k_2411_; lean_object* v_v_2412_; lean_object* v_l_2413_; lean_object* v_r_2414_; lean_object* v___x_2415_; 
lean_dec(v_h__1_2408_);
v_size_2410_ = lean_ctor_get(v_x_2405_, 0);
lean_inc(v_size_2410_);
v_k_2411_ = lean_ctor_get(v_x_2405_, 1);
lean_inc(v_k_2411_);
v_v_2412_ = lean_ctor_get(v_x_2405_, 2);
lean_inc(v_v_2412_);
v_l_2413_ = lean_ctor_get(v_x_2405_, 3);
lean_inc(v_l_2413_);
v_r_2414_ = lean_ctor_get(v_x_2405_, 4);
lean_inc(v_r_2414_);
lean_dec_ref_known(v_x_2405_, 5);
v___x_2415_ = lean_apply_7(v_h__2_2409_, v_size_2410_, v_k_2411_, v_v_2412_, v_l_2413_, v_r_2414_, v_x_2406_, v_x_2407_);
return v___x_2415_;
}
else
{
lean_object* v___x_2416_; 
lean_dec(v_h__2_2409_);
v___x_2416_ = lean_apply_2(v_h__1_2408_, v_x_2406_, v_x_2407_);
return v___x_2416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(lean_object* v_x_2417_, lean_object* v_c_2418_, lean_object* v_x_2419_, lean_object* v_r_2420_){
_start:
{
if (lean_obj_tag(v_c_2418_) == 0)
{
lean_object* v___x_2421_; 
v___x_2421_ = l_List_head_x3f___redArg(v_r_2420_);
return v___x_2421_;
}
else
{
lean_object* v_val_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
v_val_2422_ = lean_ctor_get(v_c_2418_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v_c_2418_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v_c_2418_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_val_2422_);
lean_dec(v_c_2418_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_val_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed(lean_object* v_x_2430_, lean_object* v_c_2431_, lean_object* v_x_2432_, lean_object* v_r_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(v_x_2430_, v_c_2431_, v_x_2432_, v_r_2433_);
lean_dec(v_r_2433_);
lean_dec(v_x_2430_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(lean_object* v_inst_2436_, lean_object* v_k_2437_, lean_object* v_t_2438_){
_start:
{
lean_object* v___f_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___f_2439_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0));
v___x_2440_ = lean_apply_1(v_inst_2436_, v_k_2437_);
v___x_2441_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___x_2440_, v_t_2438_, v___f_2439_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098(lean_object* v_00_u03b1_2442_, lean_object* v_00_u03b2_2443_, lean_object* v_inst_2444_, lean_object* v_k_2445_, lean_object* v_t_2446_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(v_inst_2444_, v_k_2445_, v_t_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(lean_object* v_x_2448_, lean_object* v_x_2449_){
_start:
{
switch(lean_obj_tag(v_x_2449_))
{
case 0:
{
lean_object* v_a_2450_; lean_object* v_a_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v_a_2450_ = lean_ctor_get(v_x_2449_, 0);
lean_inc(v_a_2450_);
v_a_2451_ = lean_ctor_get(v_x_2449_, 1);
lean_inc(v_a_2451_);
lean_dec_ref_known(v_x_2449_, 3);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v_a_2450_);
lean_ctor_set(v___x_2452_, 1, v_a_2451_);
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
return v___x_2453_;
}
case 1:
{
lean_object* v_a_2454_; 
v_a_2454_ = lean_ctor_get(v_x_2449_, 1);
lean_inc(v_a_2454_);
if (lean_obj_tag(v_a_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2456_; 
v_a_2455_ = lean_ctor_get(v_x_2449_, 2);
lean_inc(v_a_2455_);
lean_dec_ref_known(v_x_2449_, 3);
v___x_2456_ = l_List_head_x3f___redArg(v_a_2455_);
lean_dec(v_a_2455_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_inc(v_x_2448_);
return v_x_2448_;
}
else
{
return v___x_2456_;
}
}
else
{
lean_object* v_val_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec_ref_known(v_x_2449_, 3);
v_val_2457_ = lean_ctor_get(v_a_2454_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v_a_2454_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v_a_2454_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_val_2457_);
lean_dec(v_a_2454_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_val_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
default: 
{
lean_dec_ref_known(v_x_2449_, 3);
lean_inc(v_x_2448_);
return v_x_2448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* v_x_2465_, lean_object* v_x_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(v_x_2465_, v_x_2466_);
lean_dec(v_x_2465_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(lean_object* v_inst_2469_, lean_object* v_k_2470_, lean_object* v_t_2471_){
_start:
{
lean_object* v___f_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___f_2472_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0));
v___x_2473_ = lean_apply_1(v_inst_2469_, v_k_2470_);
v___x_2474_ = lean_box(0);
v___x_2475_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___x_2473_, v___x_2474_, v___f_2472_, v_t_2471_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27(lean_object* v_00_u03b1_2476_, lean_object* v_00_u03b2_2477_, lean_object* v_inst_2478_, lean_object* v_k_2479_, lean_object* v_t_2480_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(v_inst_2478_, v_k_2479_, v_t_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_x_2482_, lean_object* v_x_2483_, lean_object* v_h__1_2484_, lean_object* v_h__2_2485_, lean_object* v_h__3_2486_){
_start:
{
switch(lean_obj_tag(v_x_2483_))
{
case 0:
{
lean_object* v_a_2487_; lean_object* v_a_2488_; lean_object* v_a_2489_; lean_object* v___x_2490_; 
lean_dec(v_h__3_2486_);
lean_dec(v_h__2_2485_);
v_a_2487_ = lean_ctor_get(v_x_2483_, 0);
lean_inc(v_a_2487_);
v_a_2488_ = lean_ctor_get(v_x_2483_, 1);
lean_inc(v_a_2488_);
v_a_2489_ = lean_ctor_get(v_x_2483_, 2);
lean_inc(v_a_2489_);
lean_dec_ref_known(v_x_2483_, 3);
v___x_2490_ = lean_apply_5(v_h__1_2484_, v_x_2482_, v_a_2487_, lean_box(0), v_a_2488_, v_a_2489_);
return v___x_2490_;
}
case 1:
{
lean_object* v_a_2491_; lean_object* v_a_2492_; lean_object* v_a_2493_; lean_object* v___x_2494_; 
lean_dec(v_h__3_2486_);
lean_dec(v_h__1_2484_);
v_a_2491_ = lean_ctor_get(v_x_2483_, 0);
lean_inc(v_a_2491_);
v_a_2492_ = lean_ctor_get(v_x_2483_, 1);
lean_inc(v_a_2492_);
v_a_2493_ = lean_ctor_get(v_x_2483_, 2);
lean_inc(v_a_2493_);
lean_dec_ref_known(v_x_2483_, 3);
v___x_2494_ = lean_apply_4(v_h__2_2485_, v_x_2482_, v_a_2491_, v_a_2492_, v_a_2493_);
return v___x_2494_;
}
default: 
{
lean_object* v_a_2495_; lean_object* v_a_2496_; lean_object* v_a_2497_; lean_object* v___x_2498_; 
lean_dec(v_h__2_2485_);
lean_dec(v_h__1_2484_);
v_a_2495_ = lean_ctor_get(v_x_2483_, 0);
lean_inc(v_a_2495_);
v_a_2496_ = lean_ctor_get(v_x_2483_, 1);
lean_inc(v_a_2496_);
v_a_2497_ = lean_ctor_get(v_x_2483_, 2);
lean_inc(v_a_2497_);
lean_dec_ref_known(v_x_2483_, 3);
v___x_2498_ = lean_apply_5(v_h__3_2486_, v_x_2482_, v_a_2495_, v_a_2496_, lean_box(0), v_a_2497_);
return v___x_2498_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_2499_, lean_object* v_00_u03b2_2500_, lean_object* v_inst_2501_, lean_object* v_k_2502_, lean_object* v_motive_2503_, lean_object* v_x_2504_, lean_object* v_x_2505_, lean_object* v_h__1_2506_, lean_object* v_h__2_2507_, lean_object* v_h__3_2508_){
_start:
{
switch(lean_obj_tag(v_x_2505_))
{
case 0:
{
lean_object* v_a_2509_; lean_object* v_a_2510_; lean_object* v_a_2511_; lean_object* v___x_2512_; 
lean_dec(v_h__3_2508_);
lean_dec(v_h__2_2507_);
v_a_2509_ = lean_ctor_get(v_x_2505_, 0);
lean_inc(v_a_2509_);
v_a_2510_ = lean_ctor_get(v_x_2505_, 1);
lean_inc(v_a_2510_);
v_a_2511_ = lean_ctor_get(v_x_2505_, 2);
lean_inc(v_a_2511_);
lean_dec_ref_known(v_x_2505_, 3);
v___x_2512_ = lean_apply_5(v_h__1_2506_, v_x_2504_, v_a_2509_, lean_box(0), v_a_2510_, v_a_2511_);
return v___x_2512_;
}
case 1:
{
lean_object* v_a_2513_; lean_object* v_a_2514_; lean_object* v_a_2515_; lean_object* v___x_2516_; 
lean_dec(v_h__3_2508_);
lean_dec(v_h__1_2506_);
v_a_2513_ = lean_ctor_get(v_x_2505_, 0);
lean_inc(v_a_2513_);
v_a_2514_ = lean_ctor_get(v_x_2505_, 1);
lean_inc(v_a_2514_);
v_a_2515_ = lean_ctor_get(v_x_2505_, 2);
lean_inc(v_a_2515_);
lean_dec_ref_known(v_x_2505_, 3);
v___x_2516_ = lean_apply_4(v_h__2_2507_, v_x_2504_, v_a_2513_, v_a_2514_, v_a_2515_);
return v___x_2516_;
}
default: 
{
lean_object* v_a_2517_; lean_object* v_a_2518_; lean_object* v_a_2519_; lean_object* v___x_2520_; 
lean_dec(v_h__2_2507_);
lean_dec(v_h__1_2506_);
v_a_2517_ = lean_ctor_get(v_x_2505_, 0);
lean_inc(v_a_2517_);
v_a_2518_ = lean_ctor_get(v_x_2505_, 1);
lean_inc(v_a_2518_);
v_a_2519_ = lean_ctor_get(v_x_2505_, 2);
lean_inc(v_a_2519_);
lean_dec_ref_known(v_x_2505_, 3);
v___x_2520_ = lean_apply_5(v_h__3_2508_, v_x_2504_, v_a_2517_, v_a_2518_, lean_box(0), v_a_2519_);
return v___x_2520_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_2521_, lean_object* v_00_u03b2_2522_, lean_object* v_inst_2523_, lean_object* v_k_2524_, lean_object* v_motive_2525_, lean_object* v_x_2526_, lean_object* v_x_2527_, lean_object* v_h__1_2528_, lean_object* v_h__2_2529_, lean_object* v_h__3_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(v_00_u03b1_2521_, v_00_u03b2_2522_, v_inst_2523_, v_k_2524_, v_motive_2525_, v_x_2526_, v_x_2527_, v_h__1_2528_, v_h__2_2529_, v_h__3_2530_);
lean_dec(v_k_2524_);
lean_dec_ref(v_inst_2523_);
return v_res_2531_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(lean_object* v_inst_2532_, lean_object* v_k_2533_, lean_object* v_k_x27_2534_){
_start:
{
lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2535_ = lean_apply_2(v_inst_2532_, v_k_2533_, v_k_x27_2534_);
v___x_2536_ = lean_unbox(v___x_2535_);
if (v___x_2536_ == 1)
{
uint8_t v___x_2537_; 
v___x_2537_ = 2;
return v___x_2537_;
}
else
{
uint8_t v___x_2538_; 
v___x_2538_ = lean_unbox(v___x_2535_);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed(lean_object* v_inst_2539_, lean_object* v_k_2540_, lean_object* v_k_x27_2541_){
_start:
{
uint8_t v_res_2542_; lean_object* v_r_2543_; 
v_res_2542_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(v_inst_2539_, v_k_2540_, v_k_x27_2541_);
v_r_2543_ = lean_box(v_res_2542_);
return v_r_2543_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(lean_object* v_inst_2544_, lean_object* v_k_2545_, lean_object* v_t_2546_){
_start:
{
lean_object* v___f_2547_; lean_object* v___f_2548_; lean_object* v___x_2549_; 
v___f_2547_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2547_, 0, v_inst_2544_);
lean_closure_set(v___f_2547_, 1, v_k_2545_);
v___f_2548_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0));
v___x_2549_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_2547_, v_t_2546_, v___f_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098(lean_object* v_00_u03b1_2550_, lean_object* v_00_u03b2_2551_, lean_object* v_inst_2552_, lean_object* v_k_2553_, lean_object* v_t_2554_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(v_inst_2552_, v_k_2553_, v_t_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(lean_object* v_x_2556_, lean_object* v_x_2557_){
_start:
{
switch(lean_obj_tag(v_x_2557_))
{
case 0:
{
lean_object* v_a_2558_; lean_object* v_a_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v_a_2558_ = lean_ctor_get(v_x_2557_, 0);
v_a_2559_ = lean_ctor_get(v_x_2557_, 1);
lean_inc(v_a_2559_);
lean_inc(v_a_2558_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v_a_2558_);
lean_ctor_set(v___x_2560_, 1, v_a_2559_);
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
return v___x_2561_;
}
case 1:
{
lean_object* v_a_2562_; lean_object* v___x_2563_; 
v_a_2562_ = lean_ctor_get(v_x_2557_, 2);
v___x_2563_ = l_List_head_x3f___redArg(v_a_2562_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_inc(v_x_2556_);
return v_x_2556_;
}
else
{
return v___x_2563_;
}
}
default: 
{
lean_inc(v_x_2556_);
return v_x_2556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* v_x_2564_, lean_object* v_x_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(v_x_2564_, v_x_2565_);
lean_dec_ref(v_x_2565_);
lean_dec(v_x_2564_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(lean_object* v_inst_2568_, lean_object* v_k_2569_, lean_object* v_t_2570_){
_start:
{
lean_object* v___f_2571_; lean_object* v___f_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___f_2571_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2571_, 0, v_inst_2568_);
lean_closure_set(v___f_2571_, 1, v_k_2569_);
v___f_2572_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0));
v___x_2573_ = lean_box(0);
v___x_2574_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___f_2571_, v___x_2573_, v___f_2572_, v_t_2570_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27(lean_object* v_00_u03b1_2575_, lean_object* v_00_u03b2_2576_, lean_object* v_inst_2577_, lean_object* v_k_2578_, lean_object* v_t_2579_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(v_inst_2577_, v_k_2578_, v_t_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(uint8_t v_x_2581_, lean_object* v_h__1_2582_, lean_object* v_h__2_2583_){
_start:
{
if (v_x_2581_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_dec(v_h__2_2583_);
v___x_2584_ = lean_box(0);
v___x_2585_ = lean_apply_1(v_h__1_2582_, v___x_2584_);
return v___x_2585_;
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_dec(v_h__1_2582_);
v___x_2586_ = lean_box(v_x_2581_);
v___x_2587_ = lean_apply_2(v_h__2_2583_, v___x_2586_, lean_box(0));
return v___x_2587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg___boxed(lean_object* v_x_2588_, lean_object* v_h__1_2589_, lean_object* v_h__2_2590_){
_start:
{
uint8_t v_x_13__boxed_2591_; lean_object* v_res_2592_; 
v_x_13__boxed_2591_ = lean_unbox(v_x_2588_);
v_res_2592_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(v_x_13__boxed_2591_, v_h__1_2589_, v_h__2_2590_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(lean_object* v_motive_2593_, uint8_t v_x_2594_, lean_object* v_h__1_2595_, lean_object* v_h__2_2596_){
_start:
{
if (v_x_2594_ == 0)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_dec(v_h__2_2596_);
v___x_2597_ = lean_box(0);
v___x_2598_ = lean_apply_1(v_h__1_2595_, v___x_2597_);
return v___x_2598_;
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec(v_h__1_2595_);
v___x_2599_ = lean_box(v_x_2594_);
v___x_2600_ = lean_apply_2(v_h__2_2596_, v___x_2599_, lean_box(0));
return v___x_2600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___boxed(lean_object* v_motive_2601_, lean_object* v_x_2602_, lean_object* v_h__1_2603_, lean_object* v_h__2_2604_){
_start:
{
uint8_t v_x_24__boxed_2605_; lean_object* v_res_2606_; 
v_x_24__boxed_2605_ = lean_unbox(v_x_2602_);
v_res_2606_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(v_motive_2601_, v_x_24__boxed_2605_, v_h__1_2603_, v_h__2_2604_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_x_2607_, lean_object* v_x_2608_, lean_object* v_h__1_2609_, lean_object* v_h__2_2610_, lean_object* v_h__3_2611_){
_start:
{
switch(lean_obj_tag(v_x_2608_))
{
case 0:
{
lean_object* v_a_2612_; lean_object* v_a_2613_; lean_object* v_a_2614_; lean_object* v___x_2615_; 
lean_dec(v_h__3_2611_);
lean_dec(v_h__2_2610_);
v_a_2612_ = lean_ctor_get(v_x_2608_, 0);
lean_inc(v_a_2612_);
v_a_2613_ = lean_ctor_get(v_x_2608_, 1);
lean_inc(v_a_2613_);
v_a_2614_ = lean_ctor_get(v_x_2608_, 2);
lean_inc(v_a_2614_);
lean_dec_ref_known(v_x_2608_, 3);
v___x_2615_ = lean_apply_5(v_h__1_2609_, v_x_2607_, v_a_2612_, lean_box(0), v_a_2613_, v_a_2614_);
return v___x_2615_;
}
case 1:
{
lean_object* v_a_2616_; lean_object* v_a_2617_; lean_object* v_a_2618_; lean_object* v___x_2619_; 
lean_dec(v_h__3_2611_);
lean_dec(v_h__1_2609_);
v_a_2616_ = lean_ctor_get(v_x_2608_, 0);
lean_inc(v_a_2616_);
v_a_2617_ = lean_ctor_get(v_x_2608_, 1);
lean_inc(v_a_2617_);
v_a_2618_ = lean_ctor_get(v_x_2608_, 2);
lean_inc(v_a_2618_);
lean_dec_ref_known(v_x_2608_, 3);
v___x_2619_ = lean_apply_4(v_h__2_2610_, v_x_2607_, v_a_2616_, v_a_2617_, v_a_2618_);
return v___x_2619_;
}
default: 
{
lean_object* v_a_2620_; lean_object* v_a_2621_; lean_object* v_a_2622_; lean_object* v___x_2623_; 
lean_dec(v_h__2_2610_);
lean_dec(v_h__1_2609_);
v_a_2620_ = lean_ctor_get(v_x_2608_, 0);
lean_inc(v_a_2620_);
v_a_2621_ = lean_ctor_get(v_x_2608_, 1);
lean_inc(v_a_2621_);
v_a_2622_ = lean_ctor_get(v_x_2608_, 2);
lean_inc(v_a_2622_);
lean_dec_ref_known(v_x_2608_, 3);
v___x_2623_ = lean_apply_5(v_h__3_2611_, v_x_2607_, v_a_2620_, v_a_2621_, lean_box(0), v_a_2622_);
return v___x_2623_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_2624_, lean_object* v_00_u03b2_2625_, lean_object* v_inst_2626_, lean_object* v_k_2627_, lean_object* v_motive_2628_, lean_object* v_x_2629_, lean_object* v_x_2630_, lean_object* v_h__1_2631_, lean_object* v_h__2_2632_, lean_object* v_h__3_2633_){
_start:
{
switch(lean_obj_tag(v_x_2630_))
{
case 0:
{
lean_object* v_a_2634_; lean_object* v_a_2635_; lean_object* v_a_2636_; lean_object* v___x_2637_; 
lean_dec(v_h__3_2633_);
lean_dec(v_h__2_2632_);
v_a_2634_ = lean_ctor_get(v_x_2630_, 0);
lean_inc(v_a_2634_);
v_a_2635_ = lean_ctor_get(v_x_2630_, 1);
lean_inc(v_a_2635_);
v_a_2636_ = lean_ctor_get(v_x_2630_, 2);
lean_inc(v_a_2636_);
lean_dec_ref_known(v_x_2630_, 3);
v___x_2637_ = lean_apply_5(v_h__1_2631_, v_x_2629_, v_a_2634_, lean_box(0), v_a_2635_, v_a_2636_);
return v___x_2637_;
}
case 1:
{
lean_object* v_a_2638_; lean_object* v_a_2639_; lean_object* v_a_2640_; lean_object* v___x_2641_; 
lean_dec(v_h__3_2633_);
lean_dec(v_h__1_2631_);
v_a_2638_ = lean_ctor_get(v_x_2630_, 0);
lean_inc(v_a_2638_);
v_a_2639_ = lean_ctor_get(v_x_2630_, 1);
lean_inc(v_a_2639_);
v_a_2640_ = lean_ctor_get(v_x_2630_, 2);
lean_inc(v_a_2640_);
lean_dec_ref_known(v_x_2630_, 3);
v___x_2641_ = lean_apply_4(v_h__2_2632_, v_x_2629_, v_a_2638_, v_a_2639_, v_a_2640_);
return v___x_2641_;
}
default: 
{
lean_object* v_a_2642_; lean_object* v_a_2643_; lean_object* v_a_2644_; lean_object* v___x_2645_; 
lean_dec(v_h__2_2632_);
lean_dec(v_h__1_2631_);
v_a_2642_ = lean_ctor_get(v_x_2630_, 0);
lean_inc(v_a_2642_);
v_a_2643_ = lean_ctor_get(v_x_2630_, 1);
lean_inc(v_a_2643_);
v_a_2644_ = lean_ctor_get(v_x_2630_, 2);
lean_inc(v_a_2644_);
lean_dec_ref_known(v_x_2630_, 3);
v___x_2645_ = lean_apply_5(v_h__3_2633_, v_x_2629_, v_a_2642_, v_a_2643_, lean_box(0), v_a_2644_);
return v___x_2645_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_2646_, lean_object* v_00_u03b2_2647_, lean_object* v_inst_2648_, lean_object* v_k_2649_, lean_object* v_motive_2650_, lean_object* v_x_2651_, lean_object* v_x_2652_, lean_object* v_h__1_2653_, lean_object* v_h__2_2654_, lean_object* v_h__3_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(v_00_u03b1_2646_, v_00_u03b2_2647_, v_inst_2648_, v_k_2649_, v_motive_2650_, v_x_2651_, v_x_2652_, v_h__1_2653_, v_h__2_2654_, v_h__3_2655_);
lean_dec(v_k_2649_);
lean_dec_ref(v_inst_2648_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(uint8_t v_x_2657_, lean_object* v_h__1_2658_, lean_object* v_h__2_2659_){
_start:
{
if (v_x_2657_ == 2)
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
lean_dec(v_h__2_2659_);
v___x_2660_ = lean_box(0);
v___x_2661_ = lean_apply_1(v_h__1_2658_, v___x_2660_);
return v___x_2661_;
}
else
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
lean_dec(v_h__1_2658_);
v___x_2662_ = lean_box(v_x_2657_);
v___x_2663_ = lean_apply_2(v_h__2_2659_, v___x_2662_, lean_box(0));
return v___x_2663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg___boxed(lean_object* v_x_2664_, lean_object* v_h__1_2665_, lean_object* v_h__2_2666_){
_start:
{
uint8_t v_x_13__boxed_2667_; lean_object* v_res_2668_; 
v_x_13__boxed_2667_ = lean_unbox(v_x_2664_);
v_res_2668_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(v_x_13__boxed_2667_, v_h__1_2665_, v_h__2_2666_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(lean_object* v_motive_2669_, uint8_t v_x_2670_, lean_object* v_h__1_2671_, lean_object* v_h__2_2672_){
_start:
{
if (v_x_2670_ == 2)
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_dec(v_h__2_2672_);
v___x_2673_ = lean_box(0);
v___x_2674_ = lean_apply_1(v_h__1_2671_, v___x_2673_);
return v___x_2674_;
}
else
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
lean_dec(v_h__1_2671_);
v___x_2675_ = lean_box(v_x_2670_);
v___x_2676_ = lean_apply_2(v_h__2_2672_, v___x_2675_, lean_box(0));
return v___x_2676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___boxed(lean_object* v_motive_2677_, lean_object* v_x_2678_, lean_object* v_h__1_2679_, lean_object* v_h__2_2680_){
_start:
{
uint8_t v_x_24__boxed_2681_; lean_object* v_res_2682_; 
v_x_24__boxed_2681_ = lean_unbox(v_x_2678_);
v_res_2682_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(v_motive_2677_, v_x_24__boxed_2681_, v_h__1_2679_, v_h__2_2680_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(uint8_t v_x_2683_, lean_object* v_h__1_2684_, lean_object* v_h__2_2685_, lean_object* v_h__3_2686_){
_start:
{
switch(v_x_2683_)
{
case 0:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
lean_dec(v_h__3_2686_);
lean_dec(v_h__2_2685_);
v___x_2687_ = lean_box(0);
v___x_2688_ = lean_apply_1(v_h__1_2684_, v___x_2687_);
return v___x_2688_;
}
case 1:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
lean_dec(v_h__3_2686_);
lean_dec(v_h__1_2684_);
v___x_2689_ = lean_box(0);
v___x_2690_ = lean_apply_1(v_h__2_2685_, v___x_2689_);
return v___x_2690_;
}
default: 
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_dec(v_h__2_2685_);
lean_dec(v_h__1_2684_);
v___x_2691_ = lean_box(0);
v___x_2692_ = lean_apply_1(v_h__3_2686_, v___x_2691_);
return v___x_2692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object* v_x_2693_, lean_object* v_h__1_2694_, lean_object* v_h__2_2695_, lean_object* v_h__3_2696_){
_start:
{
uint8_t v_x_33__boxed_2697_; lean_object* v_res_2698_; 
v_x_33__boxed_2697_ = lean_unbox(v_x_2693_);
v_res_2698_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(v_x_33__boxed_2697_, v_h__1_2694_, v_h__2_2695_, v_h__3_2696_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(lean_object* v_motive_2699_, uint8_t v_x_2700_, lean_object* v_h__1_2701_, lean_object* v_h__2_2702_, lean_object* v_h__3_2703_){
_start:
{
switch(v_x_2700_)
{
case 0:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
lean_dec(v_h__3_2703_);
lean_dec(v_h__2_2702_);
v___x_2704_ = lean_box(0);
v___x_2705_ = lean_apply_1(v_h__1_2701_, v___x_2704_);
return v___x_2705_;
}
case 1:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
lean_dec(v_h__3_2703_);
lean_dec(v_h__1_2701_);
v___x_2706_ = lean_box(0);
v___x_2707_ = lean_apply_1(v_h__2_2702_, v___x_2706_);
return v___x_2707_;
}
default: 
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_dec(v_h__2_2702_);
lean_dec(v_h__1_2701_);
v___x_2708_ = lean_box(0);
v___x_2709_ = lean_apply_1(v_h__3_2703_, v___x_2708_);
return v___x_2709_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___boxed(lean_object* v_motive_2710_, lean_object* v_x_2711_, lean_object* v_h__1_2712_, lean_object* v_h__2_2713_, lean_object* v_h__3_2714_){
_start:
{
uint8_t v_x_48__boxed_2715_; lean_object* v_res_2716_; 
v_x_48__boxed_2715_ = lean_unbox(v_x_2711_);
v_res_2716_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(v_motive_2710_, v_x_48__boxed_2715_, v_h__1_2712_, v_h__2_2713_, v_h__3_2714_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___redArg(lean_object* v_x_2717_, lean_object* v_h__1_2718_, lean_object* v_h__2_2719_){
_start:
{
if (lean_obj_tag(v_x_2717_) == 0)
{
lean_object* v_size_2720_; lean_object* v_k_2721_; lean_object* v_v_2722_; lean_object* v_l_2723_; lean_object* v_r_2724_; lean_object* v___x_2725_; 
lean_dec(v_h__1_2718_);
v_size_2720_ = lean_ctor_get(v_x_2717_, 0);
lean_inc(v_size_2720_);
v_k_2721_ = lean_ctor_get(v_x_2717_, 1);
lean_inc(v_k_2721_);
v_v_2722_ = lean_ctor_get(v_x_2717_, 2);
lean_inc(v_v_2722_);
v_l_2723_ = lean_ctor_get(v_x_2717_, 3);
lean_inc(v_l_2723_);
v_r_2724_ = lean_ctor_get(v_x_2717_, 4);
lean_inc(v_r_2724_);
lean_dec_ref_known(v_x_2717_, 5);
v___x_2725_ = lean_apply_7(v_h__2_2719_, v_size_2720_, v_k_2721_, v_v_2722_, v_l_2723_, v_r_2724_, lean_box(0), lean_box(0));
return v___x_2725_;
}
else
{
lean_object* v___x_2726_; 
lean_dec(v_h__2_2719_);
v___x_2726_ = lean_apply_2(v_h__1_2718_, lean_box(0), lean_box(0));
return v___x_2726_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(lean_object* v_00_u03b1_2727_, lean_object* v_00_u03b2_2728_, lean_object* v_inst_2729_, lean_object* v_k_2730_, lean_object* v_motive_2731_, lean_object* v_x_2732_, lean_object* v_x_2733_, lean_object* v_x_2734_, lean_object* v_h__1_2735_, lean_object* v_h__2_2736_){
_start:
{
if (lean_obj_tag(v_x_2732_) == 0)
{
lean_object* v_size_2737_; lean_object* v_k_2738_; lean_object* v_v_2739_; lean_object* v_l_2740_; lean_object* v_r_2741_; lean_object* v___x_2742_; 
lean_dec(v_h__1_2735_);
v_size_2737_ = lean_ctor_get(v_x_2732_, 0);
lean_inc(v_size_2737_);
v_k_2738_ = lean_ctor_get(v_x_2732_, 1);
lean_inc(v_k_2738_);
v_v_2739_ = lean_ctor_get(v_x_2732_, 2);
lean_inc(v_v_2739_);
v_l_2740_ = lean_ctor_get(v_x_2732_, 3);
lean_inc(v_l_2740_);
v_r_2741_ = lean_ctor_get(v_x_2732_, 4);
lean_inc(v_r_2741_);
lean_dec_ref_known(v_x_2732_, 5);
v___x_2742_ = lean_apply_7(v_h__2_2736_, v_size_2737_, v_k_2738_, v_v_2739_, v_l_2740_, v_r_2741_, lean_box(0), lean_box(0));
return v___x_2742_;
}
else
{
lean_object* v___x_2743_; 
lean_dec(v_h__2_2736_);
v___x_2743_ = lean_apply_2(v_h__1_2735_, lean_box(0), lean_box(0));
return v___x_2743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___boxed(lean_object* v_00_u03b1_2744_, lean_object* v_00_u03b2_2745_, lean_object* v_inst_2746_, lean_object* v_k_2747_, lean_object* v_motive_2748_, lean_object* v_x_2749_, lean_object* v_x_2750_, lean_object* v_x_2751_, lean_object* v_h__1_2752_, lean_object* v_h__2_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(v_00_u03b1_2744_, v_00_u03b2_2745_, v_inst_2746_, v_k_2747_, v_motive_2748_, v_x_2749_, v_x_2750_, v_x_2751_, v_h__1_2752_, v_h__2_2753_);
lean_dec(v_k_2747_);
lean_dec_ref(v_inst_2746_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___redArg(lean_object* v_x_2755_, lean_object* v_h__1_2756_, lean_object* v_h__2_2757_){
_start:
{
if (lean_obj_tag(v_x_2755_) == 0)
{
lean_object* v_size_2758_; lean_object* v_k_2759_; lean_object* v_v_2760_; lean_object* v_l_2761_; lean_object* v_r_2762_; lean_object* v___x_2763_; 
lean_dec(v_h__1_2756_);
v_size_2758_ = lean_ctor_get(v_x_2755_, 0);
lean_inc(v_size_2758_);
v_k_2759_ = lean_ctor_get(v_x_2755_, 1);
lean_inc(v_k_2759_);
v_v_2760_ = lean_ctor_get(v_x_2755_, 2);
lean_inc(v_v_2760_);
v_l_2761_ = lean_ctor_get(v_x_2755_, 3);
lean_inc(v_l_2761_);
v_r_2762_ = lean_ctor_get(v_x_2755_, 4);
lean_inc(v_r_2762_);
lean_dec_ref_known(v_x_2755_, 5);
v___x_2763_ = lean_apply_7(v_h__2_2757_, v_size_2758_, v_k_2759_, v_v_2760_, v_l_2761_, v_r_2762_, lean_box(0), lean_box(0));
return v___x_2763_;
}
else
{
lean_object* v___x_2764_; 
lean_dec(v_h__2_2757_);
v___x_2764_ = lean_apply_2(v_h__1_2756_, lean_box(0), lean_box(0));
return v___x_2764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(lean_object* v_00_u03b1_2765_, lean_object* v_00_u03b2_2766_, lean_object* v_inst_2767_, lean_object* v_k_2768_, lean_object* v_motive_2769_, lean_object* v_x_2770_, lean_object* v_x_2771_, lean_object* v_x_2772_, lean_object* v_h__1_2773_, lean_object* v_h__2_2774_){
_start:
{
if (lean_obj_tag(v_x_2770_) == 0)
{
lean_object* v_size_2775_; lean_object* v_k_2776_; lean_object* v_v_2777_; lean_object* v_l_2778_; lean_object* v_r_2779_; lean_object* v___x_2780_; 
lean_dec(v_h__1_2773_);
v_size_2775_ = lean_ctor_get(v_x_2770_, 0);
lean_inc(v_size_2775_);
v_k_2776_ = lean_ctor_get(v_x_2770_, 1);
lean_inc(v_k_2776_);
v_v_2777_ = lean_ctor_get(v_x_2770_, 2);
lean_inc(v_v_2777_);
v_l_2778_ = lean_ctor_get(v_x_2770_, 3);
lean_inc(v_l_2778_);
v_r_2779_ = lean_ctor_get(v_x_2770_, 4);
lean_inc(v_r_2779_);
lean_dec_ref_known(v_x_2770_, 5);
v___x_2780_ = lean_apply_7(v_h__2_2774_, v_size_2775_, v_k_2776_, v_v_2777_, v_l_2778_, v_r_2779_, lean_box(0), lean_box(0));
return v___x_2780_;
}
else
{
lean_object* v___x_2781_; 
lean_dec(v_h__2_2774_);
v___x_2781_ = lean_apply_2(v_h__1_2773_, lean_box(0), lean_box(0));
return v___x_2781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___boxed(lean_object* v_00_u03b1_2782_, lean_object* v_00_u03b2_2783_, lean_object* v_inst_2784_, lean_object* v_k_2785_, lean_object* v_motive_2786_, lean_object* v_x_2787_, lean_object* v_x_2788_, lean_object* v_x_2789_, lean_object* v_h__1_2790_, lean_object* v_h__2_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(v_00_u03b1_2782_, v_00_u03b2_2783_, v_inst_2784_, v_k_2785_, v_motive_2786_, v_x_2787_, v_x_2788_, v_x_2789_, v_h__1_2790_, v_h__2_2791_);
lean_dec(v_k_2785_);
lean_dec_ref(v_inst_2784_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___redArg(lean_object* v_x_2793_, lean_object* v_h__1_2794_, lean_object* v_h__2_2795_){
_start:
{
if (lean_obj_tag(v_x_2793_) == 0)
{
lean_object* v_size_2796_; lean_object* v_k_2797_; lean_object* v_v_2798_; lean_object* v_l_2799_; lean_object* v_r_2800_; lean_object* v___x_2801_; 
lean_dec(v_h__1_2794_);
v_size_2796_ = lean_ctor_get(v_x_2793_, 0);
lean_inc(v_size_2796_);
v_k_2797_ = lean_ctor_get(v_x_2793_, 1);
lean_inc(v_k_2797_);
v_v_2798_ = lean_ctor_get(v_x_2793_, 2);
lean_inc(v_v_2798_);
v_l_2799_ = lean_ctor_get(v_x_2793_, 3);
lean_inc(v_l_2799_);
v_r_2800_ = lean_ctor_get(v_x_2793_, 4);
lean_inc(v_r_2800_);
lean_dec_ref_known(v_x_2793_, 5);
v___x_2801_ = lean_apply_7(v_h__2_2795_, v_size_2796_, v_k_2797_, v_v_2798_, v_l_2799_, v_r_2800_, lean_box(0), lean_box(0));
return v___x_2801_;
}
else
{
lean_object* v___x_2802_; 
lean_dec(v_h__2_2795_);
v___x_2802_ = lean_apply_2(v_h__1_2794_, lean_box(0), lean_box(0));
return v___x_2802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(lean_object* v_00_u03b1_2803_, lean_object* v_00_u03b2_2804_, lean_object* v_inst_2805_, lean_object* v_k_2806_, lean_object* v_motive_2807_, lean_object* v_x_2808_, lean_object* v_x_2809_, lean_object* v_x_2810_, lean_object* v_h__1_2811_, lean_object* v_h__2_2812_){
_start:
{
if (lean_obj_tag(v_x_2808_) == 0)
{
lean_object* v_size_2813_; lean_object* v_k_2814_; lean_object* v_v_2815_; lean_object* v_l_2816_; lean_object* v_r_2817_; lean_object* v___x_2818_; 
lean_dec(v_h__1_2811_);
v_size_2813_ = lean_ctor_get(v_x_2808_, 0);
lean_inc(v_size_2813_);
v_k_2814_ = lean_ctor_get(v_x_2808_, 1);
lean_inc(v_k_2814_);
v_v_2815_ = lean_ctor_get(v_x_2808_, 2);
lean_inc(v_v_2815_);
v_l_2816_ = lean_ctor_get(v_x_2808_, 3);
lean_inc(v_l_2816_);
v_r_2817_ = lean_ctor_get(v_x_2808_, 4);
lean_inc(v_r_2817_);
lean_dec_ref_known(v_x_2808_, 5);
v___x_2818_ = lean_apply_7(v_h__2_2812_, v_size_2813_, v_k_2814_, v_v_2815_, v_l_2816_, v_r_2817_, lean_box(0), lean_box(0));
return v___x_2818_;
}
else
{
lean_object* v___x_2819_; 
lean_dec(v_h__2_2812_);
v___x_2819_ = lean_apply_2(v_h__1_2811_, lean_box(0), lean_box(0));
return v___x_2819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___boxed(lean_object* v_00_u03b1_2820_, lean_object* v_00_u03b2_2821_, lean_object* v_inst_2822_, lean_object* v_k_2823_, lean_object* v_motive_2824_, lean_object* v_x_2825_, lean_object* v_x_2826_, lean_object* v_x_2827_, lean_object* v_h__1_2828_, lean_object* v_h__2_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(v_00_u03b1_2820_, v_00_u03b2_2821_, v_inst_2822_, v_k_2823_, v_motive_2824_, v_x_2825_, v_x_2826_, v_x_2827_, v_h__1_2828_, v_h__2_2829_);
lean_dec(v_k_2823_);
lean_dec_ref(v_inst_2822_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(uint8_t v_x_2831_, lean_object* v_h__1_2832_, lean_object* v_h__2_2833_, lean_object* v_h__3_2834_){
_start:
{
switch(v_x_2831_)
{
case 0:
{
lean_object* v___x_2835_; 
lean_dec(v_h__2_2833_);
lean_dec(v_h__1_2832_);
v___x_2835_ = lean_apply_1(v_h__3_2834_, lean_box(0));
return v___x_2835_;
}
case 1:
{
lean_object* v___x_2836_; 
lean_dec(v_h__3_2834_);
lean_dec(v_h__1_2832_);
v___x_2836_ = lean_apply_1(v_h__2_2833_, lean_box(0));
return v___x_2836_;
}
default: 
{
lean_object* v___x_2837_; 
lean_dec(v_h__3_2834_);
lean_dec(v_h__2_2833_);
v___x_2837_ = lean_apply_1(v_h__1_2832_, lean_box(0));
return v___x_2837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg___boxed(lean_object* v_x_2838_, lean_object* v_h__1_2839_, lean_object* v_h__2_2840_, lean_object* v_h__3_2841_){
_start:
{
uint8_t v_x_33__boxed_2842_; lean_object* v_res_2843_; 
v_x_33__boxed_2842_ = lean_unbox(v_x_2838_);
v_res_2843_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(v_x_33__boxed_2842_, v_h__1_2839_, v_h__2_2840_, v_h__3_2841_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(lean_object* v_motive_2844_, uint8_t v_x_2845_, lean_object* v_h__1_2846_, lean_object* v_h__2_2847_, lean_object* v_h__3_2848_){
_start:
{
switch(v_x_2845_)
{
case 0:
{
lean_object* v___x_2849_; 
lean_dec(v_h__2_2847_);
lean_dec(v_h__1_2846_);
v___x_2849_ = lean_apply_1(v_h__3_2848_, lean_box(0));
return v___x_2849_;
}
case 1:
{
lean_object* v___x_2850_; 
lean_dec(v_h__3_2848_);
lean_dec(v_h__1_2846_);
v___x_2850_ = lean_apply_1(v_h__2_2847_, lean_box(0));
return v___x_2850_;
}
default: 
{
lean_object* v___x_2851_; 
lean_dec(v_h__3_2848_);
lean_dec(v_h__2_2847_);
v___x_2851_ = lean_apply_1(v_h__1_2846_, lean_box(0));
return v___x_2851_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___boxed(lean_object* v_motive_2852_, lean_object* v_x_2853_, lean_object* v_h__1_2854_, lean_object* v_h__2_2855_, lean_object* v_h__3_2856_){
_start:
{
uint8_t v_x_42__boxed_2857_; lean_object* v_res_2858_; 
v_x_42__boxed_2857_ = lean_unbox(v_x_2853_);
v_res_2858_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(v_motive_2852_, v_x_42__boxed_2857_, v_h__1_2854_, v_h__2_2855_, v_h__3_2856_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___redArg(lean_object* v_x_2859_, lean_object* v_h__1_2860_, lean_object* v_h__2_2861_){
_start:
{
if (lean_obj_tag(v_x_2859_) == 0)
{
lean_object* v_size_2862_; lean_object* v_k_2863_; lean_object* v_v_2864_; lean_object* v_l_2865_; lean_object* v_r_2866_; lean_object* v___x_2867_; 
lean_dec(v_h__1_2860_);
v_size_2862_ = lean_ctor_get(v_x_2859_, 0);
lean_inc(v_size_2862_);
v_k_2863_ = lean_ctor_get(v_x_2859_, 1);
lean_inc(v_k_2863_);
v_v_2864_ = lean_ctor_get(v_x_2859_, 2);
lean_inc(v_v_2864_);
v_l_2865_ = lean_ctor_get(v_x_2859_, 3);
lean_inc(v_l_2865_);
v_r_2866_ = lean_ctor_get(v_x_2859_, 4);
lean_inc(v_r_2866_);
lean_dec_ref_known(v_x_2859_, 5);
v___x_2867_ = lean_apply_7(v_h__2_2861_, v_size_2862_, v_k_2863_, v_v_2864_, v_l_2865_, v_r_2866_, lean_box(0), lean_box(0));
return v___x_2867_;
}
else
{
lean_object* v___x_2868_; 
lean_dec(v_h__2_2861_);
v___x_2868_ = lean_apply_2(v_h__1_2860_, lean_box(0), lean_box(0));
return v___x_2868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(lean_object* v_00_u03b1_2869_, lean_object* v_00_u03b2_2870_, lean_object* v_inst_2871_, lean_object* v_k_2872_, lean_object* v_motive_2873_, lean_object* v_x_2874_, lean_object* v_x_2875_, lean_object* v_x_2876_, lean_object* v_h__1_2877_, lean_object* v_h__2_2878_){
_start:
{
if (lean_obj_tag(v_x_2874_) == 0)
{
lean_object* v_size_2879_; lean_object* v_k_2880_; lean_object* v_v_2881_; lean_object* v_l_2882_; lean_object* v_r_2883_; lean_object* v___x_2884_; 
lean_dec(v_h__1_2877_);
v_size_2879_ = lean_ctor_get(v_x_2874_, 0);
lean_inc(v_size_2879_);
v_k_2880_ = lean_ctor_get(v_x_2874_, 1);
lean_inc(v_k_2880_);
v_v_2881_ = lean_ctor_get(v_x_2874_, 2);
lean_inc(v_v_2881_);
v_l_2882_ = lean_ctor_get(v_x_2874_, 3);
lean_inc(v_l_2882_);
v_r_2883_ = lean_ctor_get(v_x_2874_, 4);
lean_inc(v_r_2883_);
lean_dec_ref_known(v_x_2874_, 5);
v___x_2884_ = lean_apply_7(v_h__2_2878_, v_size_2879_, v_k_2880_, v_v_2881_, v_l_2882_, v_r_2883_, lean_box(0), lean_box(0));
return v___x_2884_;
}
else
{
lean_object* v___x_2885_; 
lean_dec(v_h__2_2878_);
v___x_2885_ = lean_apply_2(v_h__1_2877_, lean_box(0), lean_box(0));
return v___x_2885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___boxed(lean_object* v_00_u03b1_2886_, lean_object* v_00_u03b2_2887_, lean_object* v_inst_2888_, lean_object* v_k_2889_, lean_object* v_motive_2890_, lean_object* v_x_2891_, lean_object* v_x_2892_, lean_object* v_x_2893_, lean_object* v_h__1_2894_, lean_object* v_h__2_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(v_00_u03b1_2886_, v_00_u03b2_2887_, v_inst_2888_, v_k_2889_, v_motive_2890_, v_x_2891_, v_x_2892_, v_x_2893_, v_h__1_2894_, v_h__2_2895_);
lean_dec(v_k_2889_);
lean_dec_ref(v_inst_2888_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(lean_object* v_x_2897_, lean_object* v_x_2898_, lean_object* v_h__1_2899_, lean_object* v_h__2_2900_){
_start:
{
if (lean_obj_tag(v_x_2897_) == 0)
{
lean_object* v_size_2901_; lean_object* v_k_2902_; lean_object* v_v_2903_; lean_object* v_l_2904_; lean_object* v_r_2905_; lean_object* v___x_2906_; 
lean_dec(v_h__1_2899_);
v_size_2901_ = lean_ctor_get(v_x_2897_, 0);
lean_inc(v_size_2901_);
v_k_2902_ = lean_ctor_get(v_x_2897_, 1);
lean_inc(v_k_2902_);
v_v_2903_ = lean_ctor_get(v_x_2897_, 2);
lean_inc(v_v_2903_);
v_l_2904_ = lean_ctor_get(v_x_2897_, 3);
lean_inc(v_l_2904_);
v_r_2905_ = lean_ctor_get(v_x_2897_, 4);
lean_inc(v_r_2905_);
lean_dec_ref_known(v_x_2897_, 5);
v___x_2906_ = lean_apply_6(v_h__2_2900_, v_size_2901_, v_k_2902_, v_v_2903_, v_l_2904_, v_r_2905_, v_x_2898_);
return v___x_2906_;
}
else
{
lean_object* v___x_2907_; 
lean_dec(v_h__2_2900_);
v___x_2907_ = lean_apply_1(v_h__1_2899_, v_x_2898_);
return v___x_2907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter(lean_object* v_00_u03b1_2908_, lean_object* v_00_u03b2_2909_, lean_object* v_motive_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_, lean_object* v_h__1_2913_, lean_object* v_h__2_2914_){
_start:
{
if (lean_obj_tag(v_x_2911_) == 0)
{
lean_object* v_size_2915_; lean_object* v_k_2916_; lean_object* v_v_2917_; lean_object* v_l_2918_; lean_object* v_r_2919_; lean_object* v___x_2920_; 
lean_dec(v_h__1_2913_);
v_size_2915_ = lean_ctor_get(v_x_2911_, 0);
lean_inc(v_size_2915_);
v_k_2916_ = lean_ctor_get(v_x_2911_, 1);
lean_inc(v_k_2916_);
v_v_2917_ = lean_ctor_get(v_x_2911_, 2);
lean_inc(v_v_2917_);
v_l_2918_ = lean_ctor_get(v_x_2911_, 3);
lean_inc(v_l_2918_);
v_r_2919_ = lean_ctor_get(v_x_2911_, 4);
lean_inc(v_r_2919_);
lean_dec_ref_known(v_x_2911_, 5);
v___x_2920_ = lean_apply_6(v_h__2_2914_, v_size_2915_, v_k_2916_, v_v_2917_, v_l_2918_, v_r_2919_, v_x_2912_);
return v___x_2920_;
}
else
{
lean_object* v___x_2921_; 
lean_dec(v_h__2_2914_);
v___x_2921_ = lean_apply_1(v_h__1_2913_, v_x_2912_);
return v___x_2921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(lean_object* v_x_2922_, lean_object* v_x_2923_, lean_object* v_h__1_2924_){
_start:
{
lean_object* v_size_2925_; lean_object* v_k_2926_; lean_object* v_v_2927_; lean_object* v_l_2928_; lean_object* v_r_2929_; lean_object* v___x_2930_; 
v_size_2925_ = lean_ctor_get(v_x_2922_, 0);
lean_inc(v_size_2925_);
v_k_2926_ = lean_ctor_get(v_x_2922_, 1);
lean_inc(v_k_2926_);
v_v_2927_ = lean_ctor_get(v_x_2922_, 2);
lean_inc(v_v_2927_);
v_l_2928_ = lean_ctor_get(v_x_2922_, 3);
lean_inc(v_l_2928_);
v_r_2929_ = lean_ctor_get(v_x_2922_, 4);
lean_inc(v_r_2929_);
lean_dec(v_x_2922_);
v___x_2930_ = lean_apply_8(v_h__1_2924_, v_size_2925_, v_k_2926_, v_v_2927_, v_l_2928_, v_r_2929_, lean_box(0), v_x_2923_, lean_box(0));
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter(lean_object* v_00_u03b1_2931_, lean_object* v_00_u03b2_2932_, lean_object* v_motive_2933_, lean_object* v_x_2934_, lean_object* v_x_2935_, lean_object* v_x_2936_, lean_object* v_x_2937_, lean_object* v_h__1_2938_){
_start:
{
lean_object* v_size_2939_; lean_object* v_k_2940_; lean_object* v_v_2941_; lean_object* v_l_2942_; lean_object* v_r_2943_; lean_object* v___x_2944_; 
v_size_2939_ = lean_ctor_get(v_x_2934_, 0);
lean_inc(v_size_2939_);
v_k_2940_ = lean_ctor_get(v_x_2934_, 1);
lean_inc(v_k_2940_);
v_v_2941_ = lean_ctor_get(v_x_2934_, 2);
lean_inc(v_v_2941_);
v_l_2942_ = lean_ctor_get(v_x_2934_, 3);
lean_inc(v_l_2942_);
v_r_2943_ = lean_ctor_get(v_x_2934_, 4);
lean_inc(v_r_2943_);
lean_dec(v_x_2934_);
v___x_2944_ = lean_apply_8(v_h__1_2938_, v_size_2939_, v_k_2940_, v_v_2941_, v_l_2942_, v_r_2943_, lean_box(0), v_x_2936_, lean_box(0));
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter___redArg(lean_object* v_x_2945_, lean_object* v_x_2946_, lean_object* v_x_2947_, lean_object* v_h__1_2948_, lean_object* v_h__2_2949_){
_start:
{
if (lean_obj_tag(v_x_2945_) == 0)
{
lean_object* v_size_2950_; lean_object* v_k_2951_; lean_object* v_v_2952_; lean_object* v_l_2953_; lean_object* v_r_2954_; lean_object* v___x_2955_; 
lean_dec(v_h__1_2948_);
v_size_2950_ = lean_ctor_get(v_x_2945_, 0);
lean_inc(v_size_2950_);
v_k_2951_ = lean_ctor_get(v_x_2945_, 1);
lean_inc(v_k_2951_);
v_v_2952_ = lean_ctor_get(v_x_2945_, 2);
lean_inc(v_v_2952_);
v_l_2953_ = lean_ctor_get(v_x_2945_, 3);
lean_inc(v_l_2953_);
v_r_2954_ = lean_ctor_get(v_x_2945_, 4);
lean_inc(v_r_2954_);
lean_dec_ref_known(v_x_2945_, 5);
v___x_2955_ = lean_apply_7(v_h__2_2949_, v_size_2950_, v_k_2951_, v_v_2952_, v_l_2953_, v_r_2954_, v_x_2946_, v_x_2947_);
return v___x_2955_;
}
else
{
lean_object* v___x_2956_; 
lean_dec(v_h__2_2949_);
v___x_2956_ = lean_apply_2(v_h__1_2948_, v_x_2946_, v_x_2947_);
return v___x_2956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2957_, lean_object* v_00_u03b2_2958_, lean_object* v_motive_2959_, lean_object* v_x_2960_, lean_object* v_x_2961_, lean_object* v_x_2962_, lean_object* v_h__1_2963_, lean_object* v_h__2_2964_){
_start:
{
if (lean_obj_tag(v_x_2960_) == 0)
{
lean_object* v_size_2965_; lean_object* v_k_2966_; lean_object* v_v_2967_; lean_object* v_l_2968_; lean_object* v_r_2969_; lean_object* v___x_2970_; 
lean_dec(v_h__1_2963_);
v_size_2965_ = lean_ctor_get(v_x_2960_, 0);
lean_inc(v_size_2965_);
v_k_2966_ = lean_ctor_get(v_x_2960_, 1);
lean_inc(v_k_2966_);
v_v_2967_ = lean_ctor_get(v_x_2960_, 2);
lean_inc(v_v_2967_);
v_l_2968_ = lean_ctor_get(v_x_2960_, 3);
lean_inc(v_l_2968_);
v_r_2969_ = lean_ctor_get(v_x_2960_, 4);
lean_inc(v_r_2969_);
lean_dec_ref_known(v_x_2960_, 5);
v___x_2970_ = lean_apply_7(v_h__2_2964_, v_size_2965_, v_k_2966_, v_v_2967_, v_l_2968_, v_r_2969_, v_x_2961_, v_x_2962_);
return v___x_2970_;
}
else
{
lean_object* v___x_2971_; 
lean_dec(v_h__2_2964_);
v___x_2971_ = lean_apply_2(v_h__1_2963_, v_x_2961_, v_x_2962_);
return v___x_2971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___redArg(lean_object* v_x_2972_, lean_object* v_h__1_2973_, lean_object* v_h__2_2974_){
_start:
{
if (lean_obj_tag(v_x_2972_) == 0)
{
lean_object* v_size_2975_; lean_object* v_k_2976_; lean_object* v_v_2977_; lean_object* v_l_2978_; lean_object* v_r_2979_; lean_object* v___x_2980_; 
lean_dec(v_h__1_2973_);
v_size_2975_ = lean_ctor_get(v_x_2972_, 0);
lean_inc(v_size_2975_);
v_k_2976_ = lean_ctor_get(v_x_2972_, 1);
lean_inc(v_k_2976_);
v_v_2977_ = lean_ctor_get(v_x_2972_, 2);
lean_inc(v_v_2977_);
v_l_2978_ = lean_ctor_get(v_x_2972_, 3);
lean_inc(v_l_2978_);
v_r_2979_ = lean_ctor_get(v_x_2972_, 4);
lean_inc(v_r_2979_);
lean_dec_ref_known(v_x_2972_, 5);
v___x_2980_ = lean_apply_7(v_h__2_2974_, v_size_2975_, v_k_2976_, v_v_2977_, v_l_2978_, v_r_2979_, lean_box(0), lean_box(0));
return v___x_2980_;
}
else
{
lean_object* v___x_2981_; 
lean_dec(v_h__2_2974_);
v___x_2981_ = lean_apply_2(v_h__1_2973_, lean_box(0), lean_box(0));
return v___x_2981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(lean_object* v_00_u03b1_2982_, lean_object* v_00_u03b2_2983_, lean_object* v_inst_2984_, lean_object* v_k_2985_, lean_object* v_motive_2986_, lean_object* v_x_2987_, lean_object* v_x_2988_, lean_object* v_x_2989_, lean_object* v_h__1_2990_, lean_object* v_h__2_2991_){
_start:
{
if (lean_obj_tag(v_x_2987_) == 0)
{
lean_object* v_size_2992_; lean_object* v_k_2993_; lean_object* v_v_2994_; lean_object* v_l_2995_; lean_object* v_r_2996_; lean_object* v___x_2997_; 
lean_dec(v_h__1_2990_);
v_size_2992_ = lean_ctor_get(v_x_2987_, 0);
lean_inc(v_size_2992_);
v_k_2993_ = lean_ctor_get(v_x_2987_, 1);
lean_inc(v_k_2993_);
v_v_2994_ = lean_ctor_get(v_x_2987_, 2);
lean_inc(v_v_2994_);
v_l_2995_ = lean_ctor_get(v_x_2987_, 3);
lean_inc(v_l_2995_);
v_r_2996_ = lean_ctor_get(v_x_2987_, 4);
lean_inc(v_r_2996_);
lean_dec_ref_known(v_x_2987_, 5);
v___x_2997_ = lean_apply_7(v_h__2_2991_, v_size_2992_, v_k_2993_, v_v_2994_, v_l_2995_, v_r_2996_, lean_box(0), lean_box(0));
return v___x_2997_;
}
else
{
lean_object* v___x_2998_; 
lean_dec(v_h__2_2991_);
v___x_2998_ = lean_apply_2(v_h__1_2990_, lean_box(0), lean_box(0));
return v___x_2998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___boxed(lean_object* v_00_u03b1_2999_, lean_object* v_00_u03b2_3000_, lean_object* v_inst_3001_, lean_object* v_k_3002_, lean_object* v_motive_3003_, lean_object* v_x_3004_, lean_object* v_x_3005_, lean_object* v_x_3006_, lean_object* v_h__1_3007_, lean_object* v_h__2_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(v_00_u03b1_2999_, v_00_u03b2_3000_, v_inst_3001_, v_k_3002_, v_motive_3003_, v_x_3004_, v_x_3005_, v_x_3006_, v_h__1_3007_, v_h__2_3008_);
lean_dec(v_k_3002_);
lean_dec_ref(v_inst_3001_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___redArg(lean_object* v_x_3010_, lean_object* v_h__1_3011_, lean_object* v_h__2_3012_){
_start:
{
if (lean_obj_tag(v_x_3010_) == 0)
{
lean_object* v_size_3013_; lean_object* v_k_3014_; lean_object* v_v_3015_; lean_object* v_l_3016_; lean_object* v_r_3017_; lean_object* v___x_3018_; 
lean_dec(v_h__1_3011_);
v_size_3013_ = lean_ctor_get(v_x_3010_, 0);
lean_inc(v_size_3013_);
v_k_3014_ = lean_ctor_get(v_x_3010_, 1);
lean_inc(v_k_3014_);
v_v_3015_ = lean_ctor_get(v_x_3010_, 2);
lean_inc(v_v_3015_);
v_l_3016_ = lean_ctor_get(v_x_3010_, 3);
lean_inc(v_l_3016_);
v_r_3017_ = lean_ctor_get(v_x_3010_, 4);
lean_inc(v_r_3017_);
lean_dec_ref_known(v_x_3010_, 5);
v___x_3018_ = lean_apply_7(v_h__2_3012_, v_size_3013_, v_k_3014_, v_v_3015_, v_l_3016_, v_r_3017_, lean_box(0), lean_box(0));
return v___x_3018_;
}
else
{
lean_object* v___x_3019_; 
lean_dec(v_h__2_3012_);
v___x_3019_ = lean_apply_2(v_h__1_3011_, lean_box(0), lean_box(0));
return v___x_3019_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(lean_object* v_00_u03b1_3020_, lean_object* v_00_u03b2_3021_, lean_object* v_inst_3022_, lean_object* v_k_3023_, lean_object* v_motive_3024_, lean_object* v_x_3025_, lean_object* v_x_3026_, lean_object* v_x_3027_, lean_object* v_h__1_3028_, lean_object* v_h__2_3029_){
_start:
{
if (lean_obj_tag(v_x_3025_) == 0)
{
lean_object* v_size_3030_; lean_object* v_k_3031_; lean_object* v_v_3032_; lean_object* v_l_3033_; lean_object* v_r_3034_; lean_object* v___x_3035_; 
lean_dec(v_h__1_3028_);
v_size_3030_ = lean_ctor_get(v_x_3025_, 0);
lean_inc(v_size_3030_);
v_k_3031_ = lean_ctor_get(v_x_3025_, 1);
lean_inc(v_k_3031_);
v_v_3032_ = lean_ctor_get(v_x_3025_, 2);
lean_inc(v_v_3032_);
v_l_3033_ = lean_ctor_get(v_x_3025_, 3);
lean_inc(v_l_3033_);
v_r_3034_ = lean_ctor_get(v_x_3025_, 4);
lean_inc(v_r_3034_);
lean_dec_ref_known(v_x_3025_, 5);
v___x_3035_ = lean_apply_7(v_h__2_3029_, v_size_3030_, v_k_3031_, v_v_3032_, v_l_3033_, v_r_3034_, lean_box(0), lean_box(0));
return v___x_3035_;
}
else
{
lean_object* v___x_3036_; 
lean_dec(v_h__2_3029_);
v___x_3036_ = lean_apply_2(v_h__1_3028_, lean_box(0), lean_box(0));
return v___x_3036_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___boxed(lean_object* v_00_u03b1_3037_, lean_object* v_00_u03b2_3038_, lean_object* v_inst_3039_, lean_object* v_k_3040_, lean_object* v_motive_3041_, lean_object* v_x_3042_, lean_object* v_x_3043_, lean_object* v_x_3044_, lean_object* v_h__1_3045_, lean_object* v_h__2_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(v_00_u03b1_3037_, v_00_u03b2_3038_, v_inst_3039_, v_k_3040_, v_motive_3041_, v_x_3042_, v_x_3043_, v_x_3044_, v_h__1_3045_, v_h__2_3046_);
lean_dec(v_k_3040_);
lean_dec_ref(v_inst_3039_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___redArg(lean_object* v_x_3048_, lean_object* v_h__1_3049_, lean_object* v_h__2_3050_){
_start:
{
if (lean_obj_tag(v_x_3048_) == 0)
{
lean_object* v_size_3051_; lean_object* v_k_3052_; lean_object* v_v_3053_; lean_object* v_l_3054_; lean_object* v_r_3055_; lean_object* v___x_3056_; 
lean_dec(v_h__1_3049_);
v_size_3051_ = lean_ctor_get(v_x_3048_, 0);
lean_inc(v_size_3051_);
v_k_3052_ = lean_ctor_get(v_x_3048_, 1);
lean_inc(v_k_3052_);
v_v_3053_ = lean_ctor_get(v_x_3048_, 2);
lean_inc(v_v_3053_);
v_l_3054_ = lean_ctor_get(v_x_3048_, 3);
lean_inc(v_l_3054_);
v_r_3055_ = lean_ctor_get(v_x_3048_, 4);
lean_inc(v_r_3055_);
lean_dec_ref_known(v_x_3048_, 5);
v___x_3056_ = lean_apply_7(v_h__2_3050_, v_size_3051_, v_k_3052_, v_v_3053_, v_l_3054_, v_r_3055_, lean_box(0), lean_box(0));
return v___x_3056_;
}
else
{
lean_object* v___x_3057_; 
lean_dec(v_h__2_3050_);
v___x_3057_ = lean_apply_2(v_h__1_3049_, lean_box(0), lean_box(0));
return v___x_3057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(lean_object* v_00_u03b1_3058_, lean_object* v_00_u03b2_3059_, lean_object* v_inst_3060_, lean_object* v_k_3061_, lean_object* v_motive_3062_, lean_object* v_x_3063_, lean_object* v_x_3064_, lean_object* v_x_3065_, lean_object* v_h__1_3066_, lean_object* v_h__2_3067_){
_start:
{
if (lean_obj_tag(v_x_3063_) == 0)
{
lean_object* v_size_3068_; lean_object* v_k_3069_; lean_object* v_v_3070_; lean_object* v_l_3071_; lean_object* v_r_3072_; lean_object* v___x_3073_; 
lean_dec(v_h__1_3066_);
v_size_3068_ = lean_ctor_get(v_x_3063_, 0);
lean_inc(v_size_3068_);
v_k_3069_ = lean_ctor_get(v_x_3063_, 1);
lean_inc(v_k_3069_);
v_v_3070_ = lean_ctor_get(v_x_3063_, 2);
lean_inc(v_v_3070_);
v_l_3071_ = lean_ctor_get(v_x_3063_, 3);
lean_inc(v_l_3071_);
v_r_3072_ = lean_ctor_get(v_x_3063_, 4);
lean_inc(v_r_3072_);
lean_dec_ref_known(v_x_3063_, 5);
v___x_3073_ = lean_apply_7(v_h__2_3067_, v_size_3068_, v_k_3069_, v_v_3070_, v_l_3071_, v_r_3072_, lean_box(0), lean_box(0));
return v___x_3073_;
}
else
{
lean_object* v___x_3074_; 
lean_dec(v_h__2_3067_);
v___x_3074_ = lean_apply_2(v_h__1_3066_, lean_box(0), lean_box(0));
return v___x_3074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___boxed(lean_object* v_00_u03b1_3075_, lean_object* v_00_u03b2_3076_, lean_object* v_inst_3077_, lean_object* v_k_3078_, lean_object* v_motive_3079_, lean_object* v_x_3080_, lean_object* v_x_3081_, lean_object* v_x_3082_, lean_object* v_h__1_3083_, lean_object* v_h__2_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(v_00_u03b1_3075_, v_00_u03b2_3076_, v_inst_3077_, v_k_3078_, v_motive_3079_, v_x_3080_, v_x_3081_, v_x_3082_, v_h__1_3083_, v_h__2_3084_);
lean_dec(v_k_3078_);
lean_dec_ref(v_inst_3077_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___redArg(lean_object* v_x_3086_, lean_object* v_h__1_3087_, lean_object* v_h__2_3088_){
_start:
{
if (lean_obj_tag(v_x_3086_) == 0)
{
lean_object* v_size_3089_; lean_object* v_k_3090_; lean_object* v_v_3091_; lean_object* v_l_3092_; lean_object* v_r_3093_; lean_object* v___x_3094_; 
lean_dec(v_h__1_3087_);
v_size_3089_ = lean_ctor_get(v_x_3086_, 0);
lean_inc(v_size_3089_);
v_k_3090_ = lean_ctor_get(v_x_3086_, 1);
lean_inc(v_k_3090_);
v_v_3091_ = lean_ctor_get(v_x_3086_, 2);
lean_inc(v_v_3091_);
v_l_3092_ = lean_ctor_get(v_x_3086_, 3);
lean_inc(v_l_3092_);
v_r_3093_ = lean_ctor_get(v_x_3086_, 4);
lean_inc(v_r_3093_);
lean_dec_ref_known(v_x_3086_, 5);
v___x_3094_ = lean_apply_7(v_h__2_3088_, v_size_3089_, v_k_3090_, v_v_3091_, v_l_3092_, v_r_3093_, lean_box(0), lean_box(0));
return v___x_3094_;
}
else
{
lean_object* v___x_3095_; 
lean_dec(v_h__2_3088_);
v___x_3095_ = lean_apply_2(v_h__1_3087_, lean_box(0), lean_box(0));
return v___x_3095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(lean_object* v_00_u03b1_3096_, lean_object* v_00_u03b2_3097_, lean_object* v_inst_3098_, lean_object* v_k_3099_, lean_object* v_motive_3100_, lean_object* v_x_3101_, lean_object* v_x_3102_, lean_object* v_x_3103_, lean_object* v_h__1_3104_, lean_object* v_h__2_3105_){
_start:
{
if (lean_obj_tag(v_x_3101_) == 0)
{
lean_object* v_size_3106_; lean_object* v_k_3107_; lean_object* v_v_3108_; lean_object* v_l_3109_; lean_object* v_r_3110_; lean_object* v___x_3111_; 
lean_dec(v_h__1_3104_);
v_size_3106_ = lean_ctor_get(v_x_3101_, 0);
lean_inc(v_size_3106_);
v_k_3107_ = lean_ctor_get(v_x_3101_, 1);
lean_inc(v_k_3107_);
v_v_3108_ = lean_ctor_get(v_x_3101_, 2);
lean_inc(v_v_3108_);
v_l_3109_ = lean_ctor_get(v_x_3101_, 3);
lean_inc(v_l_3109_);
v_r_3110_ = lean_ctor_get(v_x_3101_, 4);
lean_inc(v_r_3110_);
lean_dec_ref_known(v_x_3101_, 5);
v___x_3111_ = lean_apply_7(v_h__2_3105_, v_size_3106_, v_k_3107_, v_v_3108_, v_l_3109_, v_r_3110_, lean_box(0), lean_box(0));
return v___x_3111_;
}
else
{
lean_object* v___x_3112_; 
lean_dec(v_h__2_3105_);
v___x_3112_ = lean_apply_2(v_h__1_3104_, lean_box(0), lean_box(0));
return v___x_3112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___boxed(lean_object* v_00_u03b1_3113_, lean_object* v_00_u03b2_3114_, lean_object* v_inst_3115_, lean_object* v_k_3116_, lean_object* v_motive_3117_, lean_object* v_x_3118_, lean_object* v_x_3119_, lean_object* v_x_3120_, lean_object* v_h__1_3121_, lean_object* v_h__2_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(v_00_u03b1_3113_, v_00_u03b2_3114_, v_inst_3115_, v_k_3116_, v_motive_3117_, v_x_3118_, v_x_3119_, v_x_3120_, v_h__1_3121_, v_h__2_3122_);
lean_dec(v_k_3116_);
lean_dec_ref(v_inst_3115_);
return v_res_3123_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_WF_Defs(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Cell(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Model(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Internal_Model(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Internal_WF_Defs(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Internal_Cell(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Internal_Model(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Internal_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Internal_Model(builtin);
}
#ifdef __cplusplus
}
#endif
