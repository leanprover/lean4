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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg(lean_object* v_x_333_){
_start:
{
switch(lean_obj_tag(v_x_333_))
{
case 0:
{
lean_object* v___x_334_; 
v___x_334_ = lean_unsigned_to_nat(0u);
return v___x_334_;
}
case 1:
{
lean_object* v___x_335_; 
v___x_335_ = lean_unsigned_to_nat(1u);
return v___x_335_;
}
default: 
{
lean_object* v___x_336_; 
v___x_336_ = lean_unsigned_to_nat(2u);
return v___x_336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg___boxed(lean_object* v_x_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg(v_x_337_);
lean_dec_ref(v_x_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx(lean_object* v_00_u03b1_339_, lean_object* v_00_u03b2_340_, lean_object* v_inst_341_, lean_object* v_k_342_, lean_object* v_x_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg(v_x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___boxed(lean_object* v_00_u03b1_345_, lean_object* v_00_u03b2_346_, lean_object* v_inst_347_, lean_object* v_k_348_, lean_object* v_x_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx(v_00_u03b1_345_, v_00_u03b2_346_, v_inst_347_, v_k_348_, v_x_349_);
lean_dec_ref(v_x_349_);
lean_dec_ref(v_k_348_);
lean_dec_ref(v_inst_347_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(lean_object* v_t_351_, lean_object* v_k_352_){
_start:
{
switch(lean_obj_tag(v_t_351_))
{
case 0:
{
lean_object* v_a_353_; lean_object* v_a_354_; lean_object* v_a_355_; lean_object* v___x_356_; 
v_a_353_ = lean_ctor_get(v_t_351_, 0);
lean_inc(v_a_353_);
v_a_354_ = lean_ctor_get(v_t_351_, 1);
lean_inc(v_a_354_);
v_a_355_ = lean_ctor_get(v_t_351_, 2);
lean_inc(v_a_355_);
lean_dec_ref_known(v_t_351_, 3);
v___x_356_ = lean_apply_4(v_k_352_, v_a_353_, lean_box(0), v_a_354_, v_a_355_);
return v___x_356_;
}
case 1:
{
lean_object* v_a_357_; lean_object* v_a_358_; lean_object* v_a_359_; lean_object* v___x_360_; 
v_a_357_ = lean_ctor_get(v_t_351_, 0);
lean_inc(v_a_357_);
v_a_358_ = lean_ctor_get(v_t_351_, 1);
lean_inc(v_a_358_);
v_a_359_ = lean_ctor_get(v_t_351_, 2);
lean_inc(v_a_359_);
lean_dec_ref_known(v_t_351_, 3);
v___x_360_ = lean_apply_3(v_k_352_, v_a_357_, v_a_358_, v_a_359_);
return v___x_360_;
}
default: 
{
lean_object* v_a_361_; lean_object* v_a_362_; lean_object* v_a_363_; lean_object* v___x_364_; 
v_a_361_ = lean_ctor_get(v_t_351_, 0);
lean_inc(v_a_361_);
v_a_362_ = lean_ctor_get(v_t_351_, 1);
lean_inc(v_a_362_);
v_a_363_ = lean_ctor_get(v_t_351_, 2);
lean_inc(v_a_363_);
lean_dec_ref_known(v_t_351_, 3);
v___x_364_ = lean_apply_4(v_k_352_, v_a_361_, v_a_362_, lean_box(0), v_a_363_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim(lean_object* v_00_u03b1_365_, lean_object* v_00_u03b2_366_, lean_object* v_inst_367_, lean_object* v_k_368_, lean_object* v_motive_369_, lean_object* v_ctorIdx_370_, lean_object* v_t_371_, lean_object* v_h_372_, lean_object* v_k_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_371_, v_k_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___boxed(lean_object* v_00_u03b1_375_, lean_object* v_00_u03b2_376_, lean_object* v_inst_377_, lean_object* v_k_378_, lean_object* v_motive_379_, lean_object* v_ctorIdx_380_, lean_object* v_t_381_, lean_object* v_h_382_, lean_object* v_k_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim(v_00_u03b1_375_, v_00_u03b2_376_, v_inst_377_, v_k_378_, v_motive_379_, v_ctorIdx_380_, v_t_381_, v_h_382_, v_k_383_);
lean_dec(v_ctorIdx_380_);
lean_dec_ref(v_k_378_);
lean_dec_ref(v_inst_377_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___redArg(lean_object* v_t_385_, lean_object* v_lt_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_385_, v_lt_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_inst_390_, lean_object* v_k_391_, lean_object* v_motive_392_, lean_object* v_t_393_, lean_object* v_h_394_, lean_object* v_lt_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_393_, v_lt_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___boxed(lean_object* v_00_u03b1_397_, lean_object* v_00_u03b2_398_, lean_object* v_inst_399_, lean_object* v_k_400_, lean_object* v_motive_401_, lean_object* v_t_402_, lean_object* v_h_403_, lean_object* v_lt_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim(v_00_u03b1_397_, v_00_u03b2_398_, v_inst_399_, v_k_400_, v_motive_401_, v_t_402_, v_h_403_, v_lt_404_);
lean_dec_ref(v_k_400_);
lean_dec_ref(v_inst_399_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___redArg(lean_object* v_t_406_, lean_object* v_eq_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_406_, v_eq_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim(lean_object* v_00_u03b1_409_, lean_object* v_00_u03b2_410_, lean_object* v_inst_411_, lean_object* v_k_412_, lean_object* v_motive_413_, lean_object* v_t_414_, lean_object* v_h_415_, lean_object* v_eq_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_414_, v_eq_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___boxed(lean_object* v_00_u03b1_418_, lean_object* v_00_u03b2_419_, lean_object* v_inst_420_, lean_object* v_k_421_, lean_object* v_motive_422_, lean_object* v_t_423_, lean_object* v_h_424_, lean_object* v_eq_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim(v_00_u03b1_418_, v_00_u03b2_419_, v_inst_420_, v_k_421_, v_motive_422_, v_t_423_, v_h_424_, v_eq_425_);
lean_dec_ref(v_k_421_);
lean_dec_ref(v_inst_420_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___redArg(lean_object* v_t_427_, lean_object* v_gt_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_427_, v_gt_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim(lean_object* v_00_u03b1_430_, lean_object* v_00_u03b2_431_, lean_object* v_inst_432_, lean_object* v_k_433_, lean_object* v_motive_434_, lean_object* v_t_435_, lean_object* v_h_436_, lean_object* v_gt_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_435_, v_gt_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___boxed(lean_object* v_00_u03b1_439_, lean_object* v_00_u03b2_440_, lean_object* v_inst_441_, lean_object* v_k_442_, lean_object* v_motive_443_, lean_object* v_t_444_, lean_object* v_h_445_, lean_object* v_gt_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim(v_00_u03b1_439_, v_00_u03b2_440_, v_inst_441_, v_k_442_, v_motive_443_, v_t_444_, v_h_445_, v_gt_446_);
lean_dec_ref(v_k_442_);
lean_dec_ref(v_inst_441_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___redArg(lean_object* v_k_451_, lean_object* v_init_452_, lean_object* v_inner_453_, lean_object* v_l_454_){
_start:
{
if (lean_obj_tag(v_l_454_) == 0)
{
lean_object* v_k_455_; lean_object* v_v_456_; lean_object* v_l_457_; lean_object* v_r_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_k_455_ = lean_ctor_get(v_l_454_, 1);
lean_inc_n(v_k_455_, 2);
v_v_456_ = lean_ctor_get(v_l_454_, 2);
lean_inc(v_v_456_);
v_l_457_ = lean_ctor_get(v_l_454_, 3);
lean_inc(v_l_457_);
v_r_458_ = lean_ctor_get(v_l_454_, 4);
lean_inc(v_r_458_);
lean_dec_ref_known(v_l_454_, 5);
lean_inc_ref(v_k_451_);
v___x_459_ = lean_apply_1(v_k_451_, v_k_455_);
v___x_460_ = lean_unbox(v___x_459_);
switch(v___x_460_)
{
case 0:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_458_);
lean_dec(v_r_458_);
v___x_462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_462_, 0, v_k_455_);
lean_ctor_set(v___x_462_, 1, v_v_456_);
lean_ctor_set(v___x_462_, 2, v___x_461_);
lean_inc(v_inner_453_);
v___x_463_ = lean_apply_2(v_inner_453_, v_init_452_, v___x_462_);
v_init_452_ = v___x_463_;
v_l_454_ = v_l_457_;
goto _start;
}
case 1:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref(v_k_451_);
v___x_465_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_457_);
lean_dec(v_l_457_);
v___x_466_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_455_, v_v_456_);
v___x_467_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_458_);
lean_dec(v_r_458_);
v___x_468_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_468_, 0, v___x_465_);
lean_ctor_set(v___x_468_, 1, v___x_466_);
lean_ctor_set(v___x_468_, 2, v___x_467_);
v___x_469_ = lean_apply_2(v_inner_453_, v_init_452_, v___x_468_);
return v___x_469_;
}
default: 
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_457_);
lean_dec(v_l_457_);
v___x_471_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v_k_455_);
lean_ctor_set(v___x_471_, 2, v_v_456_);
lean_inc(v_inner_453_);
v___x_472_ = lean_apply_2(v_inner_453_, v_init_452_, v___x_471_);
v_init_452_ = v___x_472_;
v_l_454_ = v_r_458_;
goto _start;
}
}
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec_ref(v_k_451_);
v___x_474_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0));
v___x_475_ = lean_apply_2(v_inner_453_, v_init_452_, v___x_474_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore(lean_object* v_00_u03b1_476_, lean_object* v_00_u03b2_477_, lean_object* v_00_u03b3_478_, lean_object* v_inst_479_, lean_object* v_k_480_, lean_object* v_init_481_, lean_object* v_inner_482_, lean_object* v_l_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v_k_480_, v_init_481_, v_inner_482_, v_l_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___boxed(lean_object* v_00_u03b1_485_, lean_object* v_00_u03b2_486_, lean_object* v_00_u03b3_487_, lean_object* v_inst_488_, lean_object* v_k_489_, lean_object* v_init_490_, lean_object* v_inner_491_, lean_object* v_l_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_DTreeMap_Internal_Impl_explore(v_00_u03b1_485_, v_00_u03b2_486_, v_00_u03b3_487_, v_inst_488_, v_k_489_, v_init_490_, v_inner_491_, v_l_492_);
lean_dec_ref(v_inst_488_);
return v_res_493_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(lean_object* v_c_494_, lean_object* v_x_495_){
_start:
{
uint8_t v___x_496_; 
v___x_496_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0___boxed(lean_object* v_c_497_, lean_object* v_x_498_){
_start:
{
uint8_t v_res_499_; lean_object* v_r_500_; 
v_res_499_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(v_c_497_, v_x_498_);
lean_dec(v_c_497_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(lean_object* v_inst_502_, lean_object* v_l_503_, lean_object* v_k_504_){
_start:
{
lean_object* v___f_505_; lean_object* v___x_506_; 
v___f_505_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0));
v___x_506_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_502_, v_k_504_, v_l_503_, v___f_505_);
return v___x_506_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098(lean_object* v_00_u03b1_507_, lean_object* v_00_u03b2_508_, lean_object* v_inst_509_, lean_object* v_l_510_, lean_object* v_k_511_){
_start:
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(v_inst_509_, v_l_510_, v_k_511_);
v___x_513_ = lean_unbox(v___x_512_);
lean_dec(v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___boxed(lean_object* v_00_u03b1_514_, lean_object* v_00_u03b2_515_, lean_object* v_inst_516_, lean_object* v_l_517_, lean_object* v_k_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_Std_DTreeMap_Internal_Impl_contains_u2098(v_00_u03b1_514_, v_00_u03b2_515_, v_inst_516_, v_l_517_, v_k_518_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0(lean_object* v_c_521_, lean_object* v_x_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(v_c_521_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(lean_object* v_inst_525_, lean_object* v_l_526_, lean_object* v_k_527_){
_start:
{
lean_object* v___f_528_; lean_object* v___x_529_; 
v___f_528_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0));
v___x_529_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_525_, v_k_527_, v_l_526_, v___f_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098(lean_object* v_00_u03b1_530_, lean_object* v_00_u03b2_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_inst_534_, lean_object* v_l_535_, lean_object* v_k_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_532_, v_l_535_, v_k_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(lean_object* v_inst_538_, lean_object* v_l_539_, lean_object* v_k_540_){
_start:
{
lean_object* v___x_541_; lean_object* v_val_542_; 
v___x_541_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_538_, v_l_539_, v_k_540_);
v_val_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_val_542_);
lean_dec(v___x_541_);
return v_val_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098(lean_object* v_00_u03b1_543_, lean_object* v_00_u03b2_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_l_548_, lean_object* v_k_549_, lean_object* v_h_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(v_inst_545_, v_l_548_, v_k_549_);
return v___x_551_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_555_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2));
v___x_556_ = lean_unsigned_to_nat(14u);
v___x_557_ = lean_unsigned_to_nat(22u);
v___x_558_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1));
v___x_559_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0));
v___x_560_ = l_mkPanicMessageWithDecl(v___x_559_, v___x_558_, v___x_557_, v___x_556_, v___x_555_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(lean_object* v_inst_561_, lean_object* v_l_562_, lean_object* v_k_563_, lean_object* v_inst_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_561_, v_l_562_, v_k_563_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_567_ = l_panic___redArg(v_inst_564_, v___x_566_);
return v___x_567_;
}
else
{
lean_object* v_val_568_; 
v_val_568_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_val_568_);
lean_dec_ref_known(v___x_565_, 1);
return v_val_568_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___boxed(lean_object* v_inst_569_, lean_object* v_l_570_, lean_object* v_k_571_, lean_object* v_inst_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(v_inst_569_, v_l_570_, v_k_571_, v_inst_572_);
lean_dec(v_inst_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098(lean_object* v_00_u03b1_574_, lean_object* v_00_u03b2_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_l_579_, lean_object* v_k_580_, lean_object* v_inst_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(v_inst_576_, v_l_579_, v_k_580_, v_inst_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___boxed(lean_object* v_00_u03b1_583_, lean_object* v_00_u03b2_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_l_588_, lean_object* v_k_589_, lean_object* v_inst_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098(v_00_u03b1_583_, v_00_u03b2_584_, v_inst_585_, v_inst_586_, v_inst_587_, v_l_588_, v_k_589_, v_inst_590_);
lean_dec(v_inst_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(lean_object* v_inst_592_, lean_object* v_k_593_, lean_object* v_l_594_, lean_object* v_fallback_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_592_, v_l_594_, v_k_593_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_inc(v_fallback_595_);
return v_fallback_595_;
}
else
{
lean_object* v_val_597_; 
v_val_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_val_597_);
lean_dec_ref_known(v___x_596_, 1);
return v_val_597_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg___boxed(lean_object* v_inst_598_, lean_object* v_k_599_, lean_object* v_l_600_, lean_object* v_fallback_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(v_inst_598_, v_k_599_, v_l_600_, v_fallback_601_);
lean_dec(v_fallback_601_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098(lean_object* v_00_u03b1_603_, lean_object* v_00_u03b2_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_k_608_, lean_object* v_l_609_, lean_object* v_fallback_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(v_inst_605_, v_k_608_, v_l_609_, v_fallback_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___boxed(lean_object* v_00_u03b1_612_, lean_object* v_00_u03b2_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_k_617_, lean_object* v_l_618_, lean_object* v_fallback_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_DTreeMap_Internal_Impl_getD_u2098(v_00_u03b1_612_, v_00_u03b2_613_, v_inst_614_, v_inst_615_, v_inst_616_, v_k_617_, v_l_618_, v_fallback_619_);
lean_dec(v_fallback_619_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___lam__0(lean_object* v_c_621_, lean_object* v_x_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(v_c_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(lean_object* v_inst_625_, lean_object* v_l_626_, lean_object* v_k_627_){
_start:
{
lean_object* v___f_628_; lean_object* v___x_629_; 
v___f_628_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0));
v___x_629_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_625_, v_k_627_, v_l_626_, v___f_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098(lean_object* v_00_u03b1_630_, lean_object* v_00_u03b2_631_, lean_object* v_inst_632_, lean_object* v_l_633_, lean_object* v_k_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_632_, v_l_633_, v_k_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(lean_object* v_inst_636_, lean_object* v_l_637_, lean_object* v_k_638_){
_start:
{
lean_object* v___x_639_; lean_object* v_val_640_; 
v___x_639_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_636_, v_l_637_, v_k_638_);
v_val_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_640_);
lean_dec(v___x_639_);
return v_val_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098(lean_object* v_00_u03b1_641_, lean_object* v_00_u03b2_642_, lean_object* v_inst_643_, lean_object* v_l_644_, lean_object* v_k_645_, lean_object* v_h_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(v_inst_643_, v_l_644_, v_k_645_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_l_650_, lean_object* v_k_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_648_, v_l_650_, v_k_651_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_654_ = l_panic___redArg(v_inst_649_, v___x_653_);
return v___x_654_;
}
else
{
lean_object* v_val_655_; 
v_val_655_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_val_655_);
lean_dec_ref_known(v___x_652_, 1);
return v_val_655_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg___boxed(lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_l_658_, lean_object* v_k_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(v_inst_656_, v_inst_657_, v_l_658_, v_k_659_);
lean_dec_ref(v_inst_657_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(lean_object* v_00_u03b1_661_, lean_object* v_00_u03b2_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_l_665_, lean_object* v_k_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(v_inst_663_, v_inst_664_, v_l_665_, v_k_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___boxed(lean_object* v_00_u03b1_668_, lean_object* v_00_u03b2_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_l_672_, lean_object* v_k_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(v_00_u03b1_668_, v_00_u03b2_669_, v_inst_670_, v_inst_671_, v_l_672_, v_k_673_);
lean_dec_ref(v_inst_671_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(lean_object* v_inst_675_, lean_object* v_k_676_, lean_object* v_l_677_, lean_object* v_fallback_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_675_, v_l_677_, v_k_676_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_inc_ref(v_fallback_678_);
return v_fallback_678_;
}
else
{
lean_object* v_val_680_; 
v_val_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_val_680_);
lean_dec_ref_known(v___x_679_, 1);
return v_val_680_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg___boxed(lean_object* v_inst_681_, lean_object* v_k_682_, lean_object* v_l_683_, lean_object* v_fallback_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(v_inst_681_, v_k_682_, v_l_683_, v_fallback_684_);
lean_dec_ref(v_fallback_684_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(lean_object* v_00_u03b1_686_, lean_object* v_00_u03b2_687_, lean_object* v_inst_688_, lean_object* v_k_689_, lean_object* v_l_690_, lean_object* v_fallback_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(v_inst_688_, v_k_689_, v_l_690_, v_fallback_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___boxed(lean_object* v_00_u03b1_693_, lean_object* v_00_u03b2_694_, lean_object* v_inst_695_, lean_object* v_k_696_, lean_object* v_l_697_, lean_object* v_fallback_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(v_00_u03b1_693_, v_00_u03b2_694_, v_inst_695_, v_k_696_, v_l_697_, v_fallback_698_);
lean_dec_ref(v_fallback_698_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0(lean_object* v_c_700_, lean_object* v_x_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(v_c_700_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(lean_object* v_inst_704_, lean_object* v_l_705_, lean_object* v_k_706_){
_start:
{
lean_object* v___f_707_; lean_object* v___x_708_; 
v___f_707_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0));
v___x_708_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_704_, v_k_706_, v_l_705_, v___f_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098(lean_object* v_00_u03b1_709_, lean_object* v_00_u03b2_710_, lean_object* v_inst_711_, lean_object* v_l_712_, lean_object* v_k_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_711_, v_l_712_, v_k_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(lean_object* v_inst_715_, lean_object* v_l_716_, lean_object* v_k_717_){
_start:
{
lean_object* v___x_718_; lean_object* v_val_719_; 
v___x_718_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_715_, v_l_716_, v_k_717_);
v_val_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_val_719_);
lean_dec(v___x_718_);
return v_val_719_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098(lean_object* v_00_u03b1_720_, lean_object* v_00_u03b2_721_, lean_object* v_inst_722_, lean_object* v_l_723_, lean_object* v_k_724_, lean_object* v_h_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(v_inst_722_, v_l_723_, v_k_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(lean_object* v_inst_727_, lean_object* v_l_728_, lean_object* v_k_729_, lean_object* v_inst_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_727_, v_l_728_, v_k_729_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_733_ = l_panic___redArg(v_inst_730_, v___x_732_);
return v___x_733_;
}
else
{
lean_object* v_val_734_; 
v_val_734_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_val_734_);
lean_dec_ref_known(v___x_731_, 1);
return v_val_734_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg___boxed(lean_object* v_inst_735_, lean_object* v_l_736_, lean_object* v_k_737_, lean_object* v_inst_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(v_inst_735_, v_l_736_, v_k_737_, v_inst_738_);
lean_dec(v_inst_738_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(lean_object* v_00_u03b1_740_, lean_object* v_00_u03b2_741_, lean_object* v_inst_742_, lean_object* v_l_743_, lean_object* v_k_744_, lean_object* v_inst_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(v_inst_742_, v_l_743_, v_k_744_, v_inst_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___boxed(lean_object* v_00_u03b1_747_, lean_object* v_00_u03b2_748_, lean_object* v_inst_749_, lean_object* v_l_750_, lean_object* v_k_751_, lean_object* v_inst_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(v_00_u03b1_747_, v_00_u03b2_748_, v_inst_749_, v_l_750_, v_k_751_, v_inst_752_);
lean_dec(v_inst_752_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(lean_object* v_inst_754_, lean_object* v_k_755_, lean_object* v_l_756_, lean_object* v_fallback_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_754_, v_l_756_, v_k_755_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_inc(v_fallback_757_);
return v_fallback_757_;
}
else
{
lean_object* v_val_759_; 
v_val_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_759_);
lean_dec_ref_known(v___x_758_, 1);
return v_val_759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg___boxed(lean_object* v_inst_760_, lean_object* v_k_761_, lean_object* v_l_762_, lean_object* v_fallback_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(v_inst_760_, v_k_761_, v_l_762_, v_fallback_763_);
lean_dec(v_fallback_763_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(lean_object* v_00_u03b1_765_, lean_object* v_00_u03b2_766_, lean_object* v_inst_767_, lean_object* v_k_768_, lean_object* v_l_769_, lean_object* v_fallback_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(v_inst_767_, v_k_768_, v_l_769_, v_fallback_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___boxed(lean_object* v_00_u03b1_772_, lean_object* v_00_u03b2_773_, lean_object* v_inst_774_, lean_object* v_k_775_, lean_object* v_l_776_, lean_object* v_fallback_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(v_00_u03b1_772_, v_00_u03b2_773_, v_inst_774_, v_k_775_, v_l_776_, v_fallback_777_);
lean_dec(v_fallback_777_);
return v_res_778_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(lean_object* v_x_779_){
_start:
{
uint8_t v___x_780_; 
v___x_780_ = 0;
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* v_x_781_){
_start:
{
uint8_t v_res_782_; lean_object* v_r_783_; 
v_res_782_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(v_x_781_);
lean_dec(v_x_781_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(lean_object* v_sofar_784_, lean_object* v_step_785_){
_start:
{
if (lean_obj_tag(v_step_785_) == 0)
{
lean_object* v_a_786_; lean_object* v_a_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_a_786_ = lean_ctor_get(v_step_785_, 0);
v_a_787_ = lean_ctor_get(v_step_785_, 1);
lean_inc(v_a_787_);
lean_inc(v_a_786_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_a_786_);
lean_ctor_set(v___x_788_, 1, v_a_787_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
else
{
lean_object* v_a_790_; lean_object* v___x_791_; 
v_a_790_ = lean_ctor_get(v_step_785_, 2);
v___x_791_ = l_List_head_x3f___redArg(v_a_790_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_inc(v_sofar_784_);
return v_sofar_784_;
}
else
{
return v___x_791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* v_sofar_792_, lean_object* v_step_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(v_sofar_792_, v_step_793_);
lean_dec_ref(v_step_793_);
lean_dec(v_sofar_792_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(lean_object* v_l_797_){
_start:
{
lean_object* v___f_798_; lean_object* v___f_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___f_798_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0));
v___f_799_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1));
v___x_800_ = lean_box(0);
v___x_801_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___f_798_, v___x_800_, v___f_799_, v_l_797_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(lean_object* v_00_u03b1_802_, lean_object* v_00_u03b2_803_, lean_object* v_inst_804_, lean_object* v_l_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(v_l_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___boxed(lean_object* v_00_u03b1_807_, lean_object* v_00_u03b2_808_, lean_object* v_inst_809_, lean_object* v_l_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(v_00_u03b1_807_, v_00_u03b2_808_, v_inst_809_, v_l_810_);
lean_dec_ref(v_inst_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_r_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_List_head_x3f___redArg(v_r_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed(lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_r_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(v_x_817_, v_x_818_, v_x_819_, v_r_820_);
lean_dec(v_r_820_);
lean_dec(v_x_818_);
lean_dec(v_x_817_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(lean_object* v_l_823_){
_start:
{
lean_object* v___f_824_; lean_object* v___f_825_; lean_object* v___x_826_; 
v___f_824_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0));
v___f_825_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0));
v___x_826_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_824_, v_l_823_, v___f_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(lean_object* v_00_u03b1_827_, lean_object* v_00_u03b2_828_, lean_object* v_inst_829_, lean_object* v_l_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(v_l_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___boxed(lean_object* v_00_u03b1_832_, lean_object* v_00_u03b2_833_, lean_object* v_inst_834_, lean_object* v_l_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(v_00_u03b1_832_, v_00_u03b2_833_, v_inst_834_, v_l_835_);
lean_dec_ref(v_inst_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse___redArg(lean_object* v_x_837_){
_start:
{
if (lean_obj_tag(v_x_837_) == 0)
{
lean_object* v_size_838_; lean_object* v_k_839_; lean_object* v_v_840_; lean_object* v_l_841_; lean_object* v_r_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_851_; 
v_size_838_ = lean_ctor_get(v_x_837_, 0);
v_k_839_ = lean_ctor_get(v_x_837_, 1);
v_v_840_ = lean_ctor_get(v_x_837_, 2);
v_l_841_ = lean_ctor_get(v_x_837_, 3);
v_r_842_ = lean_ctor_get(v_x_837_, 4);
v_isSharedCheck_851_ = !lean_is_exclusive(v_x_837_);
if (v_isSharedCheck_851_ == 0)
{
v___x_844_ = v_x_837_;
v_isShared_845_ = v_isSharedCheck_851_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_r_842_);
lean_inc(v_l_841_);
lean_inc(v_v_840_);
lean_inc(v_k_839_);
lean_inc(v_size_838_);
lean_dec(v_x_837_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_851_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_846_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_r_842_);
v___x_847_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_l_841_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v___x_847_);
lean_ctor_set(v___x_844_, 3, v___x_846_);
v___x_849_ = v___x_844_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_size_838_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_k_839_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_v_840_);
lean_ctor_set(v_reuseFailAlloc_850_, 3, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_850_, 4, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
return v_x_837_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse(lean_object* v_00_u03b1_852_, lean_object* v_00_u03b2_853_, lean_object* v_x_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0(lean_object* v_c_856_, lean_object* v_x_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(v_c_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(lean_object* v_inst_860_, lean_object* v_l_861_, lean_object* v_k_862_){
_start:
{
lean_object* v___f_863_; lean_object* v___x_864_; 
v___f_863_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0));
v___x_864_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_860_, v_k_862_, v_l_861_, v___f_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098(lean_object* v_00_u03b1_865_, lean_object* v_00_u03b2_866_, lean_object* v_inst_867_, lean_object* v_l_868_, lean_object* v_k_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_867_, v_l_868_, v_k_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(lean_object* v_inst_871_, lean_object* v_l_872_, lean_object* v_k_873_){
_start:
{
lean_object* v___x_874_; lean_object* v_val_875_; 
v___x_874_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_871_, v_l_872_, v_k_873_);
v_val_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_val_875_);
lean_dec(v___x_874_);
return v_val_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098(lean_object* v_00_u03b1_876_, lean_object* v_00_u03b2_877_, lean_object* v_inst_878_, lean_object* v_l_879_, lean_object* v_k_880_, lean_object* v_h_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(v_inst_878_, v_l_879_, v_k_880_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(lean_object* v_inst_883_, lean_object* v_l_884_, lean_object* v_k_885_, lean_object* v_inst_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_883_, v_l_884_, v_k_885_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_889_ = l_panic___redArg(v_inst_886_, v___x_888_);
return v___x_889_;
}
else
{
lean_object* v_val_890_; 
v_val_890_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_val_890_);
lean_dec_ref_known(v___x_887_, 1);
return v_val_890_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg___boxed(lean_object* v_inst_891_, lean_object* v_l_892_, lean_object* v_k_893_, lean_object* v_inst_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(v_inst_891_, v_l_892_, v_k_893_, v_inst_894_);
lean_dec(v_inst_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(lean_object* v_00_u03b1_896_, lean_object* v_00_u03b2_897_, lean_object* v_inst_898_, lean_object* v_l_899_, lean_object* v_k_900_, lean_object* v_inst_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(v_inst_898_, v_l_899_, v_k_900_, v_inst_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___boxed(lean_object* v_00_u03b1_903_, lean_object* v_00_u03b2_904_, lean_object* v_inst_905_, lean_object* v_l_906_, lean_object* v_k_907_, lean_object* v_inst_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(v_00_u03b1_903_, v_00_u03b2_904_, v_inst_905_, v_l_906_, v_k_907_, v_inst_908_);
lean_dec(v_inst_908_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(lean_object* v_inst_910_, lean_object* v_l_911_, lean_object* v_k_912_, lean_object* v_fallback_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_910_, v_l_911_, v_k_912_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_inc(v_fallback_913_);
return v_fallback_913_;
}
else
{
lean_object* v_val_915_; 
v_val_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_val_915_);
lean_dec_ref_known(v___x_914_, 1);
return v_val_915_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg___boxed(lean_object* v_inst_916_, lean_object* v_l_917_, lean_object* v_k_918_, lean_object* v_fallback_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(v_inst_916_, v_l_917_, v_k_918_, v_fallback_919_);
lean_dec(v_fallback_919_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(lean_object* v_00_u03b1_921_, lean_object* v_00_u03b2_922_, lean_object* v_inst_923_, lean_object* v_l_924_, lean_object* v_k_925_, lean_object* v_fallback_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(v_inst_923_, v_l_924_, v_k_925_, v_fallback_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___boxed(lean_object* v_00_u03b1_928_, lean_object* v_00_u03b2_929_, lean_object* v_inst_930_, lean_object* v_l_931_, lean_object* v_k_932_, lean_object* v_fallback_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(v_00_u03b1_928_, v_00_u03b2_929_, v_inst_930_, v_l_931_, v_k_932_, v_fallback_933_);
lean_dec(v_fallback_933_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object* v_t_935_, lean_object* v_h__1_936_, lean_object* v_h__2_937_){
_start:
{
if (lean_obj_tag(v_t_935_) == 0)
{
lean_object* v_size_938_; lean_object* v_k_939_; lean_object* v_v_940_; lean_object* v_l_941_; lean_object* v_r_942_; lean_object* v___x_943_; 
lean_dec(v_h__1_936_);
v_size_938_ = lean_ctor_get(v_t_935_, 0);
lean_inc(v_size_938_);
v_k_939_ = lean_ctor_get(v_t_935_, 1);
lean_inc(v_k_939_);
v_v_940_ = lean_ctor_get(v_t_935_, 2);
lean_inc(v_v_940_);
v_l_941_ = lean_ctor_get(v_t_935_, 3);
lean_inc(v_l_941_);
v_r_942_ = lean_ctor_get(v_t_935_, 4);
lean_inc(v_r_942_);
lean_dec_ref_known(v_t_935_, 5);
v___x_943_ = lean_apply_5(v_h__2_937_, v_size_938_, v_k_939_, v_v_940_, v_l_941_, v_r_942_);
return v___x_943_;
}
else
{
lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec(v_h__2_937_);
v___x_944_ = lean_box(0);
v___x_945_ = lean_apply_1(v_h__1_936_, v___x_944_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_motive_948_, lean_object* v_t_949_, lean_object* v_h__1_950_, lean_object* v_h__2_951_){
_start:
{
if (lean_obj_tag(v_t_949_) == 0)
{
lean_object* v_size_952_; lean_object* v_k_953_; lean_object* v_v_954_; lean_object* v_l_955_; lean_object* v_r_956_; lean_object* v___x_957_; 
lean_dec(v_h__1_950_);
v_size_952_ = lean_ctor_get(v_t_949_, 0);
lean_inc(v_size_952_);
v_k_953_ = lean_ctor_get(v_t_949_, 1);
lean_inc(v_k_953_);
v_v_954_ = lean_ctor_get(v_t_949_, 2);
lean_inc(v_v_954_);
v_l_955_ = lean_ctor_get(v_t_949_, 3);
lean_inc(v_l_955_);
v_r_956_ = lean_ctor_get(v_t_949_, 4);
lean_inc(v_r_956_);
lean_dec_ref_known(v_t_949_, 5);
v___x_957_ = lean_apply_5(v_h__2_951_, v_size_952_, v_k_953_, v_v_954_, v_l_955_, v_r_956_);
return v___x_957_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v_h__2_951_);
v___x_958_ = lean_box(0);
v___x_959_ = lean_apply_1(v_h__1_950_, v___x_958_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(uint8_t v_x_960_, lean_object* v_h__1_961_, lean_object* v_h__2_962_, lean_object* v_h__3_963_){
_start:
{
switch(v_x_960_)
{
case 0:
{
lean_object* v___x_964_; 
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
v___x_964_ = lean_apply_1(v_h__1_961_, lean_box(0));
return v___x_964_;
}
case 1:
{
lean_object* v___x_965_; 
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v___x_965_ = lean_apply_1(v_h__3_963_, lean_box(0));
return v___x_965_;
}
default: 
{
lean_object* v___x_966_; 
lean_dec(v_h__3_963_);
lean_dec(v_h__1_961_);
v___x_966_ = lean_apply_1(v_h__2_962_, lean_box(0));
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_967_, lean_object* v_h__1_968_, lean_object* v_h__2_969_, lean_object* v_h__3_970_){
_start:
{
uint8_t v_x_33__boxed_971_; lean_object* v_res_972_; 
v_x_33__boxed_971_ = lean_unbox(v_x_967_);
v_res_972_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(v_x_33__boxed_971_, v_h__1_968_, v_h__2_969_, v_h__3_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(lean_object* v_motive_973_, uint8_t v_x_974_, lean_object* v_h__1_975_, lean_object* v_h__2_976_, lean_object* v_h__3_977_){
_start:
{
switch(v_x_974_)
{
case 0:
{
lean_object* v___x_978_; 
lean_dec(v_h__3_977_);
lean_dec(v_h__2_976_);
v___x_978_ = lean_apply_1(v_h__1_975_, lean_box(0));
return v___x_978_;
}
case 1:
{
lean_object* v___x_979_; 
lean_dec(v_h__2_976_);
lean_dec(v_h__1_975_);
v___x_979_ = lean_apply_1(v_h__3_977_, lean_box(0));
return v___x_979_;
}
default: 
{
lean_object* v___x_980_; 
lean_dec(v_h__3_977_);
lean_dec(v_h__1_975_);
v___x_980_ = lean_apply_1(v_h__2_976_, lean_box(0));
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___boxed(lean_object* v_motive_981_, lean_object* v_x_982_, lean_object* v_h__1_983_, lean_object* v_h__2_984_, lean_object* v_h__3_985_){
_start:
{
uint8_t v_x_42__boxed_986_; lean_object* v_res_987_; 
v_x_42__boxed_986_ = lean_unbox(v_x_982_);
v_res_987_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(v_motive_981_, v_x_42__boxed_986_, v_h__1_983_, v_h__2_984_, v_h__3_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object* v_x_988_, lean_object* v_h__1_989_, lean_object* v_h__2_990_){
_start:
{
if (lean_obj_tag(v_x_988_) == 0)
{
lean_object* v___x_991_; 
lean_dec(v_h__2_990_);
v___x_991_ = lean_apply_1(v_h__1_989_, lean_box(0));
return v___x_991_;
}
else
{
lean_object* v_val_992_; lean_object* v___x_993_; 
lean_dec(v_h__1_989_);
v_val_992_ = lean_ctor_get(v_x_988_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v_x_988_, 1);
v___x_993_ = lean_apply_2(v_h__2_990_, v_val_992_, lean_box(0));
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object* v_00_u03b1_994_, lean_object* v_00_u03b2_995_, lean_object* v_motive_996_, lean_object* v_x_997_, lean_object* v_h__1_998_, lean_object* v_h__2_999_){
_start:
{
if (lean_obj_tag(v_x_997_) == 0)
{
lean_object* v___x_1000_; 
lean_dec(v_h__2_999_);
v___x_1000_ = lean_apply_1(v_h__1_998_, lean_box(0));
return v___x_1000_;
}
else
{
lean_object* v_val_1001_; lean_object* v___x_1002_; 
lean_dec(v_h__1_998_);
v_val_1001_ = lean_ctor_get(v_x_997_, 0);
lean_inc(v_val_1001_);
lean_dec_ref_known(v_x_997_, 1);
v___x_1002_ = lean_apply_2(v_h__2_999_, v_val_1001_, lean_box(0));
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___redArg(lean_object* v_t_1003_, lean_object* v_h__1_1004_){
_start:
{
lean_object* v_size_1005_; lean_object* v_k_1006_; lean_object* v_v_1007_; lean_object* v_l_1008_; lean_object* v_r_1009_; lean_object* v___x_1010_; 
v_size_1005_ = lean_ctor_get(v_t_1003_, 0);
lean_inc(v_size_1005_);
v_k_1006_ = lean_ctor_get(v_t_1003_, 1);
lean_inc(v_k_1006_);
v_v_1007_ = lean_ctor_get(v_t_1003_, 2);
lean_inc(v_v_1007_);
v_l_1008_ = lean_ctor_get(v_t_1003_, 3);
lean_inc(v_l_1008_);
v_r_1009_ = lean_ctor_get(v_t_1003_, 4);
lean_inc(v_r_1009_);
lean_dec(v_t_1003_);
v___x_1010_ = lean_apply_6(v_h__1_1004_, v_size_1005_, v_k_1006_, v_v_1007_, v_l_1008_, v_r_1009_, lean_box(0));
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(lean_object* v_00_u03b1_1011_, lean_object* v_00_u03b2_1012_, lean_object* v_inst_1013_, lean_object* v_k_1014_, lean_object* v_motive_1015_, lean_object* v_t_1016_, lean_object* v_hlk_1017_, lean_object* v_h__1_1018_){
_start:
{
lean_object* v_size_1019_; lean_object* v_k_1020_; lean_object* v_v_1021_; lean_object* v_l_1022_; lean_object* v_r_1023_; lean_object* v___x_1024_; 
v_size_1019_ = lean_ctor_get(v_t_1016_, 0);
lean_inc(v_size_1019_);
v_k_1020_ = lean_ctor_get(v_t_1016_, 1);
lean_inc(v_k_1020_);
v_v_1021_ = lean_ctor_get(v_t_1016_, 2);
lean_inc(v_v_1021_);
v_l_1022_ = lean_ctor_get(v_t_1016_, 3);
lean_inc(v_l_1022_);
v_r_1023_ = lean_ctor_get(v_t_1016_, 4);
lean_inc(v_r_1023_);
lean_dec(v_t_1016_);
v___x_1024_ = lean_apply_6(v_h__1_1018_, v_size_1019_, v_k_1020_, v_v_1021_, v_l_1022_, v_r_1023_, lean_box(0));
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___boxed(lean_object* v_00_u03b1_1025_, lean_object* v_00_u03b2_1026_, lean_object* v_inst_1027_, lean_object* v_k_1028_, lean_object* v_motive_1029_, lean_object* v_t_1030_, lean_object* v_hlk_1031_, lean_object* v_h__1_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(v_00_u03b1_1025_, v_00_u03b2_1026_, v_inst_1027_, v_k_1028_, v_motive_1029_, v_t_1030_, v_hlk_1031_, v_h__1_1032_);
lean_dec(v_k_1028_);
lean_dec_ref(v_inst_1027_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1034_, lean_object* v_h__1_1035_, lean_object* v_h__2_1036_){
_start:
{
if (lean_obj_tag(v_x_1034_) == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec(v_h__2_1036_);
v___x_1037_ = lean_box(0);
v___x_1038_ = lean_apply_1(v_h__1_1035_, v___x_1037_);
return v___x_1038_;
}
else
{
lean_object* v_val_1039_; lean_object* v___x_1040_; 
lean_dec(v_h__1_1035_);
v_val_1039_ = lean_ctor_get(v_x_1034_, 0);
lean_inc(v_val_1039_);
lean_dec_ref_known(v_x_1034_, 1);
v___x_1040_ = lean_apply_1(v_h__2_1036_, v_val_1039_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1041_, lean_object* v_00_u03b2_1042_, lean_object* v_motive_1043_, lean_object* v_x_1044_, lean_object* v_h__1_1045_, lean_object* v_h__2_1046_){
_start:
{
if (lean_obj_tag(v_x_1044_) == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec(v_h__2_1046_);
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_apply_1(v_h__1_1045_, v___x_1047_);
return v___x_1048_;
}
else
{
lean_object* v_val_1049_; lean_object* v___x_1050_; 
lean_dec(v_h__1_1045_);
v_val_1049_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_val_1049_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1050_ = lean_apply_1(v_h__2_1046_, v_val_1049_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___redArg(lean_object* v_t_1051_, lean_object* v_h__1_1052_){
_start:
{
lean_object* v_size_1053_; lean_object* v_k_1054_; lean_object* v_v_1055_; lean_object* v_l_1056_; lean_object* v_r_1057_; lean_object* v___x_1058_; 
v_size_1053_ = lean_ctor_get(v_t_1051_, 0);
lean_inc(v_size_1053_);
v_k_1054_ = lean_ctor_get(v_t_1051_, 1);
lean_inc(v_k_1054_);
v_v_1055_ = lean_ctor_get(v_t_1051_, 2);
lean_inc(v_v_1055_);
v_l_1056_ = lean_ctor_get(v_t_1051_, 3);
lean_inc(v_l_1056_);
v_r_1057_ = lean_ctor_get(v_t_1051_, 4);
lean_inc(v_r_1057_);
lean_dec(v_t_1051_);
v___x_1058_ = lean_apply_6(v_h__1_1052_, v_size_1053_, v_k_1054_, v_v_1055_, v_l_1056_, v_r_1057_, lean_box(0));
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(lean_object* v_00_u03b1_1059_, lean_object* v_00_u03b2_1060_, lean_object* v_inst_1061_, lean_object* v_k_1062_, lean_object* v_motive_1063_, lean_object* v_t_1064_, lean_object* v_hlk_1065_, lean_object* v_h__1_1066_){
_start:
{
lean_object* v_size_1067_; lean_object* v_k_1068_; lean_object* v_v_1069_; lean_object* v_l_1070_; lean_object* v_r_1071_; lean_object* v___x_1072_; 
v_size_1067_ = lean_ctor_get(v_t_1064_, 0);
lean_inc(v_size_1067_);
v_k_1068_ = lean_ctor_get(v_t_1064_, 1);
lean_inc(v_k_1068_);
v_v_1069_ = lean_ctor_get(v_t_1064_, 2);
lean_inc(v_v_1069_);
v_l_1070_ = lean_ctor_get(v_t_1064_, 3);
lean_inc(v_l_1070_);
v_r_1071_ = lean_ctor_get(v_t_1064_, 4);
lean_inc(v_r_1071_);
lean_dec(v_t_1064_);
v___x_1072_ = lean_apply_6(v_h__1_1066_, v_size_1067_, v_k_1068_, v_v_1069_, v_l_1070_, v_r_1071_, lean_box(0));
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___boxed(lean_object* v_00_u03b1_1073_, lean_object* v_00_u03b2_1074_, lean_object* v_inst_1075_, lean_object* v_k_1076_, lean_object* v_motive_1077_, lean_object* v_t_1078_, lean_object* v_hlk_1079_, lean_object* v_h__1_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(v_00_u03b1_1073_, v_00_u03b2_1074_, v_inst_1075_, v_k_1076_, v_motive_1077_, v_t_1078_, v_hlk_1079_, v_h__1_1080_);
lean_dec(v_k_1076_);
lean_dec_ref(v_inst_1075_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1082_, lean_object* v_h__1_1083_, lean_object* v_h__2_1084_, lean_object* v_h__3_1085_){
_start:
{
if (lean_obj_tag(v_x_1082_) == 0)
{
lean_object* v_l_1086_; 
lean_dec(v_h__1_1083_);
v_l_1086_ = lean_ctor_get(v_x_1082_, 3);
if (lean_obj_tag(v_l_1086_) == 0)
{
lean_object* v_size_1087_; lean_object* v_k_1088_; lean_object* v_v_1089_; lean_object* v_r_1090_; lean_object* v_size_1091_; lean_object* v_k_1092_; lean_object* v_v_1093_; lean_object* v_l_1094_; lean_object* v_r_1095_; lean_object* v___x_1096_; 
lean_inc_ref(v_l_1086_);
lean_dec(v_h__2_1084_);
v_size_1087_ = lean_ctor_get(v_x_1082_, 0);
lean_inc(v_size_1087_);
v_k_1088_ = lean_ctor_get(v_x_1082_, 1);
lean_inc(v_k_1088_);
v_v_1089_ = lean_ctor_get(v_x_1082_, 2);
lean_inc(v_v_1089_);
v_r_1090_ = lean_ctor_get(v_x_1082_, 4);
lean_inc(v_r_1090_);
lean_dec_ref_known(v_x_1082_, 5);
v_size_1091_ = lean_ctor_get(v_l_1086_, 0);
lean_inc(v_size_1091_);
v_k_1092_ = lean_ctor_get(v_l_1086_, 1);
lean_inc(v_k_1092_);
v_v_1093_ = lean_ctor_get(v_l_1086_, 2);
lean_inc(v_v_1093_);
v_l_1094_ = lean_ctor_get(v_l_1086_, 3);
lean_inc(v_l_1094_);
v_r_1095_ = lean_ctor_get(v_l_1086_, 4);
lean_inc(v_r_1095_);
lean_dec_ref_known(v_l_1086_, 5);
v___x_1096_ = lean_apply_9(v_h__3_1085_, v_size_1087_, v_k_1088_, v_v_1089_, v_size_1091_, v_k_1092_, v_v_1093_, v_l_1094_, v_r_1095_, v_r_1090_);
return v___x_1096_;
}
else
{
lean_object* v_size_1097_; lean_object* v_k_1098_; lean_object* v_v_1099_; lean_object* v_r_1100_; lean_object* v___x_1101_; 
lean_dec(v_h__3_1085_);
v_size_1097_ = lean_ctor_get(v_x_1082_, 0);
lean_inc(v_size_1097_);
v_k_1098_ = lean_ctor_get(v_x_1082_, 1);
lean_inc(v_k_1098_);
v_v_1099_ = lean_ctor_get(v_x_1082_, 2);
lean_inc(v_v_1099_);
v_r_1100_ = lean_ctor_get(v_x_1082_, 4);
lean_inc(v_r_1100_);
lean_dec_ref_known(v_x_1082_, 5);
v___x_1101_ = lean_apply_4(v_h__2_1084_, v_size_1097_, v_k_1098_, v_v_1099_, v_r_1100_);
return v___x_1101_;
}
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec(v_h__3_1085_);
lean_dec(v_h__2_1084_);
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_apply_1(v_h__1_1083_, v___x_1102_);
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_motive_1106_, lean_object* v_x_1107_, lean_object* v_h__1_1108_, lean_object* v_h__2_1109_, lean_object* v_h__3_1110_){
_start:
{
if (lean_obj_tag(v_x_1107_) == 0)
{
lean_object* v_l_1111_; 
lean_dec(v_h__1_1108_);
v_l_1111_ = lean_ctor_get(v_x_1107_, 3);
if (lean_obj_tag(v_l_1111_) == 0)
{
lean_object* v_size_1112_; lean_object* v_k_1113_; lean_object* v_v_1114_; lean_object* v_r_1115_; lean_object* v_size_1116_; lean_object* v_k_1117_; lean_object* v_v_1118_; lean_object* v_l_1119_; lean_object* v_r_1120_; lean_object* v___x_1121_; 
lean_inc_ref(v_l_1111_);
lean_dec(v_h__2_1109_);
v_size_1112_ = lean_ctor_get(v_x_1107_, 0);
lean_inc(v_size_1112_);
v_k_1113_ = lean_ctor_get(v_x_1107_, 1);
lean_inc(v_k_1113_);
v_v_1114_ = lean_ctor_get(v_x_1107_, 2);
lean_inc(v_v_1114_);
v_r_1115_ = lean_ctor_get(v_x_1107_, 4);
lean_inc(v_r_1115_);
lean_dec_ref_known(v_x_1107_, 5);
v_size_1116_ = lean_ctor_get(v_l_1111_, 0);
lean_inc(v_size_1116_);
v_k_1117_ = lean_ctor_get(v_l_1111_, 1);
lean_inc(v_k_1117_);
v_v_1118_ = lean_ctor_get(v_l_1111_, 2);
lean_inc(v_v_1118_);
v_l_1119_ = lean_ctor_get(v_l_1111_, 3);
lean_inc(v_l_1119_);
v_r_1120_ = lean_ctor_get(v_l_1111_, 4);
lean_inc(v_r_1120_);
lean_dec_ref_known(v_l_1111_, 5);
v___x_1121_ = lean_apply_9(v_h__3_1110_, v_size_1112_, v_k_1113_, v_v_1114_, v_size_1116_, v_k_1117_, v_v_1118_, v_l_1119_, v_r_1120_, v_r_1115_);
return v___x_1121_;
}
else
{
lean_object* v_size_1122_; lean_object* v_k_1123_; lean_object* v_v_1124_; lean_object* v_r_1125_; lean_object* v___x_1126_; 
lean_dec(v_h__3_1110_);
v_size_1122_ = lean_ctor_get(v_x_1107_, 0);
lean_inc(v_size_1122_);
v_k_1123_ = lean_ctor_get(v_x_1107_, 1);
lean_inc(v_k_1123_);
v_v_1124_ = lean_ctor_get(v_x_1107_, 2);
lean_inc(v_v_1124_);
v_r_1125_ = lean_ctor_get(v_x_1107_, 4);
lean_inc(v_r_1125_);
lean_dec_ref_known(v_x_1107_, 5);
v___x_1126_ = lean_apply_4(v_h__2_1109_, v_size_1122_, v_k_1123_, v_v_1124_, v_r_1125_);
return v___x_1126_;
}
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_dec(v_h__3_1110_);
lean_dec(v_h__2_1109_);
v___x_1127_ = lean_box(0);
v___x_1128_ = lean_apply_1(v_h__1_1108_, v___x_1127_);
return v___x_1128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_step_1129_, lean_object* v_h__1_1130_, lean_object* v_h__2_1131_){
_start:
{
if (lean_obj_tag(v_step_1129_) == 0)
{
lean_object* v_a_1132_; lean_object* v_a_1133_; lean_object* v_a_1134_; lean_object* v___x_1135_; 
lean_dec(v_h__2_1131_);
v_a_1132_ = lean_ctor_get(v_step_1129_, 0);
lean_inc(v_a_1132_);
v_a_1133_ = lean_ctor_get(v_step_1129_, 1);
lean_inc(v_a_1133_);
v_a_1134_ = lean_ctor_get(v_step_1129_, 2);
lean_inc(v_a_1134_);
lean_dec_ref_known(v_step_1129_, 3);
v___x_1135_ = lean_apply_4(v_h__1_1130_, v_a_1132_, lean_box(0), v_a_1133_, v_a_1134_);
return v___x_1135_;
}
else
{
lean_object* v_a_1136_; lean_object* v_a_1137_; lean_object* v_a_1138_; lean_object* v___x_1139_; 
lean_dec(v_h__1_1130_);
v_a_1136_ = lean_ctor_get(v_step_1129_, 0);
lean_inc(v_a_1136_);
v_a_1137_ = lean_ctor_get(v_step_1129_, 1);
lean_inc(v_a_1137_);
v_a_1138_ = lean_ctor_get(v_step_1129_, 2);
lean_inc(v_a_1138_);
lean_dec_ref_known(v_step_1129_, 3);
v___x_1139_ = lean_apply_3(v_h__2_1131_, v_a_1136_, v_a_1137_, v_a_1138_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_1140_, lean_object* v_00_u03b2_1141_, lean_object* v_inst_1142_, lean_object* v_motive_1143_, lean_object* v_step_1144_, lean_object* v_h__1_1145_, lean_object* v_h__2_1146_){
_start:
{
if (lean_obj_tag(v_step_1144_) == 0)
{
lean_object* v_a_1147_; lean_object* v_a_1148_; lean_object* v_a_1149_; lean_object* v___x_1150_; 
lean_dec(v_h__2_1146_);
v_a_1147_ = lean_ctor_get(v_step_1144_, 0);
lean_inc(v_a_1147_);
v_a_1148_ = lean_ctor_get(v_step_1144_, 1);
lean_inc(v_a_1148_);
v_a_1149_ = lean_ctor_get(v_step_1144_, 2);
lean_inc(v_a_1149_);
lean_dec_ref_known(v_step_1144_, 3);
v___x_1150_ = lean_apply_4(v_h__1_1145_, v_a_1147_, lean_box(0), v_a_1148_, v_a_1149_);
return v___x_1150_;
}
else
{
lean_object* v_a_1151_; lean_object* v_a_1152_; lean_object* v_a_1153_; lean_object* v___x_1154_; 
lean_dec(v_h__1_1145_);
v_a_1151_ = lean_ctor_get(v_step_1144_, 0);
lean_inc(v_a_1151_);
v_a_1152_ = lean_ctor_get(v_step_1144_, 1);
lean_inc(v_a_1152_);
v_a_1153_ = lean_ctor_get(v_step_1144_, 2);
lean_inc(v_a_1153_);
lean_dec_ref_known(v_step_1144_, 3);
v___x_1154_ = lean_apply_3(v_h__2_1146_, v_a_1151_, v_a_1152_, v_a_1153_);
return v___x_1154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_00_u03b2_1156_, lean_object* v_inst_1157_, lean_object* v_motive_1158_, lean_object* v_step_1159_, lean_object* v_h__1_1160_, lean_object* v_h__2_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(v_00_u03b1_1155_, v_00_u03b2_1156_, v_inst_1157_, v_motive_1158_, v_step_1159_, v_h__1_1160_, v_h__2_1161_);
lean_dec_ref(v_inst_1157_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_h__1_1165_, lean_object* v_h__2_1166_, lean_object* v_h__3_1167_){
_start:
{
if (lean_obj_tag(v_x_1163_) == 0)
{
lean_object* v_l_1168_; 
lean_dec(v_h__1_1165_);
v_l_1168_ = lean_ctor_get(v_x_1163_, 3);
if (lean_obj_tag(v_l_1168_) == 0)
{
lean_object* v_size_1169_; lean_object* v_k_1170_; lean_object* v_v_1171_; lean_object* v_r_1172_; lean_object* v_size_1173_; lean_object* v_k_1174_; lean_object* v_v_1175_; lean_object* v_l_1176_; lean_object* v_r_1177_; lean_object* v___x_1178_; 
lean_inc_ref(v_l_1168_);
lean_dec(v_h__2_1166_);
v_size_1169_ = lean_ctor_get(v_x_1163_, 0);
lean_inc(v_size_1169_);
v_k_1170_ = lean_ctor_get(v_x_1163_, 1);
lean_inc(v_k_1170_);
v_v_1171_ = lean_ctor_get(v_x_1163_, 2);
lean_inc(v_v_1171_);
v_r_1172_ = lean_ctor_get(v_x_1163_, 4);
lean_inc(v_r_1172_);
lean_dec_ref_known(v_x_1163_, 5);
v_size_1173_ = lean_ctor_get(v_l_1168_, 0);
lean_inc(v_size_1173_);
v_k_1174_ = lean_ctor_get(v_l_1168_, 1);
lean_inc(v_k_1174_);
v_v_1175_ = lean_ctor_get(v_l_1168_, 2);
lean_inc(v_v_1175_);
v_l_1176_ = lean_ctor_get(v_l_1168_, 3);
lean_inc(v_l_1176_);
v_r_1177_ = lean_ctor_get(v_l_1168_, 4);
lean_inc(v_r_1177_);
lean_dec_ref_known(v_l_1168_, 5);
v___x_1178_ = lean_apply_10(v_h__3_1167_, v_size_1169_, v_k_1170_, v_v_1171_, v_size_1173_, v_k_1174_, v_v_1175_, v_l_1176_, v_r_1177_, v_r_1172_, v_x_1164_);
return v___x_1178_;
}
else
{
lean_object* v_size_1179_; lean_object* v_k_1180_; lean_object* v_v_1181_; lean_object* v_r_1182_; lean_object* v___x_1183_; 
lean_dec(v_h__3_1167_);
v_size_1179_ = lean_ctor_get(v_x_1163_, 0);
lean_inc(v_size_1179_);
v_k_1180_ = lean_ctor_get(v_x_1163_, 1);
lean_inc(v_k_1180_);
v_v_1181_ = lean_ctor_get(v_x_1163_, 2);
lean_inc(v_v_1181_);
v_r_1182_ = lean_ctor_get(v_x_1163_, 4);
lean_inc(v_r_1182_);
lean_dec_ref_known(v_x_1163_, 5);
v___x_1183_ = lean_apply_5(v_h__2_1166_, v_size_1179_, v_k_1180_, v_v_1181_, v_r_1182_, v_x_1164_);
return v___x_1183_;
}
}
else
{
lean_object* v___x_1184_; 
lean_dec(v_h__3_1167_);
lean_dec(v_h__2_1166_);
v___x_1184_ = lean_apply_1(v_h__1_1165_, v_x_1164_);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1185_, lean_object* v_00_u03b2_1186_, lean_object* v_motive_1187_, lean_object* v_x_1188_, lean_object* v_x_1189_, lean_object* v_h__1_1190_, lean_object* v_h__2_1191_, lean_object* v_h__3_1192_){
_start:
{
if (lean_obj_tag(v_x_1188_) == 0)
{
lean_object* v_l_1193_; 
lean_dec(v_h__1_1190_);
v_l_1193_ = lean_ctor_get(v_x_1188_, 3);
if (lean_obj_tag(v_l_1193_) == 0)
{
lean_object* v_size_1194_; lean_object* v_k_1195_; lean_object* v_v_1196_; lean_object* v_r_1197_; lean_object* v_size_1198_; lean_object* v_k_1199_; lean_object* v_v_1200_; lean_object* v_l_1201_; lean_object* v_r_1202_; lean_object* v___x_1203_; 
lean_inc_ref(v_l_1193_);
lean_dec(v_h__2_1191_);
v_size_1194_ = lean_ctor_get(v_x_1188_, 0);
lean_inc(v_size_1194_);
v_k_1195_ = lean_ctor_get(v_x_1188_, 1);
lean_inc(v_k_1195_);
v_v_1196_ = lean_ctor_get(v_x_1188_, 2);
lean_inc(v_v_1196_);
v_r_1197_ = lean_ctor_get(v_x_1188_, 4);
lean_inc(v_r_1197_);
lean_dec_ref_known(v_x_1188_, 5);
v_size_1198_ = lean_ctor_get(v_l_1193_, 0);
lean_inc(v_size_1198_);
v_k_1199_ = lean_ctor_get(v_l_1193_, 1);
lean_inc(v_k_1199_);
v_v_1200_ = lean_ctor_get(v_l_1193_, 2);
lean_inc(v_v_1200_);
v_l_1201_ = lean_ctor_get(v_l_1193_, 3);
lean_inc(v_l_1201_);
v_r_1202_ = lean_ctor_get(v_l_1193_, 4);
lean_inc(v_r_1202_);
lean_dec_ref_known(v_l_1193_, 5);
v___x_1203_ = lean_apply_10(v_h__3_1192_, v_size_1194_, v_k_1195_, v_v_1196_, v_size_1198_, v_k_1199_, v_v_1200_, v_l_1201_, v_r_1202_, v_r_1197_, v_x_1189_);
return v___x_1203_;
}
else
{
lean_object* v_size_1204_; lean_object* v_k_1205_; lean_object* v_v_1206_; lean_object* v_r_1207_; lean_object* v___x_1208_; 
lean_dec(v_h__3_1192_);
v_size_1204_ = lean_ctor_get(v_x_1188_, 0);
lean_inc(v_size_1204_);
v_k_1205_ = lean_ctor_get(v_x_1188_, 1);
lean_inc(v_k_1205_);
v_v_1206_ = lean_ctor_get(v_x_1188_, 2);
lean_inc(v_v_1206_);
v_r_1207_ = lean_ctor_get(v_x_1188_, 4);
lean_inc(v_r_1207_);
lean_dec_ref_known(v_x_1188_, 5);
v___x_1208_ = lean_apply_5(v_h__2_1191_, v_size_1204_, v_k_1205_, v_v_1206_, v_r_1207_, v_x_1189_);
return v___x_1208_;
}
}
else
{
lean_object* v___x_1209_; 
lean_dec(v_h__3_1192_);
lean_dec(v_h__2_1191_);
v___x_1209_ = lean_apply_1(v_h__1_1190_, v_x_1189_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object* v_x_1210_, lean_object* v_h__1_1211_, lean_object* v_h__2_1212_){
_start:
{
lean_object* v_l_1213_; 
v_l_1213_ = lean_ctor_get(v_x_1210_, 3);
if (lean_obj_tag(v_l_1213_) == 0)
{
lean_object* v_size_1214_; lean_object* v_k_1215_; lean_object* v_v_1216_; lean_object* v_r_1217_; lean_object* v_size_1218_; lean_object* v_k_1219_; lean_object* v_v_1220_; lean_object* v_l_1221_; lean_object* v_r_1222_; lean_object* v___x_1223_; 
lean_inc_ref(v_l_1213_);
lean_dec(v_h__1_1211_);
v_size_1214_ = lean_ctor_get(v_x_1210_, 0);
lean_inc(v_size_1214_);
v_k_1215_ = lean_ctor_get(v_x_1210_, 1);
lean_inc(v_k_1215_);
v_v_1216_ = lean_ctor_get(v_x_1210_, 2);
lean_inc(v_v_1216_);
v_r_1217_ = lean_ctor_get(v_x_1210_, 4);
lean_inc(v_r_1217_);
lean_dec(v_x_1210_);
v_size_1218_ = lean_ctor_get(v_l_1213_, 0);
lean_inc(v_size_1218_);
v_k_1219_ = lean_ctor_get(v_l_1213_, 1);
lean_inc(v_k_1219_);
v_v_1220_ = lean_ctor_get(v_l_1213_, 2);
lean_inc(v_v_1220_);
v_l_1221_ = lean_ctor_get(v_l_1213_, 3);
lean_inc(v_l_1221_);
v_r_1222_ = lean_ctor_get(v_l_1213_, 4);
lean_inc(v_r_1222_);
lean_dec_ref_known(v_l_1213_, 5);
v___x_1223_ = lean_apply_10(v_h__2_1212_, v_size_1214_, v_k_1215_, v_v_1216_, v_size_1218_, v_k_1219_, v_v_1220_, v_l_1221_, v_r_1222_, v_r_1217_, lean_box(0));
return v___x_1223_;
}
else
{
lean_object* v_size_1224_; lean_object* v_k_1225_; lean_object* v_v_1226_; lean_object* v_r_1227_; lean_object* v___x_1228_; 
lean_dec(v_h__2_1212_);
v_size_1224_ = lean_ctor_get(v_x_1210_, 0);
lean_inc(v_size_1224_);
v_k_1225_ = lean_ctor_get(v_x_1210_, 1);
lean_inc(v_k_1225_);
v_v_1226_ = lean_ctor_get(v_x_1210_, 2);
lean_inc(v_v_1226_);
v_r_1227_ = lean_ctor_get(v_x_1210_, 4);
lean_inc(v_r_1227_);
lean_dec(v_x_1210_);
v___x_1228_ = lean_apply_5(v_h__1_1211_, v_size_1224_, v_k_1225_, v_v_1226_, v_r_1227_, lean_box(0));
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* v_00_u03b1_1229_, lean_object* v_00_u03b2_1230_, lean_object* v_motive_1231_, lean_object* v_x_1232_, lean_object* v_x_1233_, lean_object* v_h__1_1234_, lean_object* v_h__2_1235_){
_start:
{
lean_object* v_l_1236_; 
v_l_1236_ = lean_ctor_get(v_x_1232_, 3);
if (lean_obj_tag(v_l_1236_) == 0)
{
lean_object* v_size_1237_; lean_object* v_k_1238_; lean_object* v_v_1239_; lean_object* v_r_1240_; lean_object* v_size_1241_; lean_object* v_k_1242_; lean_object* v_v_1243_; lean_object* v_l_1244_; lean_object* v_r_1245_; lean_object* v___x_1246_; 
lean_inc_ref(v_l_1236_);
lean_dec(v_h__1_1234_);
v_size_1237_ = lean_ctor_get(v_x_1232_, 0);
lean_inc(v_size_1237_);
v_k_1238_ = lean_ctor_get(v_x_1232_, 1);
lean_inc(v_k_1238_);
v_v_1239_ = lean_ctor_get(v_x_1232_, 2);
lean_inc(v_v_1239_);
v_r_1240_ = lean_ctor_get(v_x_1232_, 4);
lean_inc(v_r_1240_);
lean_dec(v_x_1232_);
v_size_1241_ = lean_ctor_get(v_l_1236_, 0);
lean_inc(v_size_1241_);
v_k_1242_ = lean_ctor_get(v_l_1236_, 1);
lean_inc(v_k_1242_);
v_v_1243_ = lean_ctor_get(v_l_1236_, 2);
lean_inc(v_v_1243_);
v_l_1244_ = lean_ctor_get(v_l_1236_, 3);
lean_inc(v_l_1244_);
v_r_1245_ = lean_ctor_get(v_l_1236_, 4);
lean_inc(v_r_1245_);
lean_dec_ref_known(v_l_1236_, 5);
v___x_1246_ = lean_apply_10(v_h__2_1235_, v_size_1237_, v_k_1238_, v_v_1239_, v_size_1241_, v_k_1242_, v_v_1243_, v_l_1244_, v_r_1245_, v_r_1240_, lean_box(0));
return v___x_1246_;
}
else
{
lean_object* v_size_1247_; lean_object* v_k_1248_; lean_object* v_v_1249_; lean_object* v_r_1250_; lean_object* v___x_1251_; 
lean_dec(v_h__2_1235_);
v_size_1247_ = lean_ctor_get(v_x_1232_, 0);
lean_inc(v_size_1247_);
v_k_1248_ = lean_ctor_get(v_x_1232_, 1);
lean_inc(v_k_1248_);
v_v_1249_ = lean_ctor_get(v_x_1232_, 2);
lean_inc(v_v_1249_);
v_r_1250_ = lean_ctor_get(v_x_1232_, 4);
lean_inc(v_r_1250_);
lean_dec(v_x_1232_);
v___x_1251_ = lean_apply_5(v_h__1_1234_, v_size_1247_, v_k_1248_, v_v_1249_, v_r_1250_, lean_box(0));
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1252_, lean_object* v_h__1_1253_, lean_object* v_h__2_1254_, lean_object* v_h__3_1255_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
lean_object* v_r_1256_; 
lean_dec(v_h__1_1253_);
v_r_1256_ = lean_ctor_get(v_x_1252_, 4);
if (lean_obj_tag(v_r_1256_) == 0)
{
lean_object* v_size_1257_; lean_object* v_k_1258_; lean_object* v_v_1259_; lean_object* v_l_1260_; lean_object* v_size_1261_; lean_object* v_k_1262_; lean_object* v_v_1263_; lean_object* v_l_1264_; lean_object* v_r_1265_; lean_object* v___x_1266_; 
lean_inc_ref(v_r_1256_);
lean_dec(v_h__2_1254_);
v_size_1257_ = lean_ctor_get(v_x_1252_, 0);
lean_inc(v_size_1257_);
v_k_1258_ = lean_ctor_get(v_x_1252_, 1);
lean_inc(v_k_1258_);
v_v_1259_ = lean_ctor_get(v_x_1252_, 2);
lean_inc(v_v_1259_);
v_l_1260_ = lean_ctor_get(v_x_1252_, 3);
lean_inc(v_l_1260_);
lean_dec_ref_known(v_x_1252_, 5);
v_size_1261_ = lean_ctor_get(v_r_1256_, 0);
lean_inc(v_size_1261_);
v_k_1262_ = lean_ctor_get(v_r_1256_, 1);
lean_inc(v_k_1262_);
v_v_1263_ = lean_ctor_get(v_r_1256_, 2);
lean_inc(v_v_1263_);
v_l_1264_ = lean_ctor_get(v_r_1256_, 3);
lean_inc(v_l_1264_);
v_r_1265_ = lean_ctor_get(v_r_1256_, 4);
lean_inc(v_r_1265_);
lean_dec_ref_known(v_r_1256_, 5);
v___x_1266_ = lean_apply_9(v_h__3_1255_, v_size_1257_, v_k_1258_, v_v_1259_, v_l_1260_, v_size_1261_, v_k_1262_, v_v_1263_, v_l_1264_, v_r_1265_);
return v___x_1266_;
}
else
{
lean_object* v_size_1267_; lean_object* v_k_1268_; lean_object* v_v_1269_; lean_object* v_l_1270_; lean_object* v___x_1271_; 
lean_dec(v_h__3_1255_);
v_size_1267_ = lean_ctor_get(v_x_1252_, 0);
lean_inc(v_size_1267_);
v_k_1268_ = lean_ctor_get(v_x_1252_, 1);
lean_inc(v_k_1268_);
v_v_1269_ = lean_ctor_get(v_x_1252_, 2);
lean_inc(v_v_1269_);
v_l_1270_ = lean_ctor_get(v_x_1252_, 3);
lean_inc(v_l_1270_);
lean_dec_ref_known(v_x_1252_, 5);
v___x_1271_ = lean_apply_4(v_h__2_1254_, v_size_1267_, v_k_1268_, v_v_1269_, v_l_1270_);
return v___x_1271_;
}
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_dec(v_h__3_1255_);
lean_dec(v_h__2_1254_);
v___x_1272_ = lean_box(0);
v___x_1273_ = lean_apply_1(v_h__1_1253_, v___x_1272_);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_motive_1276_, lean_object* v_x_1277_, lean_object* v_h__1_1278_, lean_object* v_h__2_1279_, lean_object* v_h__3_1280_){
_start:
{
if (lean_obj_tag(v_x_1277_) == 0)
{
lean_object* v_r_1281_; 
lean_dec(v_h__1_1278_);
v_r_1281_ = lean_ctor_get(v_x_1277_, 4);
if (lean_obj_tag(v_r_1281_) == 0)
{
lean_object* v_size_1282_; lean_object* v_k_1283_; lean_object* v_v_1284_; lean_object* v_l_1285_; lean_object* v_size_1286_; lean_object* v_k_1287_; lean_object* v_v_1288_; lean_object* v_l_1289_; lean_object* v_r_1290_; lean_object* v___x_1291_; 
lean_inc_ref(v_r_1281_);
lean_dec(v_h__2_1279_);
v_size_1282_ = lean_ctor_get(v_x_1277_, 0);
lean_inc(v_size_1282_);
v_k_1283_ = lean_ctor_get(v_x_1277_, 1);
lean_inc(v_k_1283_);
v_v_1284_ = lean_ctor_get(v_x_1277_, 2);
lean_inc(v_v_1284_);
v_l_1285_ = lean_ctor_get(v_x_1277_, 3);
lean_inc(v_l_1285_);
lean_dec_ref_known(v_x_1277_, 5);
v_size_1286_ = lean_ctor_get(v_r_1281_, 0);
lean_inc(v_size_1286_);
v_k_1287_ = lean_ctor_get(v_r_1281_, 1);
lean_inc(v_k_1287_);
v_v_1288_ = lean_ctor_get(v_r_1281_, 2);
lean_inc(v_v_1288_);
v_l_1289_ = lean_ctor_get(v_r_1281_, 3);
lean_inc(v_l_1289_);
v_r_1290_ = lean_ctor_get(v_r_1281_, 4);
lean_inc(v_r_1290_);
lean_dec_ref_known(v_r_1281_, 5);
v___x_1291_ = lean_apply_9(v_h__3_1280_, v_size_1282_, v_k_1283_, v_v_1284_, v_l_1285_, v_size_1286_, v_k_1287_, v_v_1288_, v_l_1289_, v_r_1290_);
return v___x_1291_;
}
else
{
lean_object* v_size_1292_; lean_object* v_k_1293_; lean_object* v_v_1294_; lean_object* v_l_1295_; lean_object* v___x_1296_; 
lean_dec(v_h__3_1280_);
v_size_1292_ = lean_ctor_get(v_x_1277_, 0);
lean_inc(v_size_1292_);
v_k_1293_ = lean_ctor_get(v_x_1277_, 1);
lean_inc(v_k_1293_);
v_v_1294_ = lean_ctor_get(v_x_1277_, 2);
lean_inc(v_v_1294_);
v_l_1295_ = lean_ctor_get(v_x_1277_, 3);
lean_inc(v_l_1295_);
lean_dec_ref_known(v_x_1277_, 5);
v___x_1296_ = lean_apply_4(v_h__2_1279_, v_size_1292_, v_k_1293_, v_v_1294_, v_l_1295_);
return v___x_1296_;
}
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_dec(v_h__3_1280_);
lean_dec(v_h__2_1279_);
v___x_1297_ = lean_box(0);
v___x_1298_ = lean_apply_1(v_h__1_1278_, v___x_1297_);
return v___x_1298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1299_, lean_object* v_x_1300_, lean_object* v_h__1_1301_, lean_object* v_h__2_1302_, lean_object* v_h__3_1303_){
_start:
{
if (lean_obj_tag(v_x_1299_) == 0)
{
lean_object* v_r_1304_; 
lean_dec(v_h__1_1301_);
v_r_1304_ = lean_ctor_get(v_x_1299_, 4);
if (lean_obj_tag(v_r_1304_) == 0)
{
lean_object* v_size_1305_; lean_object* v_k_1306_; lean_object* v_v_1307_; lean_object* v_l_1308_; lean_object* v_size_1309_; lean_object* v_k_1310_; lean_object* v_v_1311_; lean_object* v_l_1312_; lean_object* v_r_1313_; lean_object* v___x_1314_; 
lean_inc_ref(v_r_1304_);
lean_dec(v_h__2_1302_);
v_size_1305_ = lean_ctor_get(v_x_1299_, 0);
lean_inc(v_size_1305_);
v_k_1306_ = lean_ctor_get(v_x_1299_, 1);
lean_inc(v_k_1306_);
v_v_1307_ = lean_ctor_get(v_x_1299_, 2);
lean_inc(v_v_1307_);
v_l_1308_ = lean_ctor_get(v_x_1299_, 3);
lean_inc(v_l_1308_);
lean_dec_ref_known(v_x_1299_, 5);
v_size_1309_ = lean_ctor_get(v_r_1304_, 0);
lean_inc(v_size_1309_);
v_k_1310_ = lean_ctor_get(v_r_1304_, 1);
lean_inc(v_k_1310_);
v_v_1311_ = lean_ctor_get(v_r_1304_, 2);
lean_inc(v_v_1311_);
v_l_1312_ = lean_ctor_get(v_r_1304_, 3);
lean_inc(v_l_1312_);
v_r_1313_ = lean_ctor_get(v_r_1304_, 4);
lean_inc(v_r_1313_);
lean_dec_ref_known(v_r_1304_, 5);
v___x_1314_ = lean_apply_10(v_h__3_1303_, v_size_1305_, v_k_1306_, v_v_1307_, v_l_1308_, v_size_1309_, v_k_1310_, v_v_1311_, v_l_1312_, v_r_1313_, v_x_1300_);
return v___x_1314_;
}
else
{
lean_object* v_size_1315_; lean_object* v_k_1316_; lean_object* v_v_1317_; lean_object* v_l_1318_; lean_object* v___x_1319_; 
lean_dec(v_h__3_1303_);
v_size_1315_ = lean_ctor_get(v_x_1299_, 0);
lean_inc(v_size_1315_);
v_k_1316_ = lean_ctor_get(v_x_1299_, 1);
lean_inc(v_k_1316_);
v_v_1317_ = lean_ctor_get(v_x_1299_, 2);
lean_inc(v_v_1317_);
v_l_1318_ = lean_ctor_get(v_x_1299_, 3);
lean_inc(v_l_1318_);
lean_dec_ref_known(v_x_1299_, 5);
v___x_1319_ = lean_apply_5(v_h__2_1302_, v_size_1315_, v_k_1316_, v_v_1317_, v_l_1318_, v_x_1300_);
return v___x_1319_;
}
}
else
{
lean_object* v___x_1320_; 
lean_dec(v_h__3_1303_);
lean_dec(v_h__2_1302_);
v___x_1320_ = lean_apply_1(v_h__1_1301_, v_x_1300_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1321_, lean_object* v_00_u03b2_1322_, lean_object* v_motive_1323_, lean_object* v_x_1324_, lean_object* v_x_1325_, lean_object* v_h__1_1326_, lean_object* v_h__2_1327_, lean_object* v_h__3_1328_){
_start:
{
if (lean_obj_tag(v_x_1324_) == 0)
{
lean_object* v_r_1329_; 
lean_dec(v_h__1_1326_);
v_r_1329_ = lean_ctor_get(v_x_1324_, 4);
if (lean_obj_tag(v_r_1329_) == 0)
{
lean_object* v_size_1330_; lean_object* v_k_1331_; lean_object* v_v_1332_; lean_object* v_l_1333_; lean_object* v_size_1334_; lean_object* v_k_1335_; lean_object* v_v_1336_; lean_object* v_l_1337_; lean_object* v_r_1338_; lean_object* v___x_1339_; 
lean_inc_ref(v_r_1329_);
lean_dec(v_h__2_1327_);
v_size_1330_ = lean_ctor_get(v_x_1324_, 0);
lean_inc(v_size_1330_);
v_k_1331_ = lean_ctor_get(v_x_1324_, 1);
lean_inc(v_k_1331_);
v_v_1332_ = lean_ctor_get(v_x_1324_, 2);
lean_inc(v_v_1332_);
v_l_1333_ = lean_ctor_get(v_x_1324_, 3);
lean_inc(v_l_1333_);
lean_dec_ref_known(v_x_1324_, 5);
v_size_1334_ = lean_ctor_get(v_r_1329_, 0);
lean_inc(v_size_1334_);
v_k_1335_ = lean_ctor_get(v_r_1329_, 1);
lean_inc(v_k_1335_);
v_v_1336_ = lean_ctor_get(v_r_1329_, 2);
lean_inc(v_v_1336_);
v_l_1337_ = lean_ctor_get(v_r_1329_, 3);
lean_inc(v_l_1337_);
v_r_1338_ = lean_ctor_get(v_r_1329_, 4);
lean_inc(v_r_1338_);
lean_dec_ref_known(v_r_1329_, 5);
v___x_1339_ = lean_apply_10(v_h__3_1328_, v_size_1330_, v_k_1331_, v_v_1332_, v_l_1333_, v_size_1334_, v_k_1335_, v_v_1336_, v_l_1337_, v_r_1338_, v_x_1325_);
return v___x_1339_;
}
else
{
lean_object* v_size_1340_; lean_object* v_k_1341_; lean_object* v_v_1342_; lean_object* v_l_1343_; lean_object* v___x_1344_; 
lean_dec(v_h__3_1328_);
v_size_1340_ = lean_ctor_get(v_x_1324_, 0);
lean_inc(v_size_1340_);
v_k_1341_ = lean_ctor_get(v_x_1324_, 1);
lean_inc(v_k_1341_);
v_v_1342_ = lean_ctor_get(v_x_1324_, 2);
lean_inc(v_v_1342_);
v_l_1343_ = lean_ctor_get(v_x_1324_, 3);
lean_inc(v_l_1343_);
lean_dec_ref_known(v_x_1324_, 5);
v___x_1344_ = lean_apply_5(v_h__2_1327_, v_size_1340_, v_k_1341_, v_v_1342_, v_l_1343_, v_x_1325_);
return v___x_1344_;
}
}
else
{
lean_object* v___x_1345_; 
lean_dec(v_h__3_1328_);
lean_dec(v_h__2_1327_);
v___x_1345_ = lean_apply_1(v_h__1_1326_, v_x_1325_);
return v___x_1345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object* v_x_1346_, lean_object* v_h__1_1347_, lean_object* v_h__2_1348_){
_start:
{
lean_object* v_r_1349_; 
v_r_1349_ = lean_ctor_get(v_x_1346_, 4);
if (lean_obj_tag(v_r_1349_) == 0)
{
lean_object* v_size_1350_; lean_object* v_k_1351_; lean_object* v_v_1352_; lean_object* v_l_1353_; lean_object* v_size_1354_; lean_object* v_k_1355_; lean_object* v_v_1356_; lean_object* v_l_1357_; lean_object* v_r_1358_; lean_object* v___x_1359_; 
lean_inc_ref(v_r_1349_);
lean_dec(v_h__1_1347_);
v_size_1350_ = lean_ctor_get(v_x_1346_, 0);
lean_inc(v_size_1350_);
v_k_1351_ = lean_ctor_get(v_x_1346_, 1);
lean_inc(v_k_1351_);
v_v_1352_ = lean_ctor_get(v_x_1346_, 2);
lean_inc(v_v_1352_);
v_l_1353_ = lean_ctor_get(v_x_1346_, 3);
lean_inc(v_l_1353_);
lean_dec(v_x_1346_);
v_size_1354_ = lean_ctor_get(v_r_1349_, 0);
lean_inc(v_size_1354_);
v_k_1355_ = lean_ctor_get(v_r_1349_, 1);
lean_inc(v_k_1355_);
v_v_1356_ = lean_ctor_get(v_r_1349_, 2);
lean_inc(v_v_1356_);
v_l_1357_ = lean_ctor_get(v_r_1349_, 3);
lean_inc(v_l_1357_);
v_r_1358_ = lean_ctor_get(v_r_1349_, 4);
lean_inc(v_r_1358_);
lean_dec_ref_known(v_r_1349_, 5);
v___x_1359_ = lean_apply_10(v_h__2_1348_, v_size_1350_, v_k_1351_, v_v_1352_, v_l_1353_, v_size_1354_, v_k_1355_, v_v_1356_, v_l_1357_, v_r_1358_, lean_box(0));
return v___x_1359_;
}
else
{
lean_object* v_size_1360_; lean_object* v_k_1361_; lean_object* v_v_1362_; lean_object* v_l_1363_; lean_object* v___x_1364_; 
lean_dec(v_h__2_1348_);
v_size_1360_ = lean_ctor_get(v_x_1346_, 0);
lean_inc(v_size_1360_);
v_k_1361_ = lean_ctor_get(v_x_1346_, 1);
lean_inc(v_k_1361_);
v_v_1362_ = lean_ctor_get(v_x_1346_, 2);
lean_inc(v_v_1362_);
v_l_1363_ = lean_ctor_get(v_x_1346_, 3);
lean_inc(v_l_1363_);
lean_dec(v_x_1346_);
v___x_1364_ = lean_apply_5(v_h__1_1347_, v_size_1360_, v_k_1361_, v_v_1362_, v_l_1363_, lean_box(0));
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1365_, lean_object* v_00_u03b2_1366_, lean_object* v_motive_1367_, lean_object* v_x_1368_, lean_object* v_x_1369_, lean_object* v_h__1_1370_, lean_object* v_h__2_1371_){
_start:
{
lean_object* v_r_1372_; 
v_r_1372_ = lean_ctor_get(v_x_1368_, 4);
if (lean_obj_tag(v_r_1372_) == 0)
{
lean_object* v_size_1373_; lean_object* v_k_1374_; lean_object* v_v_1375_; lean_object* v_l_1376_; lean_object* v_size_1377_; lean_object* v_k_1378_; lean_object* v_v_1379_; lean_object* v_l_1380_; lean_object* v_r_1381_; lean_object* v___x_1382_; 
lean_inc_ref(v_r_1372_);
lean_dec(v_h__1_1370_);
v_size_1373_ = lean_ctor_get(v_x_1368_, 0);
lean_inc(v_size_1373_);
v_k_1374_ = lean_ctor_get(v_x_1368_, 1);
lean_inc(v_k_1374_);
v_v_1375_ = lean_ctor_get(v_x_1368_, 2);
lean_inc(v_v_1375_);
v_l_1376_ = lean_ctor_get(v_x_1368_, 3);
lean_inc(v_l_1376_);
lean_dec(v_x_1368_);
v_size_1377_ = lean_ctor_get(v_r_1372_, 0);
lean_inc(v_size_1377_);
v_k_1378_ = lean_ctor_get(v_r_1372_, 1);
lean_inc(v_k_1378_);
v_v_1379_ = lean_ctor_get(v_r_1372_, 2);
lean_inc(v_v_1379_);
v_l_1380_ = lean_ctor_get(v_r_1372_, 3);
lean_inc(v_l_1380_);
v_r_1381_ = lean_ctor_get(v_r_1372_, 4);
lean_inc(v_r_1381_);
lean_dec_ref_known(v_r_1372_, 5);
v___x_1382_ = lean_apply_10(v_h__2_1371_, v_size_1373_, v_k_1374_, v_v_1375_, v_l_1376_, v_size_1377_, v_k_1378_, v_v_1379_, v_l_1380_, v_r_1381_, lean_box(0));
return v___x_1382_;
}
else
{
lean_object* v_size_1383_; lean_object* v_k_1384_; lean_object* v_v_1385_; lean_object* v_l_1386_; lean_object* v___x_1387_; 
lean_dec(v_h__2_1371_);
v_size_1383_ = lean_ctor_get(v_x_1368_, 0);
lean_inc(v_size_1383_);
v_k_1384_ = lean_ctor_get(v_x_1368_, 1);
lean_inc(v_k_1384_);
v_v_1385_ = lean_ctor_get(v_x_1368_, 2);
lean_inc(v_v_1385_);
v_l_1386_ = lean_ctor_get(v_x_1368_, 3);
lean_inc(v_l_1386_);
lean_dec(v_x_1368_);
v___x_1387_ = lean_apply_5(v_h__1_1370_, v_size_1383_, v_k_1384_, v_v_1385_, v_l_1386_, lean_box(0));
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object* v_x_1388_, lean_object* v_x_1389_, lean_object* v_h__1_1390_, lean_object* v_h__2_1391_, lean_object* v_h__3_1392_){
_start:
{
if (lean_obj_tag(v_x_1388_) == 0)
{
lean_object* v_l_1393_; 
lean_dec(v_h__1_1390_);
v_l_1393_ = lean_ctor_get(v_x_1388_, 3);
if (lean_obj_tag(v_l_1393_) == 0)
{
lean_object* v_size_1394_; lean_object* v_k_1395_; lean_object* v_v_1396_; lean_object* v_r_1397_; lean_object* v_size_1398_; lean_object* v_k_1399_; lean_object* v_v_1400_; lean_object* v_l_1401_; lean_object* v_r_1402_; lean_object* v___x_1403_; 
lean_inc_ref(v_l_1393_);
lean_dec(v_h__2_1391_);
v_size_1394_ = lean_ctor_get(v_x_1388_, 0);
lean_inc(v_size_1394_);
v_k_1395_ = lean_ctor_get(v_x_1388_, 1);
lean_inc(v_k_1395_);
v_v_1396_ = lean_ctor_get(v_x_1388_, 2);
lean_inc(v_v_1396_);
v_r_1397_ = lean_ctor_get(v_x_1388_, 4);
lean_inc(v_r_1397_);
lean_dec_ref_known(v_x_1388_, 5);
v_size_1398_ = lean_ctor_get(v_l_1393_, 0);
lean_inc(v_size_1398_);
v_k_1399_ = lean_ctor_get(v_l_1393_, 1);
lean_inc(v_k_1399_);
v_v_1400_ = lean_ctor_get(v_l_1393_, 2);
lean_inc(v_v_1400_);
v_l_1401_ = lean_ctor_get(v_l_1393_, 3);
lean_inc(v_l_1401_);
v_r_1402_ = lean_ctor_get(v_l_1393_, 4);
lean_inc(v_r_1402_);
lean_dec_ref_known(v_l_1393_, 5);
v___x_1403_ = lean_apply_10(v_h__3_1392_, v_size_1394_, v_k_1395_, v_v_1396_, v_size_1398_, v_k_1399_, v_v_1400_, v_l_1401_, v_r_1402_, v_r_1397_, v_x_1389_);
return v___x_1403_;
}
else
{
lean_object* v_size_1404_; lean_object* v_k_1405_; lean_object* v_v_1406_; lean_object* v_r_1407_; lean_object* v___x_1408_; 
lean_dec(v_h__3_1392_);
v_size_1404_ = lean_ctor_get(v_x_1388_, 0);
lean_inc(v_size_1404_);
v_k_1405_ = lean_ctor_get(v_x_1388_, 1);
lean_inc(v_k_1405_);
v_v_1406_ = lean_ctor_get(v_x_1388_, 2);
lean_inc(v_v_1406_);
v_r_1407_ = lean_ctor_get(v_x_1388_, 4);
lean_inc(v_r_1407_);
lean_dec_ref_known(v_x_1388_, 5);
v___x_1408_ = lean_apply_5(v_h__2_1391_, v_size_1404_, v_k_1405_, v_v_1406_, v_r_1407_, v_x_1389_);
return v___x_1408_;
}
}
else
{
lean_object* v___x_1409_; 
lean_dec(v_h__3_1392_);
lean_dec(v_h__2_1391_);
v___x_1409_ = lean_apply_1(v_h__1_1390_, v_x_1389_);
return v___x_1409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* v_00_u03b1_1410_, lean_object* v_00_u03b2_1411_, lean_object* v_motive_1412_, lean_object* v_x_1413_, lean_object* v_x_1414_, lean_object* v_h__1_1415_, lean_object* v_h__2_1416_, lean_object* v_h__3_1417_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v_l_1418_; 
lean_dec(v_h__1_1415_);
v_l_1418_ = lean_ctor_get(v_x_1413_, 3);
if (lean_obj_tag(v_l_1418_) == 0)
{
lean_object* v_size_1419_; lean_object* v_k_1420_; lean_object* v_v_1421_; lean_object* v_r_1422_; lean_object* v_size_1423_; lean_object* v_k_1424_; lean_object* v_v_1425_; lean_object* v_l_1426_; lean_object* v_r_1427_; lean_object* v___x_1428_; 
lean_inc_ref(v_l_1418_);
lean_dec(v_h__2_1416_);
v_size_1419_ = lean_ctor_get(v_x_1413_, 0);
lean_inc(v_size_1419_);
v_k_1420_ = lean_ctor_get(v_x_1413_, 1);
lean_inc(v_k_1420_);
v_v_1421_ = lean_ctor_get(v_x_1413_, 2);
lean_inc(v_v_1421_);
v_r_1422_ = lean_ctor_get(v_x_1413_, 4);
lean_inc(v_r_1422_);
lean_dec_ref_known(v_x_1413_, 5);
v_size_1423_ = lean_ctor_get(v_l_1418_, 0);
lean_inc(v_size_1423_);
v_k_1424_ = lean_ctor_get(v_l_1418_, 1);
lean_inc(v_k_1424_);
v_v_1425_ = lean_ctor_get(v_l_1418_, 2);
lean_inc(v_v_1425_);
v_l_1426_ = lean_ctor_get(v_l_1418_, 3);
lean_inc(v_l_1426_);
v_r_1427_ = lean_ctor_get(v_l_1418_, 4);
lean_inc(v_r_1427_);
lean_dec_ref_known(v_l_1418_, 5);
v___x_1428_ = lean_apply_10(v_h__3_1417_, v_size_1419_, v_k_1420_, v_v_1421_, v_size_1423_, v_k_1424_, v_v_1425_, v_l_1426_, v_r_1427_, v_r_1422_, v_x_1414_);
return v___x_1428_;
}
else
{
lean_object* v_size_1429_; lean_object* v_k_1430_; lean_object* v_v_1431_; lean_object* v_r_1432_; lean_object* v___x_1433_; 
lean_dec(v_h__3_1417_);
v_size_1429_ = lean_ctor_get(v_x_1413_, 0);
lean_inc(v_size_1429_);
v_k_1430_ = lean_ctor_get(v_x_1413_, 1);
lean_inc(v_k_1430_);
v_v_1431_ = lean_ctor_get(v_x_1413_, 2);
lean_inc(v_v_1431_);
v_r_1432_ = lean_ctor_get(v_x_1413_, 4);
lean_inc(v_r_1432_);
lean_dec_ref_known(v_x_1413_, 5);
v___x_1433_ = lean_apply_5(v_h__2_1416_, v_size_1429_, v_k_1430_, v_v_1431_, v_r_1432_, v_x_1414_);
return v___x_1433_;
}
}
else
{
lean_object* v___x_1434_; 
lean_dec(v_h__3_1417_);
lean_dec(v_h__2_1416_);
v___x_1434_ = lean_apply_1(v_h__1_1415_, v_x_1414_);
return v___x_1434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object* v_x_1435_, lean_object* v_x_1436_, lean_object* v_h__1_1437_, lean_object* v_h__2_1438_, lean_object* v_h__3_1439_){
_start:
{
if (lean_obj_tag(v_x_1435_) == 0)
{
lean_object* v_r_1440_; 
lean_dec(v_h__1_1437_);
v_r_1440_ = lean_ctor_get(v_x_1435_, 4);
if (lean_obj_tag(v_r_1440_) == 0)
{
lean_object* v_size_1441_; lean_object* v_k_1442_; lean_object* v_v_1443_; lean_object* v_l_1444_; lean_object* v_size_1445_; lean_object* v_k_1446_; lean_object* v_v_1447_; lean_object* v_l_1448_; lean_object* v_r_1449_; lean_object* v___x_1450_; 
lean_inc_ref(v_r_1440_);
lean_dec(v_h__2_1438_);
v_size_1441_ = lean_ctor_get(v_x_1435_, 0);
lean_inc(v_size_1441_);
v_k_1442_ = lean_ctor_get(v_x_1435_, 1);
lean_inc(v_k_1442_);
v_v_1443_ = lean_ctor_get(v_x_1435_, 2);
lean_inc(v_v_1443_);
v_l_1444_ = lean_ctor_get(v_x_1435_, 3);
lean_inc(v_l_1444_);
lean_dec_ref_known(v_x_1435_, 5);
v_size_1445_ = lean_ctor_get(v_r_1440_, 0);
lean_inc(v_size_1445_);
v_k_1446_ = lean_ctor_get(v_r_1440_, 1);
lean_inc(v_k_1446_);
v_v_1447_ = lean_ctor_get(v_r_1440_, 2);
lean_inc(v_v_1447_);
v_l_1448_ = lean_ctor_get(v_r_1440_, 3);
lean_inc(v_l_1448_);
v_r_1449_ = lean_ctor_get(v_r_1440_, 4);
lean_inc(v_r_1449_);
lean_dec_ref_known(v_r_1440_, 5);
v___x_1450_ = lean_apply_10(v_h__3_1439_, v_size_1441_, v_k_1442_, v_v_1443_, v_l_1444_, v_size_1445_, v_k_1446_, v_v_1447_, v_l_1448_, v_r_1449_, v_x_1436_);
return v___x_1450_;
}
else
{
lean_object* v_size_1451_; lean_object* v_k_1452_; lean_object* v_v_1453_; lean_object* v_l_1454_; lean_object* v___x_1455_; 
lean_dec(v_h__3_1439_);
v_size_1451_ = lean_ctor_get(v_x_1435_, 0);
lean_inc(v_size_1451_);
v_k_1452_ = lean_ctor_get(v_x_1435_, 1);
lean_inc(v_k_1452_);
v_v_1453_ = lean_ctor_get(v_x_1435_, 2);
lean_inc(v_v_1453_);
v_l_1454_ = lean_ctor_get(v_x_1435_, 3);
lean_inc(v_l_1454_);
lean_dec_ref_known(v_x_1435_, 5);
v___x_1455_ = lean_apply_5(v_h__2_1438_, v_size_1451_, v_k_1452_, v_v_1453_, v_l_1454_, v_x_1436_);
return v___x_1455_;
}
}
else
{
lean_object* v___x_1456_; 
lean_dec(v_h__3_1439_);
lean_dec(v_h__2_1438_);
v___x_1456_ = lean_apply_1(v_h__1_1437_, v_x_1436_);
return v___x_1456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object* v_00_u03b1_1457_, lean_object* v_00_u03b2_1458_, lean_object* v_motive_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_, lean_object* v_h__1_1462_, lean_object* v_h__2_1463_, lean_object* v_h__3_1464_){
_start:
{
if (lean_obj_tag(v_x_1460_) == 0)
{
lean_object* v_r_1465_; 
lean_dec(v_h__1_1462_);
v_r_1465_ = lean_ctor_get(v_x_1460_, 4);
if (lean_obj_tag(v_r_1465_) == 0)
{
lean_object* v_size_1466_; lean_object* v_k_1467_; lean_object* v_v_1468_; lean_object* v_l_1469_; lean_object* v_size_1470_; lean_object* v_k_1471_; lean_object* v_v_1472_; lean_object* v_l_1473_; lean_object* v_r_1474_; lean_object* v___x_1475_; 
lean_inc_ref(v_r_1465_);
lean_dec(v_h__2_1463_);
v_size_1466_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_size_1466_);
v_k_1467_ = lean_ctor_get(v_x_1460_, 1);
lean_inc(v_k_1467_);
v_v_1468_ = lean_ctor_get(v_x_1460_, 2);
lean_inc(v_v_1468_);
v_l_1469_ = lean_ctor_get(v_x_1460_, 3);
lean_inc(v_l_1469_);
lean_dec_ref_known(v_x_1460_, 5);
v_size_1470_ = lean_ctor_get(v_r_1465_, 0);
lean_inc(v_size_1470_);
v_k_1471_ = lean_ctor_get(v_r_1465_, 1);
lean_inc(v_k_1471_);
v_v_1472_ = lean_ctor_get(v_r_1465_, 2);
lean_inc(v_v_1472_);
v_l_1473_ = lean_ctor_get(v_r_1465_, 3);
lean_inc(v_l_1473_);
v_r_1474_ = lean_ctor_get(v_r_1465_, 4);
lean_inc(v_r_1474_);
lean_dec_ref_known(v_r_1465_, 5);
v___x_1475_ = lean_apply_10(v_h__3_1464_, v_size_1466_, v_k_1467_, v_v_1468_, v_l_1469_, v_size_1470_, v_k_1471_, v_v_1472_, v_l_1473_, v_r_1474_, v_x_1461_);
return v___x_1475_;
}
else
{
lean_object* v_size_1476_; lean_object* v_k_1477_; lean_object* v_v_1478_; lean_object* v_l_1479_; lean_object* v___x_1480_; 
lean_dec(v_h__3_1464_);
v_size_1476_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_size_1476_);
v_k_1477_ = lean_ctor_get(v_x_1460_, 1);
lean_inc(v_k_1477_);
v_v_1478_ = lean_ctor_get(v_x_1460_, 2);
lean_inc(v_v_1478_);
v_l_1479_ = lean_ctor_get(v_x_1460_, 3);
lean_inc(v_l_1479_);
lean_dec_ref_known(v_x_1460_, 5);
v___x_1480_ = lean_apply_5(v_h__2_1463_, v_size_1476_, v_k_1477_, v_v_1478_, v_l_1479_, v_x_1461_);
return v___x_1480_;
}
}
else
{
lean_object* v___x_1481_; 
lean_dec(v_h__3_1464_);
lean_dec(v_h__2_1463_);
v___x_1481_ = lean_apply_1(v_h__1_1462_, v_x_1461_);
return v___x_1481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1482_, lean_object* v_h__1_1483_, lean_object* v_h__2_1484_, lean_object* v_h__3_1485_){
_start:
{
if (lean_obj_tag(v_x_1482_) == 0)
{
lean_object* v_l_1486_; 
lean_dec(v_h__1_1483_);
v_l_1486_ = lean_ctor_get(v_x_1482_, 3);
if (lean_obj_tag(v_l_1486_) == 0)
{
lean_object* v_size_1487_; lean_object* v_k_1488_; lean_object* v_v_1489_; lean_object* v_r_1490_; lean_object* v_size_1491_; lean_object* v_k_1492_; lean_object* v_v_1493_; lean_object* v_l_1494_; lean_object* v_r_1495_; lean_object* v___x_1496_; 
lean_inc_ref(v_l_1486_);
lean_dec(v_h__2_1484_);
v_size_1487_ = lean_ctor_get(v_x_1482_, 0);
lean_inc(v_size_1487_);
v_k_1488_ = lean_ctor_get(v_x_1482_, 1);
lean_inc(v_k_1488_);
v_v_1489_ = lean_ctor_get(v_x_1482_, 2);
lean_inc(v_v_1489_);
v_r_1490_ = lean_ctor_get(v_x_1482_, 4);
lean_inc(v_r_1490_);
lean_dec_ref_known(v_x_1482_, 5);
v_size_1491_ = lean_ctor_get(v_l_1486_, 0);
lean_inc(v_size_1491_);
v_k_1492_ = lean_ctor_get(v_l_1486_, 1);
lean_inc(v_k_1492_);
v_v_1493_ = lean_ctor_get(v_l_1486_, 2);
lean_inc(v_v_1493_);
v_l_1494_ = lean_ctor_get(v_l_1486_, 3);
lean_inc(v_l_1494_);
v_r_1495_ = lean_ctor_get(v_l_1486_, 4);
lean_inc(v_r_1495_);
lean_dec_ref_known(v_l_1486_, 5);
v___x_1496_ = lean_apply_9(v_h__3_1485_, v_size_1487_, v_k_1488_, v_v_1489_, v_size_1491_, v_k_1492_, v_v_1493_, v_l_1494_, v_r_1495_, v_r_1490_);
return v___x_1496_;
}
else
{
lean_object* v_size_1497_; lean_object* v_k_1498_; lean_object* v_v_1499_; lean_object* v_r_1500_; lean_object* v___x_1501_; 
lean_dec(v_h__3_1485_);
v_size_1497_ = lean_ctor_get(v_x_1482_, 0);
lean_inc(v_size_1497_);
v_k_1498_ = lean_ctor_get(v_x_1482_, 1);
lean_inc(v_k_1498_);
v_v_1499_ = lean_ctor_get(v_x_1482_, 2);
lean_inc(v_v_1499_);
v_r_1500_ = lean_ctor_get(v_x_1482_, 4);
lean_inc(v_r_1500_);
lean_dec_ref_known(v_x_1482_, 5);
v___x_1501_ = lean_apply_4(v_h__2_1484_, v_size_1497_, v_k_1498_, v_v_1499_, v_r_1500_);
return v___x_1501_;
}
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_dec(v_h__3_1485_);
lean_dec(v_h__2_1484_);
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_apply_1(v_h__1_1483_, v___x_1502_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1504_, lean_object* v_00_u03b2_1505_, lean_object* v_motive_1506_, lean_object* v_x_1507_, lean_object* v_h__1_1508_, lean_object* v_h__2_1509_, lean_object* v_h__3_1510_){
_start:
{
if (lean_obj_tag(v_x_1507_) == 0)
{
lean_object* v_l_1511_; 
lean_dec(v_h__1_1508_);
v_l_1511_ = lean_ctor_get(v_x_1507_, 3);
if (lean_obj_tag(v_l_1511_) == 0)
{
lean_object* v_size_1512_; lean_object* v_k_1513_; lean_object* v_v_1514_; lean_object* v_r_1515_; lean_object* v_size_1516_; lean_object* v_k_1517_; lean_object* v_v_1518_; lean_object* v_l_1519_; lean_object* v_r_1520_; lean_object* v___x_1521_; 
lean_inc_ref(v_l_1511_);
lean_dec(v_h__2_1509_);
v_size_1512_ = lean_ctor_get(v_x_1507_, 0);
lean_inc(v_size_1512_);
v_k_1513_ = lean_ctor_get(v_x_1507_, 1);
lean_inc(v_k_1513_);
v_v_1514_ = lean_ctor_get(v_x_1507_, 2);
lean_inc(v_v_1514_);
v_r_1515_ = lean_ctor_get(v_x_1507_, 4);
lean_inc(v_r_1515_);
lean_dec_ref_known(v_x_1507_, 5);
v_size_1516_ = lean_ctor_get(v_l_1511_, 0);
lean_inc(v_size_1516_);
v_k_1517_ = lean_ctor_get(v_l_1511_, 1);
lean_inc(v_k_1517_);
v_v_1518_ = lean_ctor_get(v_l_1511_, 2);
lean_inc(v_v_1518_);
v_l_1519_ = lean_ctor_get(v_l_1511_, 3);
lean_inc(v_l_1519_);
v_r_1520_ = lean_ctor_get(v_l_1511_, 4);
lean_inc(v_r_1520_);
lean_dec_ref_known(v_l_1511_, 5);
v___x_1521_ = lean_apply_9(v_h__3_1510_, v_size_1512_, v_k_1513_, v_v_1514_, v_size_1516_, v_k_1517_, v_v_1518_, v_l_1519_, v_r_1520_, v_r_1515_);
return v___x_1521_;
}
else
{
lean_object* v_size_1522_; lean_object* v_k_1523_; lean_object* v_v_1524_; lean_object* v_r_1525_; lean_object* v___x_1526_; 
lean_dec(v_h__3_1510_);
v_size_1522_ = lean_ctor_get(v_x_1507_, 0);
lean_inc(v_size_1522_);
v_k_1523_ = lean_ctor_get(v_x_1507_, 1);
lean_inc(v_k_1523_);
v_v_1524_ = lean_ctor_get(v_x_1507_, 2);
lean_inc(v_v_1524_);
v_r_1525_ = lean_ctor_get(v_x_1507_, 4);
lean_inc(v_r_1525_);
lean_dec_ref_known(v_x_1507_, 5);
v___x_1526_ = lean_apply_4(v_h__2_1509_, v_size_1522_, v_k_1523_, v_v_1524_, v_r_1525_);
return v___x_1526_;
}
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec(v_h__3_1510_);
lean_dec(v_h__2_1509_);
v___x_1527_ = lean_box(0);
v___x_1528_ = lean_apply_1(v_h__1_1508_, v___x_1527_);
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_h__1_1531_, lean_object* v_h__2_1532_, lean_object* v_h__3_1533_){
_start:
{
if (lean_obj_tag(v_x_1529_) == 0)
{
lean_object* v_l_1534_; 
lean_dec(v_h__1_1531_);
v_l_1534_ = lean_ctor_get(v_x_1529_, 3);
if (lean_obj_tag(v_l_1534_) == 0)
{
lean_object* v_size_1535_; lean_object* v_k_1536_; lean_object* v_v_1537_; lean_object* v_r_1538_; lean_object* v_size_1539_; lean_object* v_k_1540_; lean_object* v_v_1541_; lean_object* v_l_1542_; lean_object* v_r_1543_; lean_object* v___x_1544_; 
lean_inc_ref(v_l_1534_);
lean_dec(v_h__2_1532_);
v_size_1535_ = lean_ctor_get(v_x_1529_, 0);
lean_inc(v_size_1535_);
v_k_1536_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_k_1536_);
v_v_1537_ = lean_ctor_get(v_x_1529_, 2);
lean_inc(v_v_1537_);
v_r_1538_ = lean_ctor_get(v_x_1529_, 4);
lean_inc(v_r_1538_);
lean_dec_ref_known(v_x_1529_, 5);
v_size_1539_ = lean_ctor_get(v_l_1534_, 0);
lean_inc(v_size_1539_);
v_k_1540_ = lean_ctor_get(v_l_1534_, 1);
lean_inc(v_k_1540_);
v_v_1541_ = lean_ctor_get(v_l_1534_, 2);
lean_inc(v_v_1541_);
v_l_1542_ = lean_ctor_get(v_l_1534_, 3);
lean_inc(v_l_1542_);
v_r_1543_ = lean_ctor_get(v_l_1534_, 4);
lean_inc(v_r_1543_);
lean_dec_ref_known(v_l_1534_, 5);
v___x_1544_ = lean_apply_10(v_h__3_1533_, v_size_1535_, v_k_1536_, v_v_1537_, v_size_1539_, v_k_1540_, v_v_1541_, v_l_1542_, v_r_1543_, v_r_1538_, v_x_1530_);
return v___x_1544_;
}
else
{
lean_object* v_size_1545_; lean_object* v_k_1546_; lean_object* v_v_1547_; lean_object* v_r_1548_; lean_object* v___x_1549_; 
lean_dec(v_h__3_1533_);
v_size_1545_ = lean_ctor_get(v_x_1529_, 0);
lean_inc(v_size_1545_);
v_k_1546_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_k_1546_);
v_v_1547_ = lean_ctor_get(v_x_1529_, 2);
lean_inc(v_v_1547_);
v_r_1548_ = lean_ctor_get(v_x_1529_, 4);
lean_inc(v_r_1548_);
lean_dec_ref_known(v_x_1529_, 5);
v___x_1549_ = lean_apply_5(v_h__2_1532_, v_size_1545_, v_k_1546_, v_v_1547_, v_r_1548_, v_x_1530_);
return v___x_1549_;
}
}
else
{
lean_object* v___x_1550_; 
lean_dec(v_h__3_1533_);
lean_dec(v_h__2_1532_);
v___x_1550_ = lean_apply_1(v_h__1_1531_, v_x_1530_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1551_, lean_object* v_00_u03b2_1552_, lean_object* v_motive_1553_, lean_object* v_x_1554_, lean_object* v_x_1555_, lean_object* v_h__1_1556_, lean_object* v_h__2_1557_, lean_object* v_h__3_1558_){
_start:
{
if (lean_obj_tag(v_x_1554_) == 0)
{
lean_object* v_l_1559_; 
lean_dec(v_h__1_1556_);
v_l_1559_ = lean_ctor_get(v_x_1554_, 3);
if (lean_obj_tag(v_l_1559_) == 0)
{
lean_object* v_size_1560_; lean_object* v_k_1561_; lean_object* v_v_1562_; lean_object* v_r_1563_; lean_object* v_size_1564_; lean_object* v_k_1565_; lean_object* v_v_1566_; lean_object* v_l_1567_; lean_object* v_r_1568_; lean_object* v___x_1569_; 
lean_inc_ref(v_l_1559_);
lean_dec(v_h__2_1557_);
v_size_1560_ = lean_ctor_get(v_x_1554_, 0);
lean_inc(v_size_1560_);
v_k_1561_ = lean_ctor_get(v_x_1554_, 1);
lean_inc(v_k_1561_);
v_v_1562_ = lean_ctor_get(v_x_1554_, 2);
lean_inc(v_v_1562_);
v_r_1563_ = lean_ctor_get(v_x_1554_, 4);
lean_inc(v_r_1563_);
lean_dec_ref_known(v_x_1554_, 5);
v_size_1564_ = lean_ctor_get(v_l_1559_, 0);
lean_inc(v_size_1564_);
v_k_1565_ = lean_ctor_get(v_l_1559_, 1);
lean_inc(v_k_1565_);
v_v_1566_ = lean_ctor_get(v_l_1559_, 2);
lean_inc(v_v_1566_);
v_l_1567_ = lean_ctor_get(v_l_1559_, 3);
lean_inc(v_l_1567_);
v_r_1568_ = lean_ctor_get(v_l_1559_, 4);
lean_inc(v_r_1568_);
lean_dec_ref_known(v_l_1559_, 5);
v___x_1569_ = lean_apply_10(v_h__3_1558_, v_size_1560_, v_k_1561_, v_v_1562_, v_size_1564_, v_k_1565_, v_v_1566_, v_l_1567_, v_r_1568_, v_r_1563_, v_x_1555_);
return v___x_1569_;
}
else
{
lean_object* v_size_1570_; lean_object* v_k_1571_; lean_object* v_v_1572_; lean_object* v_r_1573_; lean_object* v___x_1574_; 
lean_dec(v_h__3_1558_);
v_size_1570_ = lean_ctor_get(v_x_1554_, 0);
lean_inc(v_size_1570_);
v_k_1571_ = lean_ctor_get(v_x_1554_, 1);
lean_inc(v_k_1571_);
v_v_1572_ = lean_ctor_get(v_x_1554_, 2);
lean_inc(v_v_1572_);
v_r_1573_ = lean_ctor_get(v_x_1554_, 4);
lean_inc(v_r_1573_);
lean_dec_ref_known(v_x_1554_, 5);
v___x_1574_ = lean_apply_5(v_h__2_1557_, v_size_1570_, v_k_1571_, v_v_1572_, v_r_1573_, v_x_1555_);
return v___x_1574_;
}
}
else
{
lean_object* v___x_1575_; 
lean_dec(v_h__3_1558_);
lean_dec(v_h__2_1557_);
v___x_1575_ = lean_apply_1(v_h__1_1556_, v_x_1555_);
return v___x_1575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* v_x_1576_, lean_object* v_h__1_1577_, lean_object* v_h__2_1578_){
_start:
{
lean_object* v_l_1579_; 
v_l_1579_ = lean_ctor_get(v_x_1576_, 3);
if (lean_obj_tag(v_l_1579_) == 0)
{
lean_object* v_size_1580_; lean_object* v_k_1581_; lean_object* v_v_1582_; lean_object* v_r_1583_; lean_object* v_size_1584_; lean_object* v_k_1585_; lean_object* v_v_1586_; lean_object* v_l_1587_; lean_object* v_r_1588_; lean_object* v___x_1589_; 
lean_inc_ref(v_l_1579_);
lean_dec(v_h__1_1577_);
v_size_1580_ = lean_ctor_get(v_x_1576_, 0);
lean_inc(v_size_1580_);
v_k_1581_ = lean_ctor_get(v_x_1576_, 1);
lean_inc(v_k_1581_);
v_v_1582_ = lean_ctor_get(v_x_1576_, 2);
lean_inc(v_v_1582_);
v_r_1583_ = lean_ctor_get(v_x_1576_, 4);
lean_inc(v_r_1583_);
lean_dec(v_x_1576_);
v_size_1584_ = lean_ctor_get(v_l_1579_, 0);
lean_inc(v_size_1584_);
v_k_1585_ = lean_ctor_get(v_l_1579_, 1);
lean_inc(v_k_1585_);
v_v_1586_ = lean_ctor_get(v_l_1579_, 2);
lean_inc(v_v_1586_);
v_l_1587_ = lean_ctor_get(v_l_1579_, 3);
lean_inc(v_l_1587_);
v_r_1588_ = lean_ctor_get(v_l_1579_, 4);
lean_inc(v_r_1588_);
lean_dec_ref_known(v_l_1579_, 5);
v___x_1589_ = lean_apply_10(v_h__2_1578_, v_size_1580_, v_k_1581_, v_v_1582_, v_size_1584_, v_k_1585_, v_v_1586_, v_l_1587_, v_r_1588_, v_r_1583_, lean_box(0));
return v___x_1589_;
}
else
{
lean_object* v_size_1590_; lean_object* v_k_1591_; lean_object* v_v_1592_; lean_object* v_r_1593_; lean_object* v___x_1594_; 
lean_dec(v_h__2_1578_);
v_size_1590_ = lean_ctor_get(v_x_1576_, 0);
lean_inc(v_size_1590_);
v_k_1591_ = lean_ctor_get(v_x_1576_, 1);
lean_inc(v_k_1591_);
v_v_1592_ = lean_ctor_get(v_x_1576_, 2);
lean_inc(v_v_1592_);
v_r_1593_ = lean_ctor_get(v_x_1576_, 4);
lean_inc(v_r_1593_);
lean_dec(v_x_1576_);
v___x_1594_ = lean_apply_5(v_h__1_1577_, v_size_1590_, v_k_1591_, v_v_1592_, v_r_1593_, lean_box(0));
return v___x_1594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* v_00_u03b1_1595_, lean_object* v_00_u03b2_1596_, lean_object* v_motive_1597_, lean_object* v_x_1598_, lean_object* v_x_1599_, lean_object* v_h__1_1600_, lean_object* v_h__2_1601_){
_start:
{
lean_object* v_l_1602_; 
v_l_1602_ = lean_ctor_get(v_x_1598_, 3);
if (lean_obj_tag(v_l_1602_) == 0)
{
lean_object* v_size_1603_; lean_object* v_k_1604_; lean_object* v_v_1605_; lean_object* v_r_1606_; lean_object* v_size_1607_; lean_object* v_k_1608_; lean_object* v_v_1609_; lean_object* v_l_1610_; lean_object* v_r_1611_; lean_object* v___x_1612_; 
lean_inc_ref(v_l_1602_);
lean_dec(v_h__1_1600_);
v_size_1603_ = lean_ctor_get(v_x_1598_, 0);
lean_inc(v_size_1603_);
v_k_1604_ = lean_ctor_get(v_x_1598_, 1);
lean_inc(v_k_1604_);
v_v_1605_ = lean_ctor_get(v_x_1598_, 2);
lean_inc(v_v_1605_);
v_r_1606_ = lean_ctor_get(v_x_1598_, 4);
lean_inc(v_r_1606_);
lean_dec(v_x_1598_);
v_size_1607_ = lean_ctor_get(v_l_1602_, 0);
lean_inc(v_size_1607_);
v_k_1608_ = lean_ctor_get(v_l_1602_, 1);
lean_inc(v_k_1608_);
v_v_1609_ = lean_ctor_get(v_l_1602_, 2);
lean_inc(v_v_1609_);
v_l_1610_ = lean_ctor_get(v_l_1602_, 3);
lean_inc(v_l_1610_);
v_r_1611_ = lean_ctor_get(v_l_1602_, 4);
lean_inc(v_r_1611_);
lean_dec_ref_known(v_l_1602_, 5);
v___x_1612_ = lean_apply_10(v_h__2_1601_, v_size_1603_, v_k_1604_, v_v_1605_, v_size_1607_, v_k_1608_, v_v_1609_, v_l_1610_, v_r_1611_, v_r_1606_, lean_box(0));
return v___x_1612_;
}
else
{
lean_object* v_size_1613_; lean_object* v_k_1614_; lean_object* v_v_1615_; lean_object* v_r_1616_; lean_object* v___x_1617_; 
lean_dec(v_h__2_1601_);
v_size_1613_ = lean_ctor_get(v_x_1598_, 0);
lean_inc(v_size_1613_);
v_k_1614_ = lean_ctor_get(v_x_1598_, 1);
lean_inc(v_k_1614_);
v_v_1615_ = lean_ctor_get(v_x_1598_, 2);
lean_inc(v_v_1615_);
v_r_1616_ = lean_ctor_get(v_x_1598_, 4);
lean_inc(v_r_1616_);
lean_dec(v_x_1598_);
v___x_1617_ = lean_apply_5(v_h__1_1600_, v_size_1613_, v_k_1614_, v_v_1615_, v_r_1616_, lean_box(0));
return v___x_1617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1618_, lean_object* v_h__1_1619_, lean_object* v_h__2_1620_, lean_object* v_h__3_1621_){
_start:
{
if (lean_obj_tag(v_x_1618_) == 0)
{
lean_object* v_r_1622_; 
lean_dec(v_h__1_1619_);
v_r_1622_ = lean_ctor_get(v_x_1618_, 4);
if (lean_obj_tag(v_r_1622_) == 0)
{
lean_object* v_size_1623_; lean_object* v_k_1624_; lean_object* v_v_1625_; lean_object* v_l_1626_; lean_object* v_size_1627_; lean_object* v_k_1628_; lean_object* v_v_1629_; lean_object* v_l_1630_; lean_object* v_r_1631_; lean_object* v___x_1632_; 
lean_inc_ref(v_r_1622_);
lean_dec(v_h__2_1620_);
v_size_1623_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_size_1623_);
v_k_1624_ = lean_ctor_get(v_x_1618_, 1);
lean_inc(v_k_1624_);
v_v_1625_ = lean_ctor_get(v_x_1618_, 2);
lean_inc(v_v_1625_);
v_l_1626_ = lean_ctor_get(v_x_1618_, 3);
lean_inc(v_l_1626_);
lean_dec_ref_known(v_x_1618_, 5);
v_size_1627_ = lean_ctor_get(v_r_1622_, 0);
lean_inc(v_size_1627_);
v_k_1628_ = lean_ctor_get(v_r_1622_, 1);
lean_inc(v_k_1628_);
v_v_1629_ = lean_ctor_get(v_r_1622_, 2);
lean_inc(v_v_1629_);
v_l_1630_ = lean_ctor_get(v_r_1622_, 3);
lean_inc(v_l_1630_);
v_r_1631_ = lean_ctor_get(v_r_1622_, 4);
lean_inc(v_r_1631_);
lean_dec_ref_known(v_r_1622_, 5);
v___x_1632_ = lean_apply_9(v_h__3_1621_, v_size_1623_, v_k_1624_, v_v_1625_, v_l_1626_, v_size_1627_, v_k_1628_, v_v_1629_, v_l_1630_, v_r_1631_);
return v___x_1632_;
}
else
{
lean_object* v_size_1633_; lean_object* v_k_1634_; lean_object* v_v_1635_; lean_object* v_l_1636_; lean_object* v___x_1637_; 
lean_dec(v_h__3_1621_);
v_size_1633_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_size_1633_);
v_k_1634_ = lean_ctor_get(v_x_1618_, 1);
lean_inc(v_k_1634_);
v_v_1635_ = lean_ctor_get(v_x_1618_, 2);
lean_inc(v_v_1635_);
v_l_1636_ = lean_ctor_get(v_x_1618_, 3);
lean_inc(v_l_1636_);
lean_dec_ref_known(v_x_1618_, 5);
v___x_1637_ = lean_apply_4(v_h__2_1620_, v_size_1633_, v_k_1634_, v_v_1635_, v_l_1636_);
return v___x_1637_;
}
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec(v_h__3_1621_);
lean_dec(v_h__2_1620_);
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_apply_1(v_h__1_1619_, v___x_1638_);
return v___x_1639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1640_, lean_object* v_00_u03b2_1641_, lean_object* v_motive_1642_, lean_object* v_x_1643_, lean_object* v_h__1_1644_, lean_object* v_h__2_1645_, lean_object* v_h__3_1646_){
_start:
{
if (lean_obj_tag(v_x_1643_) == 0)
{
lean_object* v_r_1647_; 
lean_dec(v_h__1_1644_);
v_r_1647_ = lean_ctor_get(v_x_1643_, 4);
if (lean_obj_tag(v_r_1647_) == 0)
{
lean_object* v_size_1648_; lean_object* v_k_1649_; lean_object* v_v_1650_; lean_object* v_l_1651_; lean_object* v_size_1652_; lean_object* v_k_1653_; lean_object* v_v_1654_; lean_object* v_l_1655_; lean_object* v_r_1656_; lean_object* v___x_1657_; 
lean_inc_ref(v_r_1647_);
lean_dec(v_h__2_1645_);
v_size_1648_ = lean_ctor_get(v_x_1643_, 0);
lean_inc(v_size_1648_);
v_k_1649_ = lean_ctor_get(v_x_1643_, 1);
lean_inc(v_k_1649_);
v_v_1650_ = lean_ctor_get(v_x_1643_, 2);
lean_inc(v_v_1650_);
v_l_1651_ = lean_ctor_get(v_x_1643_, 3);
lean_inc(v_l_1651_);
lean_dec_ref_known(v_x_1643_, 5);
v_size_1652_ = lean_ctor_get(v_r_1647_, 0);
lean_inc(v_size_1652_);
v_k_1653_ = lean_ctor_get(v_r_1647_, 1);
lean_inc(v_k_1653_);
v_v_1654_ = lean_ctor_get(v_r_1647_, 2);
lean_inc(v_v_1654_);
v_l_1655_ = lean_ctor_get(v_r_1647_, 3);
lean_inc(v_l_1655_);
v_r_1656_ = lean_ctor_get(v_r_1647_, 4);
lean_inc(v_r_1656_);
lean_dec_ref_known(v_r_1647_, 5);
v___x_1657_ = lean_apply_9(v_h__3_1646_, v_size_1648_, v_k_1649_, v_v_1650_, v_l_1651_, v_size_1652_, v_k_1653_, v_v_1654_, v_l_1655_, v_r_1656_);
return v___x_1657_;
}
else
{
lean_object* v_size_1658_; lean_object* v_k_1659_; lean_object* v_v_1660_; lean_object* v_l_1661_; lean_object* v___x_1662_; 
lean_dec(v_h__3_1646_);
v_size_1658_ = lean_ctor_get(v_x_1643_, 0);
lean_inc(v_size_1658_);
v_k_1659_ = lean_ctor_get(v_x_1643_, 1);
lean_inc(v_k_1659_);
v_v_1660_ = lean_ctor_get(v_x_1643_, 2);
lean_inc(v_v_1660_);
v_l_1661_ = lean_ctor_get(v_x_1643_, 3);
lean_inc(v_l_1661_);
lean_dec_ref_known(v_x_1643_, 5);
v___x_1662_ = lean_apply_4(v_h__2_1645_, v_size_1658_, v_k_1659_, v_v_1660_, v_l_1661_);
return v___x_1662_;
}
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_dec(v_h__3_1646_);
lean_dec(v_h__2_1645_);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_apply_1(v_h__1_1644_, v___x_1663_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1665_, lean_object* v_x_1666_, lean_object* v_h__1_1667_, lean_object* v_h__2_1668_, lean_object* v_h__3_1669_){
_start:
{
if (lean_obj_tag(v_x_1665_) == 0)
{
lean_object* v_r_1670_; 
lean_dec(v_h__1_1667_);
v_r_1670_ = lean_ctor_get(v_x_1665_, 4);
if (lean_obj_tag(v_r_1670_) == 0)
{
lean_object* v_size_1671_; lean_object* v_k_1672_; lean_object* v_v_1673_; lean_object* v_l_1674_; lean_object* v_size_1675_; lean_object* v_k_1676_; lean_object* v_v_1677_; lean_object* v_l_1678_; lean_object* v_r_1679_; lean_object* v___x_1680_; 
lean_inc_ref(v_r_1670_);
lean_dec(v_h__2_1668_);
v_size_1671_ = lean_ctor_get(v_x_1665_, 0);
lean_inc(v_size_1671_);
v_k_1672_ = lean_ctor_get(v_x_1665_, 1);
lean_inc(v_k_1672_);
v_v_1673_ = lean_ctor_get(v_x_1665_, 2);
lean_inc(v_v_1673_);
v_l_1674_ = lean_ctor_get(v_x_1665_, 3);
lean_inc(v_l_1674_);
lean_dec_ref_known(v_x_1665_, 5);
v_size_1675_ = lean_ctor_get(v_r_1670_, 0);
lean_inc(v_size_1675_);
v_k_1676_ = lean_ctor_get(v_r_1670_, 1);
lean_inc(v_k_1676_);
v_v_1677_ = lean_ctor_get(v_r_1670_, 2);
lean_inc(v_v_1677_);
v_l_1678_ = lean_ctor_get(v_r_1670_, 3);
lean_inc(v_l_1678_);
v_r_1679_ = lean_ctor_get(v_r_1670_, 4);
lean_inc(v_r_1679_);
lean_dec_ref_known(v_r_1670_, 5);
v___x_1680_ = lean_apply_10(v_h__3_1669_, v_size_1671_, v_k_1672_, v_v_1673_, v_l_1674_, v_size_1675_, v_k_1676_, v_v_1677_, v_l_1678_, v_r_1679_, v_x_1666_);
return v___x_1680_;
}
else
{
lean_object* v_size_1681_; lean_object* v_k_1682_; lean_object* v_v_1683_; lean_object* v_l_1684_; lean_object* v___x_1685_; 
lean_dec(v_h__3_1669_);
v_size_1681_ = lean_ctor_get(v_x_1665_, 0);
lean_inc(v_size_1681_);
v_k_1682_ = lean_ctor_get(v_x_1665_, 1);
lean_inc(v_k_1682_);
v_v_1683_ = lean_ctor_get(v_x_1665_, 2);
lean_inc(v_v_1683_);
v_l_1684_ = lean_ctor_get(v_x_1665_, 3);
lean_inc(v_l_1684_);
lean_dec_ref_known(v_x_1665_, 5);
v___x_1685_ = lean_apply_5(v_h__2_1668_, v_size_1681_, v_k_1682_, v_v_1683_, v_l_1684_, v_x_1666_);
return v___x_1685_;
}
}
else
{
lean_object* v___x_1686_; 
lean_dec(v_h__3_1669_);
lean_dec(v_h__2_1668_);
v___x_1686_ = lean_apply_1(v_h__1_1667_, v_x_1666_);
return v___x_1686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1687_, lean_object* v_00_u03b2_1688_, lean_object* v_motive_1689_, lean_object* v_x_1690_, lean_object* v_x_1691_, lean_object* v_h__1_1692_, lean_object* v_h__2_1693_, lean_object* v_h__3_1694_){
_start:
{
if (lean_obj_tag(v_x_1690_) == 0)
{
lean_object* v_r_1695_; 
lean_dec(v_h__1_1692_);
v_r_1695_ = lean_ctor_get(v_x_1690_, 4);
if (lean_obj_tag(v_r_1695_) == 0)
{
lean_object* v_size_1696_; lean_object* v_k_1697_; lean_object* v_v_1698_; lean_object* v_l_1699_; lean_object* v_size_1700_; lean_object* v_k_1701_; lean_object* v_v_1702_; lean_object* v_l_1703_; lean_object* v_r_1704_; lean_object* v___x_1705_; 
lean_inc_ref(v_r_1695_);
lean_dec(v_h__2_1693_);
v_size_1696_ = lean_ctor_get(v_x_1690_, 0);
lean_inc(v_size_1696_);
v_k_1697_ = lean_ctor_get(v_x_1690_, 1);
lean_inc(v_k_1697_);
v_v_1698_ = lean_ctor_get(v_x_1690_, 2);
lean_inc(v_v_1698_);
v_l_1699_ = lean_ctor_get(v_x_1690_, 3);
lean_inc(v_l_1699_);
lean_dec_ref_known(v_x_1690_, 5);
v_size_1700_ = lean_ctor_get(v_r_1695_, 0);
lean_inc(v_size_1700_);
v_k_1701_ = lean_ctor_get(v_r_1695_, 1);
lean_inc(v_k_1701_);
v_v_1702_ = lean_ctor_get(v_r_1695_, 2);
lean_inc(v_v_1702_);
v_l_1703_ = lean_ctor_get(v_r_1695_, 3);
lean_inc(v_l_1703_);
v_r_1704_ = lean_ctor_get(v_r_1695_, 4);
lean_inc(v_r_1704_);
lean_dec_ref_known(v_r_1695_, 5);
v___x_1705_ = lean_apply_10(v_h__3_1694_, v_size_1696_, v_k_1697_, v_v_1698_, v_l_1699_, v_size_1700_, v_k_1701_, v_v_1702_, v_l_1703_, v_r_1704_, v_x_1691_);
return v___x_1705_;
}
else
{
lean_object* v_size_1706_; lean_object* v_k_1707_; lean_object* v_v_1708_; lean_object* v_l_1709_; lean_object* v___x_1710_; 
lean_dec(v_h__3_1694_);
v_size_1706_ = lean_ctor_get(v_x_1690_, 0);
lean_inc(v_size_1706_);
v_k_1707_ = lean_ctor_get(v_x_1690_, 1);
lean_inc(v_k_1707_);
v_v_1708_ = lean_ctor_get(v_x_1690_, 2);
lean_inc(v_v_1708_);
v_l_1709_ = lean_ctor_get(v_x_1690_, 3);
lean_inc(v_l_1709_);
lean_dec_ref_known(v_x_1690_, 5);
v___x_1710_ = lean_apply_5(v_h__2_1693_, v_size_1706_, v_k_1707_, v_v_1708_, v_l_1709_, v_x_1691_);
return v___x_1710_;
}
}
else
{
lean_object* v___x_1711_; 
lean_dec(v_h__3_1694_);
lean_dec(v_h__2_1693_);
v___x_1711_ = lean_apply_1(v_h__1_1692_, v_x_1691_);
return v___x_1711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* v_x_1712_, lean_object* v_h__1_1713_, lean_object* v_h__2_1714_){
_start:
{
lean_object* v_r_1715_; 
v_r_1715_ = lean_ctor_get(v_x_1712_, 4);
if (lean_obj_tag(v_r_1715_) == 0)
{
lean_object* v_size_1716_; lean_object* v_k_1717_; lean_object* v_v_1718_; lean_object* v_l_1719_; lean_object* v_size_1720_; lean_object* v_k_1721_; lean_object* v_v_1722_; lean_object* v_l_1723_; lean_object* v_r_1724_; lean_object* v___x_1725_; 
lean_inc_ref(v_r_1715_);
lean_dec(v_h__1_1713_);
v_size_1716_ = lean_ctor_get(v_x_1712_, 0);
lean_inc(v_size_1716_);
v_k_1717_ = lean_ctor_get(v_x_1712_, 1);
lean_inc(v_k_1717_);
v_v_1718_ = lean_ctor_get(v_x_1712_, 2);
lean_inc(v_v_1718_);
v_l_1719_ = lean_ctor_get(v_x_1712_, 3);
lean_inc(v_l_1719_);
lean_dec(v_x_1712_);
v_size_1720_ = lean_ctor_get(v_r_1715_, 0);
lean_inc(v_size_1720_);
v_k_1721_ = lean_ctor_get(v_r_1715_, 1);
lean_inc(v_k_1721_);
v_v_1722_ = lean_ctor_get(v_r_1715_, 2);
lean_inc(v_v_1722_);
v_l_1723_ = lean_ctor_get(v_r_1715_, 3);
lean_inc(v_l_1723_);
v_r_1724_ = lean_ctor_get(v_r_1715_, 4);
lean_inc(v_r_1724_);
lean_dec_ref_known(v_r_1715_, 5);
v___x_1725_ = lean_apply_10(v_h__2_1714_, v_size_1716_, v_k_1717_, v_v_1718_, v_l_1719_, v_size_1720_, v_k_1721_, v_v_1722_, v_l_1723_, v_r_1724_, lean_box(0));
return v___x_1725_;
}
else
{
lean_object* v_size_1726_; lean_object* v_k_1727_; lean_object* v_v_1728_; lean_object* v_l_1729_; lean_object* v___x_1730_; 
lean_dec(v_h__2_1714_);
v_size_1726_ = lean_ctor_get(v_x_1712_, 0);
lean_inc(v_size_1726_);
v_k_1727_ = lean_ctor_get(v_x_1712_, 1);
lean_inc(v_k_1727_);
v_v_1728_ = lean_ctor_get(v_x_1712_, 2);
lean_inc(v_v_1728_);
v_l_1729_ = lean_ctor_get(v_x_1712_, 3);
lean_inc(v_l_1729_);
lean_dec(v_x_1712_);
v___x_1730_ = lean_apply_5(v_h__1_1713_, v_size_1726_, v_k_1727_, v_v_1728_, v_l_1729_, lean_box(0));
return v___x_1730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1731_, lean_object* v_00_u03b2_1732_, lean_object* v_motive_1733_, lean_object* v_x_1734_, lean_object* v_x_1735_, lean_object* v_h__1_1736_, lean_object* v_h__2_1737_){
_start:
{
lean_object* v_r_1738_; 
v_r_1738_ = lean_ctor_get(v_x_1734_, 4);
if (lean_obj_tag(v_r_1738_) == 0)
{
lean_object* v_size_1739_; lean_object* v_k_1740_; lean_object* v_v_1741_; lean_object* v_l_1742_; lean_object* v_size_1743_; lean_object* v_k_1744_; lean_object* v_v_1745_; lean_object* v_l_1746_; lean_object* v_r_1747_; lean_object* v___x_1748_; 
lean_inc_ref(v_r_1738_);
lean_dec(v_h__1_1736_);
v_size_1739_ = lean_ctor_get(v_x_1734_, 0);
lean_inc(v_size_1739_);
v_k_1740_ = lean_ctor_get(v_x_1734_, 1);
lean_inc(v_k_1740_);
v_v_1741_ = lean_ctor_get(v_x_1734_, 2);
lean_inc(v_v_1741_);
v_l_1742_ = lean_ctor_get(v_x_1734_, 3);
lean_inc(v_l_1742_);
lean_dec(v_x_1734_);
v_size_1743_ = lean_ctor_get(v_r_1738_, 0);
lean_inc(v_size_1743_);
v_k_1744_ = lean_ctor_get(v_r_1738_, 1);
lean_inc(v_k_1744_);
v_v_1745_ = lean_ctor_get(v_r_1738_, 2);
lean_inc(v_v_1745_);
v_l_1746_ = lean_ctor_get(v_r_1738_, 3);
lean_inc(v_l_1746_);
v_r_1747_ = lean_ctor_get(v_r_1738_, 4);
lean_inc(v_r_1747_);
lean_dec_ref_known(v_r_1738_, 5);
v___x_1748_ = lean_apply_10(v_h__2_1737_, v_size_1739_, v_k_1740_, v_v_1741_, v_l_1742_, v_size_1743_, v_k_1744_, v_v_1745_, v_l_1746_, v_r_1747_, lean_box(0));
return v___x_1748_;
}
else
{
lean_object* v_size_1749_; lean_object* v_k_1750_; lean_object* v_v_1751_; lean_object* v_l_1752_; lean_object* v___x_1753_; 
lean_dec(v_h__2_1737_);
v_size_1749_ = lean_ctor_get(v_x_1734_, 0);
lean_inc(v_size_1749_);
v_k_1750_ = lean_ctor_get(v_x_1734_, 1);
lean_inc(v_k_1750_);
v_v_1751_ = lean_ctor_get(v_x_1734_, 2);
lean_inc(v_v_1751_);
v_l_1752_ = lean_ctor_get(v_x_1734_, 3);
lean_inc(v_l_1752_);
lean_dec(v_x_1734_);
v___x_1753_ = lean_apply_5(v_h__1_1736_, v_size_1749_, v_k_1750_, v_v_1751_, v_l_1752_, lean_box(0));
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object* v_l_1754_, lean_object* v_h__1_1755_, lean_object* v_h__2_1756_){
_start:
{
if (lean_obj_tag(v_l_1754_) == 0)
{
lean_object* v_size_1757_; lean_object* v_k_1758_; lean_object* v_v_1759_; lean_object* v_l_1760_; lean_object* v_r_1761_; lean_object* v___x_1762_; 
lean_dec(v_h__1_1755_);
v_size_1757_ = lean_ctor_get(v_l_1754_, 0);
lean_inc(v_size_1757_);
v_k_1758_ = lean_ctor_get(v_l_1754_, 1);
lean_inc(v_k_1758_);
v_v_1759_ = lean_ctor_get(v_l_1754_, 2);
lean_inc(v_v_1759_);
v_l_1760_ = lean_ctor_get(v_l_1754_, 3);
lean_inc(v_l_1760_);
v_r_1761_ = lean_ctor_get(v_l_1754_, 4);
lean_inc(v_r_1761_);
lean_dec_ref_known(v_l_1754_, 5);
v___x_1762_ = lean_apply_7(v_h__2_1756_, v_size_1757_, v_k_1758_, v_v_1759_, v_l_1760_, v_r_1761_, lean_box(0), lean_box(0));
return v___x_1762_;
}
else
{
lean_object* v___x_1763_; 
lean_dec(v_h__2_1756_);
v___x_1763_ = lean_apply_2(v_h__1_1755_, lean_box(0), lean_box(0));
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object* v_00_u03b1_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_r_1766_, lean_object* v_motive_1767_, lean_object* v_l_1768_, lean_object* v_hl_1769_, lean_object* v_hlr_1770_, lean_object* v_h__1_1771_, lean_object* v_h__2_1772_){
_start:
{
if (lean_obj_tag(v_l_1768_) == 0)
{
lean_object* v_size_1773_; lean_object* v_k_1774_; lean_object* v_v_1775_; lean_object* v_l_1776_; lean_object* v_r_1777_; lean_object* v___x_1778_; 
lean_dec(v_h__1_1771_);
v_size_1773_ = lean_ctor_get(v_l_1768_, 0);
lean_inc(v_size_1773_);
v_k_1774_ = lean_ctor_get(v_l_1768_, 1);
lean_inc(v_k_1774_);
v_v_1775_ = lean_ctor_get(v_l_1768_, 2);
lean_inc(v_v_1775_);
v_l_1776_ = lean_ctor_get(v_l_1768_, 3);
lean_inc(v_l_1776_);
v_r_1777_ = lean_ctor_get(v_l_1768_, 4);
lean_inc(v_r_1777_);
lean_dec_ref_known(v_l_1768_, 5);
v___x_1778_ = lean_apply_7(v_h__2_1772_, v_size_1773_, v_k_1774_, v_v_1775_, v_l_1776_, v_r_1777_, lean_box(0), lean_box(0));
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; 
lean_dec(v_h__2_1772_);
v___x_1779_ = lean_apply_2(v_h__1_1771_, lean_box(0), lean_box(0));
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object* v_00_u03b1_1780_, lean_object* v_00_u03b2_1781_, lean_object* v_r_1782_, lean_object* v_motive_1783_, lean_object* v_l_1784_, lean_object* v_hl_1785_, lean_object* v_hlr_1786_, lean_object* v_h__1_1787_, lean_object* v_h__2_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(v_00_u03b1_1780_, v_00_u03b2_1781_, v_r_1782_, v_motive_1783_, v_l_1784_, v_hl_1785_, v_hlr_1786_, v_h__1_1787_, v_h__2_1788_);
lean_dec(v_r_1782_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(lean_object* v_x_1790_, lean_object* v_h__1_1791_){
_start:
{
lean_object* v_k_1792_; lean_object* v_v_1793_; lean_object* v_tree_1794_; lean_object* v___x_1795_; 
v_k_1792_ = lean_ctor_get(v_x_1790_, 0);
lean_inc(v_k_1792_);
v_v_1793_ = lean_ctor_get(v_x_1790_, 1);
lean_inc(v_v_1793_);
v_tree_1794_ = lean_ctor_get(v_x_1790_, 2);
lean_inc(v_tree_1794_);
lean_dec_ref(v_x_1790_);
v___x_1795_ = lean_apply_5(v_h__1_1791_, v_k_1792_, v_v_1793_, v_tree_1794_, lean_box(0), lean_box(0));
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object* v_00_u03b1_1796_, lean_object* v_00_u03b2_1797_, lean_object* v_l_x27_1798_, lean_object* v_r_x27_1799_, lean_object* v_motive_1800_, lean_object* v_x_1801_, lean_object* v_h__1_1802_){
_start:
{
lean_object* v_k_1803_; lean_object* v_v_1804_; lean_object* v_tree_1805_; lean_object* v___x_1806_; 
v_k_1803_ = lean_ctor_get(v_x_1801_, 0);
lean_inc(v_k_1803_);
v_v_1804_ = lean_ctor_get(v_x_1801_, 1);
lean_inc(v_v_1804_);
v_tree_1805_ = lean_ctor_get(v_x_1801_, 2);
lean_inc(v_tree_1805_);
lean_dec_ref(v_x_1801_);
v___x_1806_ = lean_apply_5(v_h__1_1802_, v_k_1803_, v_v_1804_, v_tree_1805_, lean_box(0), lean_box(0));
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object* v_00_u03b1_1807_, lean_object* v_00_u03b2_1808_, lean_object* v_l_x27_1809_, lean_object* v_r_x27_1810_, lean_object* v_motive_1811_, lean_object* v_x_1812_, lean_object* v_h__1_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(v_00_u03b1_1807_, v_00_u03b2_1808_, v_l_x27_1809_, v_r_x27_1810_, v_motive_1811_, v_x_1812_, v_h__1_1813_);
lean_dec(v_r_x27_1810_);
lean_dec(v_l_x27_1809_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object* v_l_1815_, lean_object* v_h__1_1816_, lean_object* v_h__2_1817_){
_start:
{
if (lean_obj_tag(v_l_1815_) == 0)
{
lean_object* v_size_1818_; lean_object* v_k_1819_; lean_object* v_v_1820_; lean_object* v_l_1821_; lean_object* v_r_1822_; lean_object* v___x_1823_; 
lean_dec(v_h__1_1816_);
v_size_1818_ = lean_ctor_get(v_l_1815_, 0);
lean_inc(v_size_1818_);
v_k_1819_ = lean_ctor_get(v_l_1815_, 1);
lean_inc(v_k_1819_);
v_v_1820_ = lean_ctor_get(v_l_1815_, 2);
lean_inc(v_v_1820_);
v_l_1821_ = lean_ctor_get(v_l_1815_, 3);
lean_inc(v_l_1821_);
v_r_1822_ = lean_ctor_get(v_l_1815_, 4);
lean_inc(v_r_1822_);
lean_dec_ref_known(v_l_1815_, 5);
v___x_1823_ = lean_apply_5(v_h__2_1817_, v_size_1818_, v_k_1819_, v_v_1820_, v_l_1821_, v_r_1822_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec(v_h__2_1817_);
v___x_1824_ = lean_box(0);
v___x_1825_ = lean_apply_1(v_h__1_1816_, v___x_1824_);
return v___x_1825_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object* v_00_u03b1_1826_, lean_object* v_00_u03b2_1827_, lean_object* v_motive_1828_, lean_object* v_l_1829_, lean_object* v_h__1_1830_, lean_object* v_h__2_1831_){
_start:
{
if (lean_obj_tag(v_l_1829_) == 0)
{
lean_object* v_size_1832_; lean_object* v_k_1833_; lean_object* v_v_1834_; lean_object* v_l_1835_; lean_object* v_r_1836_; lean_object* v___x_1837_; 
lean_dec(v_h__1_1830_);
v_size_1832_ = lean_ctor_get(v_l_1829_, 0);
lean_inc(v_size_1832_);
v_k_1833_ = lean_ctor_get(v_l_1829_, 1);
lean_inc(v_k_1833_);
v_v_1834_ = lean_ctor_get(v_l_1829_, 2);
lean_inc(v_v_1834_);
v_l_1835_ = lean_ctor_get(v_l_1829_, 3);
lean_inc(v_l_1835_);
v_r_1836_ = lean_ctor_get(v_l_1829_, 4);
lean_inc(v_r_1836_);
lean_dec_ref_known(v_l_1829_, 5);
v___x_1837_ = lean_apply_5(v_h__2_1831_, v_size_1832_, v_k_1833_, v_v_1834_, v_l_1835_, v_r_1836_);
return v___x_1837_;
}
else
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec(v_h__2_1831_);
v___x_1838_ = lean_box(0);
v___x_1839_ = lean_apply_1(v_h__1_1830_, v___x_1838_);
return v___x_1839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(lean_object* v_r_1840_, lean_object* v_h__1_1841_, lean_object* v_h__2_1842_){
_start:
{
if (lean_obj_tag(v_r_1840_) == 0)
{
lean_object* v_size_1843_; lean_object* v_k_1844_; lean_object* v_v_1845_; lean_object* v_l_1846_; lean_object* v_r_1847_; lean_object* v___x_1848_; 
lean_dec(v_h__1_1841_);
v_size_1843_ = lean_ctor_get(v_r_1840_, 0);
lean_inc(v_size_1843_);
v_k_1844_ = lean_ctor_get(v_r_1840_, 1);
lean_inc(v_k_1844_);
v_v_1845_ = lean_ctor_get(v_r_1840_, 2);
lean_inc(v_v_1845_);
v_l_1846_ = lean_ctor_get(v_r_1840_, 3);
lean_inc(v_l_1846_);
v_r_1847_ = lean_ctor_get(v_r_1840_, 4);
lean_inc(v_r_1847_);
lean_dec_ref_known(v_r_1840_, 5);
v___x_1848_ = lean_apply_7(v_h__2_1842_, v_size_1843_, v_k_1844_, v_v_1845_, v_l_1846_, v_r_1847_, lean_box(0), lean_box(0));
return v___x_1848_;
}
else
{
lean_object* v___x_1849_; 
lean_dec(v_h__2_1842_);
v___x_1849_ = lean_apply_2(v_h__1_1841_, lean_box(0), lean_box(0));
return v___x_1849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object* v_00_u03b1_1850_, lean_object* v_00_u03b2_1851_, lean_object* v_l_1852_, lean_object* v_motive_1853_, lean_object* v_r_1854_, lean_object* v_hr_1855_, lean_object* v_hlr_1856_, lean_object* v_h__1_1857_, lean_object* v_h__2_1858_){
_start:
{
if (lean_obj_tag(v_r_1854_) == 0)
{
lean_object* v_size_1859_; lean_object* v_k_1860_; lean_object* v_v_1861_; lean_object* v_l_1862_; lean_object* v_r_1863_; lean_object* v___x_1864_; 
lean_dec(v_h__1_1857_);
v_size_1859_ = lean_ctor_get(v_r_1854_, 0);
lean_inc(v_size_1859_);
v_k_1860_ = lean_ctor_get(v_r_1854_, 1);
lean_inc(v_k_1860_);
v_v_1861_ = lean_ctor_get(v_r_1854_, 2);
lean_inc(v_v_1861_);
v_l_1862_ = lean_ctor_get(v_r_1854_, 3);
lean_inc(v_l_1862_);
v_r_1863_ = lean_ctor_get(v_r_1854_, 4);
lean_inc(v_r_1863_);
lean_dec_ref_known(v_r_1854_, 5);
v___x_1864_ = lean_apply_7(v_h__2_1858_, v_size_1859_, v_k_1860_, v_v_1861_, v_l_1862_, v_r_1863_, lean_box(0), lean_box(0));
return v___x_1864_;
}
else
{
lean_object* v___x_1865_; 
lean_dec(v_h__2_1858_);
v___x_1865_ = lean_apply_2(v_h__1_1857_, lean_box(0), lean_box(0));
return v___x_1865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object* v_00_u03b1_1866_, lean_object* v_00_u03b2_1867_, lean_object* v_l_1868_, lean_object* v_motive_1869_, lean_object* v_r_1870_, lean_object* v_hr_1871_, lean_object* v_hlr_1872_, lean_object* v_h__1_1873_, lean_object* v_h__2_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(v_00_u03b1_1866_, v_00_u03b2_1867_, v_l_1868_, v_motive_1869_, v_r_1870_, v_hr_1871_, v_hlr_1872_, v_h__1_1873_, v_h__2_1874_);
lean_dec(v_l_1868_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(lean_object* v_r_1876_, lean_object* v_h__1_1877_, lean_object* v_h__2_1878_){
_start:
{
if (lean_obj_tag(v_r_1876_) == 0)
{
lean_object* v_size_1879_; lean_object* v_k_1880_; lean_object* v_v_1881_; lean_object* v_l_1882_; lean_object* v_r_1883_; lean_object* v___x_1884_; 
lean_dec(v_h__1_1877_);
v_size_1879_ = lean_ctor_get(v_r_1876_, 0);
lean_inc(v_size_1879_);
v_k_1880_ = lean_ctor_get(v_r_1876_, 1);
lean_inc(v_k_1880_);
v_v_1881_ = lean_ctor_get(v_r_1876_, 2);
lean_inc(v_v_1881_);
v_l_1882_ = lean_ctor_get(v_r_1876_, 3);
lean_inc(v_l_1882_);
v_r_1883_ = lean_ctor_get(v_r_1876_, 4);
lean_inc(v_r_1883_);
lean_dec_ref_known(v_r_1876_, 5);
v___x_1884_ = lean_apply_7(v_h__2_1878_, v_size_1879_, v_k_1880_, v_v_1881_, v_l_1882_, v_r_1883_, lean_box(0), lean_box(0));
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; 
lean_dec(v_h__2_1878_);
v___x_1885_ = lean_apply_2(v_h__1_1877_, lean_box(0), lean_box(0));
return v___x_1885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object* v_00_u03b1_1886_, lean_object* v_00_u03b2_1887_, lean_object* v_sz_1888_, lean_object* v_k_1889_, lean_object* v_v_1890_, lean_object* v_l_x27_1891_, lean_object* v_r_x27_1892_, lean_object* v_motive_1893_, lean_object* v_r_1894_, lean_object* v_hr_1895_, lean_object* v_hlr_1896_, lean_object* v_h__1_1897_, lean_object* v_h__2_1898_){
_start:
{
if (lean_obj_tag(v_r_1894_) == 0)
{
lean_object* v_size_1899_; lean_object* v_k_1900_; lean_object* v_v_1901_; lean_object* v_l_1902_; lean_object* v_r_1903_; lean_object* v___x_1904_; 
lean_dec(v_h__1_1897_);
v_size_1899_ = lean_ctor_get(v_r_1894_, 0);
lean_inc(v_size_1899_);
v_k_1900_ = lean_ctor_get(v_r_1894_, 1);
lean_inc(v_k_1900_);
v_v_1901_ = lean_ctor_get(v_r_1894_, 2);
lean_inc(v_v_1901_);
v_l_1902_ = lean_ctor_get(v_r_1894_, 3);
lean_inc(v_l_1902_);
v_r_1903_ = lean_ctor_get(v_r_1894_, 4);
lean_inc(v_r_1903_);
lean_dec_ref_known(v_r_1894_, 5);
v___x_1904_ = lean_apply_7(v_h__2_1898_, v_size_1899_, v_k_1900_, v_v_1901_, v_l_1902_, v_r_1903_, lean_box(0), lean_box(0));
return v___x_1904_;
}
else
{
lean_object* v___x_1905_; 
lean_dec(v_h__2_1898_);
v___x_1905_ = lean_apply_2(v_h__1_1897_, lean_box(0), lean_box(0));
return v___x_1905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object* v_00_u03b1_1906_, lean_object* v_00_u03b2_1907_, lean_object* v_sz_1908_, lean_object* v_k_1909_, lean_object* v_v_1910_, lean_object* v_l_x27_1911_, lean_object* v_r_x27_1912_, lean_object* v_motive_1913_, lean_object* v_r_1914_, lean_object* v_hr_1915_, lean_object* v_hlr_1916_, lean_object* v_h__1_1917_, lean_object* v_h__2_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(v_00_u03b1_1906_, v_00_u03b2_1907_, v_sz_1908_, v_k_1909_, v_v_1910_, v_l_x27_1911_, v_r_x27_1912_, v_motive_1913_, v_r_1914_, v_hr_1915_, v_hlr_1916_, v_h__1_1917_, v_h__2_1918_);
lean_dec(v_r_x27_1912_);
lean_dec(v_l_x27_1911_);
lean_dec(v_v_1910_);
lean_dec(v_k_1909_);
lean_dec(v_sz_1908_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object* v_t_1920_, lean_object* v_h__1_1921_, lean_object* v_h__2_1922_){
_start:
{
if (lean_obj_tag(v_t_1920_) == 0)
{
lean_object* v_size_1923_; lean_object* v_k_1924_; lean_object* v_v_1925_; lean_object* v_l_1926_; lean_object* v_r_1927_; lean_object* v___x_1928_; 
lean_dec(v_h__1_1921_);
v_size_1923_ = lean_ctor_get(v_t_1920_, 0);
lean_inc(v_size_1923_);
v_k_1924_ = lean_ctor_get(v_t_1920_, 1);
lean_inc(v_k_1924_);
v_v_1925_ = lean_ctor_get(v_t_1920_, 2);
lean_inc(v_v_1925_);
v_l_1926_ = lean_ctor_get(v_t_1920_, 3);
lean_inc(v_l_1926_);
v_r_1927_ = lean_ctor_get(v_t_1920_, 4);
lean_inc(v_r_1927_);
lean_dec_ref_known(v_t_1920_, 5);
v___x_1928_ = lean_apply_6(v_h__2_1922_, v_size_1923_, v_k_1924_, v_v_1925_, v_l_1926_, v_r_1927_, lean_box(0));
return v___x_1928_;
}
else
{
lean_object* v___x_1929_; 
lean_dec(v_h__2_1922_);
v___x_1929_ = lean_apply_1(v_h__1_1921_, lean_box(0));
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object* v_00_u03b1_1930_, lean_object* v_00_u03b2_1931_, lean_object* v_motive_1932_, lean_object* v_t_1933_, lean_object* v_hr_1934_, lean_object* v_h__1_1935_, lean_object* v_h__2_1936_){
_start:
{
if (lean_obj_tag(v_t_1933_) == 0)
{
lean_object* v_size_1937_; lean_object* v_k_1938_; lean_object* v_v_1939_; lean_object* v_l_1940_; lean_object* v_r_1941_; lean_object* v___x_1942_; 
lean_dec(v_h__1_1935_);
v_size_1937_ = lean_ctor_get(v_t_1933_, 0);
lean_inc(v_size_1937_);
v_k_1938_ = lean_ctor_get(v_t_1933_, 1);
lean_inc(v_k_1938_);
v_v_1939_ = lean_ctor_get(v_t_1933_, 2);
lean_inc(v_v_1939_);
v_l_1940_ = lean_ctor_get(v_t_1933_, 3);
lean_inc(v_l_1940_);
v_r_1941_ = lean_ctor_get(v_t_1933_, 4);
lean_inc(v_r_1941_);
lean_dec_ref_known(v_t_1933_, 5);
v___x_1942_ = lean_apply_6(v_h__2_1936_, v_size_1937_, v_k_1938_, v_v_1939_, v_l_1940_, v_r_1941_, lean_box(0));
return v___x_1942_;
}
else
{
lean_object* v___x_1943_; 
lean_dec(v_h__2_1936_);
v___x_1943_ = lean_apply_1(v_h__1_1935_, lean_box(0));
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t v_x_1944_, lean_object* v_h__1_1945_, lean_object* v_h__2_1946_, lean_object* v_h__3_1947_){
_start:
{
switch(v_x_1944_)
{
case 0:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec(v_h__3_1947_);
lean_dec(v_h__2_1946_);
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_apply_1(v_h__1_1945_, v___x_1948_);
return v___x_1949_;
}
case 1:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_dec(v_h__2_1946_);
lean_dec(v_h__1_1945_);
v___x_1950_ = lean_box(0);
v___x_1951_ = lean_apply_1(v_h__3_1947_, v___x_1950_);
return v___x_1951_;
}
default: 
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_dec(v_h__3_1947_);
lean_dec(v_h__1_1945_);
v___x_1952_ = lean_box(0);
v___x_1953_ = lean_apply_1(v_h__2_1946_, v___x_1952_);
return v___x_1953_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object* v_x_1954_, lean_object* v_h__1_1955_, lean_object* v_h__2_1956_, lean_object* v_h__3_1957_){
_start:
{
uint8_t v_x_33__boxed_1958_; lean_object* v_res_1959_; 
v_x_33__boxed_1958_ = lean_unbox(v_x_1954_);
v_res_1959_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_33__boxed_1958_, v_h__1_1955_, v_h__2_1956_, v_h__3_1957_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object* v_motive_1960_, uint8_t v_x_1961_, lean_object* v_h__1_1962_, lean_object* v_h__2_1963_, lean_object* v_h__3_1964_){
_start:
{
switch(v_x_1961_)
{
case 0:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_dec(v_h__3_1964_);
lean_dec(v_h__2_1963_);
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_apply_1(v_h__1_1962_, v___x_1965_);
return v___x_1966_;
}
case 1:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_dec(v_h__2_1963_);
lean_dec(v_h__1_1962_);
v___x_1967_ = lean_box(0);
v___x_1968_ = lean_apply_1(v_h__3_1964_, v___x_1967_);
return v___x_1968_;
}
default: 
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_dec(v_h__3_1964_);
lean_dec(v_h__1_1962_);
v___x_1969_ = lean_box(0);
v___x_1970_ = lean_apply_1(v_h__2_1963_, v___x_1969_);
return v___x_1970_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object* v_motive_1971_, lean_object* v_x_1972_, lean_object* v_h__1_1973_, lean_object* v_h__2_1974_, lean_object* v_h__3_1975_){
_start:
{
uint8_t v_x_48__boxed_1976_; lean_object* v_res_1977_; 
v_x_48__boxed_1976_ = lean_unbox(v_x_1972_);
v_res_1977_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_1971_, v_x_48__boxed_1976_, v_h__1_1973_, v_h__2_1974_, v_h__3_1975_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___redArg(lean_object* v_x_1978_, lean_object* v_h__1_1979_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_apply_4(v_h__1_1979_, v_x_1978_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(lean_object* v_00_u03b1_1981_, lean_object* v_00_u03b2_1982_, lean_object* v_l_x27_1983_, lean_object* v_motive_1984_, lean_object* v_x_1985_, lean_object* v_h__1_1986_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_apply_4(v_h__1_1986_, v_x_1985_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___boxed(lean_object* v_00_u03b1_1988_, lean_object* v_00_u03b2_1989_, lean_object* v_l_x27_1990_, lean_object* v_motive_1991_, lean_object* v_x_1992_, lean_object* v_h__1_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(v_00_u03b1_1988_, v_00_u03b2_1989_, v_l_x27_1990_, v_motive_1991_, v_x_1992_, v_h__1_1993_);
lean_dec(v_l_x27_1990_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(lean_object* v_l_1995_, lean_object* v_h__1_1996_, lean_object* v_h__2_1997_){
_start:
{
if (lean_obj_tag(v_l_1995_) == 0)
{
lean_object* v_size_1998_; lean_object* v_k_1999_; lean_object* v_v_2000_; lean_object* v_l_2001_; lean_object* v_r_2002_; lean_object* v___x_2003_; 
lean_dec(v_h__1_1996_);
v_size_1998_ = lean_ctor_get(v_l_1995_, 0);
lean_inc(v_size_1998_);
v_k_1999_ = lean_ctor_get(v_l_1995_, 1);
lean_inc(v_k_1999_);
v_v_2000_ = lean_ctor_get(v_l_1995_, 2);
lean_inc(v_v_2000_);
v_l_2001_ = lean_ctor_get(v_l_1995_, 3);
lean_inc(v_l_2001_);
v_r_2002_ = lean_ctor_get(v_l_1995_, 4);
lean_inc(v_r_2002_);
lean_dec_ref_known(v_l_1995_, 5);
v___x_2003_ = lean_apply_6(v_h__2_1997_, v_size_1998_, v_k_1999_, v_v_2000_, v_l_2001_, v_r_2002_, lean_box(0));
return v___x_2003_;
}
else
{
lean_object* v___x_2004_; 
lean_dec(v_h__2_1997_);
v___x_2004_ = lean_apply_1(v_h__1_1996_, lean_box(0));
return v___x_2004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(lean_object* v_00_u03b1_2005_, lean_object* v_00_u03b2_2006_, lean_object* v_motive_2007_, lean_object* v_l_2008_, lean_object* v_hl_2009_, lean_object* v_h__1_2010_, lean_object* v_h__2_2011_){
_start:
{
if (lean_obj_tag(v_l_2008_) == 0)
{
lean_object* v_size_2012_; lean_object* v_k_2013_; lean_object* v_v_2014_; lean_object* v_l_2015_; lean_object* v_r_2016_; lean_object* v___x_2017_; 
lean_dec(v_h__1_2010_);
v_size_2012_ = lean_ctor_get(v_l_2008_, 0);
lean_inc(v_size_2012_);
v_k_2013_ = lean_ctor_get(v_l_2008_, 1);
lean_inc(v_k_2013_);
v_v_2014_ = lean_ctor_get(v_l_2008_, 2);
lean_inc(v_v_2014_);
v_l_2015_ = lean_ctor_get(v_l_2008_, 3);
lean_inc(v_l_2015_);
v_r_2016_ = lean_ctor_get(v_l_2008_, 4);
lean_inc(v_r_2016_);
lean_dec_ref_known(v_l_2008_, 5);
v___x_2017_ = lean_apply_6(v_h__2_2011_, v_size_2012_, v_k_2013_, v_v_2014_, v_l_2015_, v_r_2016_, lean_box(0));
return v___x_2017_;
}
else
{
lean_object* v___x_2018_; 
lean_dec(v_h__2_2011_);
v___x_2018_ = lean_apply_1(v_h__1_2010_, lean_box(0));
return v___x_2018_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object* v_x_2019_, lean_object* v_h__1_2020_, lean_object* v_h__2_2021_){
_start:
{
if (lean_obj_tag(v_x_2019_) == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec(v_h__2_2021_);
v___x_2022_ = lean_box(0);
v___x_2023_ = lean_apply_1(v_h__1_2020_, v___x_2022_);
return v___x_2023_;
}
else
{
lean_object* v_val_2024_; lean_object* v_fst_2025_; lean_object* v_snd_2026_; lean_object* v___x_2027_; 
lean_dec(v_h__1_2020_);
v_val_2024_ = lean_ctor_get(v_x_2019_, 0);
lean_inc(v_val_2024_);
lean_dec_ref_known(v_x_2019_, 1);
v_fst_2025_ = lean_ctor_get(v_val_2024_, 0);
lean_inc(v_fst_2025_);
v_snd_2026_ = lean_ctor_get(v_val_2024_, 1);
lean_inc(v_snd_2026_);
lean_dec(v_val_2024_);
v___x_2027_ = lean_apply_2(v_h__2_2021_, v_fst_2025_, v_snd_2026_);
return v___x_2027_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* v_00_u03b1_2028_, lean_object* v_00_u03b2_2029_, lean_object* v_motive_2030_, lean_object* v_x_2031_, lean_object* v_h__1_2032_, lean_object* v_h__2_2033_){
_start:
{
if (lean_obj_tag(v_x_2031_) == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec(v_h__2_2033_);
v___x_2034_ = lean_box(0);
v___x_2035_ = lean_apply_1(v_h__1_2032_, v___x_2034_);
return v___x_2035_;
}
else
{
lean_object* v_val_2036_; lean_object* v_fst_2037_; lean_object* v_snd_2038_; lean_object* v___x_2039_; 
lean_dec(v_h__1_2032_);
v_val_2036_ = lean_ctor_get(v_x_2031_, 0);
lean_inc(v_val_2036_);
lean_dec_ref_known(v_x_2031_, 1);
v_fst_2037_ = lean_ctor_get(v_val_2036_, 0);
lean_inc(v_fst_2037_);
v_snd_2038_ = lean_ctor_get(v_val_2036_, 1);
lean_inc(v_snd_2038_);
lean_dec(v_val_2036_);
v___x_2039_ = lean_apply_2(v_h__2_2033_, v_fst_2037_, v_snd_2038_);
return v___x_2039_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(lean_object* v_x_2040_, lean_object* v_h__1_2041_){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_apply_4(v_h__1_2041_, v_x_2040_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object* v_00_u03b1_2043_, lean_object* v_00_u03b2_2044_, lean_object* v_l_2045_, lean_object* v_motive_2046_, lean_object* v_x_2047_, lean_object* v_h__1_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_apply_4(v_h__1_2048_, v_x_2047_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(lean_object* v_00_u03b1_2050_, lean_object* v_00_u03b2_2051_, lean_object* v_l_2052_, lean_object* v_motive_2053_, lean_object* v_x_2054_, lean_object* v_h__1_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_2050_, v_00_u03b2_2051_, v_l_2052_, v_motive_2053_, v_x_2054_, v_h__1_2055_);
lean_dec(v_l_2052_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___redArg(lean_object* v_x_2057_, lean_object* v_h__1_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_apply_4(v_h__1_2058_, v_x_2057_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(lean_object* v_00_u03b1_2060_, lean_object* v_00_u03b2_2061_, lean_object* v_l_2062_, lean_object* v_motive_2063_, lean_object* v_x_2064_, lean_object* v_h__1_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = lean_apply_4(v_h__1_2065_, v_x_2064_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_2067_, lean_object* v_00_u03b2_2068_, lean_object* v_l_2069_, lean_object* v_motive_2070_, lean_object* v_x_2071_, lean_object* v_h__1_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(v_00_u03b1_2067_, v_00_u03b2_2068_, v_l_2069_, v_motive_2070_, v_x_2071_, v_h__1_2072_);
lean_dec(v_l_2069_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___redArg(lean_object* v_x_2074_, lean_object* v_h__1_2075_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = lean_apply_3(v_h__1_2075_, v_x_2074_, lean_box(0), lean_box(0));
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(lean_object* v_00_u03b1_2077_, lean_object* v_00_u03b2_2078_, lean_object* v_l_x27_2079_, lean_object* v_motive_2080_, lean_object* v_x_2081_, lean_object* v_h__1_2082_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_apply_3(v_h__1_2082_, v_x_2081_, lean_box(0), lean_box(0));
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___boxed(lean_object* v_00_u03b1_2084_, lean_object* v_00_u03b2_2085_, lean_object* v_l_x27_2086_, lean_object* v_motive_2087_, lean_object* v_x_2088_, lean_object* v_h__1_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(v_00_u03b1_2084_, v_00_u03b2_2085_, v_l_x27_2086_, v_motive_2087_, v_x_2088_, v_h__1_2089_);
lean_dec(v_l_x27_2086_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___redArg(lean_object* v_x_2091_, lean_object* v_h__1_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_apply_3(v_h__1_2092_, v_x_2091_, lean_box(0), lean_box(0));
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(lean_object* v_00_u03b1_2094_, lean_object* v_00_u03b2_2095_, lean_object* v_r_x27_2096_, lean_object* v_motive_2097_, lean_object* v_x_2098_, lean_object* v_h__1_2099_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = lean_apply_3(v_h__1_2099_, v_x_2098_, lean_box(0), lean_box(0));
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___boxed(lean_object* v_00_u03b1_2101_, lean_object* v_00_u03b2_2102_, lean_object* v_r_x27_2103_, lean_object* v_motive_2104_, lean_object* v_x_2105_, lean_object* v_h__1_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(v_00_u03b1_2101_, v_00_u03b2_2102_, v_r_x27_2103_, v_motive_2104_, v_x_2105_, v_h__1_2106_);
lean_dec(v_r_x27_2103_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(lean_object* v_r_2108_, lean_object* v_h__1_2109_, lean_object* v_h__2_2110_){
_start:
{
if (lean_obj_tag(v_r_2108_) == 0)
{
lean_object* v_size_2111_; lean_object* v_k_2112_; lean_object* v_v_2113_; lean_object* v_l_2114_; lean_object* v_r_2115_; lean_object* v___x_2116_; 
lean_dec(v_h__1_2109_);
v_size_2111_ = lean_ctor_get(v_r_2108_, 0);
lean_inc(v_size_2111_);
v_k_2112_ = lean_ctor_get(v_r_2108_, 1);
lean_inc(v_k_2112_);
v_v_2113_ = lean_ctor_get(v_r_2108_, 2);
lean_inc(v_v_2113_);
v_l_2114_ = lean_ctor_get(v_r_2108_, 3);
lean_inc(v_l_2114_);
v_r_2115_ = lean_ctor_get(v_r_2108_, 4);
lean_inc(v_r_2115_);
lean_dec_ref_known(v_r_2108_, 5);
v___x_2116_ = lean_apply_5(v_h__2_2110_, v_size_2111_, v_k_2112_, v_v_2113_, v_l_2114_, v_r_2115_);
return v___x_2116_;
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec(v_h__2_2110_);
v___x_2117_ = lean_box(0);
v___x_2118_ = lean_apply_1(v_h__1_2109_, v___x_2117_);
return v___x_2118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object* v_00_u03b1_2119_, lean_object* v_00_u03b2_2120_, lean_object* v_motive_2121_, lean_object* v_r_2122_, lean_object* v_h__1_2123_, lean_object* v_h__2_2124_){
_start:
{
if (lean_obj_tag(v_r_2122_) == 0)
{
lean_object* v_size_2125_; lean_object* v_k_2126_; lean_object* v_v_2127_; lean_object* v_l_2128_; lean_object* v_r_2129_; lean_object* v___x_2130_; 
lean_dec(v_h__1_2123_);
v_size_2125_ = lean_ctor_get(v_r_2122_, 0);
lean_inc(v_size_2125_);
v_k_2126_ = lean_ctor_get(v_r_2122_, 1);
lean_inc(v_k_2126_);
v_v_2127_ = lean_ctor_get(v_r_2122_, 2);
lean_inc(v_v_2127_);
v_l_2128_ = lean_ctor_get(v_r_2122_, 3);
lean_inc(v_l_2128_);
v_r_2129_ = lean_ctor_get(v_r_2122_, 4);
lean_inc(v_r_2129_);
lean_dec_ref_known(v_r_2122_, 5);
v___x_2130_ = lean_apply_5(v_h__2_2124_, v_size_2125_, v_k_2126_, v_v_2127_, v_l_2128_, v_r_2129_);
return v___x_2130_;
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_dec(v_h__2_2124_);
v___x_2131_ = lean_box(0);
v___x_2132_ = lean_apply_1(v_h__1_2123_, v___x_2131_);
return v___x_2132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(lean_object* v_x_2133_, lean_object* v_h__1_2134_, lean_object* v_h__2_2135_){
_start:
{
if (lean_obj_tag(v_x_2133_) == 0)
{
lean_object* v_size_2136_; lean_object* v_k_2137_; lean_object* v_v_2138_; lean_object* v_l_2139_; lean_object* v_r_2140_; lean_object* v___x_2141_; 
lean_dec(v_h__2_2135_);
v_size_2136_ = lean_ctor_get(v_x_2133_, 0);
lean_inc(v_size_2136_);
v_k_2137_ = lean_ctor_get(v_x_2133_, 1);
lean_inc(v_k_2137_);
v_v_2138_ = lean_ctor_get(v_x_2133_, 2);
lean_inc(v_v_2138_);
v_l_2139_ = lean_ctor_get(v_x_2133_, 3);
lean_inc(v_l_2139_);
v_r_2140_ = lean_ctor_get(v_x_2133_, 4);
lean_inc(v_r_2140_);
lean_dec_ref_known(v_x_2133_, 5);
v___x_2141_ = lean_apply_5(v_h__1_2134_, v_size_2136_, v_k_2137_, v_v_2138_, v_l_2139_, v_r_2140_);
return v___x_2141_;
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec(v_h__1_2134_);
v___x_2142_ = lean_box(0);
v___x_2143_ = lean_apply_1(v_h__2_2135_, v___x_2142_);
return v___x_2143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(lean_object* v_00_u03b1_2144_, lean_object* v_00_u03b2_2145_, lean_object* v_motive_2146_, lean_object* v_x_2147_, lean_object* v_h__1_2148_, lean_object* v_h__2_2149_){
_start:
{
if (lean_obj_tag(v_x_2147_) == 0)
{
lean_object* v_size_2150_; lean_object* v_k_2151_; lean_object* v_v_2152_; lean_object* v_l_2153_; lean_object* v_r_2154_; lean_object* v___x_2155_; 
lean_dec(v_h__2_2149_);
v_size_2150_ = lean_ctor_get(v_x_2147_, 0);
lean_inc(v_size_2150_);
v_k_2151_ = lean_ctor_get(v_x_2147_, 1);
lean_inc(v_k_2151_);
v_v_2152_ = lean_ctor_get(v_x_2147_, 2);
lean_inc(v_v_2152_);
v_l_2153_ = lean_ctor_get(v_x_2147_, 3);
lean_inc(v_l_2153_);
v_r_2154_ = lean_ctor_get(v_x_2147_, 4);
lean_inc(v_r_2154_);
lean_dec_ref_known(v_x_2147_, 5);
v___x_2155_ = lean_apply_5(v_h__1_2148_, v_size_2150_, v_k_2151_, v_v_2152_, v_l_2153_, v_r_2154_);
return v___x_2155_;
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
lean_dec(v_h__1_2148_);
v___x_2156_ = lean_box(0);
v___x_2157_ = lean_apply_1(v_h__2_2149_, v___x_2156_);
return v___x_2157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object* v_r_2158_, lean_object* v_h__1_2159_, lean_object* v_h__2_2160_){
_start:
{
if (lean_obj_tag(v_r_2158_) == 0)
{
lean_object* v_size_2161_; lean_object* v_k_2162_; lean_object* v_v_2163_; lean_object* v_l_2164_; lean_object* v_r_2165_; lean_object* v___x_2166_; 
lean_dec(v_h__1_2159_);
v_size_2161_ = lean_ctor_get(v_r_2158_, 0);
lean_inc(v_size_2161_);
v_k_2162_ = lean_ctor_get(v_r_2158_, 1);
lean_inc(v_k_2162_);
v_v_2163_ = lean_ctor_get(v_r_2158_, 2);
lean_inc(v_v_2163_);
v_l_2164_ = lean_ctor_get(v_r_2158_, 3);
lean_inc(v_l_2164_);
v_r_2165_ = lean_ctor_get(v_r_2158_, 4);
lean_inc(v_r_2165_);
lean_dec_ref_known(v_r_2158_, 5);
v___x_2166_ = lean_apply_7(v_h__2_2160_, v_size_2161_, v_k_2162_, v_v_2163_, v_l_2164_, v_r_2165_, lean_box(0), lean_box(0));
return v___x_2166_;
}
else
{
lean_object* v___x_2167_; 
lean_dec(v_h__2_2160_);
v___x_2167_ = lean_apply_2(v_h__1_2159_, lean_box(0), lean_box(0));
return v___x_2167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object* v_00_u03b1_2168_, lean_object* v_00_u03b2_2169_, lean_object* v_motive_2170_, lean_object* v_r_2171_, lean_object* v_hr_2172_, lean_object* v_h__1_2173_, lean_object* v_h__2_2174_){
_start:
{
if (lean_obj_tag(v_r_2171_) == 0)
{
lean_object* v_size_2175_; lean_object* v_k_2176_; lean_object* v_v_2177_; lean_object* v_l_2178_; lean_object* v_r_2179_; lean_object* v___x_2180_; 
lean_dec(v_h__1_2173_);
v_size_2175_ = lean_ctor_get(v_r_2171_, 0);
lean_inc(v_size_2175_);
v_k_2176_ = lean_ctor_get(v_r_2171_, 1);
lean_inc(v_k_2176_);
v_v_2177_ = lean_ctor_get(v_r_2171_, 2);
lean_inc(v_v_2177_);
v_l_2178_ = lean_ctor_get(v_r_2171_, 3);
lean_inc(v_l_2178_);
v_r_2179_ = lean_ctor_get(v_r_2171_, 4);
lean_inc(v_r_2179_);
lean_dec_ref_known(v_r_2171_, 5);
v___x_2180_ = lean_apply_7(v_h__2_2174_, v_size_2175_, v_k_2176_, v_v_2177_, v_l_2178_, v_r_2179_, lean_box(0), lean_box(0));
return v___x_2180_;
}
else
{
lean_object* v___x_2181_; 
lean_dec(v_h__2_2174_);
v___x_2181_ = lean_apply_2(v_h__1_2173_, lean_box(0), lean_box(0));
return v___x_2181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg(lean_object* v_t_2182_, lean_object* v_h__1_2183_, lean_object* v_h__2_2184_){
_start:
{
if (lean_obj_tag(v_t_2182_) == 0)
{
lean_object* v_size_2185_; lean_object* v_k_2186_; lean_object* v_v_2187_; lean_object* v_l_2188_; lean_object* v_r_2189_; lean_object* v___x_2190_; 
lean_dec(v_h__1_2183_);
v_size_2185_ = lean_ctor_get(v_t_2182_, 0);
lean_inc(v_size_2185_);
v_k_2186_ = lean_ctor_get(v_t_2182_, 1);
lean_inc(v_k_2186_);
v_v_2187_ = lean_ctor_get(v_t_2182_, 2);
lean_inc(v_v_2187_);
v_l_2188_ = lean_ctor_get(v_t_2182_, 3);
lean_inc(v_l_2188_);
v_r_2189_ = lean_ctor_get(v_t_2182_, 4);
lean_inc(v_r_2189_);
lean_dec_ref_known(v_t_2182_, 5);
v___x_2190_ = lean_apply_5(v_h__2_2184_, v_size_2185_, v_k_2186_, v_v_2187_, v_l_2188_, v_r_2189_);
return v___x_2190_;
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec(v_h__2_2184_);
v___x_2191_ = lean_box(0);
v___x_2192_ = lean_apply_1(v_h__1_2183_, v___x_2191_);
return v___x_2192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_2193_, lean_object* v_00_u03b4_2194_, lean_object* v_motive_2195_, lean_object* v_t_2196_, lean_object* v_h__1_2197_, lean_object* v_h__2_2198_){
_start:
{
if (lean_obj_tag(v_t_2196_) == 0)
{
lean_object* v_size_2199_; lean_object* v_k_2200_; lean_object* v_v_2201_; lean_object* v_l_2202_; lean_object* v_r_2203_; lean_object* v___x_2204_; 
lean_dec(v_h__1_2197_);
v_size_2199_ = lean_ctor_get(v_t_2196_, 0);
lean_inc(v_size_2199_);
v_k_2200_ = lean_ctor_get(v_t_2196_, 1);
lean_inc(v_k_2200_);
v_v_2201_ = lean_ctor_get(v_t_2196_, 2);
lean_inc(v_v_2201_);
v_l_2202_ = lean_ctor_get(v_t_2196_, 3);
lean_inc(v_l_2202_);
v_r_2203_ = lean_ctor_get(v_t_2196_, 4);
lean_inc(v_r_2203_);
lean_dec_ref_known(v_t_2196_, 5);
v___x_2204_ = lean_apply_5(v_h__2_2198_, v_size_2199_, v_k_2200_, v_v_2201_, v_l_2202_, v_r_2203_);
return v___x_2204_;
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_dec(v_h__2_2198_);
v___x_2205_ = lean_box(0);
v___x_2206_ = lean_apply_1(v_h__1_2197_, v___x_2205_);
return v___x_2206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object* v_x_2207_, lean_object* v_h__1_2208_, lean_object* v_h__2_2209_){
_start:
{
if (lean_obj_tag(v_x_2207_) == 0)
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec(v_h__2_2209_);
v___x_2210_ = lean_box(0);
v___x_2211_ = lean_apply_1(v_h__1_2208_, v___x_2210_);
return v___x_2211_;
}
else
{
lean_object* v_val_2212_; lean_object* v___x_2213_; 
lean_dec(v_h__1_2208_);
v_val_2212_ = lean_ctor_get(v_x_2207_, 0);
lean_inc(v_val_2212_);
lean_dec_ref_known(v_x_2207_, 1);
v___x_2213_ = lean_apply_1(v_h__2_2209_, v_val_2212_);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_2214_, lean_object* v_00_u03b2_2215_, lean_object* v_motive_2216_, lean_object* v_x_2217_, lean_object* v_h__1_2218_, lean_object* v_h__2_2219_){
_start:
{
if (lean_obj_tag(v_x_2217_) == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_dec(v_h__2_2219_);
v___x_2220_ = lean_box(0);
v___x_2221_ = lean_apply_1(v_h__1_2218_, v___x_2220_);
return v___x_2221_;
}
else
{
lean_object* v_val_2222_; lean_object* v___x_2223_; 
lean_dec(v_h__1_2218_);
v_val_2222_ = lean_ctor_get(v_x_2217_, 0);
lean_inc(v_val_2222_);
lean_dec_ref_known(v_x_2217_, 1);
v___x_2223_ = lean_apply_1(v_h__2_2219_, v_val_2222_);
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___redArg(lean_object* v_t_2224_, lean_object* v_h__1_2225_){
_start:
{
lean_object* v_size_2226_; lean_object* v_k_2227_; lean_object* v_v_2228_; lean_object* v_l_2229_; lean_object* v_r_2230_; lean_object* v___x_2231_; 
v_size_2226_ = lean_ctor_get(v_t_2224_, 0);
lean_inc(v_size_2226_);
v_k_2227_ = lean_ctor_get(v_t_2224_, 1);
lean_inc(v_k_2227_);
v_v_2228_ = lean_ctor_get(v_t_2224_, 2);
lean_inc(v_v_2228_);
v_l_2229_ = lean_ctor_get(v_t_2224_, 3);
lean_inc(v_l_2229_);
v_r_2230_ = lean_ctor_get(v_t_2224_, 4);
lean_inc(v_r_2230_);
lean_dec(v_t_2224_);
v___x_2231_ = lean_apply_6(v_h__1_2225_, v_size_2226_, v_k_2227_, v_v_2228_, v_l_2229_, v_r_2230_, lean_box(0));
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(lean_object* v_00_u03b1_2232_, lean_object* v_00_u03b4_2233_, lean_object* v_inst_2234_, lean_object* v_k_2235_, lean_object* v_motive_2236_, lean_object* v_t_2237_, lean_object* v_hlk_2238_, lean_object* v_h__1_2239_){
_start:
{
lean_object* v_size_2240_; lean_object* v_k_2241_; lean_object* v_v_2242_; lean_object* v_l_2243_; lean_object* v_r_2244_; lean_object* v___x_2245_; 
v_size_2240_ = lean_ctor_get(v_t_2237_, 0);
lean_inc(v_size_2240_);
v_k_2241_ = lean_ctor_get(v_t_2237_, 1);
lean_inc(v_k_2241_);
v_v_2242_ = lean_ctor_get(v_t_2237_, 2);
lean_inc(v_v_2242_);
v_l_2243_ = lean_ctor_get(v_t_2237_, 3);
lean_inc(v_l_2243_);
v_r_2244_ = lean_ctor_get(v_t_2237_, 4);
lean_inc(v_r_2244_);
lean_dec(v_t_2237_);
v___x_2245_ = lean_apply_6(v_h__1_2239_, v_size_2240_, v_k_2241_, v_v_2242_, v_l_2243_, v_r_2244_, lean_box(0));
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___boxed(lean_object* v_00_u03b1_2246_, lean_object* v_00_u03b4_2247_, lean_object* v_inst_2248_, lean_object* v_k_2249_, lean_object* v_motive_2250_, lean_object* v_t_2251_, lean_object* v_hlk_2252_, lean_object* v_h__1_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(v_00_u03b1_2246_, v_00_u03b4_2247_, v_inst_2248_, v_k_2249_, v_motive_2250_, v_t_2251_, v_hlk_2252_, v_h__1_2253_);
lean_dec(v_k_2249_);
lean_dec_ref(v_inst_2248_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(lean_object* v_x_2255_, lean_object* v_x_2256_, lean_object* v_h__1_2257_){
_start:
{
lean_object* v_size_2258_; lean_object* v_k_2259_; lean_object* v_v_2260_; lean_object* v_l_2261_; lean_object* v_r_2262_; lean_object* v___x_2263_; 
v_size_2258_ = lean_ctor_get(v_x_2255_, 0);
lean_inc(v_size_2258_);
v_k_2259_ = lean_ctor_get(v_x_2255_, 1);
lean_inc(v_k_2259_);
v_v_2260_ = lean_ctor_get(v_x_2255_, 2);
lean_inc(v_v_2260_);
v_l_2261_ = lean_ctor_get(v_x_2255_, 3);
lean_inc(v_l_2261_);
v_r_2262_ = lean_ctor_get(v_x_2255_, 4);
lean_inc(v_r_2262_);
lean_dec(v_x_2255_);
v___x_2263_ = lean_apply_8(v_h__1_2257_, v_size_2258_, v_k_2259_, v_v_2260_, v_l_2261_, v_r_2262_, lean_box(0), v_x_2256_, lean_box(0));
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter(lean_object* v_00_u03b1_2264_, lean_object* v_00_u03b2_2265_, lean_object* v_motive_2266_, lean_object* v_x_2267_, lean_object* v_x_2268_, lean_object* v_x_2269_, lean_object* v_x_2270_, lean_object* v_h__1_2271_){
_start:
{
lean_object* v_size_2272_; lean_object* v_k_2273_; lean_object* v_v_2274_; lean_object* v_l_2275_; lean_object* v_r_2276_; lean_object* v___x_2277_; 
v_size_2272_ = lean_ctor_get(v_x_2267_, 0);
lean_inc(v_size_2272_);
v_k_2273_ = lean_ctor_get(v_x_2267_, 1);
lean_inc(v_k_2273_);
v_v_2274_ = lean_ctor_get(v_x_2267_, 2);
lean_inc(v_v_2274_);
v_l_2275_ = lean_ctor_get(v_x_2267_, 3);
lean_inc(v_l_2275_);
v_r_2276_ = lean_ctor_get(v_x_2267_, 4);
lean_inc(v_r_2276_);
lean_dec(v_x_2267_);
v___x_2277_ = lean_apply_8(v_h__1_2271_, v_size_2272_, v_k_2273_, v_v_2274_, v_l_2275_, v_r_2276_, lean_box(0), v_x_2269_, lean_box(0));
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(uint8_t v_x_2278_, lean_object* v_h__1_2279_, lean_object* v_h__2_2280_, lean_object* v_h__3_2281_){
_start:
{
switch(v_x_2278_)
{
case 0:
{
lean_object* v___x_2282_; 
lean_dec(v_h__3_2281_);
lean_dec(v_h__2_2280_);
v___x_2282_ = lean_apply_1(v_h__1_2279_, lean_box(0));
return v___x_2282_;
}
case 1:
{
lean_object* v___x_2283_; 
lean_dec(v_h__3_2281_);
lean_dec(v_h__1_2279_);
v___x_2283_ = lean_apply_1(v_h__2_2280_, lean_box(0));
return v___x_2283_;
}
default: 
{
lean_object* v___x_2284_; 
lean_dec(v_h__2_2280_);
lean_dec(v_h__1_2279_);
v___x_2284_ = lean_apply_1(v_h__3_2281_, lean_box(0));
return v___x_2284_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg___boxed(lean_object* v_x_2285_, lean_object* v_h__1_2286_, lean_object* v_h__2_2287_, lean_object* v_h__3_2288_){
_start:
{
uint8_t v_x_33__boxed_2289_; lean_object* v_res_2290_; 
v_x_33__boxed_2289_ = lean_unbox(v_x_2285_);
v_res_2290_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(v_x_33__boxed_2289_, v_h__1_2286_, v_h__2_2287_, v_h__3_2288_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(lean_object* v_motive_2291_, uint8_t v_x_2292_, lean_object* v_h__1_2293_, lean_object* v_h__2_2294_, lean_object* v_h__3_2295_){
_start:
{
switch(v_x_2292_)
{
case 0:
{
lean_object* v___x_2296_; 
lean_dec(v_h__3_2295_);
lean_dec(v_h__2_2294_);
v___x_2296_ = lean_apply_1(v_h__1_2293_, lean_box(0));
return v___x_2296_;
}
case 1:
{
lean_object* v___x_2297_; 
lean_dec(v_h__3_2295_);
lean_dec(v_h__1_2293_);
v___x_2297_ = lean_apply_1(v_h__2_2294_, lean_box(0));
return v___x_2297_;
}
default: 
{
lean_object* v___x_2298_; 
lean_dec(v_h__2_2294_);
lean_dec(v_h__1_2293_);
v___x_2298_ = lean_apply_1(v_h__3_2295_, lean_box(0));
return v___x_2298_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___boxed(lean_object* v_motive_2299_, lean_object* v_x_2300_, lean_object* v_h__1_2301_, lean_object* v_h__2_2302_, lean_object* v_h__3_2303_){
_start:
{
uint8_t v_x_42__boxed_2304_; lean_object* v_res_2305_; 
v_x_42__boxed_2304_ = lean_unbox(v_x_2300_);
v_res_2305_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(v_motive_2299_, v_x_42__boxed_2304_, v_h__1_2301_, v_h__2_2302_, v_h__3_2303_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object* v_x_2306_, lean_object* v_x_2307_, lean_object* v_h__1_2308_, lean_object* v_h__2_2309_){
_start:
{
if (lean_obj_tag(v_x_2306_) == 0)
{
lean_object* v_size_2310_; lean_object* v_k_2311_; lean_object* v_v_2312_; lean_object* v_l_2313_; lean_object* v_r_2314_; lean_object* v___x_2315_; 
lean_dec(v_h__1_2308_);
v_size_2310_ = lean_ctor_get(v_x_2306_, 0);
lean_inc(v_size_2310_);
v_k_2311_ = lean_ctor_get(v_x_2306_, 1);
lean_inc(v_k_2311_);
v_v_2312_ = lean_ctor_get(v_x_2306_, 2);
lean_inc(v_v_2312_);
v_l_2313_ = lean_ctor_get(v_x_2306_, 3);
lean_inc(v_l_2313_);
v_r_2314_ = lean_ctor_get(v_x_2306_, 4);
lean_inc(v_r_2314_);
lean_dec_ref_known(v_x_2306_, 5);
v___x_2315_ = lean_apply_6(v_h__2_2309_, v_size_2310_, v_k_2311_, v_v_2312_, v_l_2313_, v_r_2314_, v_x_2307_);
return v___x_2315_;
}
else
{
lean_object* v___x_2316_; 
lean_dec(v_h__2_2309_);
v___x_2316_ = lean_apply_1(v_h__1_2308_, v_x_2307_);
return v___x_2316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object* v_00_u03b1_2317_, lean_object* v_00_u03b2_2318_, lean_object* v_motive_2319_, lean_object* v_x_2320_, lean_object* v_x_2321_, lean_object* v_h__1_2322_, lean_object* v_h__2_2323_){
_start:
{
if (lean_obj_tag(v_x_2320_) == 0)
{
lean_object* v_size_2324_; lean_object* v_k_2325_; lean_object* v_v_2326_; lean_object* v_l_2327_; lean_object* v_r_2328_; lean_object* v___x_2329_; 
lean_dec(v_h__1_2322_);
v_size_2324_ = lean_ctor_get(v_x_2320_, 0);
lean_inc(v_size_2324_);
v_k_2325_ = lean_ctor_get(v_x_2320_, 1);
lean_inc(v_k_2325_);
v_v_2326_ = lean_ctor_get(v_x_2320_, 2);
lean_inc(v_v_2326_);
v_l_2327_ = lean_ctor_get(v_x_2320_, 3);
lean_inc(v_l_2327_);
v_r_2328_ = lean_ctor_get(v_x_2320_, 4);
lean_inc(v_r_2328_);
lean_dec_ref_known(v_x_2320_, 5);
v___x_2329_ = lean_apply_6(v_h__2_2323_, v_size_2324_, v_k_2325_, v_v_2326_, v_l_2327_, v_r_2328_, v_x_2321_);
return v___x_2329_;
}
else
{
lean_object* v___x_2330_; 
lean_dec(v_h__2_2323_);
v___x_2330_ = lean_apply_1(v_h__1_2322_, v_x_2321_);
return v___x_2330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t v_x_2331_, lean_object* v_h__1_2332_, lean_object* v_h__2_2333_, lean_object* v_h__3_2334_){
_start:
{
switch(v_x_2331_)
{
case 0:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_dec(v_h__3_2334_);
lean_dec(v_h__2_2333_);
v___x_2335_ = lean_box(0);
v___x_2336_ = lean_apply_1(v_h__1_2332_, v___x_2335_);
return v___x_2336_;
}
case 1:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec(v_h__3_2334_);
lean_dec(v_h__1_2332_);
v___x_2337_ = lean_box(0);
v___x_2338_ = lean_apply_1(v_h__2_2333_, v___x_2337_);
return v___x_2338_;
}
default: 
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
lean_dec(v_h__2_2333_);
lean_dec(v_h__1_2332_);
v___x_2339_ = lean_box(0);
v___x_2340_ = lean_apply_1(v_h__3_2334_, v___x_2339_);
return v___x_2340_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_2341_, lean_object* v_h__1_2342_, lean_object* v_h__2_2343_, lean_object* v_h__3_2344_){
_start:
{
uint8_t v_x_33__boxed_2345_; lean_object* v_res_2346_; 
v_x_33__boxed_2345_ = lean_unbox(v_x_2341_);
v_res_2346_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_33__boxed_2345_, v_h__1_2342_, v_h__2_2343_, v_h__3_2344_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object* v_motive_2347_, uint8_t v_x_2348_, lean_object* v_h__1_2349_, lean_object* v_h__2_2350_, lean_object* v_h__3_2351_){
_start:
{
switch(v_x_2348_)
{
case 0:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_dec(v_h__3_2351_);
lean_dec(v_h__2_2350_);
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_apply_1(v_h__1_2349_, v___x_2352_);
return v___x_2353_;
}
case 1:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
lean_dec(v_h__3_2351_);
lean_dec(v_h__1_2349_);
v___x_2354_ = lean_box(0);
v___x_2355_ = lean_apply_1(v_h__2_2350_, v___x_2354_);
return v___x_2355_;
}
default: 
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
lean_dec(v_h__2_2350_);
lean_dec(v_h__1_2349_);
v___x_2356_ = lean_box(0);
v___x_2357_ = lean_apply_1(v_h__3_2351_, v___x_2356_);
return v___x_2357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object* v_motive_2358_, lean_object* v_x_2359_, lean_object* v_h__1_2360_, lean_object* v_h__2_2361_, lean_object* v_h__3_2362_){
_start:
{
uint8_t v_x_48__boxed_2363_; lean_object* v_res_2364_; 
v_x_48__boxed_2363_ = lean_unbox(v_x_2359_);
v_res_2364_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(v_motive_2358_, v_x_48__boxed_2363_, v_h__1_2360_, v_h__2_2361_, v_h__3_2362_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter___redArg(lean_object* v_x_2365_, lean_object* v_x_2366_, lean_object* v_x_2367_, lean_object* v_h__1_2368_, lean_object* v_h__2_2369_){
_start:
{
if (lean_obj_tag(v_x_2365_) == 0)
{
lean_object* v_size_2370_; lean_object* v_k_2371_; lean_object* v_v_2372_; lean_object* v_l_2373_; lean_object* v_r_2374_; lean_object* v___x_2375_; 
lean_dec(v_h__1_2368_);
v_size_2370_ = lean_ctor_get(v_x_2365_, 0);
lean_inc(v_size_2370_);
v_k_2371_ = lean_ctor_get(v_x_2365_, 1);
lean_inc(v_k_2371_);
v_v_2372_ = lean_ctor_get(v_x_2365_, 2);
lean_inc(v_v_2372_);
v_l_2373_ = lean_ctor_get(v_x_2365_, 3);
lean_inc(v_l_2373_);
v_r_2374_ = lean_ctor_get(v_x_2365_, 4);
lean_inc(v_r_2374_);
lean_dec_ref_known(v_x_2365_, 5);
v___x_2375_ = lean_apply_7(v_h__2_2369_, v_size_2370_, v_k_2371_, v_v_2372_, v_l_2373_, v_r_2374_, v_x_2366_, v_x_2367_);
return v___x_2375_;
}
else
{
lean_object* v___x_2376_; 
lean_dec(v_h__2_2369_);
v___x_2376_ = lean_apply_2(v_h__1_2368_, v_x_2366_, v_x_2367_);
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2377_, lean_object* v_00_u03b2_2378_, lean_object* v_motive_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_, lean_object* v_h__1_2383_, lean_object* v_h__2_2384_){
_start:
{
if (lean_obj_tag(v_x_2380_) == 0)
{
lean_object* v_size_2385_; lean_object* v_k_2386_; lean_object* v_v_2387_; lean_object* v_l_2388_; lean_object* v_r_2389_; lean_object* v___x_2390_; 
lean_dec(v_h__1_2383_);
v_size_2385_ = lean_ctor_get(v_x_2380_, 0);
lean_inc(v_size_2385_);
v_k_2386_ = lean_ctor_get(v_x_2380_, 1);
lean_inc(v_k_2386_);
v_v_2387_ = lean_ctor_get(v_x_2380_, 2);
lean_inc(v_v_2387_);
v_l_2388_ = lean_ctor_get(v_x_2380_, 3);
lean_inc(v_l_2388_);
v_r_2389_ = lean_ctor_get(v_x_2380_, 4);
lean_inc(v_r_2389_);
lean_dec_ref_known(v_x_2380_, 5);
v___x_2390_ = lean_apply_7(v_h__2_2384_, v_size_2385_, v_k_2386_, v_v_2387_, v_l_2388_, v_r_2389_, v_x_2381_, v_x_2382_);
return v___x_2390_;
}
else
{
lean_object* v___x_2391_; 
lean_dec(v_h__2_2384_);
v___x_2391_ = lean_apply_2(v_h__1_2383_, v_x_2381_, v_x_2382_);
return v___x_2391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter___redArg(lean_object* v_x_2392_, lean_object* v_x_2393_, lean_object* v_x_2394_, lean_object* v_h__1_2395_, lean_object* v_h__2_2396_){
_start:
{
if (lean_obj_tag(v_x_2392_) == 0)
{
lean_object* v_size_2397_; lean_object* v_k_2398_; lean_object* v_v_2399_; lean_object* v_l_2400_; lean_object* v_r_2401_; lean_object* v___x_2402_; 
lean_dec(v_h__1_2395_);
v_size_2397_ = lean_ctor_get(v_x_2392_, 0);
lean_inc(v_size_2397_);
v_k_2398_ = lean_ctor_get(v_x_2392_, 1);
lean_inc(v_k_2398_);
v_v_2399_ = lean_ctor_get(v_x_2392_, 2);
lean_inc(v_v_2399_);
v_l_2400_ = lean_ctor_get(v_x_2392_, 3);
lean_inc(v_l_2400_);
v_r_2401_ = lean_ctor_get(v_x_2392_, 4);
lean_inc(v_r_2401_);
lean_dec_ref_known(v_x_2392_, 5);
v___x_2402_ = lean_apply_7(v_h__2_2396_, v_size_2397_, v_k_2398_, v_v_2399_, v_l_2400_, v_r_2401_, v_x_2393_, v_x_2394_);
return v___x_2402_;
}
else
{
lean_object* v___x_2403_; 
lean_dec(v_h__2_2396_);
v___x_2403_ = lean_apply_2(v_h__1_2395_, v_x_2393_, v_x_2394_);
return v___x_2403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2404_, lean_object* v_00_u03b2_2405_, lean_object* v_motive_2406_, lean_object* v_x_2407_, lean_object* v_x_2408_, lean_object* v_x_2409_, lean_object* v_h__1_2410_, lean_object* v_h__2_2411_){
_start:
{
if (lean_obj_tag(v_x_2407_) == 0)
{
lean_object* v_size_2412_; lean_object* v_k_2413_; lean_object* v_v_2414_; lean_object* v_l_2415_; lean_object* v_r_2416_; lean_object* v___x_2417_; 
lean_dec(v_h__1_2410_);
v_size_2412_ = lean_ctor_get(v_x_2407_, 0);
lean_inc(v_size_2412_);
v_k_2413_ = lean_ctor_get(v_x_2407_, 1);
lean_inc(v_k_2413_);
v_v_2414_ = lean_ctor_get(v_x_2407_, 2);
lean_inc(v_v_2414_);
v_l_2415_ = lean_ctor_get(v_x_2407_, 3);
lean_inc(v_l_2415_);
v_r_2416_ = lean_ctor_get(v_x_2407_, 4);
lean_inc(v_r_2416_);
lean_dec_ref_known(v_x_2407_, 5);
v___x_2417_ = lean_apply_7(v_h__2_2411_, v_size_2412_, v_k_2413_, v_v_2414_, v_l_2415_, v_r_2416_, v_x_2408_, v_x_2409_);
return v___x_2417_;
}
else
{
lean_object* v___x_2418_; 
lean_dec(v_h__2_2411_);
v___x_2418_ = lean_apply_2(v_h__1_2410_, v_x_2408_, v_x_2409_);
return v___x_2418_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(lean_object* v_x_2419_, lean_object* v_c_2420_, lean_object* v_x_2421_, lean_object* v_r_2422_){
_start:
{
if (lean_obj_tag(v_c_2420_) == 0)
{
lean_object* v___x_2423_; 
v___x_2423_ = l_List_head_x3f___redArg(v_r_2422_);
return v___x_2423_;
}
else
{
lean_object* v_val_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
v_val_2424_ = lean_ctor_get(v_c_2420_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_c_2420_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v_c_2420_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_val_2424_);
lean_dec(v_c_2420_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_val_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed(lean_object* v_x_2432_, lean_object* v_c_2433_, lean_object* v_x_2434_, lean_object* v_r_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(v_x_2432_, v_c_2433_, v_x_2434_, v_r_2435_);
lean_dec(v_r_2435_);
lean_dec(v_x_2432_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(lean_object* v_inst_2438_, lean_object* v_k_2439_, lean_object* v_t_2440_){
_start:
{
lean_object* v___f_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___f_2441_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0));
v___x_2442_ = lean_apply_1(v_inst_2438_, v_k_2439_);
v___x_2443_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___x_2442_, v_t_2440_, v___f_2441_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098(lean_object* v_00_u03b1_2444_, lean_object* v_00_u03b2_2445_, lean_object* v_inst_2446_, lean_object* v_k_2447_, lean_object* v_t_2448_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(v_inst_2446_, v_k_2447_, v_t_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(lean_object* v_x_2450_, lean_object* v_x_2451_){
_start:
{
switch(lean_obj_tag(v_x_2451_))
{
case 0:
{
lean_object* v_a_2452_; lean_object* v_a_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v_a_2452_ = lean_ctor_get(v_x_2451_, 0);
lean_inc(v_a_2452_);
v_a_2453_ = lean_ctor_get(v_x_2451_, 1);
lean_inc(v_a_2453_);
lean_dec_ref_known(v_x_2451_, 3);
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v_a_2452_);
lean_ctor_set(v___x_2454_, 1, v_a_2453_);
v___x_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
return v___x_2455_;
}
case 1:
{
lean_object* v_a_2456_; 
v_a_2456_ = lean_ctor_get(v_x_2451_, 1);
lean_inc(v_a_2456_);
if (lean_obj_tag(v_a_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2458_; 
v_a_2457_ = lean_ctor_get(v_x_2451_, 2);
lean_inc(v_a_2457_);
lean_dec_ref_known(v_x_2451_, 3);
v___x_2458_ = l_List_head_x3f___redArg(v_a_2457_);
lean_dec(v_a_2457_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_inc(v_x_2450_);
return v_x_2450_;
}
else
{
return v___x_2458_;
}
}
else
{
lean_object* v_val_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec_ref_known(v_x_2451_, 3);
v_val_2459_ = lean_ctor_get(v_a_2456_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_a_2456_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v_a_2456_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_val_2459_);
lean_dec(v_a_2456_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_val_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
default: 
{
lean_dec_ref_known(v_x_2451_, 3);
lean_inc(v_x_2450_);
return v_x_2450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* v_x_2467_, lean_object* v_x_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(v_x_2467_, v_x_2468_);
lean_dec(v_x_2467_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(lean_object* v_inst_2471_, lean_object* v_k_2472_, lean_object* v_t_2473_){
_start:
{
lean_object* v___f_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___f_2474_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0));
v___x_2475_ = lean_apply_1(v_inst_2471_, v_k_2472_);
v___x_2476_ = lean_box(0);
v___x_2477_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___x_2475_, v___x_2476_, v___f_2474_, v_t_2473_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27(lean_object* v_00_u03b1_2478_, lean_object* v_00_u03b2_2479_, lean_object* v_inst_2480_, lean_object* v_k_2481_, lean_object* v_t_2482_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(v_inst_2480_, v_k_2481_, v_t_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_x_2484_, lean_object* v_x_2485_, lean_object* v_h__1_2486_, lean_object* v_h__2_2487_, lean_object* v_h__3_2488_){
_start:
{
switch(lean_obj_tag(v_x_2485_))
{
case 0:
{
lean_object* v_a_2489_; lean_object* v_a_2490_; lean_object* v_a_2491_; lean_object* v___x_2492_; 
lean_dec(v_h__3_2488_);
lean_dec(v_h__2_2487_);
v_a_2489_ = lean_ctor_get(v_x_2485_, 0);
lean_inc(v_a_2489_);
v_a_2490_ = lean_ctor_get(v_x_2485_, 1);
lean_inc(v_a_2490_);
v_a_2491_ = lean_ctor_get(v_x_2485_, 2);
lean_inc(v_a_2491_);
lean_dec_ref_known(v_x_2485_, 3);
v___x_2492_ = lean_apply_5(v_h__1_2486_, v_x_2484_, v_a_2489_, lean_box(0), v_a_2490_, v_a_2491_);
return v___x_2492_;
}
case 1:
{
lean_object* v_a_2493_; lean_object* v_a_2494_; lean_object* v_a_2495_; lean_object* v___x_2496_; 
lean_dec(v_h__3_2488_);
lean_dec(v_h__1_2486_);
v_a_2493_ = lean_ctor_get(v_x_2485_, 0);
lean_inc(v_a_2493_);
v_a_2494_ = lean_ctor_get(v_x_2485_, 1);
lean_inc(v_a_2494_);
v_a_2495_ = lean_ctor_get(v_x_2485_, 2);
lean_inc(v_a_2495_);
lean_dec_ref_known(v_x_2485_, 3);
v___x_2496_ = lean_apply_4(v_h__2_2487_, v_x_2484_, v_a_2493_, v_a_2494_, v_a_2495_);
return v___x_2496_;
}
default: 
{
lean_object* v_a_2497_; lean_object* v_a_2498_; lean_object* v_a_2499_; lean_object* v___x_2500_; 
lean_dec(v_h__2_2487_);
lean_dec(v_h__1_2486_);
v_a_2497_ = lean_ctor_get(v_x_2485_, 0);
lean_inc(v_a_2497_);
v_a_2498_ = lean_ctor_get(v_x_2485_, 1);
lean_inc(v_a_2498_);
v_a_2499_ = lean_ctor_get(v_x_2485_, 2);
lean_inc(v_a_2499_);
lean_dec_ref_known(v_x_2485_, 3);
v___x_2500_ = lean_apply_5(v_h__3_2488_, v_x_2484_, v_a_2497_, v_a_2498_, lean_box(0), v_a_2499_);
return v___x_2500_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_2501_, lean_object* v_00_u03b2_2502_, lean_object* v_inst_2503_, lean_object* v_k_2504_, lean_object* v_motive_2505_, lean_object* v_x_2506_, lean_object* v_x_2507_, lean_object* v_h__1_2508_, lean_object* v_h__2_2509_, lean_object* v_h__3_2510_){
_start:
{
switch(lean_obj_tag(v_x_2507_))
{
case 0:
{
lean_object* v_a_2511_; lean_object* v_a_2512_; lean_object* v_a_2513_; lean_object* v___x_2514_; 
lean_dec(v_h__3_2510_);
lean_dec(v_h__2_2509_);
v_a_2511_ = lean_ctor_get(v_x_2507_, 0);
lean_inc(v_a_2511_);
v_a_2512_ = lean_ctor_get(v_x_2507_, 1);
lean_inc(v_a_2512_);
v_a_2513_ = lean_ctor_get(v_x_2507_, 2);
lean_inc(v_a_2513_);
lean_dec_ref_known(v_x_2507_, 3);
v___x_2514_ = lean_apply_5(v_h__1_2508_, v_x_2506_, v_a_2511_, lean_box(0), v_a_2512_, v_a_2513_);
return v___x_2514_;
}
case 1:
{
lean_object* v_a_2515_; lean_object* v_a_2516_; lean_object* v_a_2517_; lean_object* v___x_2518_; 
lean_dec(v_h__3_2510_);
lean_dec(v_h__1_2508_);
v_a_2515_ = lean_ctor_get(v_x_2507_, 0);
lean_inc(v_a_2515_);
v_a_2516_ = lean_ctor_get(v_x_2507_, 1);
lean_inc(v_a_2516_);
v_a_2517_ = lean_ctor_get(v_x_2507_, 2);
lean_inc(v_a_2517_);
lean_dec_ref_known(v_x_2507_, 3);
v___x_2518_ = lean_apply_4(v_h__2_2509_, v_x_2506_, v_a_2515_, v_a_2516_, v_a_2517_);
return v___x_2518_;
}
default: 
{
lean_object* v_a_2519_; lean_object* v_a_2520_; lean_object* v_a_2521_; lean_object* v___x_2522_; 
lean_dec(v_h__2_2509_);
lean_dec(v_h__1_2508_);
v_a_2519_ = lean_ctor_get(v_x_2507_, 0);
lean_inc(v_a_2519_);
v_a_2520_ = lean_ctor_get(v_x_2507_, 1);
lean_inc(v_a_2520_);
v_a_2521_ = lean_ctor_get(v_x_2507_, 2);
lean_inc(v_a_2521_);
lean_dec_ref_known(v_x_2507_, 3);
v___x_2522_ = lean_apply_5(v_h__3_2510_, v_x_2506_, v_a_2519_, v_a_2520_, lean_box(0), v_a_2521_);
return v___x_2522_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_2523_, lean_object* v_00_u03b2_2524_, lean_object* v_inst_2525_, lean_object* v_k_2526_, lean_object* v_motive_2527_, lean_object* v_x_2528_, lean_object* v_x_2529_, lean_object* v_h__1_2530_, lean_object* v_h__2_2531_, lean_object* v_h__3_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(v_00_u03b1_2523_, v_00_u03b2_2524_, v_inst_2525_, v_k_2526_, v_motive_2527_, v_x_2528_, v_x_2529_, v_h__1_2530_, v_h__2_2531_, v_h__3_2532_);
lean_dec(v_k_2526_);
lean_dec_ref(v_inst_2525_);
return v_res_2533_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(lean_object* v_inst_2534_, lean_object* v_k_2535_, lean_object* v_k_x27_2536_){
_start:
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = lean_apply_2(v_inst_2534_, v_k_2535_, v_k_x27_2536_);
v___x_2538_ = lean_unbox(v___x_2537_);
if (v___x_2538_ == 1)
{
uint8_t v___x_2539_; 
v___x_2539_ = 2;
return v___x_2539_;
}
else
{
uint8_t v___x_2540_; 
v___x_2540_ = lean_unbox(v___x_2537_);
return v___x_2540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed(lean_object* v_inst_2541_, lean_object* v_k_2542_, lean_object* v_k_x27_2543_){
_start:
{
uint8_t v_res_2544_; lean_object* v_r_2545_; 
v_res_2544_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(v_inst_2541_, v_k_2542_, v_k_x27_2543_);
v_r_2545_ = lean_box(v_res_2544_);
return v_r_2545_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(lean_object* v_inst_2546_, lean_object* v_k_2547_, lean_object* v_t_2548_){
_start:
{
lean_object* v___f_2549_; lean_object* v___f_2550_; lean_object* v___x_2551_; 
v___f_2549_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2549_, 0, v_inst_2546_);
lean_closure_set(v___f_2549_, 1, v_k_2547_);
v___f_2550_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0));
v___x_2551_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_2549_, v_t_2548_, v___f_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098(lean_object* v_00_u03b1_2552_, lean_object* v_00_u03b2_2553_, lean_object* v_inst_2554_, lean_object* v_k_2555_, lean_object* v_t_2556_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(v_inst_2554_, v_k_2555_, v_t_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(lean_object* v_x_2558_, lean_object* v_x_2559_){
_start:
{
switch(lean_obj_tag(v_x_2559_))
{
case 0:
{
lean_object* v_a_2560_; lean_object* v_a_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v_a_2560_ = lean_ctor_get(v_x_2559_, 0);
v_a_2561_ = lean_ctor_get(v_x_2559_, 1);
lean_inc(v_a_2561_);
lean_inc(v_a_2560_);
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v_a_2560_);
lean_ctor_set(v___x_2562_, 1, v_a_2561_);
v___x_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
return v___x_2563_;
}
case 1:
{
lean_object* v_a_2564_; lean_object* v___x_2565_; 
v_a_2564_ = lean_ctor_get(v_x_2559_, 2);
v___x_2565_ = l_List_head_x3f___redArg(v_a_2564_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_inc(v_x_2558_);
return v_x_2558_;
}
else
{
return v___x_2565_;
}
}
default: 
{
lean_inc(v_x_2558_);
return v_x_2558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* v_x_2566_, lean_object* v_x_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(v_x_2566_, v_x_2567_);
lean_dec_ref(v_x_2567_);
lean_dec(v_x_2566_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(lean_object* v_inst_2570_, lean_object* v_k_2571_, lean_object* v_t_2572_){
_start:
{
lean_object* v___f_2573_; lean_object* v___f_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___f_2573_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2573_, 0, v_inst_2570_);
lean_closure_set(v___f_2573_, 1, v_k_2571_);
v___f_2574_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0));
v___x_2575_ = lean_box(0);
v___x_2576_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___f_2573_, v___x_2575_, v___f_2574_, v_t_2572_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27(lean_object* v_00_u03b1_2577_, lean_object* v_00_u03b2_2578_, lean_object* v_inst_2579_, lean_object* v_k_2580_, lean_object* v_t_2581_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(v_inst_2579_, v_k_2580_, v_t_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(uint8_t v_x_2583_, lean_object* v_h__1_2584_, lean_object* v_h__2_2585_){
_start:
{
if (v_x_2583_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_dec(v_h__2_2585_);
v___x_2586_ = lean_box(0);
v___x_2587_ = lean_apply_1(v_h__1_2584_, v___x_2586_);
return v___x_2587_;
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_dec(v_h__1_2584_);
v___x_2588_ = lean_box(v_x_2583_);
v___x_2589_ = lean_apply_2(v_h__2_2585_, v___x_2588_, lean_box(0));
return v___x_2589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg___boxed(lean_object* v_x_2590_, lean_object* v_h__1_2591_, lean_object* v_h__2_2592_){
_start:
{
uint8_t v_x_13__boxed_2593_; lean_object* v_res_2594_; 
v_x_13__boxed_2593_ = lean_unbox(v_x_2590_);
v_res_2594_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(v_x_13__boxed_2593_, v_h__1_2591_, v_h__2_2592_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(lean_object* v_motive_2595_, uint8_t v_x_2596_, lean_object* v_h__1_2597_, lean_object* v_h__2_2598_){
_start:
{
if (v_x_2596_ == 0)
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec(v_h__2_2598_);
v___x_2599_ = lean_box(0);
v___x_2600_ = lean_apply_1(v_h__1_2597_, v___x_2599_);
return v___x_2600_;
}
else
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_dec(v_h__1_2597_);
v___x_2601_ = lean_box(v_x_2596_);
v___x_2602_ = lean_apply_2(v_h__2_2598_, v___x_2601_, lean_box(0));
return v___x_2602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___boxed(lean_object* v_motive_2603_, lean_object* v_x_2604_, lean_object* v_h__1_2605_, lean_object* v_h__2_2606_){
_start:
{
uint8_t v_x_24__boxed_2607_; lean_object* v_res_2608_; 
v_x_24__boxed_2607_ = lean_unbox(v_x_2604_);
v_res_2608_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(v_motive_2603_, v_x_24__boxed_2607_, v_h__1_2605_, v_h__2_2606_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_x_2609_, lean_object* v_x_2610_, lean_object* v_h__1_2611_, lean_object* v_h__2_2612_, lean_object* v_h__3_2613_){
_start:
{
switch(lean_obj_tag(v_x_2610_))
{
case 0:
{
lean_object* v_a_2614_; lean_object* v_a_2615_; lean_object* v_a_2616_; lean_object* v___x_2617_; 
lean_dec(v_h__3_2613_);
lean_dec(v_h__2_2612_);
v_a_2614_ = lean_ctor_get(v_x_2610_, 0);
lean_inc(v_a_2614_);
v_a_2615_ = lean_ctor_get(v_x_2610_, 1);
lean_inc(v_a_2615_);
v_a_2616_ = lean_ctor_get(v_x_2610_, 2);
lean_inc(v_a_2616_);
lean_dec_ref_known(v_x_2610_, 3);
v___x_2617_ = lean_apply_5(v_h__1_2611_, v_x_2609_, v_a_2614_, lean_box(0), v_a_2615_, v_a_2616_);
return v___x_2617_;
}
case 1:
{
lean_object* v_a_2618_; lean_object* v_a_2619_; lean_object* v_a_2620_; lean_object* v___x_2621_; 
lean_dec(v_h__3_2613_);
lean_dec(v_h__1_2611_);
v_a_2618_ = lean_ctor_get(v_x_2610_, 0);
lean_inc(v_a_2618_);
v_a_2619_ = lean_ctor_get(v_x_2610_, 1);
lean_inc(v_a_2619_);
v_a_2620_ = lean_ctor_get(v_x_2610_, 2);
lean_inc(v_a_2620_);
lean_dec_ref_known(v_x_2610_, 3);
v___x_2621_ = lean_apply_4(v_h__2_2612_, v_x_2609_, v_a_2618_, v_a_2619_, v_a_2620_);
return v___x_2621_;
}
default: 
{
lean_object* v_a_2622_; lean_object* v_a_2623_; lean_object* v_a_2624_; lean_object* v___x_2625_; 
lean_dec(v_h__2_2612_);
lean_dec(v_h__1_2611_);
v_a_2622_ = lean_ctor_get(v_x_2610_, 0);
lean_inc(v_a_2622_);
v_a_2623_ = lean_ctor_get(v_x_2610_, 1);
lean_inc(v_a_2623_);
v_a_2624_ = lean_ctor_get(v_x_2610_, 2);
lean_inc(v_a_2624_);
lean_dec_ref_known(v_x_2610_, 3);
v___x_2625_ = lean_apply_5(v_h__3_2613_, v_x_2609_, v_a_2622_, v_a_2623_, lean_box(0), v_a_2624_);
return v___x_2625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_2626_, lean_object* v_00_u03b2_2627_, lean_object* v_inst_2628_, lean_object* v_k_2629_, lean_object* v_motive_2630_, lean_object* v_x_2631_, lean_object* v_x_2632_, lean_object* v_h__1_2633_, lean_object* v_h__2_2634_, lean_object* v_h__3_2635_){
_start:
{
switch(lean_obj_tag(v_x_2632_))
{
case 0:
{
lean_object* v_a_2636_; lean_object* v_a_2637_; lean_object* v_a_2638_; lean_object* v___x_2639_; 
lean_dec(v_h__3_2635_);
lean_dec(v_h__2_2634_);
v_a_2636_ = lean_ctor_get(v_x_2632_, 0);
lean_inc(v_a_2636_);
v_a_2637_ = lean_ctor_get(v_x_2632_, 1);
lean_inc(v_a_2637_);
v_a_2638_ = lean_ctor_get(v_x_2632_, 2);
lean_inc(v_a_2638_);
lean_dec_ref_known(v_x_2632_, 3);
v___x_2639_ = lean_apply_5(v_h__1_2633_, v_x_2631_, v_a_2636_, lean_box(0), v_a_2637_, v_a_2638_);
return v___x_2639_;
}
case 1:
{
lean_object* v_a_2640_; lean_object* v_a_2641_; lean_object* v_a_2642_; lean_object* v___x_2643_; 
lean_dec(v_h__3_2635_);
lean_dec(v_h__1_2633_);
v_a_2640_ = lean_ctor_get(v_x_2632_, 0);
lean_inc(v_a_2640_);
v_a_2641_ = lean_ctor_get(v_x_2632_, 1);
lean_inc(v_a_2641_);
v_a_2642_ = lean_ctor_get(v_x_2632_, 2);
lean_inc(v_a_2642_);
lean_dec_ref_known(v_x_2632_, 3);
v___x_2643_ = lean_apply_4(v_h__2_2634_, v_x_2631_, v_a_2640_, v_a_2641_, v_a_2642_);
return v___x_2643_;
}
default: 
{
lean_object* v_a_2644_; lean_object* v_a_2645_; lean_object* v_a_2646_; lean_object* v___x_2647_; 
lean_dec(v_h__2_2634_);
lean_dec(v_h__1_2633_);
v_a_2644_ = lean_ctor_get(v_x_2632_, 0);
lean_inc(v_a_2644_);
v_a_2645_ = lean_ctor_get(v_x_2632_, 1);
lean_inc(v_a_2645_);
v_a_2646_ = lean_ctor_get(v_x_2632_, 2);
lean_inc(v_a_2646_);
lean_dec_ref_known(v_x_2632_, 3);
v___x_2647_ = lean_apply_5(v_h__3_2635_, v_x_2631_, v_a_2644_, v_a_2645_, lean_box(0), v_a_2646_);
return v___x_2647_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_2648_, lean_object* v_00_u03b2_2649_, lean_object* v_inst_2650_, lean_object* v_k_2651_, lean_object* v_motive_2652_, lean_object* v_x_2653_, lean_object* v_x_2654_, lean_object* v_h__1_2655_, lean_object* v_h__2_2656_, lean_object* v_h__3_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(v_00_u03b1_2648_, v_00_u03b2_2649_, v_inst_2650_, v_k_2651_, v_motive_2652_, v_x_2653_, v_x_2654_, v_h__1_2655_, v_h__2_2656_, v_h__3_2657_);
lean_dec(v_k_2651_);
lean_dec_ref(v_inst_2650_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(uint8_t v_x_2659_, lean_object* v_h__1_2660_, lean_object* v_h__2_2661_){
_start:
{
if (v_x_2659_ == 2)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
lean_dec(v_h__2_2661_);
v___x_2662_ = lean_box(0);
v___x_2663_ = lean_apply_1(v_h__1_2660_, v___x_2662_);
return v___x_2663_;
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
lean_dec(v_h__1_2660_);
v___x_2664_ = lean_box(v_x_2659_);
v___x_2665_ = lean_apply_2(v_h__2_2661_, v___x_2664_, lean_box(0));
return v___x_2665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg___boxed(lean_object* v_x_2666_, lean_object* v_h__1_2667_, lean_object* v_h__2_2668_){
_start:
{
uint8_t v_x_13__boxed_2669_; lean_object* v_res_2670_; 
v_x_13__boxed_2669_ = lean_unbox(v_x_2666_);
v_res_2670_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(v_x_13__boxed_2669_, v_h__1_2667_, v_h__2_2668_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(lean_object* v_motive_2671_, uint8_t v_x_2672_, lean_object* v_h__1_2673_, lean_object* v_h__2_2674_){
_start:
{
if (v_x_2672_ == 2)
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
lean_dec(v_h__2_2674_);
v___x_2675_ = lean_box(0);
v___x_2676_ = lean_apply_1(v_h__1_2673_, v___x_2675_);
return v___x_2676_;
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_dec(v_h__1_2673_);
v___x_2677_ = lean_box(v_x_2672_);
v___x_2678_ = lean_apply_2(v_h__2_2674_, v___x_2677_, lean_box(0));
return v___x_2678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___boxed(lean_object* v_motive_2679_, lean_object* v_x_2680_, lean_object* v_h__1_2681_, lean_object* v_h__2_2682_){
_start:
{
uint8_t v_x_24__boxed_2683_; lean_object* v_res_2684_; 
v_x_24__boxed_2683_ = lean_unbox(v_x_2680_);
v_res_2684_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(v_motive_2679_, v_x_24__boxed_2683_, v_h__1_2681_, v_h__2_2682_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(uint8_t v_x_2685_, lean_object* v_h__1_2686_, lean_object* v_h__2_2687_, lean_object* v_h__3_2688_){
_start:
{
switch(v_x_2685_)
{
case 0:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
lean_dec(v_h__3_2688_);
lean_dec(v_h__2_2687_);
v___x_2689_ = lean_box(0);
v___x_2690_ = lean_apply_1(v_h__1_2686_, v___x_2689_);
return v___x_2690_;
}
case 1:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_dec(v_h__3_2688_);
lean_dec(v_h__1_2686_);
v___x_2691_ = lean_box(0);
v___x_2692_ = lean_apply_1(v_h__2_2687_, v___x_2691_);
return v___x_2692_;
}
default: 
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
lean_dec(v_h__2_2687_);
lean_dec(v_h__1_2686_);
v___x_2693_ = lean_box(0);
v___x_2694_ = lean_apply_1(v_h__3_2688_, v___x_2693_);
return v___x_2694_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object* v_x_2695_, lean_object* v_h__1_2696_, lean_object* v_h__2_2697_, lean_object* v_h__3_2698_){
_start:
{
uint8_t v_x_33__boxed_2699_; lean_object* v_res_2700_; 
v_x_33__boxed_2699_ = lean_unbox(v_x_2695_);
v_res_2700_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(v_x_33__boxed_2699_, v_h__1_2696_, v_h__2_2697_, v_h__3_2698_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(lean_object* v_motive_2701_, uint8_t v_x_2702_, lean_object* v_h__1_2703_, lean_object* v_h__2_2704_, lean_object* v_h__3_2705_){
_start:
{
switch(v_x_2702_)
{
case 0:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
lean_dec(v_h__3_2705_);
lean_dec(v_h__2_2704_);
v___x_2706_ = lean_box(0);
v___x_2707_ = lean_apply_1(v_h__1_2703_, v___x_2706_);
return v___x_2707_;
}
case 1:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_dec(v_h__3_2705_);
lean_dec(v_h__1_2703_);
v___x_2708_ = lean_box(0);
v___x_2709_ = lean_apply_1(v_h__2_2704_, v___x_2708_);
return v___x_2709_;
}
default: 
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_dec(v_h__2_2704_);
lean_dec(v_h__1_2703_);
v___x_2710_ = lean_box(0);
v___x_2711_ = lean_apply_1(v_h__3_2705_, v___x_2710_);
return v___x_2711_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___boxed(lean_object* v_motive_2712_, lean_object* v_x_2713_, lean_object* v_h__1_2714_, lean_object* v_h__2_2715_, lean_object* v_h__3_2716_){
_start:
{
uint8_t v_x_48__boxed_2717_; lean_object* v_res_2718_; 
v_x_48__boxed_2717_ = lean_unbox(v_x_2713_);
v_res_2718_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(v_motive_2712_, v_x_48__boxed_2717_, v_h__1_2714_, v_h__2_2715_, v_h__3_2716_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___redArg(lean_object* v_x_2719_, lean_object* v_h__1_2720_, lean_object* v_h__2_2721_){
_start:
{
if (lean_obj_tag(v_x_2719_) == 0)
{
lean_object* v_size_2722_; lean_object* v_k_2723_; lean_object* v_v_2724_; lean_object* v_l_2725_; lean_object* v_r_2726_; lean_object* v___x_2727_; 
lean_dec(v_h__1_2720_);
v_size_2722_ = lean_ctor_get(v_x_2719_, 0);
lean_inc(v_size_2722_);
v_k_2723_ = lean_ctor_get(v_x_2719_, 1);
lean_inc(v_k_2723_);
v_v_2724_ = lean_ctor_get(v_x_2719_, 2);
lean_inc(v_v_2724_);
v_l_2725_ = lean_ctor_get(v_x_2719_, 3);
lean_inc(v_l_2725_);
v_r_2726_ = lean_ctor_get(v_x_2719_, 4);
lean_inc(v_r_2726_);
lean_dec_ref_known(v_x_2719_, 5);
v___x_2727_ = lean_apply_7(v_h__2_2721_, v_size_2722_, v_k_2723_, v_v_2724_, v_l_2725_, v_r_2726_, lean_box(0), lean_box(0));
return v___x_2727_;
}
else
{
lean_object* v___x_2728_; 
lean_dec(v_h__2_2721_);
v___x_2728_ = lean_apply_2(v_h__1_2720_, lean_box(0), lean_box(0));
return v___x_2728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(lean_object* v_00_u03b1_2729_, lean_object* v_00_u03b2_2730_, lean_object* v_inst_2731_, lean_object* v_k_2732_, lean_object* v_motive_2733_, lean_object* v_x_2734_, lean_object* v_x_2735_, lean_object* v_x_2736_, lean_object* v_h__1_2737_, lean_object* v_h__2_2738_){
_start:
{
if (lean_obj_tag(v_x_2734_) == 0)
{
lean_object* v_size_2739_; lean_object* v_k_2740_; lean_object* v_v_2741_; lean_object* v_l_2742_; lean_object* v_r_2743_; lean_object* v___x_2744_; 
lean_dec(v_h__1_2737_);
v_size_2739_ = lean_ctor_get(v_x_2734_, 0);
lean_inc(v_size_2739_);
v_k_2740_ = lean_ctor_get(v_x_2734_, 1);
lean_inc(v_k_2740_);
v_v_2741_ = lean_ctor_get(v_x_2734_, 2);
lean_inc(v_v_2741_);
v_l_2742_ = lean_ctor_get(v_x_2734_, 3);
lean_inc(v_l_2742_);
v_r_2743_ = lean_ctor_get(v_x_2734_, 4);
lean_inc(v_r_2743_);
lean_dec_ref_known(v_x_2734_, 5);
v___x_2744_ = lean_apply_7(v_h__2_2738_, v_size_2739_, v_k_2740_, v_v_2741_, v_l_2742_, v_r_2743_, lean_box(0), lean_box(0));
return v___x_2744_;
}
else
{
lean_object* v___x_2745_; 
lean_dec(v_h__2_2738_);
v___x_2745_ = lean_apply_2(v_h__1_2737_, lean_box(0), lean_box(0));
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___boxed(lean_object* v_00_u03b1_2746_, lean_object* v_00_u03b2_2747_, lean_object* v_inst_2748_, lean_object* v_k_2749_, lean_object* v_motive_2750_, lean_object* v_x_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_, lean_object* v_h__1_2754_, lean_object* v_h__2_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(v_00_u03b1_2746_, v_00_u03b2_2747_, v_inst_2748_, v_k_2749_, v_motive_2750_, v_x_2751_, v_x_2752_, v_x_2753_, v_h__1_2754_, v_h__2_2755_);
lean_dec(v_k_2749_);
lean_dec_ref(v_inst_2748_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___redArg(lean_object* v_x_2757_, lean_object* v_h__1_2758_, lean_object* v_h__2_2759_){
_start:
{
if (lean_obj_tag(v_x_2757_) == 0)
{
lean_object* v_size_2760_; lean_object* v_k_2761_; lean_object* v_v_2762_; lean_object* v_l_2763_; lean_object* v_r_2764_; lean_object* v___x_2765_; 
lean_dec(v_h__1_2758_);
v_size_2760_ = lean_ctor_get(v_x_2757_, 0);
lean_inc(v_size_2760_);
v_k_2761_ = lean_ctor_get(v_x_2757_, 1);
lean_inc(v_k_2761_);
v_v_2762_ = lean_ctor_get(v_x_2757_, 2);
lean_inc(v_v_2762_);
v_l_2763_ = lean_ctor_get(v_x_2757_, 3);
lean_inc(v_l_2763_);
v_r_2764_ = lean_ctor_get(v_x_2757_, 4);
lean_inc(v_r_2764_);
lean_dec_ref_known(v_x_2757_, 5);
v___x_2765_ = lean_apply_7(v_h__2_2759_, v_size_2760_, v_k_2761_, v_v_2762_, v_l_2763_, v_r_2764_, lean_box(0), lean_box(0));
return v___x_2765_;
}
else
{
lean_object* v___x_2766_; 
lean_dec(v_h__2_2759_);
v___x_2766_ = lean_apply_2(v_h__1_2758_, lean_box(0), lean_box(0));
return v___x_2766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(lean_object* v_00_u03b1_2767_, lean_object* v_00_u03b2_2768_, lean_object* v_inst_2769_, lean_object* v_k_2770_, lean_object* v_motive_2771_, lean_object* v_x_2772_, lean_object* v_x_2773_, lean_object* v_x_2774_, lean_object* v_h__1_2775_, lean_object* v_h__2_2776_){
_start:
{
if (lean_obj_tag(v_x_2772_) == 0)
{
lean_object* v_size_2777_; lean_object* v_k_2778_; lean_object* v_v_2779_; lean_object* v_l_2780_; lean_object* v_r_2781_; lean_object* v___x_2782_; 
lean_dec(v_h__1_2775_);
v_size_2777_ = lean_ctor_get(v_x_2772_, 0);
lean_inc(v_size_2777_);
v_k_2778_ = lean_ctor_get(v_x_2772_, 1);
lean_inc(v_k_2778_);
v_v_2779_ = lean_ctor_get(v_x_2772_, 2);
lean_inc(v_v_2779_);
v_l_2780_ = lean_ctor_get(v_x_2772_, 3);
lean_inc(v_l_2780_);
v_r_2781_ = lean_ctor_get(v_x_2772_, 4);
lean_inc(v_r_2781_);
lean_dec_ref_known(v_x_2772_, 5);
v___x_2782_ = lean_apply_7(v_h__2_2776_, v_size_2777_, v_k_2778_, v_v_2779_, v_l_2780_, v_r_2781_, lean_box(0), lean_box(0));
return v___x_2782_;
}
else
{
lean_object* v___x_2783_; 
lean_dec(v_h__2_2776_);
v___x_2783_ = lean_apply_2(v_h__1_2775_, lean_box(0), lean_box(0));
return v___x_2783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___boxed(lean_object* v_00_u03b1_2784_, lean_object* v_00_u03b2_2785_, lean_object* v_inst_2786_, lean_object* v_k_2787_, lean_object* v_motive_2788_, lean_object* v_x_2789_, lean_object* v_x_2790_, lean_object* v_x_2791_, lean_object* v_h__1_2792_, lean_object* v_h__2_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(v_00_u03b1_2784_, v_00_u03b2_2785_, v_inst_2786_, v_k_2787_, v_motive_2788_, v_x_2789_, v_x_2790_, v_x_2791_, v_h__1_2792_, v_h__2_2793_);
lean_dec(v_k_2787_);
lean_dec_ref(v_inst_2786_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___redArg(lean_object* v_x_2795_, lean_object* v_h__1_2796_, lean_object* v_h__2_2797_){
_start:
{
if (lean_obj_tag(v_x_2795_) == 0)
{
lean_object* v_size_2798_; lean_object* v_k_2799_; lean_object* v_v_2800_; lean_object* v_l_2801_; lean_object* v_r_2802_; lean_object* v___x_2803_; 
lean_dec(v_h__1_2796_);
v_size_2798_ = lean_ctor_get(v_x_2795_, 0);
lean_inc(v_size_2798_);
v_k_2799_ = lean_ctor_get(v_x_2795_, 1);
lean_inc(v_k_2799_);
v_v_2800_ = lean_ctor_get(v_x_2795_, 2);
lean_inc(v_v_2800_);
v_l_2801_ = lean_ctor_get(v_x_2795_, 3);
lean_inc(v_l_2801_);
v_r_2802_ = lean_ctor_get(v_x_2795_, 4);
lean_inc(v_r_2802_);
lean_dec_ref_known(v_x_2795_, 5);
v___x_2803_ = lean_apply_7(v_h__2_2797_, v_size_2798_, v_k_2799_, v_v_2800_, v_l_2801_, v_r_2802_, lean_box(0), lean_box(0));
return v___x_2803_;
}
else
{
lean_object* v___x_2804_; 
lean_dec(v_h__2_2797_);
v___x_2804_ = lean_apply_2(v_h__1_2796_, lean_box(0), lean_box(0));
return v___x_2804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(lean_object* v_00_u03b1_2805_, lean_object* v_00_u03b2_2806_, lean_object* v_inst_2807_, lean_object* v_k_2808_, lean_object* v_motive_2809_, lean_object* v_x_2810_, lean_object* v_x_2811_, lean_object* v_x_2812_, lean_object* v_h__1_2813_, lean_object* v_h__2_2814_){
_start:
{
if (lean_obj_tag(v_x_2810_) == 0)
{
lean_object* v_size_2815_; lean_object* v_k_2816_; lean_object* v_v_2817_; lean_object* v_l_2818_; lean_object* v_r_2819_; lean_object* v___x_2820_; 
lean_dec(v_h__1_2813_);
v_size_2815_ = lean_ctor_get(v_x_2810_, 0);
lean_inc(v_size_2815_);
v_k_2816_ = lean_ctor_get(v_x_2810_, 1);
lean_inc(v_k_2816_);
v_v_2817_ = lean_ctor_get(v_x_2810_, 2);
lean_inc(v_v_2817_);
v_l_2818_ = lean_ctor_get(v_x_2810_, 3);
lean_inc(v_l_2818_);
v_r_2819_ = lean_ctor_get(v_x_2810_, 4);
lean_inc(v_r_2819_);
lean_dec_ref_known(v_x_2810_, 5);
v___x_2820_ = lean_apply_7(v_h__2_2814_, v_size_2815_, v_k_2816_, v_v_2817_, v_l_2818_, v_r_2819_, lean_box(0), lean_box(0));
return v___x_2820_;
}
else
{
lean_object* v___x_2821_; 
lean_dec(v_h__2_2814_);
v___x_2821_ = lean_apply_2(v_h__1_2813_, lean_box(0), lean_box(0));
return v___x_2821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___boxed(lean_object* v_00_u03b1_2822_, lean_object* v_00_u03b2_2823_, lean_object* v_inst_2824_, lean_object* v_k_2825_, lean_object* v_motive_2826_, lean_object* v_x_2827_, lean_object* v_x_2828_, lean_object* v_x_2829_, lean_object* v_h__1_2830_, lean_object* v_h__2_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(v_00_u03b1_2822_, v_00_u03b2_2823_, v_inst_2824_, v_k_2825_, v_motive_2826_, v_x_2827_, v_x_2828_, v_x_2829_, v_h__1_2830_, v_h__2_2831_);
lean_dec(v_k_2825_);
lean_dec_ref(v_inst_2824_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(uint8_t v_x_2833_, lean_object* v_h__1_2834_, lean_object* v_h__2_2835_, lean_object* v_h__3_2836_){
_start:
{
switch(v_x_2833_)
{
case 0:
{
lean_object* v___x_2837_; 
lean_dec(v_h__2_2835_);
lean_dec(v_h__1_2834_);
v___x_2837_ = lean_apply_1(v_h__3_2836_, lean_box(0));
return v___x_2837_;
}
case 1:
{
lean_object* v___x_2838_; 
lean_dec(v_h__3_2836_);
lean_dec(v_h__1_2834_);
v___x_2838_ = lean_apply_1(v_h__2_2835_, lean_box(0));
return v___x_2838_;
}
default: 
{
lean_object* v___x_2839_; 
lean_dec(v_h__3_2836_);
lean_dec(v_h__2_2835_);
v___x_2839_ = lean_apply_1(v_h__1_2834_, lean_box(0));
return v___x_2839_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg___boxed(lean_object* v_x_2840_, lean_object* v_h__1_2841_, lean_object* v_h__2_2842_, lean_object* v_h__3_2843_){
_start:
{
uint8_t v_x_33__boxed_2844_; lean_object* v_res_2845_; 
v_x_33__boxed_2844_ = lean_unbox(v_x_2840_);
v_res_2845_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(v_x_33__boxed_2844_, v_h__1_2841_, v_h__2_2842_, v_h__3_2843_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(lean_object* v_motive_2846_, uint8_t v_x_2847_, lean_object* v_h__1_2848_, lean_object* v_h__2_2849_, lean_object* v_h__3_2850_){
_start:
{
switch(v_x_2847_)
{
case 0:
{
lean_object* v___x_2851_; 
lean_dec(v_h__2_2849_);
lean_dec(v_h__1_2848_);
v___x_2851_ = lean_apply_1(v_h__3_2850_, lean_box(0));
return v___x_2851_;
}
case 1:
{
lean_object* v___x_2852_; 
lean_dec(v_h__3_2850_);
lean_dec(v_h__1_2848_);
v___x_2852_ = lean_apply_1(v_h__2_2849_, lean_box(0));
return v___x_2852_;
}
default: 
{
lean_object* v___x_2853_; 
lean_dec(v_h__3_2850_);
lean_dec(v_h__2_2849_);
v___x_2853_ = lean_apply_1(v_h__1_2848_, lean_box(0));
return v___x_2853_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___boxed(lean_object* v_motive_2854_, lean_object* v_x_2855_, lean_object* v_h__1_2856_, lean_object* v_h__2_2857_, lean_object* v_h__3_2858_){
_start:
{
uint8_t v_x_42__boxed_2859_; lean_object* v_res_2860_; 
v_x_42__boxed_2859_ = lean_unbox(v_x_2855_);
v_res_2860_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(v_motive_2854_, v_x_42__boxed_2859_, v_h__1_2856_, v_h__2_2857_, v_h__3_2858_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___redArg(lean_object* v_x_2861_, lean_object* v_h__1_2862_, lean_object* v_h__2_2863_){
_start:
{
if (lean_obj_tag(v_x_2861_) == 0)
{
lean_object* v_size_2864_; lean_object* v_k_2865_; lean_object* v_v_2866_; lean_object* v_l_2867_; lean_object* v_r_2868_; lean_object* v___x_2869_; 
lean_dec(v_h__1_2862_);
v_size_2864_ = lean_ctor_get(v_x_2861_, 0);
lean_inc(v_size_2864_);
v_k_2865_ = lean_ctor_get(v_x_2861_, 1);
lean_inc(v_k_2865_);
v_v_2866_ = lean_ctor_get(v_x_2861_, 2);
lean_inc(v_v_2866_);
v_l_2867_ = lean_ctor_get(v_x_2861_, 3);
lean_inc(v_l_2867_);
v_r_2868_ = lean_ctor_get(v_x_2861_, 4);
lean_inc(v_r_2868_);
lean_dec_ref_known(v_x_2861_, 5);
v___x_2869_ = lean_apply_7(v_h__2_2863_, v_size_2864_, v_k_2865_, v_v_2866_, v_l_2867_, v_r_2868_, lean_box(0), lean_box(0));
return v___x_2869_;
}
else
{
lean_object* v___x_2870_; 
lean_dec(v_h__2_2863_);
v___x_2870_ = lean_apply_2(v_h__1_2862_, lean_box(0), lean_box(0));
return v___x_2870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(lean_object* v_00_u03b1_2871_, lean_object* v_00_u03b2_2872_, lean_object* v_inst_2873_, lean_object* v_k_2874_, lean_object* v_motive_2875_, lean_object* v_x_2876_, lean_object* v_x_2877_, lean_object* v_x_2878_, lean_object* v_h__1_2879_, lean_object* v_h__2_2880_){
_start:
{
if (lean_obj_tag(v_x_2876_) == 0)
{
lean_object* v_size_2881_; lean_object* v_k_2882_; lean_object* v_v_2883_; lean_object* v_l_2884_; lean_object* v_r_2885_; lean_object* v___x_2886_; 
lean_dec(v_h__1_2879_);
v_size_2881_ = lean_ctor_get(v_x_2876_, 0);
lean_inc(v_size_2881_);
v_k_2882_ = lean_ctor_get(v_x_2876_, 1);
lean_inc(v_k_2882_);
v_v_2883_ = lean_ctor_get(v_x_2876_, 2);
lean_inc(v_v_2883_);
v_l_2884_ = lean_ctor_get(v_x_2876_, 3);
lean_inc(v_l_2884_);
v_r_2885_ = lean_ctor_get(v_x_2876_, 4);
lean_inc(v_r_2885_);
lean_dec_ref_known(v_x_2876_, 5);
v___x_2886_ = lean_apply_7(v_h__2_2880_, v_size_2881_, v_k_2882_, v_v_2883_, v_l_2884_, v_r_2885_, lean_box(0), lean_box(0));
return v___x_2886_;
}
else
{
lean_object* v___x_2887_; 
lean_dec(v_h__2_2880_);
v___x_2887_ = lean_apply_2(v_h__1_2879_, lean_box(0), lean_box(0));
return v___x_2887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___boxed(lean_object* v_00_u03b1_2888_, lean_object* v_00_u03b2_2889_, lean_object* v_inst_2890_, lean_object* v_k_2891_, lean_object* v_motive_2892_, lean_object* v_x_2893_, lean_object* v_x_2894_, lean_object* v_x_2895_, lean_object* v_h__1_2896_, lean_object* v_h__2_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(v_00_u03b1_2888_, v_00_u03b2_2889_, v_inst_2890_, v_k_2891_, v_motive_2892_, v_x_2893_, v_x_2894_, v_x_2895_, v_h__1_2896_, v_h__2_2897_);
lean_dec(v_k_2891_);
lean_dec_ref(v_inst_2890_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(lean_object* v_x_2899_, lean_object* v_x_2900_, lean_object* v_h__1_2901_, lean_object* v_h__2_2902_){
_start:
{
if (lean_obj_tag(v_x_2899_) == 0)
{
lean_object* v_size_2903_; lean_object* v_k_2904_; lean_object* v_v_2905_; lean_object* v_l_2906_; lean_object* v_r_2907_; lean_object* v___x_2908_; 
lean_dec(v_h__1_2901_);
v_size_2903_ = lean_ctor_get(v_x_2899_, 0);
lean_inc(v_size_2903_);
v_k_2904_ = lean_ctor_get(v_x_2899_, 1);
lean_inc(v_k_2904_);
v_v_2905_ = lean_ctor_get(v_x_2899_, 2);
lean_inc(v_v_2905_);
v_l_2906_ = lean_ctor_get(v_x_2899_, 3);
lean_inc(v_l_2906_);
v_r_2907_ = lean_ctor_get(v_x_2899_, 4);
lean_inc(v_r_2907_);
lean_dec_ref_known(v_x_2899_, 5);
v___x_2908_ = lean_apply_6(v_h__2_2902_, v_size_2903_, v_k_2904_, v_v_2905_, v_l_2906_, v_r_2907_, v_x_2900_);
return v___x_2908_;
}
else
{
lean_object* v___x_2909_; 
lean_dec(v_h__2_2902_);
v___x_2909_ = lean_apply_1(v_h__1_2901_, v_x_2900_);
return v___x_2909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter(lean_object* v_00_u03b1_2910_, lean_object* v_00_u03b2_2911_, lean_object* v_motive_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_, lean_object* v_h__1_2915_, lean_object* v_h__2_2916_){
_start:
{
if (lean_obj_tag(v_x_2913_) == 0)
{
lean_object* v_size_2917_; lean_object* v_k_2918_; lean_object* v_v_2919_; lean_object* v_l_2920_; lean_object* v_r_2921_; lean_object* v___x_2922_; 
lean_dec(v_h__1_2915_);
v_size_2917_ = lean_ctor_get(v_x_2913_, 0);
lean_inc(v_size_2917_);
v_k_2918_ = lean_ctor_get(v_x_2913_, 1);
lean_inc(v_k_2918_);
v_v_2919_ = lean_ctor_get(v_x_2913_, 2);
lean_inc(v_v_2919_);
v_l_2920_ = lean_ctor_get(v_x_2913_, 3);
lean_inc(v_l_2920_);
v_r_2921_ = lean_ctor_get(v_x_2913_, 4);
lean_inc(v_r_2921_);
lean_dec_ref_known(v_x_2913_, 5);
v___x_2922_ = lean_apply_6(v_h__2_2916_, v_size_2917_, v_k_2918_, v_v_2919_, v_l_2920_, v_r_2921_, v_x_2914_);
return v___x_2922_;
}
else
{
lean_object* v___x_2923_; 
lean_dec(v_h__2_2916_);
v___x_2923_ = lean_apply_1(v_h__1_2915_, v_x_2914_);
return v___x_2923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(lean_object* v_x_2924_, lean_object* v_x_2925_, lean_object* v_h__1_2926_){
_start:
{
lean_object* v_size_2927_; lean_object* v_k_2928_; lean_object* v_v_2929_; lean_object* v_l_2930_; lean_object* v_r_2931_; lean_object* v___x_2932_; 
v_size_2927_ = lean_ctor_get(v_x_2924_, 0);
lean_inc(v_size_2927_);
v_k_2928_ = lean_ctor_get(v_x_2924_, 1);
lean_inc(v_k_2928_);
v_v_2929_ = lean_ctor_get(v_x_2924_, 2);
lean_inc(v_v_2929_);
v_l_2930_ = lean_ctor_get(v_x_2924_, 3);
lean_inc(v_l_2930_);
v_r_2931_ = lean_ctor_get(v_x_2924_, 4);
lean_inc(v_r_2931_);
lean_dec(v_x_2924_);
v___x_2932_ = lean_apply_8(v_h__1_2926_, v_size_2927_, v_k_2928_, v_v_2929_, v_l_2930_, v_r_2931_, lean_box(0), v_x_2925_, lean_box(0));
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter(lean_object* v_00_u03b1_2933_, lean_object* v_00_u03b2_2934_, lean_object* v_motive_2935_, lean_object* v_x_2936_, lean_object* v_x_2937_, lean_object* v_x_2938_, lean_object* v_x_2939_, lean_object* v_h__1_2940_){
_start:
{
lean_object* v_size_2941_; lean_object* v_k_2942_; lean_object* v_v_2943_; lean_object* v_l_2944_; lean_object* v_r_2945_; lean_object* v___x_2946_; 
v_size_2941_ = lean_ctor_get(v_x_2936_, 0);
lean_inc(v_size_2941_);
v_k_2942_ = lean_ctor_get(v_x_2936_, 1);
lean_inc(v_k_2942_);
v_v_2943_ = lean_ctor_get(v_x_2936_, 2);
lean_inc(v_v_2943_);
v_l_2944_ = lean_ctor_get(v_x_2936_, 3);
lean_inc(v_l_2944_);
v_r_2945_ = lean_ctor_get(v_x_2936_, 4);
lean_inc(v_r_2945_);
lean_dec(v_x_2936_);
v___x_2946_ = lean_apply_8(v_h__1_2940_, v_size_2941_, v_k_2942_, v_v_2943_, v_l_2944_, v_r_2945_, lean_box(0), v_x_2938_, lean_box(0));
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter___redArg(lean_object* v_x_2947_, lean_object* v_x_2948_, lean_object* v_x_2949_, lean_object* v_h__1_2950_, lean_object* v_h__2_2951_){
_start:
{
if (lean_obj_tag(v_x_2947_) == 0)
{
lean_object* v_size_2952_; lean_object* v_k_2953_; lean_object* v_v_2954_; lean_object* v_l_2955_; lean_object* v_r_2956_; lean_object* v___x_2957_; 
lean_dec(v_h__1_2950_);
v_size_2952_ = lean_ctor_get(v_x_2947_, 0);
lean_inc(v_size_2952_);
v_k_2953_ = lean_ctor_get(v_x_2947_, 1);
lean_inc(v_k_2953_);
v_v_2954_ = lean_ctor_get(v_x_2947_, 2);
lean_inc(v_v_2954_);
v_l_2955_ = lean_ctor_get(v_x_2947_, 3);
lean_inc(v_l_2955_);
v_r_2956_ = lean_ctor_get(v_x_2947_, 4);
lean_inc(v_r_2956_);
lean_dec_ref_known(v_x_2947_, 5);
v___x_2957_ = lean_apply_7(v_h__2_2951_, v_size_2952_, v_k_2953_, v_v_2954_, v_l_2955_, v_r_2956_, v_x_2948_, v_x_2949_);
return v___x_2957_;
}
else
{
lean_object* v___x_2958_; 
lean_dec(v_h__2_2951_);
v___x_2958_ = lean_apply_2(v_h__1_2950_, v_x_2948_, v_x_2949_);
return v___x_2958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2959_, lean_object* v_00_u03b2_2960_, lean_object* v_motive_2961_, lean_object* v_x_2962_, lean_object* v_x_2963_, lean_object* v_x_2964_, lean_object* v_h__1_2965_, lean_object* v_h__2_2966_){
_start:
{
if (lean_obj_tag(v_x_2962_) == 0)
{
lean_object* v_size_2967_; lean_object* v_k_2968_; lean_object* v_v_2969_; lean_object* v_l_2970_; lean_object* v_r_2971_; lean_object* v___x_2972_; 
lean_dec(v_h__1_2965_);
v_size_2967_ = lean_ctor_get(v_x_2962_, 0);
lean_inc(v_size_2967_);
v_k_2968_ = lean_ctor_get(v_x_2962_, 1);
lean_inc(v_k_2968_);
v_v_2969_ = lean_ctor_get(v_x_2962_, 2);
lean_inc(v_v_2969_);
v_l_2970_ = lean_ctor_get(v_x_2962_, 3);
lean_inc(v_l_2970_);
v_r_2971_ = lean_ctor_get(v_x_2962_, 4);
lean_inc(v_r_2971_);
lean_dec_ref_known(v_x_2962_, 5);
v___x_2972_ = lean_apply_7(v_h__2_2966_, v_size_2967_, v_k_2968_, v_v_2969_, v_l_2970_, v_r_2971_, v_x_2963_, v_x_2964_);
return v___x_2972_;
}
else
{
lean_object* v___x_2973_; 
lean_dec(v_h__2_2966_);
v___x_2973_ = lean_apply_2(v_h__1_2965_, v_x_2963_, v_x_2964_);
return v___x_2973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___redArg(lean_object* v_x_2974_, lean_object* v_h__1_2975_, lean_object* v_h__2_2976_){
_start:
{
if (lean_obj_tag(v_x_2974_) == 0)
{
lean_object* v_size_2977_; lean_object* v_k_2978_; lean_object* v_v_2979_; lean_object* v_l_2980_; lean_object* v_r_2981_; lean_object* v___x_2982_; 
lean_dec(v_h__1_2975_);
v_size_2977_ = lean_ctor_get(v_x_2974_, 0);
lean_inc(v_size_2977_);
v_k_2978_ = lean_ctor_get(v_x_2974_, 1);
lean_inc(v_k_2978_);
v_v_2979_ = lean_ctor_get(v_x_2974_, 2);
lean_inc(v_v_2979_);
v_l_2980_ = lean_ctor_get(v_x_2974_, 3);
lean_inc(v_l_2980_);
v_r_2981_ = lean_ctor_get(v_x_2974_, 4);
lean_inc(v_r_2981_);
lean_dec_ref_known(v_x_2974_, 5);
v___x_2982_ = lean_apply_7(v_h__2_2976_, v_size_2977_, v_k_2978_, v_v_2979_, v_l_2980_, v_r_2981_, lean_box(0), lean_box(0));
return v___x_2982_;
}
else
{
lean_object* v___x_2983_; 
lean_dec(v_h__2_2976_);
v___x_2983_ = lean_apply_2(v_h__1_2975_, lean_box(0), lean_box(0));
return v___x_2983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(lean_object* v_00_u03b1_2984_, lean_object* v_00_u03b2_2985_, lean_object* v_inst_2986_, lean_object* v_k_2987_, lean_object* v_motive_2988_, lean_object* v_x_2989_, lean_object* v_x_2990_, lean_object* v_x_2991_, lean_object* v_h__1_2992_, lean_object* v_h__2_2993_){
_start:
{
if (lean_obj_tag(v_x_2989_) == 0)
{
lean_object* v_size_2994_; lean_object* v_k_2995_; lean_object* v_v_2996_; lean_object* v_l_2997_; lean_object* v_r_2998_; lean_object* v___x_2999_; 
lean_dec(v_h__1_2992_);
v_size_2994_ = lean_ctor_get(v_x_2989_, 0);
lean_inc(v_size_2994_);
v_k_2995_ = lean_ctor_get(v_x_2989_, 1);
lean_inc(v_k_2995_);
v_v_2996_ = lean_ctor_get(v_x_2989_, 2);
lean_inc(v_v_2996_);
v_l_2997_ = lean_ctor_get(v_x_2989_, 3);
lean_inc(v_l_2997_);
v_r_2998_ = lean_ctor_get(v_x_2989_, 4);
lean_inc(v_r_2998_);
lean_dec_ref_known(v_x_2989_, 5);
v___x_2999_ = lean_apply_7(v_h__2_2993_, v_size_2994_, v_k_2995_, v_v_2996_, v_l_2997_, v_r_2998_, lean_box(0), lean_box(0));
return v___x_2999_;
}
else
{
lean_object* v___x_3000_; 
lean_dec(v_h__2_2993_);
v___x_3000_ = lean_apply_2(v_h__1_2992_, lean_box(0), lean_box(0));
return v___x_3000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___boxed(lean_object* v_00_u03b1_3001_, lean_object* v_00_u03b2_3002_, lean_object* v_inst_3003_, lean_object* v_k_3004_, lean_object* v_motive_3005_, lean_object* v_x_3006_, lean_object* v_x_3007_, lean_object* v_x_3008_, lean_object* v_h__1_3009_, lean_object* v_h__2_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(v_00_u03b1_3001_, v_00_u03b2_3002_, v_inst_3003_, v_k_3004_, v_motive_3005_, v_x_3006_, v_x_3007_, v_x_3008_, v_h__1_3009_, v_h__2_3010_);
lean_dec(v_k_3004_);
lean_dec_ref(v_inst_3003_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___redArg(lean_object* v_x_3012_, lean_object* v_h__1_3013_, lean_object* v_h__2_3014_){
_start:
{
if (lean_obj_tag(v_x_3012_) == 0)
{
lean_object* v_size_3015_; lean_object* v_k_3016_; lean_object* v_v_3017_; lean_object* v_l_3018_; lean_object* v_r_3019_; lean_object* v___x_3020_; 
lean_dec(v_h__1_3013_);
v_size_3015_ = lean_ctor_get(v_x_3012_, 0);
lean_inc(v_size_3015_);
v_k_3016_ = lean_ctor_get(v_x_3012_, 1);
lean_inc(v_k_3016_);
v_v_3017_ = lean_ctor_get(v_x_3012_, 2);
lean_inc(v_v_3017_);
v_l_3018_ = lean_ctor_get(v_x_3012_, 3);
lean_inc(v_l_3018_);
v_r_3019_ = lean_ctor_get(v_x_3012_, 4);
lean_inc(v_r_3019_);
lean_dec_ref_known(v_x_3012_, 5);
v___x_3020_ = lean_apply_7(v_h__2_3014_, v_size_3015_, v_k_3016_, v_v_3017_, v_l_3018_, v_r_3019_, lean_box(0), lean_box(0));
return v___x_3020_;
}
else
{
lean_object* v___x_3021_; 
lean_dec(v_h__2_3014_);
v___x_3021_ = lean_apply_2(v_h__1_3013_, lean_box(0), lean_box(0));
return v___x_3021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(lean_object* v_00_u03b1_3022_, lean_object* v_00_u03b2_3023_, lean_object* v_inst_3024_, lean_object* v_k_3025_, lean_object* v_motive_3026_, lean_object* v_x_3027_, lean_object* v_x_3028_, lean_object* v_x_3029_, lean_object* v_h__1_3030_, lean_object* v_h__2_3031_){
_start:
{
if (lean_obj_tag(v_x_3027_) == 0)
{
lean_object* v_size_3032_; lean_object* v_k_3033_; lean_object* v_v_3034_; lean_object* v_l_3035_; lean_object* v_r_3036_; lean_object* v___x_3037_; 
lean_dec(v_h__1_3030_);
v_size_3032_ = lean_ctor_get(v_x_3027_, 0);
lean_inc(v_size_3032_);
v_k_3033_ = lean_ctor_get(v_x_3027_, 1);
lean_inc(v_k_3033_);
v_v_3034_ = lean_ctor_get(v_x_3027_, 2);
lean_inc(v_v_3034_);
v_l_3035_ = lean_ctor_get(v_x_3027_, 3);
lean_inc(v_l_3035_);
v_r_3036_ = lean_ctor_get(v_x_3027_, 4);
lean_inc(v_r_3036_);
lean_dec_ref_known(v_x_3027_, 5);
v___x_3037_ = lean_apply_7(v_h__2_3031_, v_size_3032_, v_k_3033_, v_v_3034_, v_l_3035_, v_r_3036_, lean_box(0), lean_box(0));
return v___x_3037_;
}
else
{
lean_object* v___x_3038_; 
lean_dec(v_h__2_3031_);
v___x_3038_ = lean_apply_2(v_h__1_3030_, lean_box(0), lean_box(0));
return v___x_3038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___boxed(lean_object* v_00_u03b1_3039_, lean_object* v_00_u03b2_3040_, lean_object* v_inst_3041_, lean_object* v_k_3042_, lean_object* v_motive_3043_, lean_object* v_x_3044_, lean_object* v_x_3045_, lean_object* v_x_3046_, lean_object* v_h__1_3047_, lean_object* v_h__2_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(v_00_u03b1_3039_, v_00_u03b2_3040_, v_inst_3041_, v_k_3042_, v_motive_3043_, v_x_3044_, v_x_3045_, v_x_3046_, v_h__1_3047_, v_h__2_3048_);
lean_dec(v_k_3042_);
lean_dec_ref(v_inst_3041_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___redArg(lean_object* v_x_3050_, lean_object* v_h__1_3051_, lean_object* v_h__2_3052_){
_start:
{
if (lean_obj_tag(v_x_3050_) == 0)
{
lean_object* v_size_3053_; lean_object* v_k_3054_; lean_object* v_v_3055_; lean_object* v_l_3056_; lean_object* v_r_3057_; lean_object* v___x_3058_; 
lean_dec(v_h__1_3051_);
v_size_3053_ = lean_ctor_get(v_x_3050_, 0);
lean_inc(v_size_3053_);
v_k_3054_ = lean_ctor_get(v_x_3050_, 1);
lean_inc(v_k_3054_);
v_v_3055_ = lean_ctor_get(v_x_3050_, 2);
lean_inc(v_v_3055_);
v_l_3056_ = lean_ctor_get(v_x_3050_, 3);
lean_inc(v_l_3056_);
v_r_3057_ = lean_ctor_get(v_x_3050_, 4);
lean_inc(v_r_3057_);
lean_dec_ref_known(v_x_3050_, 5);
v___x_3058_ = lean_apply_7(v_h__2_3052_, v_size_3053_, v_k_3054_, v_v_3055_, v_l_3056_, v_r_3057_, lean_box(0), lean_box(0));
return v___x_3058_;
}
else
{
lean_object* v___x_3059_; 
lean_dec(v_h__2_3052_);
v___x_3059_ = lean_apply_2(v_h__1_3051_, lean_box(0), lean_box(0));
return v___x_3059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(lean_object* v_00_u03b1_3060_, lean_object* v_00_u03b2_3061_, lean_object* v_inst_3062_, lean_object* v_k_3063_, lean_object* v_motive_3064_, lean_object* v_x_3065_, lean_object* v_x_3066_, lean_object* v_x_3067_, lean_object* v_h__1_3068_, lean_object* v_h__2_3069_){
_start:
{
if (lean_obj_tag(v_x_3065_) == 0)
{
lean_object* v_size_3070_; lean_object* v_k_3071_; lean_object* v_v_3072_; lean_object* v_l_3073_; lean_object* v_r_3074_; lean_object* v___x_3075_; 
lean_dec(v_h__1_3068_);
v_size_3070_ = lean_ctor_get(v_x_3065_, 0);
lean_inc(v_size_3070_);
v_k_3071_ = lean_ctor_get(v_x_3065_, 1);
lean_inc(v_k_3071_);
v_v_3072_ = lean_ctor_get(v_x_3065_, 2);
lean_inc(v_v_3072_);
v_l_3073_ = lean_ctor_get(v_x_3065_, 3);
lean_inc(v_l_3073_);
v_r_3074_ = lean_ctor_get(v_x_3065_, 4);
lean_inc(v_r_3074_);
lean_dec_ref_known(v_x_3065_, 5);
v___x_3075_ = lean_apply_7(v_h__2_3069_, v_size_3070_, v_k_3071_, v_v_3072_, v_l_3073_, v_r_3074_, lean_box(0), lean_box(0));
return v___x_3075_;
}
else
{
lean_object* v___x_3076_; 
lean_dec(v_h__2_3069_);
v___x_3076_ = lean_apply_2(v_h__1_3068_, lean_box(0), lean_box(0));
return v___x_3076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___boxed(lean_object* v_00_u03b1_3077_, lean_object* v_00_u03b2_3078_, lean_object* v_inst_3079_, lean_object* v_k_3080_, lean_object* v_motive_3081_, lean_object* v_x_3082_, lean_object* v_x_3083_, lean_object* v_x_3084_, lean_object* v_h__1_3085_, lean_object* v_h__2_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(v_00_u03b1_3077_, v_00_u03b2_3078_, v_inst_3079_, v_k_3080_, v_motive_3081_, v_x_3082_, v_x_3083_, v_x_3084_, v_h__1_3085_, v_h__2_3086_);
lean_dec(v_k_3080_);
lean_dec_ref(v_inst_3079_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___redArg(lean_object* v_x_3088_, lean_object* v_h__1_3089_, lean_object* v_h__2_3090_){
_start:
{
if (lean_obj_tag(v_x_3088_) == 0)
{
lean_object* v_size_3091_; lean_object* v_k_3092_; lean_object* v_v_3093_; lean_object* v_l_3094_; lean_object* v_r_3095_; lean_object* v___x_3096_; 
lean_dec(v_h__1_3089_);
v_size_3091_ = lean_ctor_get(v_x_3088_, 0);
lean_inc(v_size_3091_);
v_k_3092_ = lean_ctor_get(v_x_3088_, 1);
lean_inc(v_k_3092_);
v_v_3093_ = lean_ctor_get(v_x_3088_, 2);
lean_inc(v_v_3093_);
v_l_3094_ = lean_ctor_get(v_x_3088_, 3);
lean_inc(v_l_3094_);
v_r_3095_ = lean_ctor_get(v_x_3088_, 4);
lean_inc(v_r_3095_);
lean_dec_ref_known(v_x_3088_, 5);
v___x_3096_ = lean_apply_7(v_h__2_3090_, v_size_3091_, v_k_3092_, v_v_3093_, v_l_3094_, v_r_3095_, lean_box(0), lean_box(0));
return v___x_3096_;
}
else
{
lean_object* v___x_3097_; 
lean_dec(v_h__2_3090_);
v___x_3097_ = lean_apply_2(v_h__1_3089_, lean_box(0), lean_box(0));
return v___x_3097_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(lean_object* v_00_u03b1_3098_, lean_object* v_00_u03b2_3099_, lean_object* v_inst_3100_, lean_object* v_k_3101_, lean_object* v_motive_3102_, lean_object* v_x_3103_, lean_object* v_x_3104_, lean_object* v_x_3105_, lean_object* v_h__1_3106_, lean_object* v_h__2_3107_){
_start:
{
if (lean_obj_tag(v_x_3103_) == 0)
{
lean_object* v_size_3108_; lean_object* v_k_3109_; lean_object* v_v_3110_; lean_object* v_l_3111_; lean_object* v_r_3112_; lean_object* v___x_3113_; 
lean_dec(v_h__1_3106_);
v_size_3108_ = lean_ctor_get(v_x_3103_, 0);
lean_inc(v_size_3108_);
v_k_3109_ = lean_ctor_get(v_x_3103_, 1);
lean_inc(v_k_3109_);
v_v_3110_ = lean_ctor_get(v_x_3103_, 2);
lean_inc(v_v_3110_);
v_l_3111_ = lean_ctor_get(v_x_3103_, 3);
lean_inc(v_l_3111_);
v_r_3112_ = lean_ctor_get(v_x_3103_, 4);
lean_inc(v_r_3112_);
lean_dec_ref_known(v_x_3103_, 5);
v___x_3113_ = lean_apply_7(v_h__2_3107_, v_size_3108_, v_k_3109_, v_v_3110_, v_l_3111_, v_r_3112_, lean_box(0), lean_box(0));
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; 
lean_dec(v_h__2_3107_);
v___x_3114_ = lean_apply_2(v_h__1_3106_, lean_box(0), lean_box(0));
return v___x_3114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___boxed(lean_object* v_00_u03b1_3115_, lean_object* v_00_u03b2_3116_, lean_object* v_inst_3117_, lean_object* v_k_3118_, lean_object* v_motive_3119_, lean_object* v_x_3120_, lean_object* v_x_3121_, lean_object* v_x_3122_, lean_object* v_h__1_3123_, lean_object* v_h__2_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(v_00_u03b1_3115_, v_00_u03b2_3116_, v_inst_3117_, v_k_3118_, v_motive_3119_, v_x_3120_, v_x_3121_, v_x_3122_, v_h__1_3123_, v_h__2_3124_);
lean_dec(v_k_3118_);
lean_dec_ref(v_inst_3117_);
return v_res_3125_;
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
