// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Model
// Imports: public import Std.Data.DTreeMap.Internal.WF.Defs public import Std.Data.DTreeMap.Internal.Cell import Init.Data.Nat.Linear import Init.Omega
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_l_2_);
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
lean_dec_ref(v_l_29_);
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
lean_dec_ref(v_l_43_);
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
uint8_t v_x_36__boxed_68_; lean_object* v_res_69_; 
v_x_36__boxed_68_ = lean_unbox(v_x_64_);
v_res_69_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_36__boxed_68_, v_h__1_65_, v_h__2_66_, v_h__3_67_);
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
uint8_t v_x_51__boxed_86_; lean_object* v_res_87_; 
v_x_51__boxed_86_ = lean_unbox(v_x_82_);
v_res_87_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_81_, v_x_51__boxed_86_, v_h__1_83_, v_h__2_84_, v_h__3_85_);
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
uint8_t v_x_36__boxed_102_; lean_object* v_res_103_; 
v_x_36__boxed_102_ = lean_unbox(v_x_98_);
v_res_103_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_36__boxed_102_, v_h__1_99_, v_h__2_100_, v_h__3_101_);
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
uint8_t v_x_51__boxed_120_; lean_object* v_res_121_; 
v_x_51__boxed_120_ = lean_unbox(v_x_116_);
v_res_121_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_115_, v_x_51__boxed_120_, v_h__1_117_, v_h__2_118_, v_h__3_119_);
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
lean_dec_ref(v_m_125_);
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
lean_dec_ref(v_l_204_);
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
lean_dec_ref(v_l_228_);
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
lean_dec_ref(v_l_245_);
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
lean_dec_ref(v_m_295_);
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
lean_dec_ref(v_m_311_);
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
lean_dec_ref(v_t_351_);
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
lean_dec_ref(v_t_351_);
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
lean_dec_ref(v_t_351_);
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
lean_dec_ref(v_l_454_);
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(lean_object* v_inst_502_, lean_object* v_l_503_, lean_object* v_k_504_){
_start:
{
lean_object* v___f_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___f_505_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0));
v___x_506_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_502_, v_k_504_, v_l_503_, v___f_505_);
v___x_507_ = lean_unbox(v___x_506_);
lean_dec(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___boxed(lean_object* v_inst_508_, lean_object* v_l_509_, lean_object* v_k_510_){
_start:
{
uint8_t v_res_511_; lean_object* v_r_512_; 
v_res_511_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(v_inst_508_, v_l_509_, v_k_510_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098(lean_object* v_00_u03b1_513_, lean_object* v_00_u03b2_514_, lean_object* v_inst_515_, lean_object* v_l_516_, lean_object* v_k_517_){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(v_inst_515_, v_l_516_, v_k_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___boxed(lean_object* v_00_u03b1_519_, lean_object* v_00_u03b2_520_, lean_object* v_inst_521_, lean_object* v_l_522_, lean_object* v_k_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l_Std_DTreeMap_Internal_Impl_contains_u2098(v_00_u03b1_519_, v_00_u03b2_520_, v_inst_521_, v_l_522_, v_k_523_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0(lean_object* v_c_526_, lean_object* v_x_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(v_c_526_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(lean_object* v_inst_530_, lean_object* v_l_531_, lean_object* v_k_532_){
_start:
{
lean_object* v___f_533_; lean_object* v___x_534_; 
v___f_533_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0));
v___x_534_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_530_, v_k_532_, v_l_531_, v___f_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098(lean_object* v_00_u03b1_535_, lean_object* v_00_u03b2_536_, lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_l_540_, lean_object* v_k_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_537_, v_l_540_, v_k_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(lean_object* v_inst_543_, lean_object* v_l_544_, lean_object* v_k_545_){
_start:
{
lean_object* v___x_546_; lean_object* v_val_547_; 
v___x_546_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_543_, v_l_544_, v_k_545_);
v_val_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_val_547_);
lean_dec(v___x_546_);
return v_val_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098(lean_object* v_00_u03b1_548_, lean_object* v_00_u03b2_549_, lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_inst_552_, lean_object* v_l_553_, lean_object* v_k_554_, lean_object* v_h_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(v_inst_550_, v_l_553_, v_k_554_);
return v___x_556_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_560_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2));
v___x_561_ = lean_unsigned_to_nat(14u);
v___x_562_ = lean_unsigned_to_nat(22u);
v___x_563_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1));
v___x_564_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0));
v___x_565_ = l_mkPanicMessageWithDecl(v___x_564_, v___x_563_, v___x_562_, v___x_561_, v___x_560_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(lean_object* v_inst_566_, lean_object* v_l_567_, lean_object* v_k_568_, lean_object* v_inst_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_566_, v_l_567_, v_k_568_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_572_ = l_panic___redArg(v_inst_569_, v___x_571_);
return v___x_572_;
}
else
{
lean_object* v_val_573_; 
v_val_573_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_val_573_);
lean_dec_ref(v___x_570_);
return v_val_573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___boxed(lean_object* v_inst_574_, lean_object* v_l_575_, lean_object* v_k_576_, lean_object* v_inst_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(v_inst_574_, v_l_575_, v_k_576_, v_inst_577_);
lean_dec(v_inst_577_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098(lean_object* v_00_u03b1_579_, lean_object* v_00_u03b2_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_l_584_, lean_object* v_k_585_, lean_object* v_inst_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(v_inst_581_, v_l_584_, v_k_585_, v_inst_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___boxed(lean_object* v_00_u03b1_588_, lean_object* v_00_u03b2_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_l_593_, lean_object* v_k_594_, lean_object* v_inst_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098(v_00_u03b1_588_, v_00_u03b2_589_, v_inst_590_, v_inst_591_, v_inst_592_, v_l_593_, v_k_594_, v_inst_595_);
lean_dec(v_inst_595_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(lean_object* v_inst_597_, lean_object* v_k_598_, lean_object* v_l_599_, lean_object* v_fallback_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_597_, v_l_599_, v_k_598_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_inc(v_fallback_600_);
return v_fallback_600_;
}
else
{
lean_object* v_val_602_; 
v_val_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_val_602_);
lean_dec_ref(v___x_601_);
return v_val_602_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg___boxed(lean_object* v_inst_603_, lean_object* v_k_604_, lean_object* v_l_605_, lean_object* v_fallback_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(v_inst_603_, v_k_604_, v_l_605_, v_fallback_606_);
lean_dec(v_fallback_606_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b2_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_k_613_, lean_object* v_l_614_, lean_object* v_fallback_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(v_inst_610_, v_k_613_, v_l_614_, v_fallback_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___boxed(lean_object* v_00_u03b1_617_, lean_object* v_00_u03b2_618_, lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_k_622_, lean_object* v_l_623_, lean_object* v_fallback_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Std_DTreeMap_Internal_Impl_getD_u2098(v_00_u03b1_617_, v_00_u03b2_618_, v_inst_619_, v_inst_620_, v_inst_621_, v_k_622_, v_l_623_, v_fallback_624_);
lean_dec(v_fallback_624_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___lam__0(lean_object* v_c_626_, lean_object* v_x_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(v_c_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(lean_object* v_inst_630_, lean_object* v_l_631_, lean_object* v_k_632_){
_start:
{
lean_object* v___f_633_; lean_object* v___x_634_; 
v___f_633_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0));
v___x_634_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_630_, v_k_632_, v_l_631_, v___f_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098(lean_object* v_00_u03b1_635_, lean_object* v_00_u03b2_636_, lean_object* v_inst_637_, lean_object* v_l_638_, lean_object* v_k_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_637_, v_l_638_, v_k_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(lean_object* v_inst_641_, lean_object* v_l_642_, lean_object* v_k_643_){
_start:
{
lean_object* v___x_644_; lean_object* v_val_645_; 
v___x_644_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_641_, v_l_642_, v_k_643_);
v_val_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_val_645_);
lean_dec(v___x_644_);
return v_val_645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098(lean_object* v_00_u03b1_646_, lean_object* v_00_u03b2_647_, lean_object* v_inst_648_, lean_object* v_l_649_, lean_object* v_k_650_, lean_object* v_h_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(v_inst_648_, v_l_649_, v_k_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_l_655_, lean_object* v_k_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_653_, v_l_655_, v_k_656_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_659_ = l_panic___redArg(v_inst_654_, v___x_658_);
return v___x_659_;
}
else
{
lean_object* v_val_660_; 
v_val_660_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_val_660_);
lean_dec_ref(v___x_657_);
return v_val_660_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg___boxed(lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_l_663_, lean_object* v_k_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(v_inst_661_, v_inst_662_, v_l_663_, v_k_664_);
lean_dec_ref(v_inst_662_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(lean_object* v_00_u03b1_666_, lean_object* v_00_u03b2_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_l_670_, lean_object* v_k_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(v_inst_668_, v_inst_669_, v_l_670_, v_k_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___boxed(lean_object* v_00_u03b1_673_, lean_object* v_00_u03b2_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_l_677_, lean_object* v_k_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(v_00_u03b1_673_, v_00_u03b2_674_, v_inst_675_, v_inst_676_, v_l_677_, v_k_678_);
lean_dec_ref(v_inst_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(lean_object* v_inst_680_, lean_object* v_k_681_, lean_object* v_l_682_, lean_object* v_fallback_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_680_, v_l_682_, v_k_681_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_inc_ref(v_fallback_683_);
return v_fallback_683_;
}
else
{
lean_object* v_val_685_; 
v_val_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_val_685_);
lean_dec_ref(v___x_684_);
return v_val_685_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg___boxed(lean_object* v_inst_686_, lean_object* v_k_687_, lean_object* v_l_688_, lean_object* v_fallback_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(v_inst_686_, v_k_687_, v_l_688_, v_fallback_689_);
lean_dec_ref(v_fallback_689_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(lean_object* v_00_u03b1_691_, lean_object* v_00_u03b2_692_, lean_object* v_inst_693_, lean_object* v_k_694_, lean_object* v_l_695_, lean_object* v_fallback_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(v_inst_693_, v_k_694_, v_l_695_, v_fallback_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___boxed(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_inst_700_, lean_object* v_k_701_, lean_object* v_l_702_, lean_object* v_fallback_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(v_00_u03b1_698_, v_00_u03b2_699_, v_inst_700_, v_k_701_, v_l_702_, v_fallback_703_);
lean_dec_ref(v_fallback_703_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0(lean_object* v_c_705_, lean_object* v_x_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(v_c_705_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(lean_object* v_inst_709_, lean_object* v_l_710_, lean_object* v_k_711_){
_start:
{
lean_object* v___f_712_; lean_object* v___x_713_; 
v___f_712_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0));
v___x_713_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_709_, v_k_711_, v_l_710_, v___f_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098(lean_object* v_00_u03b1_714_, lean_object* v_00_u03b2_715_, lean_object* v_inst_716_, lean_object* v_l_717_, lean_object* v_k_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_716_, v_l_717_, v_k_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(lean_object* v_inst_720_, lean_object* v_l_721_, lean_object* v_k_722_){
_start:
{
lean_object* v___x_723_; lean_object* v_val_724_; 
v___x_723_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_720_, v_l_721_, v_k_722_);
v_val_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_val_724_);
lean_dec(v___x_723_);
return v_val_724_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098(lean_object* v_00_u03b1_725_, lean_object* v_00_u03b2_726_, lean_object* v_inst_727_, lean_object* v_l_728_, lean_object* v_k_729_, lean_object* v_h_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(v_inst_727_, v_l_728_, v_k_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(lean_object* v_inst_732_, lean_object* v_l_733_, lean_object* v_k_734_, lean_object* v_inst_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_732_, v_l_733_, v_k_734_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_738_ = l_panic___redArg(v_inst_735_, v___x_737_);
return v___x_738_;
}
else
{
lean_object* v_val_739_; 
v_val_739_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_val_739_);
lean_dec_ref(v___x_736_);
return v_val_739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg___boxed(lean_object* v_inst_740_, lean_object* v_l_741_, lean_object* v_k_742_, lean_object* v_inst_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(v_inst_740_, v_l_741_, v_k_742_, v_inst_743_);
lean_dec(v_inst_743_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(lean_object* v_00_u03b1_745_, lean_object* v_00_u03b2_746_, lean_object* v_inst_747_, lean_object* v_l_748_, lean_object* v_k_749_, lean_object* v_inst_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(v_inst_747_, v_l_748_, v_k_749_, v_inst_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___boxed(lean_object* v_00_u03b1_752_, lean_object* v_00_u03b2_753_, lean_object* v_inst_754_, lean_object* v_l_755_, lean_object* v_k_756_, lean_object* v_inst_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(v_00_u03b1_752_, v_00_u03b2_753_, v_inst_754_, v_l_755_, v_k_756_, v_inst_757_);
lean_dec(v_inst_757_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(lean_object* v_inst_759_, lean_object* v_k_760_, lean_object* v_l_761_, lean_object* v_fallback_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_759_, v_l_761_, v_k_760_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_inc(v_fallback_762_);
return v_fallback_762_;
}
else
{
lean_object* v_val_764_; 
v_val_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_val_764_);
lean_dec_ref(v___x_763_);
return v_val_764_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg___boxed(lean_object* v_inst_765_, lean_object* v_k_766_, lean_object* v_l_767_, lean_object* v_fallback_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(v_inst_765_, v_k_766_, v_l_767_, v_fallback_768_);
lean_dec(v_fallback_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(lean_object* v_00_u03b1_770_, lean_object* v_00_u03b2_771_, lean_object* v_inst_772_, lean_object* v_k_773_, lean_object* v_l_774_, lean_object* v_fallback_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(v_inst_772_, v_k_773_, v_l_774_, v_fallback_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___boxed(lean_object* v_00_u03b1_777_, lean_object* v_00_u03b2_778_, lean_object* v_inst_779_, lean_object* v_k_780_, lean_object* v_l_781_, lean_object* v_fallback_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(v_00_u03b1_777_, v_00_u03b2_778_, v_inst_779_, v_k_780_, v_l_781_, v_fallback_782_);
lean_dec(v_fallback_782_);
return v_res_783_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(lean_object* v_x_784_){
_start:
{
uint8_t v___x_785_; 
v___x_785_ = 0;
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* v_x_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(v_x_786_);
lean_dec(v_x_786_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(lean_object* v_sofar_789_, lean_object* v_step_790_){
_start:
{
if (lean_obj_tag(v_step_790_) == 0)
{
lean_object* v_a_791_; lean_object* v_a_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_a_791_ = lean_ctor_get(v_step_790_, 0);
v_a_792_ = lean_ctor_get(v_step_790_, 1);
lean_inc(v_a_792_);
lean_inc(v_a_791_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v_a_791_);
lean_ctor_set(v___x_793_, 1, v_a_792_);
v___x_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
return v___x_794_;
}
else
{
lean_object* v_a_795_; lean_object* v___x_796_; 
v_a_795_ = lean_ctor_get(v_step_790_, 2);
v___x_796_ = l_List_head_x3f___redArg(v_a_795_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_inc(v_sofar_789_);
return v_sofar_789_;
}
else
{
return v___x_796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* v_sofar_797_, lean_object* v_step_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(v_sofar_797_, v_step_798_);
lean_dec_ref(v_step_798_);
lean_dec(v_sofar_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(lean_object* v_l_802_){
_start:
{
lean_object* v___f_803_; lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___f_803_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0));
v___f_804_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1));
v___x_805_ = lean_box(0);
v___x_806_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___f_803_, v___x_805_, v___f_804_, v_l_802_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(lean_object* v_00_u03b1_807_, lean_object* v_00_u03b2_808_, lean_object* v_inst_809_, lean_object* v_l_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(v_l_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___boxed(lean_object* v_00_u03b1_812_, lean_object* v_00_u03b2_813_, lean_object* v_inst_814_, lean_object* v_l_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(v_00_u03b1_812_, v_00_u03b2_813_, v_inst_814_, v_l_815_);
lean_dec_ref(v_inst_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_r_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_List_head_x3f___redArg(v_r_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed(lean_object* v_x_822_, lean_object* v_x_823_, lean_object* v_x_824_, lean_object* v_r_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(v_x_822_, v_x_823_, v_x_824_, v_r_825_);
lean_dec(v_r_825_);
lean_dec(v_x_823_);
lean_dec(v_x_822_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(lean_object* v_l_828_){
_start:
{
lean_object* v___f_829_; lean_object* v___f_830_; lean_object* v___x_831_; 
v___f_829_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0));
v___f_830_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0));
v___x_831_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_829_, v_l_828_, v___f_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(lean_object* v_00_u03b1_832_, lean_object* v_00_u03b2_833_, lean_object* v_inst_834_, lean_object* v_l_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(v_l_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___boxed(lean_object* v_00_u03b1_837_, lean_object* v_00_u03b2_838_, lean_object* v_inst_839_, lean_object* v_l_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(v_00_u03b1_837_, v_00_u03b2_838_, v_inst_839_, v_l_840_);
lean_dec_ref(v_inst_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse___redArg(lean_object* v_x_842_){
_start:
{
if (lean_obj_tag(v_x_842_) == 0)
{
lean_object* v_size_843_; lean_object* v_k_844_; lean_object* v_v_845_; lean_object* v_l_846_; lean_object* v_r_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_856_; 
v_size_843_ = lean_ctor_get(v_x_842_, 0);
v_k_844_ = lean_ctor_get(v_x_842_, 1);
v_v_845_ = lean_ctor_get(v_x_842_, 2);
v_l_846_ = lean_ctor_get(v_x_842_, 3);
v_r_847_ = lean_ctor_get(v_x_842_, 4);
v_isSharedCheck_856_ = !lean_is_exclusive(v_x_842_);
if (v_isSharedCheck_856_ == 0)
{
v___x_849_ = v_x_842_;
v_isShared_850_ = v_isSharedCheck_856_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_r_847_);
lean_inc(v_l_846_);
lean_inc(v_v_845_);
lean_inc(v_k_844_);
lean_inc(v_size_843_);
lean_dec(v_x_842_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_856_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_851_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_r_847_);
v___x_852_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_l_846_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 4, v___x_852_);
lean_ctor_set(v___x_849_, 3, v___x_851_);
v___x_854_ = v___x_849_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_size_843_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_k_844_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_v_845_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_855_, 4, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
else
{
return v_x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse(lean_object* v_00_u03b1_857_, lean_object* v_00_u03b2_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0(lean_object* v_c_861_, lean_object* v_x_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(v_c_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(lean_object* v_inst_865_, lean_object* v_l_866_, lean_object* v_k_867_){
_start:
{
lean_object* v___f_868_; lean_object* v___x_869_; 
v___f_868_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0));
v___x_869_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_865_, v_k_867_, v_l_866_, v___f_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098(lean_object* v_00_u03b1_870_, lean_object* v_00_u03b2_871_, lean_object* v_inst_872_, lean_object* v_l_873_, lean_object* v_k_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_872_, v_l_873_, v_k_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(lean_object* v_inst_876_, lean_object* v_l_877_, lean_object* v_k_878_){
_start:
{
lean_object* v___x_879_; lean_object* v_val_880_; 
v___x_879_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_876_, v_l_877_, v_k_878_);
v_val_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_val_880_);
lean_dec(v___x_879_);
return v_val_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_inst_883_, lean_object* v_l_884_, lean_object* v_k_885_, lean_object* v_h_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(v_inst_883_, v_l_884_, v_k_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(lean_object* v_inst_888_, lean_object* v_l_889_, lean_object* v_k_890_, lean_object* v_inst_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_888_, v_l_889_, v_k_890_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_894_ = l_panic___redArg(v_inst_891_, v___x_893_);
return v___x_894_;
}
else
{
lean_object* v_val_895_; 
v_val_895_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_val_895_);
lean_dec_ref(v___x_892_);
return v_val_895_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg___boxed(lean_object* v_inst_896_, lean_object* v_l_897_, lean_object* v_k_898_, lean_object* v_inst_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(v_inst_896_, v_l_897_, v_k_898_, v_inst_899_);
lean_dec(v_inst_899_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(lean_object* v_00_u03b1_901_, lean_object* v_00_u03b2_902_, lean_object* v_inst_903_, lean_object* v_l_904_, lean_object* v_k_905_, lean_object* v_inst_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(v_inst_903_, v_l_904_, v_k_905_, v_inst_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___boxed(lean_object* v_00_u03b1_908_, lean_object* v_00_u03b2_909_, lean_object* v_inst_910_, lean_object* v_l_911_, lean_object* v_k_912_, lean_object* v_inst_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(v_00_u03b1_908_, v_00_u03b2_909_, v_inst_910_, v_l_911_, v_k_912_, v_inst_913_);
lean_dec(v_inst_913_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(lean_object* v_inst_915_, lean_object* v_l_916_, lean_object* v_k_917_, lean_object* v_fallback_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_915_, v_l_916_, v_k_917_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_inc(v_fallback_918_);
return v_fallback_918_;
}
else
{
lean_object* v_val_920_; 
v_val_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_val_920_);
lean_dec_ref(v___x_919_);
return v_val_920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg___boxed(lean_object* v_inst_921_, lean_object* v_l_922_, lean_object* v_k_923_, lean_object* v_fallback_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(v_inst_921_, v_l_922_, v_k_923_, v_fallback_924_);
lean_dec(v_fallback_924_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(lean_object* v_00_u03b1_926_, lean_object* v_00_u03b2_927_, lean_object* v_inst_928_, lean_object* v_l_929_, lean_object* v_k_930_, lean_object* v_fallback_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(v_inst_928_, v_l_929_, v_k_930_, v_fallback_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___boxed(lean_object* v_00_u03b1_933_, lean_object* v_00_u03b2_934_, lean_object* v_inst_935_, lean_object* v_l_936_, lean_object* v_k_937_, lean_object* v_fallback_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(v_00_u03b1_933_, v_00_u03b2_934_, v_inst_935_, v_l_936_, v_k_937_, v_fallback_938_);
lean_dec(v_fallback_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object* v_t_940_, lean_object* v_h__1_941_, lean_object* v_h__2_942_){
_start:
{
if (lean_obj_tag(v_t_940_) == 0)
{
lean_object* v_size_943_; lean_object* v_k_944_; lean_object* v_v_945_; lean_object* v_l_946_; lean_object* v_r_947_; lean_object* v___x_948_; 
lean_dec(v_h__1_941_);
v_size_943_ = lean_ctor_get(v_t_940_, 0);
lean_inc(v_size_943_);
v_k_944_ = lean_ctor_get(v_t_940_, 1);
lean_inc(v_k_944_);
v_v_945_ = lean_ctor_get(v_t_940_, 2);
lean_inc(v_v_945_);
v_l_946_ = lean_ctor_get(v_t_940_, 3);
lean_inc(v_l_946_);
v_r_947_ = lean_ctor_get(v_t_940_, 4);
lean_inc(v_r_947_);
lean_dec_ref(v_t_940_);
v___x_948_ = lean_apply_5(v_h__2_942_, v_size_943_, v_k_944_, v_v_945_, v_l_946_, v_r_947_);
return v___x_948_;
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec(v_h__2_942_);
v___x_949_ = lean_box(0);
v___x_950_ = lean_apply_1(v_h__1_941_, v___x_949_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object* v_00_u03b1_951_, lean_object* v_00_u03b2_952_, lean_object* v_motive_953_, lean_object* v_t_954_, lean_object* v_h__1_955_, lean_object* v_h__2_956_){
_start:
{
if (lean_obj_tag(v_t_954_) == 0)
{
lean_object* v_size_957_; lean_object* v_k_958_; lean_object* v_v_959_; lean_object* v_l_960_; lean_object* v_r_961_; lean_object* v___x_962_; 
lean_dec(v_h__1_955_);
v_size_957_ = lean_ctor_get(v_t_954_, 0);
lean_inc(v_size_957_);
v_k_958_ = lean_ctor_get(v_t_954_, 1);
lean_inc(v_k_958_);
v_v_959_ = lean_ctor_get(v_t_954_, 2);
lean_inc(v_v_959_);
v_l_960_ = lean_ctor_get(v_t_954_, 3);
lean_inc(v_l_960_);
v_r_961_ = lean_ctor_get(v_t_954_, 4);
lean_inc(v_r_961_);
lean_dec_ref(v_t_954_);
v___x_962_ = lean_apply_5(v_h__2_956_, v_size_957_, v_k_958_, v_v_959_, v_l_960_, v_r_961_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec(v_h__2_956_);
v___x_963_ = lean_box(0);
v___x_964_ = lean_apply_1(v_h__1_955_, v___x_963_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(uint8_t v_x_965_, lean_object* v_h__1_966_, lean_object* v_h__2_967_, lean_object* v_h__3_968_){
_start:
{
switch(v_x_965_)
{
case 0:
{
lean_object* v___x_969_; 
lean_dec(v_h__3_968_);
lean_dec(v_h__2_967_);
v___x_969_ = lean_apply_1(v_h__1_966_, lean_box(0));
return v___x_969_;
}
case 1:
{
lean_object* v___x_970_; 
lean_dec(v_h__2_967_);
lean_dec(v_h__1_966_);
v___x_970_ = lean_apply_1(v_h__3_968_, lean_box(0));
return v___x_970_;
}
default: 
{
lean_object* v___x_971_; 
lean_dec(v_h__3_968_);
lean_dec(v_h__1_966_);
v___x_971_ = lean_apply_1(v_h__2_967_, lean_box(0));
return v___x_971_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_972_, lean_object* v_h__1_973_, lean_object* v_h__2_974_, lean_object* v_h__3_975_){
_start:
{
uint8_t v_x_33__boxed_976_; lean_object* v_res_977_; 
v_x_33__boxed_976_ = lean_unbox(v_x_972_);
v_res_977_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(v_x_33__boxed_976_, v_h__1_973_, v_h__2_974_, v_h__3_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(lean_object* v_motive_978_, uint8_t v_x_979_, lean_object* v_h__1_980_, lean_object* v_h__2_981_, lean_object* v_h__3_982_){
_start:
{
switch(v_x_979_)
{
case 0:
{
lean_object* v___x_983_; 
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
v___x_983_ = lean_apply_1(v_h__1_980_, lean_box(0));
return v___x_983_;
}
case 1:
{
lean_object* v___x_984_; 
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v___x_984_ = lean_apply_1(v_h__3_982_, lean_box(0));
return v___x_984_;
}
default: 
{
lean_object* v___x_985_; 
lean_dec(v_h__3_982_);
lean_dec(v_h__1_980_);
v___x_985_ = lean_apply_1(v_h__2_981_, lean_box(0));
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___boxed(lean_object* v_motive_986_, lean_object* v_x_987_, lean_object* v_h__1_988_, lean_object* v_h__2_989_, lean_object* v_h__3_990_){
_start:
{
uint8_t v_x_42__boxed_991_; lean_object* v_res_992_; 
v_x_42__boxed_991_ = lean_unbox(v_x_987_);
v_res_992_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(v_motive_986_, v_x_42__boxed_991_, v_h__1_988_, v_h__2_989_, v_h__3_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object* v_x_993_, lean_object* v_h__1_994_, lean_object* v_h__2_995_){
_start:
{
if (lean_obj_tag(v_x_993_) == 0)
{
lean_object* v___x_996_; 
lean_dec(v_h__2_995_);
v___x_996_ = lean_apply_1(v_h__1_994_, lean_box(0));
return v___x_996_;
}
else
{
lean_object* v_val_997_; lean_object* v___x_998_; 
lean_dec(v_h__1_994_);
v_val_997_ = lean_ctor_get(v_x_993_, 0);
lean_inc(v_val_997_);
lean_dec_ref(v_x_993_);
v___x_998_ = lean_apply_2(v_h__2_995_, v_val_997_, lean_box(0));
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object* v_00_u03b1_999_, lean_object* v_00_u03b2_1000_, lean_object* v_motive_1001_, lean_object* v_x_1002_, lean_object* v_h__1_1003_, lean_object* v_h__2_1004_){
_start:
{
if (lean_obj_tag(v_x_1002_) == 0)
{
lean_object* v___x_1005_; 
lean_dec(v_h__2_1004_);
v___x_1005_ = lean_apply_1(v_h__1_1003_, lean_box(0));
return v___x_1005_;
}
else
{
lean_object* v_val_1006_; lean_object* v___x_1007_; 
lean_dec(v_h__1_1003_);
v_val_1006_ = lean_ctor_get(v_x_1002_, 0);
lean_inc(v_val_1006_);
lean_dec_ref(v_x_1002_);
v___x_1007_ = lean_apply_2(v_h__2_1004_, v_val_1006_, lean_box(0));
return v___x_1007_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___redArg(lean_object* v_t_1008_, lean_object* v_h__1_1009_){
_start:
{
lean_object* v_size_1010_; lean_object* v_k_1011_; lean_object* v_v_1012_; lean_object* v_l_1013_; lean_object* v_r_1014_; lean_object* v___x_1015_; 
v_size_1010_ = lean_ctor_get(v_t_1008_, 0);
lean_inc(v_size_1010_);
v_k_1011_ = lean_ctor_get(v_t_1008_, 1);
lean_inc(v_k_1011_);
v_v_1012_ = lean_ctor_get(v_t_1008_, 2);
lean_inc(v_v_1012_);
v_l_1013_ = lean_ctor_get(v_t_1008_, 3);
lean_inc(v_l_1013_);
v_r_1014_ = lean_ctor_get(v_t_1008_, 4);
lean_inc(v_r_1014_);
lean_dec(v_t_1008_);
v___x_1015_ = lean_apply_6(v_h__1_1009_, v_size_1010_, v_k_1011_, v_v_1012_, v_l_1013_, v_r_1014_, lean_box(0));
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(lean_object* v_00_u03b1_1016_, lean_object* v_00_u03b2_1017_, lean_object* v_inst_1018_, lean_object* v_k_1019_, lean_object* v_motive_1020_, lean_object* v_t_1021_, lean_object* v_hlk_1022_, lean_object* v_h__1_1023_){
_start:
{
lean_object* v_size_1024_; lean_object* v_k_1025_; lean_object* v_v_1026_; lean_object* v_l_1027_; lean_object* v_r_1028_; lean_object* v___x_1029_; 
v_size_1024_ = lean_ctor_get(v_t_1021_, 0);
lean_inc(v_size_1024_);
v_k_1025_ = lean_ctor_get(v_t_1021_, 1);
lean_inc(v_k_1025_);
v_v_1026_ = lean_ctor_get(v_t_1021_, 2);
lean_inc(v_v_1026_);
v_l_1027_ = lean_ctor_get(v_t_1021_, 3);
lean_inc(v_l_1027_);
v_r_1028_ = lean_ctor_get(v_t_1021_, 4);
lean_inc(v_r_1028_);
lean_dec(v_t_1021_);
v___x_1029_ = lean_apply_6(v_h__1_1023_, v_size_1024_, v_k_1025_, v_v_1026_, v_l_1027_, v_r_1028_, lean_box(0));
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___boxed(lean_object* v_00_u03b1_1030_, lean_object* v_00_u03b2_1031_, lean_object* v_inst_1032_, lean_object* v_k_1033_, lean_object* v_motive_1034_, lean_object* v_t_1035_, lean_object* v_hlk_1036_, lean_object* v_h__1_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(v_00_u03b1_1030_, v_00_u03b2_1031_, v_inst_1032_, v_k_1033_, v_motive_1034_, v_t_1035_, v_hlk_1036_, v_h__1_1037_);
lean_dec(v_k_1033_);
lean_dec_ref(v_inst_1032_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1039_, lean_object* v_h__1_1040_, lean_object* v_h__2_1041_){
_start:
{
if (lean_obj_tag(v_x_1039_) == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec(v_h__2_1041_);
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_apply_1(v_h__1_1040_, v___x_1042_);
return v___x_1043_;
}
else
{
lean_object* v_val_1044_; lean_object* v___x_1045_; 
lean_dec(v_h__1_1040_);
v_val_1044_ = lean_ctor_get(v_x_1039_, 0);
lean_inc(v_val_1044_);
lean_dec_ref(v_x_1039_);
v___x_1045_ = lean_apply_1(v_h__2_1041_, v_val_1044_);
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1046_, lean_object* v_00_u03b2_1047_, lean_object* v_motive_1048_, lean_object* v_x_1049_, lean_object* v_h__1_1050_, lean_object* v_h__2_1051_){
_start:
{
if (lean_obj_tag(v_x_1049_) == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec(v_h__2_1051_);
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_apply_1(v_h__1_1050_, v___x_1052_);
return v___x_1053_;
}
else
{
lean_object* v_val_1054_; lean_object* v___x_1055_; 
lean_dec(v_h__1_1050_);
v_val_1054_ = lean_ctor_get(v_x_1049_, 0);
lean_inc(v_val_1054_);
lean_dec_ref(v_x_1049_);
v___x_1055_ = lean_apply_1(v_h__2_1051_, v_val_1054_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___redArg(lean_object* v_t_1056_, lean_object* v_h__1_1057_){
_start:
{
lean_object* v_size_1058_; lean_object* v_k_1059_; lean_object* v_v_1060_; lean_object* v_l_1061_; lean_object* v_r_1062_; lean_object* v___x_1063_; 
v_size_1058_ = lean_ctor_get(v_t_1056_, 0);
lean_inc(v_size_1058_);
v_k_1059_ = lean_ctor_get(v_t_1056_, 1);
lean_inc(v_k_1059_);
v_v_1060_ = lean_ctor_get(v_t_1056_, 2);
lean_inc(v_v_1060_);
v_l_1061_ = lean_ctor_get(v_t_1056_, 3);
lean_inc(v_l_1061_);
v_r_1062_ = lean_ctor_get(v_t_1056_, 4);
lean_inc(v_r_1062_);
lean_dec(v_t_1056_);
v___x_1063_ = lean_apply_6(v_h__1_1057_, v_size_1058_, v_k_1059_, v_v_1060_, v_l_1061_, v_r_1062_, lean_box(0));
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(lean_object* v_00_u03b1_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_inst_1066_, lean_object* v_k_1067_, lean_object* v_motive_1068_, lean_object* v_t_1069_, lean_object* v_hlk_1070_, lean_object* v_h__1_1071_){
_start:
{
lean_object* v_size_1072_; lean_object* v_k_1073_; lean_object* v_v_1074_; lean_object* v_l_1075_; lean_object* v_r_1076_; lean_object* v___x_1077_; 
v_size_1072_ = lean_ctor_get(v_t_1069_, 0);
lean_inc(v_size_1072_);
v_k_1073_ = lean_ctor_get(v_t_1069_, 1);
lean_inc(v_k_1073_);
v_v_1074_ = lean_ctor_get(v_t_1069_, 2);
lean_inc(v_v_1074_);
v_l_1075_ = lean_ctor_get(v_t_1069_, 3);
lean_inc(v_l_1075_);
v_r_1076_ = lean_ctor_get(v_t_1069_, 4);
lean_inc(v_r_1076_);
lean_dec(v_t_1069_);
v___x_1077_ = lean_apply_6(v_h__1_1071_, v_size_1072_, v_k_1073_, v_v_1074_, v_l_1075_, v_r_1076_, lean_box(0));
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___boxed(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_inst_1080_, lean_object* v_k_1081_, lean_object* v_motive_1082_, lean_object* v_t_1083_, lean_object* v_hlk_1084_, lean_object* v_h__1_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(v_00_u03b1_1078_, v_00_u03b2_1079_, v_inst_1080_, v_k_1081_, v_motive_1082_, v_t_1083_, v_hlk_1084_, v_h__1_1085_);
lean_dec(v_k_1081_);
lean_dec_ref(v_inst_1080_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1087_, lean_object* v_h__1_1088_, lean_object* v_h__2_1089_, lean_object* v_h__3_1090_){
_start:
{
if (lean_obj_tag(v_x_1087_) == 0)
{
lean_object* v_l_1091_; 
lean_dec(v_h__1_1088_);
v_l_1091_ = lean_ctor_get(v_x_1087_, 3);
if (lean_obj_tag(v_l_1091_) == 0)
{
lean_object* v_size_1092_; lean_object* v_k_1093_; lean_object* v_v_1094_; lean_object* v_r_1095_; lean_object* v_size_1096_; lean_object* v_k_1097_; lean_object* v_v_1098_; lean_object* v_l_1099_; lean_object* v_r_1100_; lean_object* v___x_1101_; 
lean_inc_ref(v_l_1091_);
lean_dec(v_h__2_1089_);
v_size_1092_ = lean_ctor_get(v_x_1087_, 0);
lean_inc(v_size_1092_);
v_k_1093_ = lean_ctor_get(v_x_1087_, 1);
lean_inc(v_k_1093_);
v_v_1094_ = lean_ctor_get(v_x_1087_, 2);
lean_inc(v_v_1094_);
v_r_1095_ = lean_ctor_get(v_x_1087_, 4);
lean_inc(v_r_1095_);
lean_dec_ref(v_x_1087_);
v_size_1096_ = lean_ctor_get(v_l_1091_, 0);
lean_inc(v_size_1096_);
v_k_1097_ = lean_ctor_get(v_l_1091_, 1);
lean_inc(v_k_1097_);
v_v_1098_ = lean_ctor_get(v_l_1091_, 2);
lean_inc(v_v_1098_);
v_l_1099_ = lean_ctor_get(v_l_1091_, 3);
lean_inc(v_l_1099_);
v_r_1100_ = lean_ctor_get(v_l_1091_, 4);
lean_inc(v_r_1100_);
lean_dec_ref(v_l_1091_);
v___x_1101_ = lean_apply_9(v_h__3_1090_, v_size_1092_, v_k_1093_, v_v_1094_, v_size_1096_, v_k_1097_, v_v_1098_, v_l_1099_, v_r_1100_, v_r_1095_);
return v___x_1101_;
}
else
{
lean_object* v_size_1102_; lean_object* v_k_1103_; lean_object* v_v_1104_; lean_object* v_r_1105_; lean_object* v___x_1106_; 
lean_dec(v_h__3_1090_);
v_size_1102_ = lean_ctor_get(v_x_1087_, 0);
lean_inc(v_size_1102_);
v_k_1103_ = lean_ctor_get(v_x_1087_, 1);
lean_inc(v_k_1103_);
v_v_1104_ = lean_ctor_get(v_x_1087_, 2);
lean_inc(v_v_1104_);
v_r_1105_ = lean_ctor_get(v_x_1087_, 4);
lean_inc(v_r_1105_);
lean_dec_ref(v_x_1087_);
v___x_1106_ = lean_apply_4(v_h__2_1089_, v_size_1102_, v_k_1103_, v_v_1104_, v_r_1105_);
return v___x_1106_;
}
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec(v_h__3_1090_);
lean_dec(v_h__2_1089_);
v___x_1107_ = lean_box(0);
v___x_1108_ = lean_apply_1(v_h__1_1088_, v___x_1107_);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1109_, lean_object* v_00_u03b2_1110_, lean_object* v_motive_1111_, lean_object* v_x_1112_, lean_object* v_h__1_1113_, lean_object* v_h__2_1114_, lean_object* v_h__3_1115_){
_start:
{
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_object* v_l_1116_; 
lean_dec(v_h__1_1113_);
v_l_1116_ = lean_ctor_get(v_x_1112_, 3);
if (lean_obj_tag(v_l_1116_) == 0)
{
lean_object* v_size_1117_; lean_object* v_k_1118_; lean_object* v_v_1119_; lean_object* v_r_1120_; lean_object* v_size_1121_; lean_object* v_k_1122_; lean_object* v_v_1123_; lean_object* v_l_1124_; lean_object* v_r_1125_; lean_object* v___x_1126_; 
lean_inc_ref(v_l_1116_);
lean_dec(v_h__2_1114_);
v_size_1117_ = lean_ctor_get(v_x_1112_, 0);
lean_inc(v_size_1117_);
v_k_1118_ = lean_ctor_get(v_x_1112_, 1);
lean_inc(v_k_1118_);
v_v_1119_ = lean_ctor_get(v_x_1112_, 2);
lean_inc(v_v_1119_);
v_r_1120_ = lean_ctor_get(v_x_1112_, 4);
lean_inc(v_r_1120_);
lean_dec_ref(v_x_1112_);
v_size_1121_ = lean_ctor_get(v_l_1116_, 0);
lean_inc(v_size_1121_);
v_k_1122_ = lean_ctor_get(v_l_1116_, 1);
lean_inc(v_k_1122_);
v_v_1123_ = lean_ctor_get(v_l_1116_, 2);
lean_inc(v_v_1123_);
v_l_1124_ = lean_ctor_get(v_l_1116_, 3);
lean_inc(v_l_1124_);
v_r_1125_ = lean_ctor_get(v_l_1116_, 4);
lean_inc(v_r_1125_);
lean_dec_ref(v_l_1116_);
v___x_1126_ = lean_apply_9(v_h__3_1115_, v_size_1117_, v_k_1118_, v_v_1119_, v_size_1121_, v_k_1122_, v_v_1123_, v_l_1124_, v_r_1125_, v_r_1120_);
return v___x_1126_;
}
else
{
lean_object* v_size_1127_; lean_object* v_k_1128_; lean_object* v_v_1129_; lean_object* v_r_1130_; lean_object* v___x_1131_; 
lean_dec(v_h__3_1115_);
v_size_1127_ = lean_ctor_get(v_x_1112_, 0);
lean_inc(v_size_1127_);
v_k_1128_ = lean_ctor_get(v_x_1112_, 1);
lean_inc(v_k_1128_);
v_v_1129_ = lean_ctor_get(v_x_1112_, 2);
lean_inc(v_v_1129_);
v_r_1130_ = lean_ctor_get(v_x_1112_, 4);
lean_inc(v_r_1130_);
lean_dec_ref(v_x_1112_);
v___x_1131_ = lean_apply_4(v_h__2_1114_, v_size_1127_, v_k_1128_, v_v_1129_, v_r_1130_);
return v___x_1131_;
}
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_dec(v_h__3_1115_);
lean_dec(v_h__2_1114_);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_apply_1(v_h__1_1113_, v___x_1132_);
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_step_1134_, lean_object* v_h__1_1135_, lean_object* v_h__2_1136_){
_start:
{
if (lean_obj_tag(v_step_1134_) == 0)
{
lean_object* v_a_1137_; lean_object* v_a_1138_; lean_object* v_a_1139_; lean_object* v___x_1140_; 
lean_dec(v_h__2_1136_);
v_a_1137_ = lean_ctor_get(v_step_1134_, 0);
lean_inc(v_a_1137_);
v_a_1138_ = lean_ctor_get(v_step_1134_, 1);
lean_inc(v_a_1138_);
v_a_1139_ = lean_ctor_get(v_step_1134_, 2);
lean_inc(v_a_1139_);
lean_dec_ref(v_step_1134_);
v___x_1140_ = lean_apply_4(v_h__1_1135_, v_a_1137_, lean_box(0), v_a_1138_, v_a_1139_);
return v___x_1140_;
}
else
{
lean_object* v_a_1141_; lean_object* v_a_1142_; lean_object* v_a_1143_; lean_object* v___x_1144_; 
lean_dec(v_h__1_1135_);
v_a_1141_ = lean_ctor_get(v_step_1134_, 0);
lean_inc(v_a_1141_);
v_a_1142_ = lean_ctor_get(v_step_1134_, 1);
lean_inc(v_a_1142_);
v_a_1143_ = lean_ctor_get(v_step_1134_, 2);
lean_inc(v_a_1143_);
lean_dec_ref(v_step_1134_);
v___x_1144_ = lean_apply_3(v_h__2_1136_, v_a_1141_, v_a_1142_, v_a_1143_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_1145_, lean_object* v_00_u03b2_1146_, lean_object* v_inst_1147_, lean_object* v_motive_1148_, lean_object* v_step_1149_, lean_object* v_h__1_1150_, lean_object* v_h__2_1151_){
_start:
{
if (lean_obj_tag(v_step_1149_) == 0)
{
lean_object* v_a_1152_; lean_object* v_a_1153_; lean_object* v_a_1154_; lean_object* v___x_1155_; 
lean_dec(v_h__2_1151_);
v_a_1152_ = lean_ctor_get(v_step_1149_, 0);
lean_inc(v_a_1152_);
v_a_1153_ = lean_ctor_get(v_step_1149_, 1);
lean_inc(v_a_1153_);
v_a_1154_ = lean_ctor_get(v_step_1149_, 2);
lean_inc(v_a_1154_);
lean_dec_ref(v_step_1149_);
v___x_1155_ = lean_apply_4(v_h__1_1150_, v_a_1152_, lean_box(0), v_a_1153_, v_a_1154_);
return v___x_1155_;
}
else
{
lean_object* v_a_1156_; lean_object* v_a_1157_; lean_object* v_a_1158_; lean_object* v___x_1159_; 
lean_dec(v_h__1_1150_);
v_a_1156_ = lean_ctor_get(v_step_1149_, 0);
lean_inc(v_a_1156_);
v_a_1157_ = lean_ctor_get(v_step_1149_, 1);
lean_inc(v_a_1157_);
v_a_1158_ = lean_ctor_get(v_step_1149_, 2);
lean_inc(v_a_1158_);
lean_dec_ref(v_step_1149_);
v___x_1159_ = lean_apply_3(v_h__2_1151_, v_a_1156_, v_a_1157_, v_a_1158_);
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_1160_, lean_object* v_00_u03b2_1161_, lean_object* v_inst_1162_, lean_object* v_motive_1163_, lean_object* v_step_1164_, lean_object* v_h__1_1165_, lean_object* v_h__2_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(v_00_u03b1_1160_, v_00_u03b2_1161_, v_inst_1162_, v_motive_1163_, v_step_1164_, v_h__1_1165_, v_h__2_1166_);
lean_dec_ref(v_inst_1162_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object* v_x_1168_, lean_object* v_x_1169_, lean_object* v_h__1_1170_, lean_object* v_h__2_1171_, lean_object* v_h__3_1172_){
_start:
{
if (lean_obj_tag(v_x_1168_) == 0)
{
lean_object* v_l_1173_; 
lean_dec(v_h__1_1170_);
v_l_1173_ = lean_ctor_get(v_x_1168_, 3);
if (lean_obj_tag(v_l_1173_) == 0)
{
lean_object* v_size_1174_; lean_object* v_k_1175_; lean_object* v_v_1176_; lean_object* v_r_1177_; lean_object* v_size_1178_; lean_object* v_k_1179_; lean_object* v_v_1180_; lean_object* v_l_1181_; lean_object* v_r_1182_; lean_object* v___x_1183_; 
lean_inc_ref(v_l_1173_);
lean_dec(v_h__2_1171_);
v_size_1174_ = lean_ctor_get(v_x_1168_, 0);
lean_inc(v_size_1174_);
v_k_1175_ = lean_ctor_get(v_x_1168_, 1);
lean_inc(v_k_1175_);
v_v_1176_ = lean_ctor_get(v_x_1168_, 2);
lean_inc(v_v_1176_);
v_r_1177_ = lean_ctor_get(v_x_1168_, 4);
lean_inc(v_r_1177_);
lean_dec_ref(v_x_1168_);
v_size_1178_ = lean_ctor_get(v_l_1173_, 0);
lean_inc(v_size_1178_);
v_k_1179_ = lean_ctor_get(v_l_1173_, 1);
lean_inc(v_k_1179_);
v_v_1180_ = lean_ctor_get(v_l_1173_, 2);
lean_inc(v_v_1180_);
v_l_1181_ = lean_ctor_get(v_l_1173_, 3);
lean_inc(v_l_1181_);
v_r_1182_ = lean_ctor_get(v_l_1173_, 4);
lean_inc(v_r_1182_);
lean_dec_ref(v_l_1173_);
v___x_1183_ = lean_apply_10(v_h__3_1172_, v_size_1174_, v_k_1175_, v_v_1176_, v_size_1178_, v_k_1179_, v_v_1180_, v_l_1181_, v_r_1182_, v_r_1177_, v_x_1169_);
return v___x_1183_;
}
else
{
lean_object* v_size_1184_; lean_object* v_k_1185_; lean_object* v_v_1186_; lean_object* v_r_1187_; lean_object* v___x_1188_; 
lean_dec(v_h__3_1172_);
v_size_1184_ = lean_ctor_get(v_x_1168_, 0);
lean_inc(v_size_1184_);
v_k_1185_ = lean_ctor_get(v_x_1168_, 1);
lean_inc(v_k_1185_);
v_v_1186_ = lean_ctor_get(v_x_1168_, 2);
lean_inc(v_v_1186_);
v_r_1187_ = lean_ctor_get(v_x_1168_, 4);
lean_inc(v_r_1187_);
lean_dec_ref(v_x_1168_);
v___x_1188_ = lean_apply_5(v_h__2_1171_, v_size_1184_, v_k_1185_, v_v_1186_, v_r_1187_, v_x_1169_);
return v___x_1188_;
}
}
else
{
lean_object* v___x_1189_; 
lean_dec(v_h__3_1172_);
lean_dec(v_h__2_1171_);
v___x_1189_ = lean_apply_1(v_h__1_1170_, v_x_1169_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1190_, lean_object* v_00_u03b2_1191_, lean_object* v_motive_1192_, lean_object* v_x_1193_, lean_object* v_x_1194_, lean_object* v_h__1_1195_, lean_object* v_h__2_1196_, lean_object* v_h__3_1197_){
_start:
{
if (lean_obj_tag(v_x_1193_) == 0)
{
lean_object* v_l_1198_; 
lean_dec(v_h__1_1195_);
v_l_1198_ = lean_ctor_get(v_x_1193_, 3);
if (lean_obj_tag(v_l_1198_) == 0)
{
lean_object* v_size_1199_; lean_object* v_k_1200_; lean_object* v_v_1201_; lean_object* v_r_1202_; lean_object* v_size_1203_; lean_object* v_k_1204_; lean_object* v_v_1205_; lean_object* v_l_1206_; lean_object* v_r_1207_; lean_object* v___x_1208_; 
lean_inc_ref(v_l_1198_);
lean_dec(v_h__2_1196_);
v_size_1199_ = lean_ctor_get(v_x_1193_, 0);
lean_inc(v_size_1199_);
v_k_1200_ = lean_ctor_get(v_x_1193_, 1);
lean_inc(v_k_1200_);
v_v_1201_ = lean_ctor_get(v_x_1193_, 2);
lean_inc(v_v_1201_);
v_r_1202_ = lean_ctor_get(v_x_1193_, 4);
lean_inc(v_r_1202_);
lean_dec_ref(v_x_1193_);
v_size_1203_ = lean_ctor_get(v_l_1198_, 0);
lean_inc(v_size_1203_);
v_k_1204_ = lean_ctor_get(v_l_1198_, 1);
lean_inc(v_k_1204_);
v_v_1205_ = lean_ctor_get(v_l_1198_, 2);
lean_inc(v_v_1205_);
v_l_1206_ = lean_ctor_get(v_l_1198_, 3);
lean_inc(v_l_1206_);
v_r_1207_ = lean_ctor_get(v_l_1198_, 4);
lean_inc(v_r_1207_);
lean_dec_ref(v_l_1198_);
v___x_1208_ = lean_apply_10(v_h__3_1197_, v_size_1199_, v_k_1200_, v_v_1201_, v_size_1203_, v_k_1204_, v_v_1205_, v_l_1206_, v_r_1207_, v_r_1202_, v_x_1194_);
return v___x_1208_;
}
else
{
lean_object* v_size_1209_; lean_object* v_k_1210_; lean_object* v_v_1211_; lean_object* v_r_1212_; lean_object* v___x_1213_; 
lean_dec(v_h__3_1197_);
v_size_1209_ = lean_ctor_get(v_x_1193_, 0);
lean_inc(v_size_1209_);
v_k_1210_ = lean_ctor_get(v_x_1193_, 1);
lean_inc(v_k_1210_);
v_v_1211_ = lean_ctor_get(v_x_1193_, 2);
lean_inc(v_v_1211_);
v_r_1212_ = lean_ctor_get(v_x_1193_, 4);
lean_inc(v_r_1212_);
lean_dec_ref(v_x_1193_);
v___x_1213_ = lean_apply_5(v_h__2_1196_, v_size_1209_, v_k_1210_, v_v_1211_, v_r_1212_, v_x_1194_);
return v___x_1213_;
}
}
else
{
lean_object* v___x_1214_; 
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
v___x_1214_ = lean_apply_1(v_h__1_1195_, v_x_1194_);
return v___x_1214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object* v_x_1215_, lean_object* v_h__1_1216_, lean_object* v_h__2_1217_){
_start:
{
lean_object* v_l_1218_; 
v_l_1218_ = lean_ctor_get(v_x_1215_, 3);
if (lean_obj_tag(v_l_1218_) == 0)
{
lean_object* v_size_1219_; lean_object* v_k_1220_; lean_object* v_v_1221_; lean_object* v_r_1222_; lean_object* v_size_1223_; lean_object* v_k_1224_; lean_object* v_v_1225_; lean_object* v_l_1226_; lean_object* v_r_1227_; lean_object* v___x_1228_; 
lean_inc_ref(v_l_1218_);
lean_dec(v_h__1_1216_);
v_size_1219_ = lean_ctor_get(v_x_1215_, 0);
lean_inc(v_size_1219_);
v_k_1220_ = lean_ctor_get(v_x_1215_, 1);
lean_inc(v_k_1220_);
v_v_1221_ = lean_ctor_get(v_x_1215_, 2);
lean_inc(v_v_1221_);
v_r_1222_ = lean_ctor_get(v_x_1215_, 4);
lean_inc(v_r_1222_);
lean_dec(v_x_1215_);
v_size_1223_ = lean_ctor_get(v_l_1218_, 0);
lean_inc(v_size_1223_);
v_k_1224_ = lean_ctor_get(v_l_1218_, 1);
lean_inc(v_k_1224_);
v_v_1225_ = lean_ctor_get(v_l_1218_, 2);
lean_inc(v_v_1225_);
v_l_1226_ = lean_ctor_get(v_l_1218_, 3);
lean_inc(v_l_1226_);
v_r_1227_ = lean_ctor_get(v_l_1218_, 4);
lean_inc(v_r_1227_);
lean_dec_ref(v_l_1218_);
v___x_1228_ = lean_apply_10(v_h__2_1217_, v_size_1219_, v_k_1220_, v_v_1221_, v_size_1223_, v_k_1224_, v_v_1225_, v_l_1226_, v_r_1227_, v_r_1222_, lean_box(0));
return v___x_1228_;
}
else
{
lean_object* v_size_1229_; lean_object* v_k_1230_; lean_object* v_v_1231_; lean_object* v_r_1232_; lean_object* v___x_1233_; 
lean_dec(v_h__2_1217_);
v_size_1229_ = lean_ctor_get(v_x_1215_, 0);
lean_inc(v_size_1229_);
v_k_1230_ = lean_ctor_get(v_x_1215_, 1);
lean_inc(v_k_1230_);
v_v_1231_ = lean_ctor_get(v_x_1215_, 2);
lean_inc(v_v_1231_);
v_r_1232_ = lean_ctor_get(v_x_1215_, 4);
lean_inc(v_r_1232_);
lean_dec(v_x_1215_);
v___x_1233_ = lean_apply_5(v_h__1_1216_, v_size_1229_, v_k_1230_, v_v_1231_, v_r_1232_, lean_box(0));
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* v_00_u03b1_1234_, lean_object* v_00_u03b2_1235_, lean_object* v_motive_1236_, lean_object* v_x_1237_, lean_object* v_x_1238_, lean_object* v_h__1_1239_, lean_object* v_h__2_1240_){
_start:
{
lean_object* v_l_1241_; 
v_l_1241_ = lean_ctor_get(v_x_1237_, 3);
if (lean_obj_tag(v_l_1241_) == 0)
{
lean_object* v_size_1242_; lean_object* v_k_1243_; lean_object* v_v_1244_; lean_object* v_r_1245_; lean_object* v_size_1246_; lean_object* v_k_1247_; lean_object* v_v_1248_; lean_object* v_l_1249_; lean_object* v_r_1250_; lean_object* v___x_1251_; 
lean_inc_ref(v_l_1241_);
lean_dec(v_h__1_1239_);
v_size_1242_ = lean_ctor_get(v_x_1237_, 0);
lean_inc(v_size_1242_);
v_k_1243_ = lean_ctor_get(v_x_1237_, 1);
lean_inc(v_k_1243_);
v_v_1244_ = lean_ctor_get(v_x_1237_, 2);
lean_inc(v_v_1244_);
v_r_1245_ = lean_ctor_get(v_x_1237_, 4);
lean_inc(v_r_1245_);
lean_dec(v_x_1237_);
v_size_1246_ = lean_ctor_get(v_l_1241_, 0);
lean_inc(v_size_1246_);
v_k_1247_ = lean_ctor_get(v_l_1241_, 1);
lean_inc(v_k_1247_);
v_v_1248_ = lean_ctor_get(v_l_1241_, 2);
lean_inc(v_v_1248_);
v_l_1249_ = lean_ctor_get(v_l_1241_, 3);
lean_inc(v_l_1249_);
v_r_1250_ = lean_ctor_get(v_l_1241_, 4);
lean_inc(v_r_1250_);
lean_dec_ref(v_l_1241_);
v___x_1251_ = lean_apply_10(v_h__2_1240_, v_size_1242_, v_k_1243_, v_v_1244_, v_size_1246_, v_k_1247_, v_v_1248_, v_l_1249_, v_r_1250_, v_r_1245_, lean_box(0));
return v___x_1251_;
}
else
{
lean_object* v_size_1252_; lean_object* v_k_1253_; lean_object* v_v_1254_; lean_object* v_r_1255_; lean_object* v___x_1256_; 
lean_dec(v_h__2_1240_);
v_size_1252_ = lean_ctor_get(v_x_1237_, 0);
lean_inc(v_size_1252_);
v_k_1253_ = lean_ctor_get(v_x_1237_, 1);
lean_inc(v_k_1253_);
v_v_1254_ = lean_ctor_get(v_x_1237_, 2);
lean_inc(v_v_1254_);
v_r_1255_ = lean_ctor_get(v_x_1237_, 4);
lean_inc(v_r_1255_);
lean_dec(v_x_1237_);
v___x_1256_ = lean_apply_5(v_h__1_1239_, v_size_1252_, v_k_1253_, v_v_1254_, v_r_1255_, lean_box(0));
return v___x_1256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1257_, lean_object* v_h__1_1258_, lean_object* v_h__2_1259_, lean_object* v_h__3_1260_){
_start:
{
if (lean_obj_tag(v_x_1257_) == 0)
{
lean_object* v_r_1261_; 
lean_dec(v_h__1_1258_);
v_r_1261_ = lean_ctor_get(v_x_1257_, 4);
if (lean_obj_tag(v_r_1261_) == 0)
{
lean_object* v_size_1262_; lean_object* v_k_1263_; lean_object* v_v_1264_; lean_object* v_l_1265_; lean_object* v_size_1266_; lean_object* v_k_1267_; lean_object* v_v_1268_; lean_object* v_l_1269_; lean_object* v_r_1270_; lean_object* v___x_1271_; 
lean_inc_ref(v_r_1261_);
lean_dec(v_h__2_1259_);
v_size_1262_ = lean_ctor_get(v_x_1257_, 0);
lean_inc(v_size_1262_);
v_k_1263_ = lean_ctor_get(v_x_1257_, 1);
lean_inc(v_k_1263_);
v_v_1264_ = lean_ctor_get(v_x_1257_, 2);
lean_inc(v_v_1264_);
v_l_1265_ = lean_ctor_get(v_x_1257_, 3);
lean_inc(v_l_1265_);
lean_dec_ref(v_x_1257_);
v_size_1266_ = lean_ctor_get(v_r_1261_, 0);
lean_inc(v_size_1266_);
v_k_1267_ = lean_ctor_get(v_r_1261_, 1);
lean_inc(v_k_1267_);
v_v_1268_ = lean_ctor_get(v_r_1261_, 2);
lean_inc(v_v_1268_);
v_l_1269_ = lean_ctor_get(v_r_1261_, 3);
lean_inc(v_l_1269_);
v_r_1270_ = lean_ctor_get(v_r_1261_, 4);
lean_inc(v_r_1270_);
lean_dec_ref(v_r_1261_);
v___x_1271_ = lean_apply_9(v_h__3_1260_, v_size_1262_, v_k_1263_, v_v_1264_, v_l_1265_, v_size_1266_, v_k_1267_, v_v_1268_, v_l_1269_, v_r_1270_);
return v___x_1271_;
}
else
{
lean_object* v_size_1272_; lean_object* v_k_1273_; lean_object* v_v_1274_; lean_object* v_l_1275_; lean_object* v___x_1276_; 
lean_dec(v_h__3_1260_);
v_size_1272_ = lean_ctor_get(v_x_1257_, 0);
lean_inc(v_size_1272_);
v_k_1273_ = lean_ctor_get(v_x_1257_, 1);
lean_inc(v_k_1273_);
v_v_1274_ = lean_ctor_get(v_x_1257_, 2);
lean_inc(v_v_1274_);
v_l_1275_ = lean_ctor_get(v_x_1257_, 3);
lean_inc(v_l_1275_);
lean_dec_ref(v_x_1257_);
v___x_1276_ = lean_apply_4(v_h__2_1259_, v_size_1272_, v_k_1273_, v_v_1274_, v_l_1275_);
return v___x_1276_;
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec(v_h__3_1260_);
lean_dec(v_h__2_1259_);
v___x_1277_ = lean_box(0);
v___x_1278_ = lean_apply_1(v_h__1_1258_, v___x_1277_);
return v___x_1278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1279_, lean_object* v_00_u03b2_1280_, lean_object* v_motive_1281_, lean_object* v_x_1282_, lean_object* v_h__1_1283_, lean_object* v_h__2_1284_, lean_object* v_h__3_1285_){
_start:
{
if (lean_obj_tag(v_x_1282_) == 0)
{
lean_object* v_r_1286_; 
lean_dec(v_h__1_1283_);
v_r_1286_ = lean_ctor_get(v_x_1282_, 4);
if (lean_obj_tag(v_r_1286_) == 0)
{
lean_object* v_size_1287_; lean_object* v_k_1288_; lean_object* v_v_1289_; lean_object* v_l_1290_; lean_object* v_size_1291_; lean_object* v_k_1292_; lean_object* v_v_1293_; lean_object* v_l_1294_; lean_object* v_r_1295_; lean_object* v___x_1296_; 
lean_inc_ref(v_r_1286_);
lean_dec(v_h__2_1284_);
v_size_1287_ = lean_ctor_get(v_x_1282_, 0);
lean_inc(v_size_1287_);
v_k_1288_ = lean_ctor_get(v_x_1282_, 1);
lean_inc(v_k_1288_);
v_v_1289_ = lean_ctor_get(v_x_1282_, 2);
lean_inc(v_v_1289_);
v_l_1290_ = lean_ctor_get(v_x_1282_, 3);
lean_inc(v_l_1290_);
lean_dec_ref(v_x_1282_);
v_size_1291_ = lean_ctor_get(v_r_1286_, 0);
lean_inc(v_size_1291_);
v_k_1292_ = lean_ctor_get(v_r_1286_, 1);
lean_inc(v_k_1292_);
v_v_1293_ = lean_ctor_get(v_r_1286_, 2);
lean_inc(v_v_1293_);
v_l_1294_ = lean_ctor_get(v_r_1286_, 3);
lean_inc(v_l_1294_);
v_r_1295_ = lean_ctor_get(v_r_1286_, 4);
lean_inc(v_r_1295_);
lean_dec_ref(v_r_1286_);
v___x_1296_ = lean_apply_9(v_h__3_1285_, v_size_1287_, v_k_1288_, v_v_1289_, v_l_1290_, v_size_1291_, v_k_1292_, v_v_1293_, v_l_1294_, v_r_1295_);
return v___x_1296_;
}
else
{
lean_object* v_size_1297_; lean_object* v_k_1298_; lean_object* v_v_1299_; lean_object* v_l_1300_; lean_object* v___x_1301_; 
lean_dec(v_h__3_1285_);
v_size_1297_ = lean_ctor_get(v_x_1282_, 0);
lean_inc(v_size_1297_);
v_k_1298_ = lean_ctor_get(v_x_1282_, 1);
lean_inc(v_k_1298_);
v_v_1299_ = lean_ctor_get(v_x_1282_, 2);
lean_inc(v_v_1299_);
v_l_1300_ = lean_ctor_get(v_x_1282_, 3);
lean_inc(v_l_1300_);
lean_dec_ref(v_x_1282_);
v___x_1301_ = lean_apply_4(v_h__2_1284_, v_size_1297_, v_k_1298_, v_v_1299_, v_l_1300_);
return v___x_1301_;
}
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_dec(v_h__3_1285_);
lean_dec(v_h__2_1284_);
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_apply_1(v_h__1_1283_, v___x_1302_);
return v___x_1303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1304_, lean_object* v_x_1305_, lean_object* v_h__1_1306_, lean_object* v_h__2_1307_, lean_object* v_h__3_1308_){
_start:
{
if (lean_obj_tag(v_x_1304_) == 0)
{
lean_object* v_r_1309_; 
lean_dec(v_h__1_1306_);
v_r_1309_ = lean_ctor_get(v_x_1304_, 4);
if (lean_obj_tag(v_r_1309_) == 0)
{
lean_object* v_size_1310_; lean_object* v_k_1311_; lean_object* v_v_1312_; lean_object* v_l_1313_; lean_object* v_size_1314_; lean_object* v_k_1315_; lean_object* v_v_1316_; lean_object* v_l_1317_; lean_object* v_r_1318_; lean_object* v___x_1319_; 
lean_inc_ref(v_r_1309_);
lean_dec(v_h__2_1307_);
v_size_1310_ = lean_ctor_get(v_x_1304_, 0);
lean_inc(v_size_1310_);
v_k_1311_ = lean_ctor_get(v_x_1304_, 1);
lean_inc(v_k_1311_);
v_v_1312_ = lean_ctor_get(v_x_1304_, 2);
lean_inc(v_v_1312_);
v_l_1313_ = lean_ctor_get(v_x_1304_, 3);
lean_inc(v_l_1313_);
lean_dec_ref(v_x_1304_);
v_size_1314_ = lean_ctor_get(v_r_1309_, 0);
lean_inc(v_size_1314_);
v_k_1315_ = lean_ctor_get(v_r_1309_, 1);
lean_inc(v_k_1315_);
v_v_1316_ = lean_ctor_get(v_r_1309_, 2);
lean_inc(v_v_1316_);
v_l_1317_ = lean_ctor_get(v_r_1309_, 3);
lean_inc(v_l_1317_);
v_r_1318_ = lean_ctor_get(v_r_1309_, 4);
lean_inc(v_r_1318_);
lean_dec_ref(v_r_1309_);
v___x_1319_ = lean_apply_10(v_h__3_1308_, v_size_1310_, v_k_1311_, v_v_1312_, v_l_1313_, v_size_1314_, v_k_1315_, v_v_1316_, v_l_1317_, v_r_1318_, v_x_1305_);
return v___x_1319_;
}
else
{
lean_object* v_size_1320_; lean_object* v_k_1321_; lean_object* v_v_1322_; lean_object* v_l_1323_; lean_object* v___x_1324_; 
lean_dec(v_h__3_1308_);
v_size_1320_ = lean_ctor_get(v_x_1304_, 0);
lean_inc(v_size_1320_);
v_k_1321_ = lean_ctor_get(v_x_1304_, 1);
lean_inc(v_k_1321_);
v_v_1322_ = lean_ctor_get(v_x_1304_, 2);
lean_inc(v_v_1322_);
v_l_1323_ = lean_ctor_get(v_x_1304_, 3);
lean_inc(v_l_1323_);
lean_dec_ref(v_x_1304_);
v___x_1324_ = lean_apply_5(v_h__2_1307_, v_size_1320_, v_k_1321_, v_v_1322_, v_l_1323_, v_x_1305_);
return v___x_1324_;
}
}
else
{
lean_object* v___x_1325_; 
lean_dec(v_h__3_1308_);
lean_dec(v_h__2_1307_);
v___x_1325_ = lean_apply_1(v_h__1_1306_, v_x_1305_);
return v___x_1325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1326_, lean_object* v_00_u03b2_1327_, lean_object* v_motive_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_, lean_object* v_h__1_1331_, lean_object* v_h__2_1332_, lean_object* v_h__3_1333_){
_start:
{
if (lean_obj_tag(v_x_1329_) == 0)
{
lean_object* v_r_1334_; 
lean_dec(v_h__1_1331_);
v_r_1334_ = lean_ctor_get(v_x_1329_, 4);
if (lean_obj_tag(v_r_1334_) == 0)
{
lean_object* v_size_1335_; lean_object* v_k_1336_; lean_object* v_v_1337_; lean_object* v_l_1338_; lean_object* v_size_1339_; lean_object* v_k_1340_; lean_object* v_v_1341_; lean_object* v_l_1342_; lean_object* v_r_1343_; lean_object* v___x_1344_; 
lean_inc_ref(v_r_1334_);
lean_dec(v_h__2_1332_);
v_size_1335_ = lean_ctor_get(v_x_1329_, 0);
lean_inc(v_size_1335_);
v_k_1336_ = lean_ctor_get(v_x_1329_, 1);
lean_inc(v_k_1336_);
v_v_1337_ = lean_ctor_get(v_x_1329_, 2);
lean_inc(v_v_1337_);
v_l_1338_ = lean_ctor_get(v_x_1329_, 3);
lean_inc(v_l_1338_);
lean_dec_ref(v_x_1329_);
v_size_1339_ = lean_ctor_get(v_r_1334_, 0);
lean_inc(v_size_1339_);
v_k_1340_ = lean_ctor_get(v_r_1334_, 1);
lean_inc(v_k_1340_);
v_v_1341_ = lean_ctor_get(v_r_1334_, 2);
lean_inc(v_v_1341_);
v_l_1342_ = lean_ctor_get(v_r_1334_, 3);
lean_inc(v_l_1342_);
v_r_1343_ = lean_ctor_get(v_r_1334_, 4);
lean_inc(v_r_1343_);
lean_dec_ref(v_r_1334_);
v___x_1344_ = lean_apply_10(v_h__3_1333_, v_size_1335_, v_k_1336_, v_v_1337_, v_l_1338_, v_size_1339_, v_k_1340_, v_v_1341_, v_l_1342_, v_r_1343_, v_x_1330_);
return v___x_1344_;
}
else
{
lean_object* v_size_1345_; lean_object* v_k_1346_; lean_object* v_v_1347_; lean_object* v_l_1348_; lean_object* v___x_1349_; 
lean_dec(v_h__3_1333_);
v_size_1345_ = lean_ctor_get(v_x_1329_, 0);
lean_inc(v_size_1345_);
v_k_1346_ = lean_ctor_get(v_x_1329_, 1);
lean_inc(v_k_1346_);
v_v_1347_ = lean_ctor_get(v_x_1329_, 2);
lean_inc(v_v_1347_);
v_l_1348_ = lean_ctor_get(v_x_1329_, 3);
lean_inc(v_l_1348_);
lean_dec_ref(v_x_1329_);
v___x_1349_ = lean_apply_5(v_h__2_1332_, v_size_1345_, v_k_1346_, v_v_1347_, v_l_1348_, v_x_1330_);
return v___x_1349_;
}
}
else
{
lean_object* v___x_1350_; 
lean_dec(v_h__3_1333_);
lean_dec(v_h__2_1332_);
v___x_1350_ = lean_apply_1(v_h__1_1331_, v_x_1330_);
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object* v_x_1351_, lean_object* v_h__1_1352_, lean_object* v_h__2_1353_){
_start:
{
lean_object* v_r_1354_; 
v_r_1354_ = lean_ctor_get(v_x_1351_, 4);
if (lean_obj_tag(v_r_1354_) == 0)
{
lean_object* v_size_1355_; lean_object* v_k_1356_; lean_object* v_v_1357_; lean_object* v_l_1358_; lean_object* v_size_1359_; lean_object* v_k_1360_; lean_object* v_v_1361_; lean_object* v_l_1362_; lean_object* v_r_1363_; lean_object* v___x_1364_; 
lean_inc_ref(v_r_1354_);
lean_dec(v_h__1_1352_);
v_size_1355_ = lean_ctor_get(v_x_1351_, 0);
lean_inc(v_size_1355_);
v_k_1356_ = lean_ctor_get(v_x_1351_, 1);
lean_inc(v_k_1356_);
v_v_1357_ = lean_ctor_get(v_x_1351_, 2);
lean_inc(v_v_1357_);
v_l_1358_ = lean_ctor_get(v_x_1351_, 3);
lean_inc(v_l_1358_);
lean_dec(v_x_1351_);
v_size_1359_ = lean_ctor_get(v_r_1354_, 0);
lean_inc(v_size_1359_);
v_k_1360_ = lean_ctor_get(v_r_1354_, 1);
lean_inc(v_k_1360_);
v_v_1361_ = lean_ctor_get(v_r_1354_, 2);
lean_inc(v_v_1361_);
v_l_1362_ = lean_ctor_get(v_r_1354_, 3);
lean_inc(v_l_1362_);
v_r_1363_ = lean_ctor_get(v_r_1354_, 4);
lean_inc(v_r_1363_);
lean_dec_ref(v_r_1354_);
v___x_1364_ = lean_apply_10(v_h__2_1353_, v_size_1355_, v_k_1356_, v_v_1357_, v_l_1358_, v_size_1359_, v_k_1360_, v_v_1361_, v_l_1362_, v_r_1363_, lean_box(0));
return v___x_1364_;
}
else
{
lean_object* v_size_1365_; lean_object* v_k_1366_; lean_object* v_v_1367_; lean_object* v_l_1368_; lean_object* v___x_1369_; 
lean_dec(v_h__2_1353_);
v_size_1365_ = lean_ctor_get(v_x_1351_, 0);
lean_inc(v_size_1365_);
v_k_1366_ = lean_ctor_get(v_x_1351_, 1);
lean_inc(v_k_1366_);
v_v_1367_ = lean_ctor_get(v_x_1351_, 2);
lean_inc(v_v_1367_);
v_l_1368_ = lean_ctor_get(v_x_1351_, 3);
lean_inc(v_l_1368_);
lean_dec(v_x_1351_);
v___x_1369_ = lean_apply_5(v_h__1_1352_, v_size_1365_, v_k_1366_, v_v_1367_, v_l_1368_, lean_box(0));
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1370_, lean_object* v_00_u03b2_1371_, lean_object* v_motive_1372_, lean_object* v_x_1373_, lean_object* v_x_1374_, lean_object* v_h__1_1375_, lean_object* v_h__2_1376_){
_start:
{
lean_object* v_r_1377_; 
v_r_1377_ = lean_ctor_get(v_x_1373_, 4);
if (lean_obj_tag(v_r_1377_) == 0)
{
lean_object* v_size_1378_; lean_object* v_k_1379_; lean_object* v_v_1380_; lean_object* v_l_1381_; lean_object* v_size_1382_; lean_object* v_k_1383_; lean_object* v_v_1384_; lean_object* v_l_1385_; lean_object* v_r_1386_; lean_object* v___x_1387_; 
lean_inc_ref(v_r_1377_);
lean_dec(v_h__1_1375_);
v_size_1378_ = lean_ctor_get(v_x_1373_, 0);
lean_inc(v_size_1378_);
v_k_1379_ = lean_ctor_get(v_x_1373_, 1);
lean_inc(v_k_1379_);
v_v_1380_ = lean_ctor_get(v_x_1373_, 2);
lean_inc(v_v_1380_);
v_l_1381_ = lean_ctor_get(v_x_1373_, 3);
lean_inc(v_l_1381_);
lean_dec(v_x_1373_);
v_size_1382_ = lean_ctor_get(v_r_1377_, 0);
lean_inc(v_size_1382_);
v_k_1383_ = lean_ctor_get(v_r_1377_, 1);
lean_inc(v_k_1383_);
v_v_1384_ = lean_ctor_get(v_r_1377_, 2);
lean_inc(v_v_1384_);
v_l_1385_ = lean_ctor_get(v_r_1377_, 3);
lean_inc(v_l_1385_);
v_r_1386_ = lean_ctor_get(v_r_1377_, 4);
lean_inc(v_r_1386_);
lean_dec_ref(v_r_1377_);
v___x_1387_ = lean_apply_10(v_h__2_1376_, v_size_1378_, v_k_1379_, v_v_1380_, v_l_1381_, v_size_1382_, v_k_1383_, v_v_1384_, v_l_1385_, v_r_1386_, lean_box(0));
return v___x_1387_;
}
else
{
lean_object* v_size_1388_; lean_object* v_k_1389_; lean_object* v_v_1390_; lean_object* v_l_1391_; lean_object* v___x_1392_; 
lean_dec(v_h__2_1376_);
v_size_1388_ = lean_ctor_get(v_x_1373_, 0);
lean_inc(v_size_1388_);
v_k_1389_ = lean_ctor_get(v_x_1373_, 1);
lean_inc(v_k_1389_);
v_v_1390_ = lean_ctor_get(v_x_1373_, 2);
lean_inc(v_v_1390_);
v_l_1391_ = lean_ctor_get(v_x_1373_, 3);
lean_inc(v_l_1391_);
lean_dec(v_x_1373_);
v___x_1392_ = lean_apply_5(v_h__1_1375_, v_size_1388_, v_k_1389_, v_v_1390_, v_l_1391_, lean_box(0));
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object* v_x_1393_, lean_object* v_x_1394_, lean_object* v_h__1_1395_, lean_object* v_h__2_1396_, lean_object* v_h__3_1397_){
_start:
{
if (lean_obj_tag(v_x_1393_) == 0)
{
lean_object* v_l_1398_; 
lean_dec(v_h__1_1395_);
v_l_1398_ = lean_ctor_get(v_x_1393_, 3);
if (lean_obj_tag(v_l_1398_) == 0)
{
lean_object* v_size_1399_; lean_object* v_k_1400_; lean_object* v_v_1401_; lean_object* v_r_1402_; lean_object* v_size_1403_; lean_object* v_k_1404_; lean_object* v_v_1405_; lean_object* v_l_1406_; lean_object* v_r_1407_; lean_object* v___x_1408_; 
lean_inc_ref(v_l_1398_);
lean_dec(v_h__2_1396_);
v_size_1399_ = lean_ctor_get(v_x_1393_, 0);
lean_inc(v_size_1399_);
v_k_1400_ = lean_ctor_get(v_x_1393_, 1);
lean_inc(v_k_1400_);
v_v_1401_ = lean_ctor_get(v_x_1393_, 2);
lean_inc(v_v_1401_);
v_r_1402_ = lean_ctor_get(v_x_1393_, 4);
lean_inc(v_r_1402_);
lean_dec_ref(v_x_1393_);
v_size_1403_ = lean_ctor_get(v_l_1398_, 0);
lean_inc(v_size_1403_);
v_k_1404_ = lean_ctor_get(v_l_1398_, 1);
lean_inc(v_k_1404_);
v_v_1405_ = lean_ctor_get(v_l_1398_, 2);
lean_inc(v_v_1405_);
v_l_1406_ = lean_ctor_get(v_l_1398_, 3);
lean_inc(v_l_1406_);
v_r_1407_ = lean_ctor_get(v_l_1398_, 4);
lean_inc(v_r_1407_);
lean_dec_ref(v_l_1398_);
v___x_1408_ = lean_apply_10(v_h__3_1397_, v_size_1399_, v_k_1400_, v_v_1401_, v_size_1403_, v_k_1404_, v_v_1405_, v_l_1406_, v_r_1407_, v_r_1402_, v_x_1394_);
return v___x_1408_;
}
else
{
lean_object* v_size_1409_; lean_object* v_k_1410_; lean_object* v_v_1411_; lean_object* v_r_1412_; lean_object* v___x_1413_; 
lean_dec(v_h__3_1397_);
v_size_1409_ = lean_ctor_get(v_x_1393_, 0);
lean_inc(v_size_1409_);
v_k_1410_ = lean_ctor_get(v_x_1393_, 1);
lean_inc(v_k_1410_);
v_v_1411_ = lean_ctor_get(v_x_1393_, 2);
lean_inc(v_v_1411_);
v_r_1412_ = lean_ctor_get(v_x_1393_, 4);
lean_inc(v_r_1412_);
lean_dec_ref(v_x_1393_);
v___x_1413_ = lean_apply_5(v_h__2_1396_, v_size_1409_, v_k_1410_, v_v_1411_, v_r_1412_, v_x_1394_);
return v___x_1413_;
}
}
else
{
lean_object* v___x_1414_; 
lean_dec(v_h__3_1397_);
lean_dec(v_h__2_1396_);
v___x_1414_ = lean_apply_1(v_h__1_1395_, v_x_1394_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* v_00_u03b1_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_motive_1417_, lean_object* v_x_1418_, lean_object* v_x_1419_, lean_object* v_h__1_1420_, lean_object* v_h__2_1421_, lean_object* v_h__3_1422_){
_start:
{
if (lean_obj_tag(v_x_1418_) == 0)
{
lean_object* v_l_1423_; 
lean_dec(v_h__1_1420_);
v_l_1423_ = lean_ctor_get(v_x_1418_, 3);
if (lean_obj_tag(v_l_1423_) == 0)
{
lean_object* v_size_1424_; lean_object* v_k_1425_; lean_object* v_v_1426_; lean_object* v_r_1427_; lean_object* v_size_1428_; lean_object* v_k_1429_; lean_object* v_v_1430_; lean_object* v_l_1431_; lean_object* v_r_1432_; lean_object* v___x_1433_; 
lean_inc_ref(v_l_1423_);
lean_dec(v_h__2_1421_);
v_size_1424_ = lean_ctor_get(v_x_1418_, 0);
lean_inc(v_size_1424_);
v_k_1425_ = lean_ctor_get(v_x_1418_, 1);
lean_inc(v_k_1425_);
v_v_1426_ = lean_ctor_get(v_x_1418_, 2);
lean_inc(v_v_1426_);
v_r_1427_ = lean_ctor_get(v_x_1418_, 4);
lean_inc(v_r_1427_);
lean_dec_ref(v_x_1418_);
v_size_1428_ = lean_ctor_get(v_l_1423_, 0);
lean_inc(v_size_1428_);
v_k_1429_ = lean_ctor_get(v_l_1423_, 1);
lean_inc(v_k_1429_);
v_v_1430_ = lean_ctor_get(v_l_1423_, 2);
lean_inc(v_v_1430_);
v_l_1431_ = lean_ctor_get(v_l_1423_, 3);
lean_inc(v_l_1431_);
v_r_1432_ = lean_ctor_get(v_l_1423_, 4);
lean_inc(v_r_1432_);
lean_dec_ref(v_l_1423_);
v___x_1433_ = lean_apply_10(v_h__3_1422_, v_size_1424_, v_k_1425_, v_v_1426_, v_size_1428_, v_k_1429_, v_v_1430_, v_l_1431_, v_r_1432_, v_r_1427_, v_x_1419_);
return v___x_1433_;
}
else
{
lean_object* v_size_1434_; lean_object* v_k_1435_; lean_object* v_v_1436_; lean_object* v_r_1437_; lean_object* v___x_1438_; 
lean_dec(v_h__3_1422_);
v_size_1434_ = lean_ctor_get(v_x_1418_, 0);
lean_inc(v_size_1434_);
v_k_1435_ = lean_ctor_get(v_x_1418_, 1);
lean_inc(v_k_1435_);
v_v_1436_ = lean_ctor_get(v_x_1418_, 2);
lean_inc(v_v_1436_);
v_r_1437_ = lean_ctor_get(v_x_1418_, 4);
lean_inc(v_r_1437_);
lean_dec_ref(v_x_1418_);
v___x_1438_ = lean_apply_5(v_h__2_1421_, v_size_1434_, v_k_1435_, v_v_1436_, v_r_1437_, v_x_1419_);
return v___x_1438_;
}
}
else
{
lean_object* v___x_1439_; 
lean_dec(v_h__3_1422_);
lean_dec(v_h__2_1421_);
v___x_1439_ = lean_apply_1(v_h__1_1420_, v_x_1419_);
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_h__1_1442_, lean_object* v_h__2_1443_, lean_object* v_h__3_1444_){
_start:
{
if (lean_obj_tag(v_x_1440_) == 0)
{
lean_object* v_r_1445_; 
lean_dec(v_h__1_1442_);
v_r_1445_ = lean_ctor_get(v_x_1440_, 4);
if (lean_obj_tag(v_r_1445_) == 0)
{
lean_object* v_size_1446_; lean_object* v_k_1447_; lean_object* v_v_1448_; lean_object* v_l_1449_; lean_object* v_size_1450_; lean_object* v_k_1451_; lean_object* v_v_1452_; lean_object* v_l_1453_; lean_object* v_r_1454_; lean_object* v___x_1455_; 
lean_inc_ref(v_r_1445_);
lean_dec(v_h__2_1443_);
v_size_1446_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_size_1446_);
v_k_1447_ = lean_ctor_get(v_x_1440_, 1);
lean_inc(v_k_1447_);
v_v_1448_ = lean_ctor_get(v_x_1440_, 2);
lean_inc(v_v_1448_);
v_l_1449_ = lean_ctor_get(v_x_1440_, 3);
lean_inc(v_l_1449_);
lean_dec_ref(v_x_1440_);
v_size_1450_ = lean_ctor_get(v_r_1445_, 0);
lean_inc(v_size_1450_);
v_k_1451_ = lean_ctor_get(v_r_1445_, 1);
lean_inc(v_k_1451_);
v_v_1452_ = lean_ctor_get(v_r_1445_, 2);
lean_inc(v_v_1452_);
v_l_1453_ = lean_ctor_get(v_r_1445_, 3);
lean_inc(v_l_1453_);
v_r_1454_ = lean_ctor_get(v_r_1445_, 4);
lean_inc(v_r_1454_);
lean_dec_ref(v_r_1445_);
v___x_1455_ = lean_apply_10(v_h__3_1444_, v_size_1446_, v_k_1447_, v_v_1448_, v_l_1449_, v_size_1450_, v_k_1451_, v_v_1452_, v_l_1453_, v_r_1454_, v_x_1441_);
return v___x_1455_;
}
else
{
lean_object* v_size_1456_; lean_object* v_k_1457_; lean_object* v_v_1458_; lean_object* v_l_1459_; lean_object* v___x_1460_; 
lean_dec(v_h__3_1444_);
v_size_1456_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_size_1456_);
v_k_1457_ = lean_ctor_get(v_x_1440_, 1);
lean_inc(v_k_1457_);
v_v_1458_ = lean_ctor_get(v_x_1440_, 2);
lean_inc(v_v_1458_);
v_l_1459_ = lean_ctor_get(v_x_1440_, 3);
lean_inc(v_l_1459_);
lean_dec_ref(v_x_1440_);
v___x_1460_ = lean_apply_5(v_h__2_1443_, v_size_1456_, v_k_1457_, v_v_1458_, v_l_1459_, v_x_1441_);
return v___x_1460_;
}
}
else
{
lean_object* v___x_1461_; 
lean_dec(v_h__3_1444_);
lean_dec(v_h__2_1443_);
v___x_1461_ = lean_apply_1(v_h__1_1442_, v_x_1441_);
return v___x_1461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object* v_00_u03b1_1462_, lean_object* v_00_u03b2_1463_, lean_object* v_motive_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_h__1_1467_, lean_object* v_h__2_1468_, lean_object* v_h__3_1469_){
_start:
{
if (lean_obj_tag(v_x_1465_) == 0)
{
lean_object* v_r_1470_; 
lean_dec(v_h__1_1467_);
v_r_1470_ = lean_ctor_get(v_x_1465_, 4);
if (lean_obj_tag(v_r_1470_) == 0)
{
lean_object* v_size_1471_; lean_object* v_k_1472_; lean_object* v_v_1473_; lean_object* v_l_1474_; lean_object* v_size_1475_; lean_object* v_k_1476_; lean_object* v_v_1477_; lean_object* v_l_1478_; lean_object* v_r_1479_; lean_object* v___x_1480_; 
lean_inc_ref(v_r_1470_);
lean_dec(v_h__2_1468_);
v_size_1471_ = lean_ctor_get(v_x_1465_, 0);
lean_inc(v_size_1471_);
v_k_1472_ = lean_ctor_get(v_x_1465_, 1);
lean_inc(v_k_1472_);
v_v_1473_ = lean_ctor_get(v_x_1465_, 2);
lean_inc(v_v_1473_);
v_l_1474_ = lean_ctor_get(v_x_1465_, 3);
lean_inc(v_l_1474_);
lean_dec_ref(v_x_1465_);
v_size_1475_ = lean_ctor_get(v_r_1470_, 0);
lean_inc(v_size_1475_);
v_k_1476_ = lean_ctor_get(v_r_1470_, 1);
lean_inc(v_k_1476_);
v_v_1477_ = lean_ctor_get(v_r_1470_, 2);
lean_inc(v_v_1477_);
v_l_1478_ = lean_ctor_get(v_r_1470_, 3);
lean_inc(v_l_1478_);
v_r_1479_ = lean_ctor_get(v_r_1470_, 4);
lean_inc(v_r_1479_);
lean_dec_ref(v_r_1470_);
v___x_1480_ = lean_apply_10(v_h__3_1469_, v_size_1471_, v_k_1472_, v_v_1473_, v_l_1474_, v_size_1475_, v_k_1476_, v_v_1477_, v_l_1478_, v_r_1479_, v_x_1466_);
return v___x_1480_;
}
else
{
lean_object* v_size_1481_; lean_object* v_k_1482_; lean_object* v_v_1483_; lean_object* v_l_1484_; lean_object* v___x_1485_; 
lean_dec(v_h__3_1469_);
v_size_1481_ = lean_ctor_get(v_x_1465_, 0);
lean_inc(v_size_1481_);
v_k_1482_ = lean_ctor_get(v_x_1465_, 1);
lean_inc(v_k_1482_);
v_v_1483_ = lean_ctor_get(v_x_1465_, 2);
lean_inc(v_v_1483_);
v_l_1484_ = lean_ctor_get(v_x_1465_, 3);
lean_inc(v_l_1484_);
lean_dec_ref(v_x_1465_);
v___x_1485_ = lean_apply_5(v_h__2_1468_, v_size_1481_, v_k_1482_, v_v_1483_, v_l_1484_, v_x_1466_);
return v___x_1485_;
}
}
else
{
lean_object* v___x_1486_; 
lean_dec(v_h__3_1469_);
lean_dec(v_h__2_1468_);
v___x_1486_ = lean_apply_1(v_h__1_1467_, v_x_1466_);
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1487_, lean_object* v_h__1_1488_, lean_object* v_h__2_1489_, lean_object* v_h__3_1490_){
_start:
{
if (lean_obj_tag(v_x_1487_) == 0)
{
lean_object* v_l_1491_; 
lean_dec(v_h__1_1488_);
v_l_1491_ = lean_ctor_get(v_x_1487_, 3);
if (lean_obj_tag(v_l_1491_) == 0)
{
lean_object* v_size_1492_; lean_object* v_k_1493_; lean_object* v_v_1494_; lean_object* v_r_1495_; lean_object* v_size_1496_; lean_object* v_k_1497_; lean_object* v_v_1498_; lean_object* v_l_1499_; lean_object* v_r_1500_; lean_object* v___x_1501_; 
lean_inc_ref(v_l_1491_);
lean_dec(v_h__2_1489_);
v_size_1492_ = lean_ctor_get(v_x_1487_, 0);
lean_inc(v_size_1492_);
v_k_1493_ = lean_ctor_get(v_x_1487_, 1);
lean_inc(v_k_1493_);
v_v_1494_ = lean_ctor_get(v_x_1487_, 2);
lean_inc(v_v_1494_);
v_r_1495_ = lean_ctor_get(v_x_1487_, 4);
lean_inc(v_r_1495_);
lean_dec_ref(v_x_1487_);
v_size_1496_ = lean_ctor_get(v_l_1491_, 0);
lean_inc(v_size_1496_);
v_k_1497_ = lean_ctor_get(v_l_1491_, 1);
lean_inc(v_k_1497_);
v_v_1498_ = lean_ctor_get(v_l_1491_, 2);
lean_inc(v_v_1498_);
v_l_1499_ = lean_ctor_get(v_l_1491_, 3);
lean_inc(v_l_1499_);
v_r_1500_ = lean_ctor_get(v_l_1491_, 4);
lean_inc(v_r_1500_);
lean_dec_ref(v_l_1491_);
v___x_1501_ = lean_apply_9(v_h__3_1490_, v_size_1492_, v_k_1493_, v_v_1494_, v_size_1496_, v_k_1497_, v_v_1498_, v_l_1499_, v_r_1500_, v_r_1495_);
return v___x_1501_;
}
else
{
lean_object* v_size_1502_; lean_object* v_k_1503_; lean_object* v_v_1504_; lean_object* v_r_1505_; lean_object* v___x_1506_; 
lean_dec(v_h__3_1490_);
v_size_1502_ = lean_ctor_get(v_x_1487_, 0);
lean_inc(v_size_1502_);
v_k_1503_ = lean_ctor_get(v_x_1487_, 1);
lean_inc(v_k_1503_);
v_v_1504_ = lean_ctor_get(v_x_1487_, 2);
lean_inc(v_v_1504_);
v_r_1505_ = lean_ctor_get(v_x_1487_, 4);
lean_inc(v_r_1505_);
lean_dec_ref(v_x_1487_);
v___x_1506_ = lean_apply_4(v_h__2_1489_, v_size_1502_, v_k_1503_, v_v_1504_, v_r_1505_);
return v___x_1506_;
}
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_dec(v_h__3_1490_);
lean_dec(v_h__2_1489_);
v___x_1507_ = lean_box(0);
v___x_1508_ = lean_apply_1(v_h__1_1488_, v___x_1507_);
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1509_, lean_object* v_00_u03b2_1510_, lean_object* v_motive_1511_, lean_object* v_x_1512_, lean_object* v_h__1_1513_, lean_object* v_h__2_1514_, lean_object* v_h__3_1515_){
_start:
{
if (lean_obj_tag(v_x_1512_) == 0)
{
lean_object* v_l_1516_; 
lean_dec(v_h__1_1513_);
v_l_1516_ = lean_ctor_get(v_x_1512_, 3);
if (lean_obj_tag(v_l_1516_) == 0)
{
lean_object* v_size_1517_; lean_object* v_k_1518_; lean_object* v_v_1519_; lean_object* v_r_1520_; lean_object* v_size_1521_; lean_object* v_k_1522_; lean_object* v_v_1523_; lean_object* v_l_1524_; lean_object* v_r_1525_; lean_object* v___x_1526_; 
lean_inc_ref(v_l_1516_);
lean_dec(v_h__2_1514_);
v_size_1517_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_size_1517_);
v_k_1518_ = lean_ctor_get(v_x_1512_, 1);
lean_inc(v_k_1518_);
v_v_1519_ = lean_ctor_get(v_x_1512_, 2);
lean_inc(v_v_1519_);
v_r_1520_ = lean_ctor_get(v_x_1512_, 4);
lean_inc(v_r_1520_);
lean_dec_ref(v_x_1512_);
v_size_1521_ = lean_ctor_get(v_l_1516_, 0);
lean_inc(v_size_1521_);
v_k_1522_ = lean_ctor_get(v_l_1516_, 1);
lean_inc(v_k_1522_);
v_v_1523_ = lean_ctor_get(v_l_1516_, 2);
lean_inc(v_v_1523_);
v_l_1524_ = lean_ctor_get(v_l_1516_, 3);
lean_inc(v_l_1524_);
v_r_1525_ = lean_ctor_get(v_l_1516_, 4);
lean_inc(v_r_1525_);
lean_dec_ref(v_l_1516_);
v___x_1526_ = lean_apply_9(v_h__3_1515_, v_size_1517_, v_k_1518_, v_v_1519_, v_size_1521_, v_k_1522_, v_v_1523_, v_l_1524_, v_r_1525_, v_r_1520_);
return v___x_1526_;
}
else
{
lean_object* v_size_1527_; lean_object* v_k_1528_; lean_object* v_v_1529_; lean_object* v_r_1530_; lean_object* v___x_1531_; 
lean_dec(v_h__3_1515_);
v_size_1527_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_size_1527_);
v_k_1528_ = lean_ctor_get(v_x_1512_, 1);
lean_inc(v_k_1528_);
v_v_1529_ = lean_ctor_get(v_x_1512_, 2);
lean_inc(v_v_1529_);
v_r_1530_ = lean_ctor_get(v_x_1512_, 4);
lean_inc(v_r_1530_);
lean_dec_ref(v_x_1512_);
v___x_1531_ = lean_apply_4(v_h__2_1514_, v_size_1527_, v_k_1528_, v_v_1529_, v_r_1530_);
return v___x_1531_;
}
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_apply_1(v_h__1_1513_, v___x_1532_);
return v___x_1533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object* v_x_1534_, lean_object* v_x_1535_, lean_object* v_h__1_1536_, lean_object* v_h__2_1537_, lean_object* v_h__3_1538_){
_start:
{
if (lean_obj_tag(v_x_1534_) == 0)
{
lean_object* v_l_1539_; 
lean_dec(v_h__1_1536_);
v_l_1539_ = lean_ctor_get(v_x_1534_, 3);
if (lean_obj_tag(v_l_1539_) == 0)
{
lean_object* v_size_1540_; lean_object* v_k_1541_; lean_object* v_v_1542_; lean_object* v_r_1543_; lean_object* v_size_1544_; lean_object* v_k_1545_; lean_object* v_v_1546_; lean_object* v_l_1547_; lean_object* v_r_1548_; lean_object* v___x_1549_; 
lean_inc_ref(v_l_1539_);
lean_dec(v_h__2_1537_);
v_size_1540_ = lean_ctor_get(v_x_1534_, 0);
lean_inc(v_size_1540_);
v_k_1541_ = lean_ctor_get(v_x_1534_, 1);
lean_inc(v_k_1541_);
v_v_1542_ = lean_ctor_get(v_x_1534_, 2);
lean_inc(v_v_1542_);
v_r_1543_ = lean_ctor_get(v_x_1534_, 4);
lean_inc(v_r_1543_);
lean_dec_ref(v_x_1534_);
v_size_1544_ = lean_ctor_get(v_l_1539_, 0);
lean_inc(v_size_1544_);
v_k_1545_ = lean_ctor_get(v_l_1539_, 1);
lean_inc(v_k_1545_);
v_v_1546_ = lean_ctor_get(v_l_1539_, 2);
lean_inc(v_v_1546_);
v_l_1547_ = lean_ctor_get(v_l_1539_, 3);
lean_inc(v_l_1547_);
v_r_1548_ = lean_ctor_get(v_l_1539_, 4);
lean_inc(v_r_1548_);
lean_dec_ref(v_l_1539_);
v___x_1549_ = lean_apply_10(v_h__3_1538_, v_size_1540_, v_k_1541_, v_v_1542_, v_size_1544_, v_k_1545_, v_v_1546_, v_l_1547_, v_r_1548_, v_r_1543_, v_x_1535_);
return v___x_1549_;
}
else
{
lean_object* v_size_1550_; lean_object* v_k_1551_; lean_object* v_v_1552_; lean_object* v_r_1553_; lean_object* v___x_1554_; 
lean_dec(v_h__3_1538_);
v_size_1550_ = lean_ctor_get(v_x_1534_, 0);
lean_inc(v_size_1550_);
v_k_1551_ = lean_ctor_get(v_x_1534_, 1);
lean_inc(v_k_1551_);
v_v_1552_ = lean_ctor_get(v_x_1534_, 2);
lean_inc(v_v_1552_);
v_r_1553_ = lean_ctor_get(v_x_1534_, 4);
lean_inc(v_r_1553_);
lean_dec_ref(v_x_1534_);
v___x_1554_ = lean_apply_5(v_h__2_1537_, v_size_1550_, v_k_1551_, v_v_1552_, v_r_1553_, v_x_1535_);
return v___x_1554_;
}
}
else
{
lean_object* v___x_1555_; 
lean_dec(v_h__3_1538_);
lean_dec(v_h__2_1537_);
v___x_1555_ = lean_apply_1(v_h__1_1536_, v_x_1535_);
return v___x_1555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1556_, lean_object* v_00_u03b2_1557_, lean_object* v_motive_1558_, lean_object* v_x_1559_, lean_object* v_x_1560_, lean_object* v_h__1_1561_, lean_object* v_h__2_1562_, lean_object* v_h__3_1563_){
_start:
{
if (lean_obj_tag(v_x_1559_) == 0)
{
lean_object* v_l_1564_; 
lean_dec(v_h__1_1561_);
v_l_1564_ = lean_ctor_get(v_x_1559_, 3);
if (lean_obj_tag(v_l_1564_) == 0)
{
lean_object* v_size_1565_; lean_object* v_k_1566_; lean_object* v_v_1567_; lean_object* v_r_1568_; lean_object* v_size_1569_; lean_object* v_k_1570_; lean_object* v_v_1571_; lean_object* v_l_1572_; lean_object* v_r_1573_; lean_object* v___x_1574_; 
lean_inc_ref(v_l_1564_);
lean_dec(v_h__2_1562_);
v_size_1565_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_size_1565_);
v_k_1566_ = lean_ctor_get(v_x_1559_, 1);
lean_inc(v_k_1566_);
v_v_1567_ = lean_ctor_get(v_x_1559_, 2);
lean_inc(v_v_1567_);
v_r_1568_ = lean_ctor_get(v_x_1559_, 4);
lean_inc(v_r_1568_);
lean_dec_ref(v_x_1559_);
v_size_1569_ = lean_ctor_get(v_l_1564_, 0);
lean_inc(v_size_1569_);
v_k_1570_ = lean_ctor_get(v_l_1564_, 1);
lean_inc(v_k_1570_);
v_v_1571_ = lean_ctor_get(v_l_1564_, 2);
lean_inc(v_v_1571_);
v_l_1572_ = lean_ctor_get(v_l_1564_, 3);
lean_inc(v_l_1572_);
v_r_1573_ = lean_ctor_get(v_l_1564_, 4);
lean_inc(v_r_1573_);
lean_dec_ref(v_l_1564_);
v___x_1574_ = lean_apply_10(v_h__3_1563_, v_size_1565_, v_k_1566_, v_v_1567_, v_size_1569_, v_k_1570_, v_v_1571_, v_l_1572_, v_r_1573_, v_r_1568_, v_x_1560_);
return v___x_1574_;
}
else
{
lean_object* v_size_1575_; lean_object* v_k_1576_; lean_object* v_v_1577_; lean_object* v_r_1578_; lean_object* v___x_1579_; 
lean_dec(v_h__3_1563_);
v_size_1575_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_size_1575_);
v_k_1576_ = lean_ctor_get(v_x_1559_, 1);
lean_inc(v_k_1576_);
v_v_1577_ = lean_ctor_get(v_x_1559_, 2);
lean_inc(v_v_1577_);
v_r_1578_ = lean_ctor_get(v_x_1559_, 4);
lean_inc(v_r_1578_);
lean_dec_ref(v_x_1559_);
v___x_1579_ = lean_apply_5(v_h__2_1562_, v_size_1575_, v_k_1576_, v_v_1577_, v_r_1578_, v_x_1560_);
return v___x_1579_;
}
}
else
{
lean_object* v___x_1580_; 
lean_dec(v_h__3_1563_);
lean_dec(v_h__2_1562_);
v___x_1580_ = lean_apply_1(v_h__1_1561_, v_x_1560_);
return v___x_1580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* v_x_1581_, lean_object* v_h__1_1582_, lean_object* v_h__2_1583_){
_start:
{
lean_object* v_l_1584_; 
v_l_1584_ = lean_ctor_get(v_x_1581_, 3);
if (lean_obj_tag(v_l_1584_) == 0)
{
lean_object* v_size_1585_; lean_object* v_k_1586_; lean_object* v_v_1587_; lean_object* v_r_1588_; lean_object* v_size_1589_; lean_object* v_k_1590_; lean_object* v_v_1591_; lean_object* v_l_1592_; lean_object* v_r_1593_; lean_object* v___x_1594_; 
lean_inc_ref(v_l_1584_);
lean_dec(v_h__1_1582_);
v_size_1585_ = lean_ctor_get(v_x_1581_, 0);
lean_inc(v_size_1585_);
v_k_1586_ = lean_ctor_get(v_x_1581_, 1);
lean_inc(v_k_1586_);
v_v_1587_ = lean_ctor_get(v_x_1581_, 2);
lean_inc(v_v_1587_);
v_r_1588_ = lean_ctor_get(v_x_1581_, 4);
lean_inc(v_r_1588_);
lean_dec(v_x_1581_);
v_size_1589_ = lean_ctor_get(v_l_1584_, 0);
lean_inc(v_size_1589_);
v_k_1590_ = lean_ctor_get(v_l_1584_, 1);
lean_inc(v_k_1590_);
v_v_1591_ = lean_ctor_get(v_l_1584_, 2);
lean_inc(v_v_1591_);
v_l_1592_ = lean_ctor_get(v_l_1584_, 3);
lean_inc(v_l_1592_);
v_r_1593_ = lean_ctor_get(v_l_1584_, 4);
lean_inc(v_r_1593_);
lean_dec_ref(v_l_1584_);
v___x_1594_ = lean_apply_10(v_h__2_1583_, v_size_1585_, v_k_1586_, v_v_1587_, v_size_1589_, v_k_1590_, v_v_1591_, v_l_1592_, v_r_1593_, v_r_1588_, lean_box(0));
return v___x_1594_;
}
else
{
lean_object* v_size_1595_; lean_object* v_k_1596_; lean_object* v_v_1597_; lean_object* v_r_1598_; lean_object* v___x_1599_; 
lean_dec(v_h__2_1583_);
v_size_1595_ = lean_ctor_get(v_x_1581_, 0);
lean_inc(v_size_1595_);
v_k_1596_ = lean_ctor_get(v_x_1581_, 1);
lean_inc(v_k_1596_);
v_v_1597_ = lean_ctor_get(v_x_1581_, 2);
lean_inc(v_v_1597_);
v_r_1598_ = lean_ctor_get(v_x_1581_, 4);
lean_inc(v_r_1598_);
lean_dec(v_x_1581_);
v___x_1599_ = lean_apply_5(v_h__1_1582_, v_size_1595_, v_k_1596_, v_v_1597_, v_r_1598_, lean_box(0));
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* v_00_u03b1_1600_, lean_object* v_00_u03b2_1601_, lean_object* v_motive_1602_, lean_object* v_x_1603_, lean_object* v_x_1604_, lean_object* v_h__1_1605_, lean_object* v_h__2_1606_){
_start:
{
lean_object* v_l_1607_; 
v_l_1607_ = lean_ctor_get(v_x_1603_, 3);
if (lean_obj_tag(v_l_1607_) == 0)
{
lean_object* v_size_1608_; lean_object* v_k_1609_; lean_object* v_v_1610_; lean_object* v_r_1611_; lean_object* v_size_1612_; lean_object* v_k_1613_; lean_object* v_v_1614_; lean_object* v_l_1615_; lean_object* v_r_1616_; lean_object* v___x_1617_; 
lean_inc_ref(v_l_1607_);
lean_dec(v_h__1_1605_);
v_size_1608_ = lean_ctor_get(v_x_1603_, 0);
lean_inc(v_size_1608_);
v_k_1609_ = lean_ctor_get(v_x_1603_, 1);
lean_inc(v_k_1609_);
v_v_1610_ = lean_ctor_get(v_x_1603_, 2);
lean_inc(v_v_1610_);
v_r_1611_ = lean_ctor_get(v_x_1603_, 4);
lean_inc(v_r_1611_);
lean_dec(v_x_1603_);
v_size_1612_ = lean_ctor_get(v_l_1607_, 0);
lean_inc(v_size_1612_);
v_k_1613_ = lean_ctor_get(v_l_1607_, 1);
lean_inc(v_k_1613_);
v_v_1614_ = lean_ctor_get(v_l_1607_, 2);
lean_inc(v_v_1614_);
v_l_1615_ = lean_ctor_get(v_l_1607_, 3);
lean_inc(v_l_1615_);
v_r_1616_ = lean_ctor_get(v_l_1607_, 4);
lean_inc(v_r_1616_);
lean_dec_ref(v_l_1607_);
v___x_1617_ = lean_apply_10(v_h__2_1606_, v_size_1608_, v_k_1609_, v_v_1610_, v_size_1612_, v_k_1613_, v_v_1614_, v_l_1615_, v_r_1616_, v_r_1611_, lean_box(0));
return v___x_1617_;
}
else
{
lean_object* v_size_1618_; lean_object* v_k_1619_; lean_object* v_v_1620_; lean_object* v_r_1621_; lean_object* v___x_1622_; 
lean_dec(v_h__2_1606_);
v_size_1618_ = lean_ctor_get(v_x_1603_, 0);
lean_inc(v_size_1618_);
v_k_1619_ = lean_ctor_get(v_x_1603_, 1);
lean_inc(v_k_1619_);
v_v_1620_ = lean_ctor_get(v_x_1603_, 2);
lean_inc(v_v_1620_);
v_r_1621_ = lean_ctor_get(v_x_1603_, 4);
lean_inc(v_r_1621_);
lean_dec(v_x_1603_);
v___x_1622_ = lean_apply_5(v_h__1_1605_, v_size_1618_, v_k_1619_, v_v_1620_, v_r_1621_, lean_box(0));
return v___x_1622_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1623_, lean_object* v_h__1_1624_, lean_object* v_h__2_1625_, lean_object* v_h__3_1626_){
_start:
{
if (lean_obj_tag(v_x_1623_) == 0)
{
lean_object* v_r_1627_; 
lean_dec(v_h__1_1624_);
v_r_1627_ = lean_ctor_get(v_x_1623_, 4);
if (lean_obj_tag(v_r_1627_) == 0)
{
lean_object* v_size_1628_; lean_object* v_k_1629_; lean_object* v_v_1630_; lean_object* v_l_1631_; lean_object* v_size_1632_; lean_object* v_k_1633_; lean_object* v_v_1634_; lean_object* v_l_1635_; lean_object* v_r_1636_; lean_object* v___x_1637_; 
lean_inc_ref(v_r_1627_);
lean_dec(v_h__2_1625_);
v_size_1628_ = lean_ctor_get(v_x_1623_, 0);
lean_inc(v_size_1628_);
v_k_1629_ = lean_ctor_get(v_x_1623_, 1);
lean_inc(v_k_1629_);
v_v_1630_ = lean_ctor_get(v_x_1623_, 2);
lean_inc(v_v_1630_);
v_l_1631_ = lean_ctor_get(v_x_1623_, 3);
lean_inc(v_l_1631_);
lean_dec_ref(v_x_1623_);
v_size_1632_ = lean_ctor_get(v_r_1627_, 0);
lean_inc(v_size_1632_);
v_k_1633_ = lean_ctor_get(v_r_1627_, 1);
lean_inc(v_k_1633_);
v_v_1634_ = lean_ctor_get(v_r_1627_, 2);
lean_inc(v_v_1634_);
v_l_1635_ = lean_ctor_get(v_r_1627_, 3);
lean_inc(v_l_1635_);
v_r_1636_ = lean_ctor_get(v_r_1627_, 4);
lean_inc(v_r_1636_);
lean_dec_ref(v_r_1627_);
v___x_1637_ = lean_apply_9(v_h__3_1626_, v_size_1628_, v_k_1629_, v_v_1630_, v_l_1631_, v_size_1632_, v_k_1633_, v_v_1634_, v_l_1635_, v_r_1636_);
return v___x_1637_;
}
else
{
lean_object* v_size_1638_; lean_object* v_k_1639_; lean_object* v_v_1640_; lean_object* v_l_1641_; lean_object* v___x_1642_; 
lean_dec(v_h__3_1626_);
v_size_1638_ = lean_ctor_get(v_x_1623_, 0);
lean_inc(v_size_1638_);
v_k_1639_ = lean_ctor_get(v_x_1623_, 1);
lean_inc(v_k_1639_);
v_v_1640_ = lean_ctor_get(v_x_1623_, 2);
lean_inc(v_v_1640_);
v_l_1641_ = lean_ctor_get(v_x_1623_, 3);
lean_inc(v_l_1641_);
lean_dec_ref(v_x_1623_);
v___x_1642_ = lean_apply_4(v_h__2_1625_, v_size_1638_, v_k_1639_, v_v_1640_, v_l_1641_);
return v___x_1642_;
}
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_dec(v_h__3_1626_);
lean_dec(v_h__2_1625_);
v___x_1643_ = lean_box(0);
v___x_1644_ = lean_apply_1(v_h__1_1624_, v___x_1643_);
return v___x_1644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1645_, lean_object* v_00_u03b2_1646_, lean_object* v_motive_1647_, lean_object* v_x_1648_, lean_object* v_h__1_1649_, lean_object* v_h__2_1650_, lean_object* v_h__3_1651_){
_start:
{
if (lean_obj_tag(v_x_1648_) == 0)
{
lean_object* v_r_1652_; 
lean_dec(v_h__1_1649_);
v_r_1652_ = lean_ctor_get(v_x_1648_, 4);
if (lean_obj_tag(v_r_1652_) == 0)
{
lean_object* v_size_1653_; lean_object* v_k_1654_; lean_object* v_v_1655_; lean_object* v_l_1656_; lean_object* v_size_1657_; lean_object* v_k_1658_; lean_object* v_v_1659_; lean_object* v_l_1660_; lean_object* v_r_1661_; lean_object* v___x_1662_; 
lean_inc_ref(v_r_1652_);
lean_dec(v_h__2_1650_);
v_size_1653_ = lean_ctor_get(v_x_1648_, 0);
lean_inc(v_size_1653_);
v_k_1654_ = lean_ctor_get(v_x_1648_, 1);
lean_inc(v_k_1654_);
v_v_1655_ = lean_ctor_get(v_x_1648_, 2);
lean_inc(v_v_1655_);
v_l_1656_ = lean_ctor_get(v_x_1648_, 3);
lean_inc(v_l_1656_);
lean_dec_ref(v_x_1648_);
v_size_1657_ = lean_ctor_get(v_r_1652_, 0);
lean_inc(v_size_1657_);
v_k_1658_ = lean_ctor_get(v_r_1652_, 1);
lean_inc(v_k_1658_);
v_v_1659_ = lean_ctor_get(v_r_1652_, 2);
lean_inc(v_v_1659_);
v_l_1660_ = lean_ctor_get(v_r_1652_, 3);
lean_inc(v_l_1660_);
v_r_1661_ = lean_ctor_get(v_r_1652_, 4);
lean_inc(v_r_1661_);
lean_dec_ref(v_r_1652_);
v___x_1662_ = lean_apply_9(v_h__3_1651_, v_size_1653_, v_k_1654_, v_v_1655_, v_l_1656_, v_size_1657_, v_k_1658_, v_v_1659_, v_l_1660_, v_r_1661_);
return v___x_1662_;
}
else
{
lean_object* v_size_1663_; lean_object* v_k_1664_; lean_object* v_v_1665_; lean_object* v_l_1666_; lean_object* v___x_1667_; 
lean_dec(v_h__3_1651_);
v_size_1663_ = lean_ctor_get(v_x_1648_, 0);
lean_inc(v_size_1663_);
v_k_1664_ = lean_ctor_get(v_x_1648_, 1);
lean_inc(v_k_1664_);
v_v_1665_ = lean_ctor_get(v_x_1648_, 2);
lean_inc(v_v_1665_);
v_l_1666_ = lean_ctor_get(v_x_1648_, 3);
lean_inc(v_l_1666_);
lean_dec_ref(v_x_1648_);
v___x_1667_ = lean_apply_4(v_h__2_1650_, v_size_1663_, v_k_1664_, v_v_1665_, v_l_1666_);
return v___x_1667_;
}
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec(v_h__3_1651_);
lean_dec(v_h__2_1650_);
v___x_1668_ = lean_box(0);
v___x_1669_ = lean_apply_1(v_h__1_1649_, v___x_1668_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1670_, lean_object* v_x_1671_, lean_object* v_h__1_1672_, lean_object* v_h__2_1673_, lean_object* v_h__3_1674_){
_start:
{
if (lean_obj_tag(v_x_1670_) == 0)
{
lean_object* v_r_1675_; 
lean_dec(v_h__1_1672_);
v_r_1675_ = lean_ctor_get(v_x_1670_, 4);
if (lean_obj_tag(v_r_1675_) == 0)
{
lean_object* v_size_1676_; lean_object* v_k_1677_; lean_object* v_v_1678_; lean_object* v_l_1679_; lean_object* v_size_1680_; lean_object* v_k_1681_; lean_object* v_v_1682_; lean_object* v_l_1683_; lean_object* v_r_1684_; lean_object* v___x_1685_; 
lean_inc_ref(v_r_1675_);
lean_dec(v_h__2_1673_);
v_size_1676_ = lean_ctor_get(v_x_1670_, 0);
lean_inc(v_size_1676_);
v_k_1677_ = lean_ctor_get(v_x_1670_, 1);
lean_inc(v_k_1677_);
v_v_1678_ = lean_ctor_get(v_x_1670_, 2);
lean_inc(v_v_1678_);
v_l_1679_ = lean_ctor_get(v_x_1670_, 3);
lean_inc(v_l_1679_);
lean_dec_ref(v_x_1670_);
v_size_1680_ = lean_ctor_get(v_r_1675_, 0);
lean_inc(v_size_1680_);
v_k_1681_ = lean_ctor_get(v_r_1675_, 1);
lean_inc(v_k_1681_);
v_v_1682_ = lean_ctor_get(v_r_1675_, 2);
lean_inc(v_v_1682_);
v_l_1683_ = lean_ctor_get(v_r_1675_, 3);
lean_inc(v_l_1683_);
v_r_1684_ = lean_ctor_get(v_r_1675_, 4);
lean_inc(v_r_1684_);
lean_dec_ref(v_r_1675_);
v___x_1685_ = lean_apply_10(v_h__3_1674_, v_size_1676_, v_k_1677_, v_v_1678_, v_l_1679_, v_size_1680_, v_k_1681_, v_v_1682_, v_l_1683_, v_r_1684_, v_x_1671_);
return v___x_1685_;
}
else
{
lean_object* v_size_1686_; lean_object* v_k_1687_; lean_object* v_v_1688_; lean_object* v_l_1689_; lean_object* v___x_1690_; 
lean_dec(v_h__3_1674_);
v_size_1686_ = lean_ctor_get(v_x_1670_, 0);
lean_inc(v_size_1686_);
v_k_1687_ = lean_ctor_get(v_x_1670_, 1);
lean_inc(v_k_1687_);
v_v_1688_ = lean_ctor_get(v_x_1670_, 2);
lean_inc(v_v_1688_);
v_l_1689_ = lean_ctor_get(v_x_1670_, 3);
lean_inc(v_l_1689_);
lean_dec_ref(v_x_1670_);
v___x_1690_ = lean_apply_5(v_h__2_1673_, v_size_1686_, v_k_1687_, v_v_1688_, v_l_1689_, v_x_1671_);
return v___x_1690_;
}
}
else
{
lean_object* v___x_1691_; 
lean_dec(v_h__3_1674_);
lean_dec(v_h__2_1673_);
v___x_1691_ = lean_apply_1(v_h__1_1672_, v_x_1671_);
return v___x_1691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1692_, lean_object* v_00_u03b2_1693_, lean_object* v_motive_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_, lean_object* v_h__1_1697_, lean_object* v_h__2_1698_, lean_object* v_h__3_1699_){
_start:
{
if (lean_obj_tag(v_x_1695_) == 0)
{
lean_object* v_r_1700_; 
lean_dec(v_h__1_1697_);
v_r_1700_ = lean_ctor_get(v_x_1695_, 4);
if (lean_obj_tag(v_r_1700_) == 0)
{
lean_object* v_size_1701_; lean_object* v_k_1702_; lean_object* v_v_1703_; lean_object* v_l_1704_; lean_object* v_size_1705_; lean_object* v_k_1706_; lean_object* v_v_1707_; lean_object* v_l_1708_; lean_object* v_r_1709_; lean_object* v___x_1710_; 
lean_inc_ref(v_r_1700_);
lean_dec(v_h__2_1698_);
v_size_1701_ = lean_ctor_get(v_x_1695_, 0);
lean_inc(v_size_1701_);
v_k_1702_ = lean_ctor_get(v_x_1695_, 1);
lean_inc(v_k_1702_);
v_v_1703_ = lean_ctor_get(v_x_1695_, 2);
lean_inc(v_v_1703_);
v_l_1704_ = lean_ctor_get(v_x_1695_, 3);
lean_inc(v_l_1704_);
lean_dec_ref(v_x_1695_);
v_size_1705_ = lean_ctor_get(v_r_1700_, 0);
lean_inc(v_size_1705_);
v_k_1706_ = lean_ctor_get(v_r_1700_, 1);
lean_inc(v_k_1706_);
v_v_1707_ = lean_ctor_get(v_r_1700_, 2);
lean_inc(v_v_1707_);
v_l_1708_ = lean_ctor_get(v_r_1700_, 3);
lean_inc(v_l_1708_);
v_r_1709_ = lean_ctor_get(v_r_1700_, 4);
lean_inc(v_r_1709_);
lean_dec_ref(v_r_1700_);
v___x_1710_ = lean_apply_10(v_h__3_1699_, v_size_1701_, v_k_1702_, v_v_1703_, v_l_1704_, v_size_1705_, v_k_1706_, v_v_1707_, v_l_1708_, v_r_1709_, v_x_1696_);
return v___x_1710_;
}
else
{
lean_object* v_size_1711_; lean_object* v_k_1712_; lean_object* v_v_1713_; lean_object* v_l_1714_; lean_object* v___x_1715_; 
lean_dec(v_h__3_1699_);
v_size_1711_ = lean_ctor_get(v_x_1695_, 0);
lean_inc(v_size_1711_);
v_k_1712_ = lean_ctor_get(v_x_1695_, 1);
lean_inc(v_k_1712_);
v_v_1713_ = lean_ctor_get(v_x_1695_, 2);
lean_inc(v_v_1713_);
v_l_1714_ = lean_ctor_get(v_x_1695_, 3);
lean_inc(v_l_1714_);
lean_dec_ref(v_x_1695_);
v___x_1715_ = lean_apply_5(v_h__2_1698_, v_size_1711_, v_k_1712_, v_v_1713_, v_l_1714_, v_x_1696_);
return v___x_1715_;
}
}
else
{
lean_object* v___x_1716_; 
lean_dec(v_h__3_1699_);
lean_dec(v_h__2_1698_);
v___x_1716_ = lean_apply_1(v_h__1_1697_, v_x_1696_);
return v___x_1716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* v_x_1717_, lean_object* v_h__1_1718_, lean_object* v_h__2_1719_){
_start:
{
lean_object* v_r_1720_; 
v_r_1720_ = lean_ctor_get(v_x_1717_, 4);
if (lean_obj_tag(v_r_1720_) == 0)
{
lean_object* v_size_1721_; lean_object* v_k_1722_; lean_object* v_v_1723_; lean_object* v_l_1724_; lean_object* v_size_1725_; lean_object* v_k_1726_; lean_object* v_v_1727_; lean_object* v_l_1728_; lean_object* v_r_1729_; lean_object* v___x_1730_; 
lean_inc_ref(v_r_1720_);
lean_dec(v_h__1_1718_);
v_size_1721_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_size_1721_);
v_k_1722_ = lean_ctor_get(v_x_1717_, 1);
lean_inc(v_k_1722_);
v_v_1723_ = lean_ctor_get(v_x_1717_, 2);
lean_inc(v_v_1723_);
v_l_1724_ = lean_ctor_get(v_x_1717_, 3);
lean_inc(v_l_1724_);
lean_dec(v_x_1717_);
v_size_1725_ = lean_ctor_get(v_r_1720_, 0);
lean_inc(v_size_1725_);
v_k_1726_ = lean_ctor_get(v_r_1720_, 1);
lean_inc(v_k_1726_);
v_v_1727_ = lean_ctor_get(v_r_1720_, 2);
lean_inc(v_v_1727_);
v_l_1728_ = lean_ctor_get(v_r_1720_, 3);
lean_inc(v_l_1728_);
v_r_1729_ = lean_ctor_get(v_r_1720_, 4);
lean_inc(v_r_1729_);
lean_dec_ref(v_r_1720_);
v___x_1730_ = lean_apply_10(v_h__2_1719_, v_size_1721_, v_k_1722_, v_v_1723_, v_l_1724_, v_size_1725_, v_k_1726_, v_v_1727_, v_l_1728_, v_r_1729_, lean_box(0));
return v___x_1730_;
}
else
{
lean_object* v_size_1731_; lean_object* v_k_1732_; lean_object* v_v_1733_; lean_object* v_l_1734_; lean_object* v___x_1735_; 
lean_dec(v_h__2_1719_);
v_size_1731_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_size_1731_);
v_k_1732_ = lean_ctor_get(v_x_1717_, 1);
lean_inc(v_k_1732_);
v_v_1733_ = lean_ctor_get(v_x_1717_, 2);
lean_inc(v_v_1733_);
v_l_1734_ = lean_ctor_get(v_x_1717_, 3);
lean_inc(v_l_1734_);
lean_dec(v_x_1717_);
v___x_1735_ = lean_apply_5(v_h__1_1718_, v_size_1731_, v_k_1732_, v_v_1733_, v_l_1734_, lean_box(0));
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1736_, lean_object* v_00_u03b2_1737_, lean_object* v_motive_1738_, lean_object* v_x_1739_, lean_object* v_x_1740_, lean_object* v_h__1_1741_, lean_object* v_h__2_1742_){
_start:
{
lean_object* v_r_1743_; 
v_r_1743_ = lean_ctor_get(v_x_1739_, 4);
if (lean_obj_tag(v_r_1743_) == 0)
{
lean_object* v_size_1744_; lean_object* v_k_1745_; lean_object* v_v_1746_; lean_object* v_l_1747_; lean_object* v_size_1748_; lean_object* v_k_1749_; lean_object* v_v_1750_; lean_object* v_l_1751_; lean_object* v_r_1752_; lean_object* v___x_1753_; 
lean_inc_ref(v_r_1743_);
lean_dec(v_h__1_1741_);
v_size_1744_ = lean_ctor_get(v_x_1739_, 0);
lean_inc(v_size_1744_);
v_k_1745_ = lean_ctor_get(v_x_1739_, 1);
lean_inc(v_k_1745_);
v_v_1746_ = lean_ctor_get(v_x_1739_, 2);
lean_inc(v_v_1746_);
v_l_1747_ = lean_ctor_get(v_x_1739_, 3);
lean_inc(v_l_1747_);
lean_dec(v_x_1739_);
v_size_1748_ = lean_ctor_get(v_r_1743_, 0);
lean_inc(v_size_1748_);
v_k_1749_ = lean_ctor_get(v_r_1743_, 1);
lean_inc(v_k_1749_);
v_v_1750_ = lean_ctor_get(v_r_1743_, 2);
lean_inc(v_v_1750_);
v_l_1751_ = lean_ctor_get(v_r_1743_, 3);
lean_inc(v_l_1751_);
v_r_1752_ = lean_ctor_get(v_r_1743_, 4);
lean_inc(v_r_1752_);
lean_dec_ref(v_r_1743_);
v___x_1753_ = lean_apply_10(v_h__2_1742_, v_size_1744_, v_k_1745_, v_v_1746_, v_l_1747_, v_size_1748_, v_k_1749_, v_v_1750_, v_l_1751_, v_r_1752_, lean_box(0));
return v___x_1753_;
}
else
{
lean_object* v_size_1754_; lean_object* v_k_1755_; lean_object* v_v_1756_; lean_object* v_l_1757_; lean_object* v___x_1758_; 
lean_dec(v_h__2_1742_);
v_size_1754_ = lean_ctor_get(v_x_1739_, 0);
lean_inc(v_size_1754_);
v_k_1755_ = lean_ctor_get(v_x_1739_, 1);
lean_inc(v_k_1755_);
v_v_1756_ = lean_ctor_get(v_x_1739_, 2);
lean_inc(v_v_1756_);
v_l_1757_ = lean_ctor_get(v_x_1739_, 3);
lean_inc(v_l_1757_);
lean_dec(v_x_1739_);
v___x_1758_ = lean_apply_5(v_h__1_1741_, v_size_1754_, v_k_1755_, v_v_1756_, v_l_1757_, lean_box(0));
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object* v_l_1759_, lean_object* v_h__1_1760_, lean_object* v_h__2_1761_){
_start:
{
if (lean_obj_tag(v_l_1759_) == 0)
{
lean_object* v_size_1762_; lean_object* v_k_1763_; lean_object* v_v_1764_; lean_object* v_l_1765_; lean_object* v_r_1766_; lean_object* v___x_1767_; 
lean_dec(v_h__1_1760_);
v_size_1762_ = lean_ctor_get(v_l_1759_, 0);
lean_inc(v_size_1762_);
v_k_1763_ = lean_ctor_get(v_l_1759_, 1);
lean_inc(v_k_1763_);
v_v_1764_ = lean_ctor_get(v_l_1759_, 2);
lean_inc(v_v_1764_);
v_l_1765_ = lean_ctor_get(v_l_1759_, 3);
lean_inc(v_l_1765_);
v_r_1766_ = lean_ctor_get(v_l_1759_, 4);
lean_inc(v_r_1766_);
lean_dec_ref(v_l_1759_);
v___x_1767_ = lean_apply_7(v_h__2_1761_, v_size_1762_, v_k_1763_, v_v_1764_, v_l_1765_, v_r_1766_, lean_box(0), lean_box(0));
return v___x_1767_;
}
else
{
lean_object* v___x_1768_; 
lean_dec(v_h__2_1761_);
v___x_1768_ = lean_apply_2(v_h__1_1760_, lean_box(0), lean_box(0));
return v___x_1768_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object* v_00_u03b1_1769_, lean_object* v_00_u03b2_1770_, lean_object* v_r_1771_, lean_object* v_motive_1772_, lean_object* v_l_1773_, lean_object* v_hl_1774_, lean_object* v_hlr_1775_, lean_object* v_h__1_1776_, lean_object* v_h__2_1777_){
_start:
{
if (lean_obj_tag(v_l_1773_) == 0)
{
lean_object* v_size_1778_; lean_object* v_k_1779_; lean_object* v_v_1780_; lean_object* v_l_1781_; lean_object* v_r_1782_; lean_object* v___x_1783_; 
lean_dec(v_h__1_1776_);
v_size_1778_ = lean_ctor_get(v_l_1773_, 0);
lean_inc(v_size_1778_);
v_k_1779_ = lean_ctor_get(v_l_1773_, 1);
lean_inc(v_k_1779_);
v_v_1780_ = lean_ctor_get(v_l_1773_, 2);
lean_inc(v_v_1780_);
v_l_1781_ = lean_ctor_get(v_l_1773_, 3);
lean_inc(v_l_1781_);
v_r_1782_ = lean_ctor_get(v_l_1773_, 4);
lean_inc(v_r_1782_);
lean_dec_ref(v_l_1773_);
v___x_1783_ = lean_apply_7(v_h__2_1777_, v_size_1778_, v_k_1779_, v_v_1780_, v_l_1781_, v_r_1782_, lean_box(0), lean_box(0));
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; 
lean_dec(v_h__2_1777_);
v___x_1784_ = lean_apply_2(v_h__1_1776_, lean_box(0), lean_box(0));
return v___x_1784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object* v_00_u03b1_1785_, lean_object* v_00_u03b2_1786_, lean_object* v_r_1787_, lean_object* v_motive_1788_, lean_object* v_l_1789_, lean_object* v_hl_1790_, lean_object* v_hlr_1791_, lean_object* v_h__1_1792_, lean_object* v_h__2_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(v_00_u03b1_1785_, v_00_u03b2_1786_, v_r_1787_, v_motive_1788_, v_l_1789_, v_hl_1790_, v_hlr_1791_, v_h__1_1792_, v_h__2_1793_);
lean_dec(v_r_1787_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(lean_object* v_x_1795_, lean_object* v_h__1_1796_){
_start:
{
lean_object* v_k_1797_; lean_object* v_v_1798_; lean_object* v_tree_1799_; lean_object* v___x_1800_; 
v_k_1797_ = lean_ctor_get(v_x_1795_, 0);
lean_inc(v_k_1797_);
v_v_1798_ = lean_ctor_get(v_x_1795_, 1);
lean_inc(v_v_1798_);
v_tree_1799_ = lean_ctor_get(v_x_1795_, 2);
lean_inc(v_tree_1799_);
lean_dec_ref(v_x_1795_);
v___x_1800_ = lean_apply_5(v_h__1_1796_, v_k_1797_, v_v_1798_, v_tree_1799_, lean_box(0), lean_box(0));
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object* v_00_u03b1_1801_, lean_object* v_00_u03b2_1802_, lean_object* v_l_x27_1803_, lean_object* v_r_x27_1804_, lean_object* v_motive_1805_, lean_object* v_x_1806_, lean_object* v_h__1_1807_){
_start:
{
lean_object* v_k_1808_; lean_object* v_v_1809_; lean_object* v_tree_1810_; lean_object* v___x_1811_; 
v_k_1808_ = lean_ctor_get(v_x_1806_, 0);
lean_inc(v_k_1808_);
v_v_1809_ = lean_ctor_get(v_x_1806_, 1);
lean_inc(v_v_1809_);
v_tree_1810_ = lean_ctor_get(v_x_1806_, 2);
lean_inc(v_tree_1810_);
lean_dec_ref(v_x_1806_);
v___x_1811_ = lean_apply_5(v_h__1_1807_, v_k_1808_, v_v_1809_, v_tree_1810_, lean_box(0), lean_box(0));
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object* v_00_u03b1_1812_, lean_object* v_00_u03b2_1813_, lean_object* v_l_x27_1814_, lean_object* v_r_x27_1815_, lean_object* v_motive_1816_, lean_object* v_x_1817_, lean_object* v_h__1_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(v_00_u03b1_1812_, v_00_u03b2_1813_, v_l_x27_1814_, v_r_x27_1815_, v_motive_1816_, v_x_1817_, v_h__1_1818_);
lean_dec(v_r_x27_1815_);
lean_dec(v_l_x27_1814_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object* v_l_1820_, lean_object* v_h__1_1821_, lean_object* v_h__2_1822_){
_start:
{
if (lean_obj_tag(v_l_1820_) == 0)
{
lean_object* v_size_1823_; lean_object* v_k_1824_; lean_object* v_v_1825_; lean_object* v_l_1826_; lean_object* v_r_1827_; lean_object* v___x_1828_; 
lean_dec(v_h__1_1821_);
v_size_1823_ = lean_ctor_get(v_l_1820_, 0);
lean_inc(v_size_1823_);
v_k_1824_ = lean_ctor_get(v_l_1820_, 1);
lean_inc(v_k_1824_);
v_v_1825_ = lean_ctor_get(v_l_1820_, 2);
lean_inc(v_v_1825_);
v_l_1826_ = lean_ctor_get(v_l_1820_, 3);
lean_inc(v_l_1826_);
v_r_1827_ = lean_ctor_get(v_l_1820_, 4);
lean_inc(v_r_1827_);
lean_dec_ref(v_l_1820_);
v___x_1828_ = lean_apply_5(v_h__2_1822_, v_size_1823_, v_k_1824_, v_v_1825_, v_l_1826_, v_r_1827_);
return v___x_1828_;
}
else
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec(v_h__2_1822_);
v___x_1829_ = lean_box(0);
v___x_1830_ = lean_apply_1(v_h__1_1821_, v___x_1829_);
return v___x_1830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object* v_00_u03b1_1831_, lean_object* v_00_u03b2_1832_, lean_object* v_motive_1833_, lean_object* v_l_1834_, lean_object* v_h__1_1835_, lean_object* v_h__2_1836_){
_start:
{
if (lean_obj_tag(v_l_1834_) == 0)
{
lean_object* v_size_1837_; lean_object* v_k_1838_; lean_object* v_v_1839_; lean_object* v_l_1840_; lean_object* v_r_1841_; lean_object* v___x_1842_; 
lean_dec(v_h__1_1835_);
v_size_1837_ = lean_ctor_get(v_l_1834_, 0);
lean_inc(v_size_1837_);
v_k_1838_ = lean_ctor_get(v_l_1834_, 1);
lean_inc(v_k_1838_);
v_v_1839_ = lean_ctor_get(v_l_1834_, 2);
lean_inc(v_v_1839_);
v_l_1840_ = lean_ctor_get(v_l_1834_, 3);
lean_inc(v_l_1840_);
v_r_1841_ = lean_ctor_get(v_l_1834_, 4);
lean_inc(v_r_1841_);
lean_dec_ref(v_l_1834_);
v___x_1842_ = lean_apply_5(v_h__2_1836_, v_size_1837_, v_k_1838_, v_v_1839_, v_l_1840_, v_r_1841_);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec(v_h__2_1836_);
v___x_1843_ = lean_box(0);
v___x_1844_ = lean_apply_1(v_h__1_1835_, v___x_1843_);
return v___x_1844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(lean_object* v_r_1845_, lean_object* v_h__1_1846_, lean_object* v_h__2_1847_){
_start:
{
if (lean_obj_tag(v_r_1845_) == 0)
{
lean_object* v_size_1848_; lean_object* v_k_1849_; lean_object* v_v_1850_; lean_object* v_l_1851_; lean_object* v_r_1852_; lean_object* v___x_1853_; 
lean_dec(v_h__1_1846_);
v_size_1848_ = lean_ctor_get(v_r_1845_, 0);
lean_inc(v_size_1848_);
v_k_1849_ = lean_ctor_get(v_r_1845_, 1);
lean_inc(v_k_1849_);
v_v_1850_ = lean_ctor_get(v_r_1845_, 2);
lean_inc(v_v_1850_);
v_l_1851_ = lean_ctor_get(v_r_1845_, 3);
lean_inc(v_l_1851_);
v_r_1852_ = lean_ctor_get(v_r_1845_, 4);
lean_inc(v_r_1852_);
lean_dec_ref(v_r_1845_);
v___x_1853_ = lean_apply_7(v_h__2_1847_, v_size_1848_, v_k_1849_, v_v_1850_, v_l_1851_, v_r_1852_, lean_box(0), lean_box(0));
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; 
lean_dec(v_h__2_1847_);
v___x_1854_ = lean_apply_2(v_h__1_1846_, lean_box(0), lean_box(0));
return v___x_1854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object* v_00_u03b1_1855_, lean_object* v_00_u03b2_1856_, lean_object* v_l_1857_, lean_object* v_motive_1858_, lean_object* v_r_1859_, lean_object* v_hr_1860_, lean_object* v_hlr_1861_, lean_object* v_h__1_1862_, lean_object* v_h__2_1863_){
_start:
{
if (lean_obj_tag(v_r_1859_) == 0)
{
lean_object* v_size_1864_; lean_object* v_k_1865_; lean_object* v_v_1866_; lean_object* v_l_1867_; lean_object* v_r_1868_; lean_object* v___x_1869_; 
lean_dec(v_h__1_1862_);
v_size_1864_ = lean_ctor_get(v_r_1859_, 0);
lean_inc(v_size_1864_);
v_k_1865_ = lean_ctor_get(v_r_1859_, 1);
lean_inc(v_k_1865_);
v_v_1866_ = lean_ctor_get(v_r_1859_, 2);
lean_inc(v_v_1866_);
v_l_1867_ = lean_ctor_get(v_r_1859_, 3);
lean_inc(v_l_1867_);
v_r_1868_ = lean_ctor_get(v_r_1859_, 4);
lean_inc(v_r_1868_);
lean_dec_ref(v_r_1859_);
v___x_1869_ = lean_apply_7(v_h__2_1863_, v_size_1864_, v_k_1865_, v_v_1866_, v_l_1867_, v_r_1868_, lean_box(0), lean_box(0));
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; 
lean_dec(v_h__2_1863_);
v___x_1870_ = lean_apply_2(v_h__1_1862_, lean_box(0), lean_box(0));
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object* v_00_u03b1_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_l_1873_, lean_object* v_motive_1874_, lean_object* v_r_1875_, lean_object* v_hr_1876_, lean_object* v_hlr_1877_, lean_object* v_h__1_1878_, lean_object* v_h__2_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(v_00_u03b1_1871_, v_00_u03b2_1872_, v_l_1873_, v_motive_1874_, v_r_1875_, v_hr_1876_, v_hlr_1877_, v_h__1_1878_, v_h__2_1879_);
lean_dec(v_l_1873_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(lean_object* v_r_1881_, lean_object* v_h__1_1882_, lean_object* v_h__2_1883_){
_start:
{
if (lean_obj_tag(v_r_1881_) == 0)
{
lean_object* v_size_1884_; lean_object* v_k_1885_; lean_object* v_v_1886_; lean_object* v_l_1887_; lean_object* v_r_1888_; lean_object* v___x_1889_; 
lean_dec(v_h__1_1882_);
v_size_1884_ = lean_ctor_get(v_r_1881_, 0);
lean_inc(v_size_1884_);
v_k_1885_ = lean_ctor_get(v_r_1881_, 1);
lean_inc(v_k_1885_);
v_v_1886_ = lean_ctor_get(v_r_1881_, 2);
lean_inc(v_v_1886_);
v_l_1887_ = lean_ctor_get(v_r_1881_, 3);
lean_inc(v_l_1887_);
v_r_1888_ = lean_ctor_get(v_r_1881_, 4);
lean_inc(v_r_1888_);
lean_dec_ref(v_r_1881_);
v___x_1889_ = lean_apply_7(v_h__2_1883_, v_size_1884_, v_k_1885_, v_v_1886_, v_l_1887_, v_r_1888_, lean_box(0), lean_box(0));
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; 
lean_dec(v_h__2_1883_);
v___x_1890_ = lean_apply_2(v_h__1_1882_, lean_box(0), lean_box(0));
return v___x_1890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object* v_00_u03b1_1891_, lean_object* v_00_u03b2_1892_, lean_object* v_sz_1893_, lean_object* v_k_1894_, lean_object* v_v_1895_, lean_object* v_l_x27_1896_, lean_object* v_r_x27_1897_, lean_object* v_motive_1898_, lean_object* v_r_1899_, lean_object* v_hr_1900_, lean_object* v_hlr_1901_, lean_object* v_h__1_1902_, lean_object* v_h__2_1903_){
_start:
{
if (lean_obj_tag(v_r_1899_) == 0)
{
lean_object* v_size_1904_; lean_object* v_k_1905_; lean_object* v_v_1906_; lean_object* v_l_1907_; lean_object* v_r_1908_; lean_object* v___x_1909_; 
lean_dec(v_h__1_1902_);
v_size_1904_ = lean_ctor_get(v_r_1899_, 0);
lean_inc(v_size_1904_);
v_k_1905_ = lean_ctor_get(v_r_1899_, 1);
lean_inc(v_k_1905_);
v_v_1906_ = lean_ctor_get(v_r_1899_, 2);
lean_inc(v_v_1906_);
v_l_1907_ = lean_ctor_get(v_r_1899_, 3);
lean_inc(v_l_1907_);
v_r_1908_ = lean_ctor_get(v_r_1899_, 4);
lean_inc(v_r_1908_);
lean_dec_ref(v_r_1899_);
v___x_1909_ = lean_apply_7(v_h__2_1903_, v_size_1904_, v_k_1905_, v_v_1906_, v_l_1907_, v_r_1908_, lean_box(0), lean_box(0));
return v___x_1909_;
}
else
{
lean_object* v___x_1910_; 
lean_dec(v_h__2_1903_);
v___x_1910_ = lean_apply_2(v_h__1_1902_, lean_box(0), lean_box(0));
return v___x_1910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object* v_00_u03b1_1911_, lean_object* v_00_u03b2_1912_, lean_object* v_sz_1913_, lean_object* v_k_1914_, lean_object* v_v_1915_, lean_object* v_l_x27_1916_, lean_object* v_r_x27_1917_, lean_object* v_motive_1918_, lean_object* v_r_1919_, lean_object* v_hr_1920_, lean_object* v_hlr_1921_, lean_object* v_h__1_1922_, lean_object* v_h__2_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(v_00_u03b1_1911_, v_00_u03b2_1912_, v_sz_1913_, v_k_1914_, v_v_1915_, v_l_x27_1916_, v_r_x27_1917_, v_motive_1918_, v_r_1919_, v_hr_1920_, v_hlr_1921_, v_h__1_1922_, v_h__2_1923_);
lean_dec(v_r_x27_1917_);
lean_dec(v_l_x27_1916_);
lean_dec(v_v_1915_);
lean_dec(v_k_1914_);
lean_dec(v_sz_1913_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object* v_t_1925_, lean_object* v_h__1_1926_, lean_object* v_h__2_1927_){
_start:
{
if (lean_obj_tag(v_t_1925_) == 0)
{
lean_object* v_size_1928_; lean_object* v_k_1929_; lean_object* v_v_1930_; lean_object* v_l_1931_; lean_object* v_r_1932_; lean_object* v___x_1933_; 
lean_dec(v_h__1_1926_);
v_size_1928_ = lean_ctor_get(v_t_1925_, 0);
lean_inc(v_size_1928_);
v_k_1929_ = lean_ctor_get(v_t_1925_, 1);
lean_inc(v_k_1929_);
v_v_1930_ = lean_ctor_get(v_t_1925_, 2);
lean_inc(v_v_1930_);
v_l_1931_ = lean_ctor_get(v_t_1925_, 3);
lean_inc(v_l_1931_);
v_r_1932_ = lean_ctor_get(v_t_1925_, 4);
lean_inc(v_r_1932_);
lean_dec_ref(v_t_1925_);
v___x_1933_ = lean_apply_6(v_h__2_1927_, v_size_1928_, v_k_1929_, v_v_1930_, v_l_1931_, v_r_1932_, lean_box(0));
return v___x_1933_;
}
else
{
lean_object* v___x_1934_; 
lean_dec(v_h__2_1927_);
v___x_1934_ = lean_apply_1(v_h__1_1926_, lean_box(0));
return v___x_1934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object* v_00_u03b1_1935_, lean_object* v_00_u03b2_1936_, lean_object* v_motive_1937_, lean_object* v_t_1938_, lean_object* v_hr_1939_, lean_object* v_h__1_1940_, lean_object* v_h__2_1941_){
_start:
{
if (lean_obj_tag(v_t_1938_) == 0)
{
lean_object* v_size_1942_; lean_object* v_k_1943_; lean_object* v_v_1944_; lean_object* v_l_1945_; lean_object* v_r_1946_; lean_object* v___x_1947_; 
lean_dec(v_h__1_1940_);
v_size_1942_ = lean_ctor_get(v_t_1938_, 0);
lean_inc(v_size_1942_);
v_k_1943_ = lean_ctor_get(v_t_1938_, 1);
lean_inc(v_k_1943_);
v_v_1944_ = lean_ctor_get(v_t_1938_, 2);
lean_inc(v_v_1944_);
v_l_1945_ = lean_ctor_get(v_t_1938_, 3);
lean_inc(v_l_1945_);
v_r_1946_ = lean_ctor_get(v_t_1938_, 4);
lean_inc(v_r_1946_);
lean_dec_ref(v_t_1938_);
v___x_1947_ = lean_apply_6(v_h__2_1941_, v_size_1942_, v_k_1943_, v_v_1944_, v_l_1945_, v_r_1946_, lean_box(0));
return v___x_1947_;
}
else
{
lean_object* v___x_1948_; 
lean_dec(v_h__2_1941_);
v___x_1948_ = lean_apply_1(v_h__1_1940_, lean_box(0));
return v___x_1948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t v_x_1949_, lean_object* v_h__1_1950_, lean_object* v_h__2_1951_, lean_object* v_h__3_1952_){
_start:
{
switch(v_x_1949_)
{
case 0:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_dec(v_h__3_1952_);
lean_dec(v_h__2_1951_);
v___x_1953_ = lean_box(0);
v___x_1954_ = lean_apply_1(v_h__1_1950_, v___x_1953_);
return v___x_1954_;
}
case 1:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_dec(v_h__2_1951_);
lean_dec(v_h__1_1950_);
v___x_1955_ = lean_box(0);
v___x_1956_ = lean_apply_1(v_h__3_1952_, v___x_1955_);
return v___x_1956_;
}
default: 
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec(v_h__3_1952_);
lean_dec(v_h__1_1950_);
v___x_1957_ = lean_box(0);
v___x_1958_ = lean_apply_1(v_h__2_1951_, v___x_1957_);
return v___x_1958_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object* v_x_1959_, lean_object* v_h__1_1960_, lean_object* v_h__2_1961_, lean_object* v_h__3_1962_){
_start:
{
uint8_t v_x_36__boxed_1963_; lean_object* v_res_1964_; 
v_x_36__boxed_1963_ = lean_unbox(v_x_1959_);
v_res_1964_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_36__boxed_1963_, v_h__1_1960_, v_h__2_1961_, v_h__3_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object* v_motive_1965_, uint8_t v_x_1966_, lean_object* v_h__1_1967_, lean_object* v_h__2_1968_, lean_object* v_h__3_1969_){
_start:
{
switch(v_x_1966_)
{
case 0:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec(v_h__3_1969_);
lean_dec(v_h__2_1968_);
v___x_1970_ = lean_box(0);
v___x_1971_ = lean_apply_1(v_h__1_1967_, v___x_1970_);
return v___x_1971_;
}
case 1:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_dec(v_h__2_1968_);
lean_dec(v_h__1_1967_);
v___x_1972_ = lean_box(0);
v___x_1973_ = lean_apply_1(v_h__3_1969_, v___x_1972_);
return v___x_1973_;
}
default: 
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_dec(v_h__3_1969_);
lean_dec(v_h__1_1967_);
v___x_1974_ = lean_box(0);
v___x_1975_ = lean_apply_1(v_h__2_1968_, v___x_1974_);
return v___x_1975_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object* v_motive_1976_, lean_object* v_x_1977_, lean_object* v_h__1_1978_, lean_object* v_h__2_1979_, lean_object* v_h__3_1980_){
_start:
{
uint8_t v_x_51__boxed_1981_; lean_object* v_res_1982_; 
v_x_51__boxed_1981_ = lean_unbox(v_x_1977_);
v_res_1982_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_1976_, v_x_51__boxed_1981_, v_h__1_1978_, v_h__2_1979_, v_h__3_1980_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___redArg(lean_object* v_x_1983_, lean_object* v_h__1_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_apply_4(v_h__1_1984_, v_x_1983_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(lean_object* v_00_u03b1_1986_, lean_object* v_00_u03b2_1987_, lean_object* v_l_x27_1988_, lean_object* v_motive_1989_, lean_object* v_x_1990_, lean_object* v_h__1_1991_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_apply_4(v_h__1_1991_, v_x_1990_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___boxed(lean_object* v_00_u03b1_1993_, lean_object* v_00_u03b2_1994_, lean_object* v_l_x27_1995_, lean_object* v_motive_1996_, lean_object* v_x_1997_, lean_object* v_h__1_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(v_00_u03b1_1993_, v_00_u03b2_1994_, v_l_x27_1995_, v_motive_1996_, v_x_1997_, v_h__1_1998_);
lean_dec(v_l_x27_1995_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(lean_object* v_l_2000_, lean_object* v_h__1_2001_, lean_object* v_h__2_2002_){
_start:
{
if (lean_obj_tag(v_l_2000_) == 0)
{
lean_object* v_size_2003_; lean_object* v_k_2004_; lean_object* v_v_2005_; lean_object* v_l_2006_; lean_object* v_r_2007_; lean_object* v___x_2008_; 
lean_dec(v_h__1_2001_);
v_size_2003_ = lean_ctor_get(v_l_2000_, 0);
lean_inc(v_size_2003_);
v_k_2004_ = lean_ctor_get(v_l_2000_, 1);
lean_inc(v_k_2004_);
v_v_2005_ = lean_ctor_get(v_l_2000_, 2);
lean_inc(v_v_2005_);
v_l_2006_ = lean_ctor_get(v_l_2000_, 3);
lean_inc(v_l_2006_);
v_r_2007_ = lean_ctor_get(v_l_2000_, 4);
lean_inc(v_r_2007_);
lean_dec_ref(v_l_2000_);
v___x_2008_ = lean_apply_6(v_h__2_2002_, v_size_2003_, v_k_2004_, v_v_2005_, v_l_2006_, v_r_2007_, lean_box(0));
return v___x_2008_;
}
else
{
lean_object* v___x_2009_; 
lean_dec(v_h__2_2002_);
v___x_2009_ = lean_apply_1(v_h__1_2001_, lean_box(0));
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(lean_object* v_00_u03b1_2010_, lean_object* v_00_u03b2_2011_, lean_object* v_motive_2012_, lean_object* v_l_2013_, lean_object* v_hl_2014_, lean_object* v_h__1_2015_, lean_object* v_h__2_2016_){
_start:
{
if (lean_obj_tag(v_l_2013_) == 0)
{
lean_object* v_size_2017_; lean_object* v_k_2018_; lean_object* v_v_2019_; lean_object* v_l_2020_; lean_object* v_r_2021_; lean_object* v___x_2022_; 
lean_dec(v_h__1_2015_);
v_size_2017_ = lean_ctor_get(v_l_2013_, 0);
lean_inc(v_size_2017_);
v_k_2018_ = lean_ctor_get(v_l_2013_, 1);
lean_inc(v_k_2018_);
v_v_2019_ = lean_ctor_get(v_l_2013_, 2);
lean_inc(v_v_2019_);
v_l_2020_ = lean_ctor_get(v_l_2013_, 3);
lean_inc(v_l_2020_);
v_r_2021_ = lean_ctor_get(v_l_2013_, 4);
lean_inc(v_r_2021_);
lean_dec_ref(v_l_2013_);
v___x_2022_ = lean_apply_6(v_h__2_2016_, v_size_2017_, v_k_2018_, v_v_2019_, v_l_2020_, v_r_2021_, lean_box(0));
return v___x_2022_;
}
else
{
lean_object* v___x_2023_; 
lean_dec(v_h__2_2016_);
v___x_2023_ = lean_apply_1(v_h__1_2015_, lean_box(0));
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object* v_x_2024_, lean_object* v_h__1_2025_, lean_object* v_h__2_2026_){
_start:
{
if (lean_obj_tag(v_x_2024_) == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_dec(v_h__2_2026_);
v___x_2027_ = lean_box(0);
v___x_2028_ = lean_apply_1(v_h__1_2025_, v___x_2027_);
return v___x_2028_;
}
else
{
lean_object* v_val_2029_; lean_object* v_fst_2030_; lean_object* v_snd_2031_; lean_object* v___x_2032_; 
lean_dec(v_h__1_2025_);
v_val_2029_ = lean_ctor_get(v_x_2024_, 0);
lean_inc(v_val_2029_);
lean_dec_ref(v_x_2024_);
v_fst_2030_ = lean_ctor_get(v_val_2029_, 0);
lean_inc(v_fst_2030_);
v_snd_2031_ = lean_ctor_get(v_val_2029_, 1);
lean_inc(v_snd_2031_);
lean_dec(v_val_2029_);
v___x_2032_ = lean_apply_2(v_h__2_2026_, v_fst_2030_, v_snd_2031_);
return v___x_2032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* v_00_u03b1_2033_, lean_object* v_00_u03b2_2034_, lean_object* v_motive_2035_, lean_object* v_x_2036_, lean_object* v_h__1_2037_, lean_object* v_h__2_2038_){
_start:
{
if (lean_obj_tag(v_x_2036_) == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec(v_h__2_2038_);
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_apply_1(v_h__1_2037_, v___x_2039_);
return v___x_2040_;
}
else
{
lean_object* v_val_2041_; lean_object* v_fst_2042_; lean_object* v_snd_2043_; lean_object* v___x_2044_; 
lean_dec(v_h__1_2037_);
v_val_2041_ = lean_ctor_get(v_x_2036_, 0);
lean_inc(v_val_2041_);
lean_dec_ref(v_x_2036_);
v_fst_2042_ = lean_ctor_get(v_val_2041_, 0);
lean_inc(v_fst_2042_);
v_snd_2043_ = lean_ctor_get(v_val_2041_, 1);
lean_inc(v_snd_2043_);
lean_dec(v_val_2041_);
v___x_2044_ = lean_apply_2(v_h__2_2038_, v_fst_2042_, v_snd_2043_);
return v___x_2044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(lean_object* v_x_2045_, lean_object* v_h__1_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_apply_4(v_h__1_2046_, v_x_2045_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object* v_00_u03b1_2048_, lean_object* v_00_u03b2_2049_, lean_object* v_l_2050_, lean_object* v_motive_2051_, lean_object* v_x_2052_, lean_object* v_h__1_2053_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = lean_apply_4(v_h__1_2053_, v_x_2052_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(lean_object* v_00_u03b1_2055_, lean_object* v_00_u03b2_2056_, lean_object* v_l_2057_, lean_object* v_motive_2058_, lean_object* v_x_2059_, lean_object* v_h__1_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_2055_, v_00_u03b2_2056_, v_l_2057_, v_motive_2058_, v_x_2059_, v_h__1_2060_);
lean_dec(v_l_2057_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___redArg(lean_object* v_x_2062_, lean_object* v_h__1_2063_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_apply_4(v_h__1_2063_, v_x_2062_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(lean_object* v_00_u03b1_2065_, lean_object* v_00_u03b2_2066_, lean_object* v_l_2067_, lean_object* v_motive_2068_, lean_object* v_x_2069_, lean_object* v_h__1_2070_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_apply_4(v_h__1_2070_, v_x_2069_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_2072_, lean_object* v_00_u03b2_2073_, lean_object* v_l_2074_, lean_object* v_motive_2075_, lean_object* v_x_2076_, lean_object* v_h__1_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(v_00_u03b1_2072_, v_00_u03b2_2073_, v_l_2074_, v_motive_2075_, v_x_2076_, v_h__1_2077_);
lean_dec(v_l_2074_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___redArg(lean_object* v_x_2079_, lean_object* v_h__1_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_apply_3(v_h__1_2080_, v_x_2079_, lean_box(0), lean_box(0));
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(lean_object* v_00_u03b1_2082_, lean_object* v_00_u03b2_2083_, lean_object* v_l_x27_2084_, lean_object* v_motive_2085_, lean_object* v_x_2086_, lean_object* v_h__1_2087_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_apply_3(v_h__1_2087_, v_x_2086_, lean_box(0), lean_box(0));
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___boxed(lean_object* v_00_u03b1_2089_, lean_object* v_00_u03b2_2090_, lean_object* v_l_x27_2091_, lean_object* v_motive_2092_, lean_object* v_x_2093_, lean_object* v_h__1_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(v_00_u03b1_2089_, v_00_u03b2_2090_, v_l_x27_2091_, v_motive_2092_, v_x_2093_, v_h__1_2094_);
lean_dec(v_l_x27_2091_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___redArg(lean_object* v_x_2096_, lean_object* v_h__1_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_apply_3(v_h__1_2097_, v_x_2096_, lean_box(0), lean_box(0));
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(lean_object* v_00_u03b1_2099_, lean_object* v_00_u03b2_2100_, lean_object* v_r_x27_2101_, lean_object* v_motive_2102_, lean_object* v_x_2103_, lean_object* v_h__1_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = lean_apply_3(v_h__1_2104_, v_x_2103_, lean_box(0), lean_box(0));
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___boxed(lean_object* v_00_u03b1_2106_, lean_object* v_00_u03b2_2107_, lean_object* v_r_x27_2108_, lean_object* v_motive_2109_, lean_object* v_x_2110_, lean_object* v_h__1_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(v_00_u03b1_2106_, v_00_u03b2_2107_, v_r_x27_2108_, v_motive_2109_, v_x_2110_, v_h__1_2111_);
lean_dec(v_r_x27_2108_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(lean_object* v_r_2113_, lean_object* v_h__1_2114_, lean_object* v_h__2_2115_){
_start:
{
if (lean_obj_tag(v_r_2113_) == 0)
{
lean_object* v_size_2116_; lean_object* v_k_2117_; lean_object* v_v_2118_; lean_object* v_l_2119_; lean_object* v_r_2120_; lean_object* v___x_2121_; 
lean_dec(v_h__1_2114_);
v_size_2116_ = lean_ctor_get(v_r_2113_, 0);
lean_inc(v_size_2116_);
v_k_2117_ = lean_ctor_get(v_r_2113_, 1);
lean_inc(v_k_2117_);
v_v_2118_ = lean_ctor_get(v_r_2113_, 2);
lean_inc(v_v_2118_);
v_l_2119_ = lean_ctor_get(v_r_2113_, 3);
lean_inc(v_l_2119_);
v_r_2120_ = lean_ctor_get(v_r_2113_, 4);
lean_inc(v_r_2120_);
lean_dec_ref(v_r_2113_);
v___x_2121_ = lean_apply_5(v_h__2_2115_, v_size_2116_, v_k_2117_, v_v_2118_, v_l_2119_, v_r_2120_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_dec(v_h__2_2115_);
v___x_2122_ = lean_box(0);
v___x_2123_ = lean_apply_1(v_h__1_2114_, v___x_2122_);
return v___x_2123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object* v_00_u03b1_2124_, lean_object* v_00_u03b2_2125_, lean_object* v_motive_2126_, lean_object* v_r_2127_, lean_object* v_h__1_2128_, lean_object* v_h__2_2129_){
_start:
{
if (lean_obj_tag(v_r_2127_) == 0)
{
lean_object* v_size_2130_; lean_object* v_k_2131_; lean_object* v_v_2132_; lean_object* v_l_2133_; lean_object* v_r_2134_; lean_object* v___x_2135_; 
lean_dec(v_h__1_2128_);
v_size_2130_ = lean_ctor_get(v_r_2127_, 0);
lean_inc(v_size_2130_);
v_k_2131_ = lean_ctor_get(v_r_2127_, 1);
lean_inc(v_k_2131_);
v_v_2132_ = lean_ctor_get(v_r_2127_, 2);
lean_inc(v_v_2132_);
v_l_2133_ = lean_ctor_get(v_r_2127_, 3);
lean_inc(v_l_2133_);
v_r_2134_ = lean_ctor_get(v_r_2127_, 4);
lean_inc(v_r_2134_);
lean_dec_ref(v_r_2127_);
v___x_2135_ = lean_apply_5(v_h__2_2129_, v_size_2130_, v_k_2131_, v_v_2132_, v_l_2133_, v_r_2134_);
return v___x_2135_;
}
else
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
lean_dec(v_h__2_2129_);
v___x_2136_ = lean_box(0);
v___x_2137_ = lean_apply_1(v_h__1_2128_, v___x_2136_);
return v___x_2137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(lean_object* v_x_2138_, lean_object* v_h__1_2139_, lean_object* v_h__2_2140_){
_start:
{
if (lean_obj_tag(v_x_2138_) == 0)
{
lean_object* v_size_2141_; lean_object* v_k_2142_; lean_object* v_v_2143_; lean_object* v_l_2144_; lean_object* v_r_2145_; lean_object* v___x_2146_; 
lean_dec(v_h__2_2140_);
v_size_2141_ = lean_ctor_get(v_x_2138_, 0);
lean_inc(v_size_2141_);
v_k_2142_ = lean_ctor_get(v_x_2138_, 1);
lean_inc(v_k_2142_);
v_v_2143_ = lean_ctor_get(v_x_2138_, 2);
lean_inc(v_v_2143_);
v_l_2144_ = lean_ctor_get(v_x_2138_, 3);
lean_inc(v_l_2144_);
v_r_2145_ = lean_ctor_get(v_x_2138_, 4);
lean_inc(v_r_2145_);
lean_dec_ref(v_x_2138_);
v___x_2146_ = lean_apply_5(v_h__1_2139_, v_size_2141_, v_k_2142_, v_v_2143_, v_l_2144_, v_r_2145_);
return v___x_2146_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_dec(v_h__1_2139_);
v___x_2147_ = lean_box(0);
v___x_2148_ = lean_apply_1(v_h__2_2140_, v___x_2147_);
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(lean_object* v_00_u03b1_2149_, lean_object* v_00_u03b2_2150_, lean_object* v_motive_2151_, lean_object* v_x_2152_, lean_object* v_h__1_2153_, lean_object* v_h__2_2154_){
_start:
{
if (lean_obj_tag(v_x_2152_) == 0)
{
lean_object* v_size_2155_; lean_object* v_k_2156_; lean_object* v_v_2157_; lean_object* v_l_2158_; lean_object* v_r_2159_; lean_object* v___x_2160_; 
lean_dec(v_h__2_2154_);
v_size_2155_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_size_2155_);
v_k_2156_ = lean_ctor_get(v_x_2152_, 1);
lean_inc(v_k_2156_);
v_v_2157_ = lean_ctor_get(v_x_2152_, 2);
lean_inc(v_v_2157_);
v_l_2158_ = lean_ctor_get(v_x_2152_, 3);
lean_inc(v_l_2158_);
v_r_2159_ = lean_ctor_get(v_x_2152_, 4);
lean_inc(v_r_2159_);
lean_dec_ref(v_x_2152_);
v___x_2160_ = lean_apply_5(v_h__1_2153_, v_size_2155_, v_k_2156_, v_v_2157_, v_l_2158_, v_r_2159_);
return v___x_2160_;
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_dec(v_h__1_2153_);
v___x_2161_ = lean_box(0);
v___x_2162_ = lean_apply_1(v_h__2_2154_, v___x_2161_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object* v_r_2163_, lean_object* v_h__1_2164_, lean_object* v_h__2_2165_){
_start:
{
if (lean_obj_tag(v_r_2163_) == 0)
{
lean_object* v_size_2166_; lean_object* v_k_2167_; lean_object* v_v_2168_; lean_object* v_l_2169_; lean_object* v_r_2170_; lean_object* v___x_2171_; 
lean_dec(v_h__1_2164_);
v_size_2166_ = lean_ctor_get(v_r_2163_, 0);
lean_inc(v_size_2166_);
v_k_2167_ = lean_ctor_get(v_r_2163_, 1);
lean_inc(v_k_2167_);
v_v_2168_ = lean_ctor_get(v_r_2163_, 2);
lean_inc(v_v_2168_);
v_l_2169_ = lean_ctor_get(v_r_2163_, 3);
lean_inc(v_l_2169_);
v_r_2170_ = lean_ctor_get(v_r_2163_, 4);
lean_inc(v_r_2170_);
lean_dec_ref(v_r_2163_);
v___x_2171_ = lean_apply_7(v_h__2_2165_, v_size_2166_, v_k_2167_, v_v_2168_, v_l_2169_, v_r_2170_, lean_box(0), lean_box(0));
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; 
lean_dec(v_h__2_2165_);
v___x_2172_ = lean_apply_2(v_h__1_2164_, lean_box(0), lean_box(0));
return v___x_2172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object* v_00_u03b1_2173_, lean_object* v_00_u03b2_2174_, lean_object* v_motive_2175_, lean_object* v_r_2176_, lean_object* v_hr_2177_, lean_object* v_h__1_2178_, lean_object* v_h__2_2179_){
_start:
{
if (lean_obj_tag(v_r_2176_) == 0)
{
lean_object* v_size_2180_; lean_object* v_k_2181_; lean_object* v_v_2182_; lean_object* v_l_2183_; lean_object* v_r_2184_; lean_object* v___x_2185_; 
lean_dec(v_h__1_2178_);
v_size_2180_ = lean_ctor_get(v_r_2176_, 0);
lean_inc(v_size_2180_);
v_k_2181_ = lean_ctor_get(v_r_2176_, 1);
lean_inc(v_k_2181_);
v_v_2182_ = lean_ctor_get(v_r_2176_, 2);
lean_inc(v_v_2182_);
v_l_2183_ = lean_ctor_get(v_r_2176_, 3);
lean_inc(v_l_2183_);
v_r_2184_ = lean_ctor_get(v_r_2176_, 4);
lean_inc(v_r_2184_);
lean_dec_ref(v_r_2176_);
v___x_2185_ = lean_apply_7(v_h__2_2179_, v_size_2180_, v_k_2181_, v_v_2182_, v_l_2183_, v_r_2184_, lean_box(0), lean_box(0));
return v___x_2185_;
}
else
{
lean_object* v___x_2186_; 
lean_dec(v_h__2_2179_);
v___x_2186_ = lean_apply_2(v_h__1_2178_, lean_box(0), lean_box(0));
return v___x_2186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg(lean_object* v_t_2187_, lean_object* v_h__1_2188_, lean_object* v_h__2_2189_){
_start:
{
if (lean_obj_tag(v_t_2187_) == 0)
{
lean_object* v_size_2190_; lean_object* v_k_2191_; lean_object* v_v_2192_; lean_object* v_l_2193_; lean_object* v_r_2194_; lean_object* v___x_2195_; 
lean_dec(v_h__1_2188_);
v_size_2190_ = lean_ctor_get(v_t_2187_, 0);
lean_inc(v_size_2190_);
v_k_2191_ = lean_ctor_get(v_t_2187_, 1);
lean_inc(v_k_2191_);
v_v_2192_ = lean_ctor_get(v_t_2187_, 2);
lean_inc(v_v_2192_);
v_l_2193_ = lean_ctor_get(v_t_2187_, 3);
lean_inc(v_l_2193_);
v_r_2194_ = lean_ctor_get(v_t_2187_, 4);
lean_inc(v_r_2194_);
lean_dec_ref(v_t_2187_);
v___x_2195_ = lean_apply_5(v_h__2_2189_, v_size_2190_, v_k_2191_, v_v_2192_, v_l_2193_, v_r_2194_);
return v___x_2195_;
}
else
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec(v_h__2_2189_);
v___x_2196_ = lean_box(0);
v___x_2197_ = lean_apply_1(v_h__1_2188_, v___x_2196_);
return v___x_2197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_2198_, lean_object* v_00_u03b4_2199_, lean_object* v_motive_2200_, lean_object* v_t_2201_, lean_object* v_h__1_2202_, lean_object* v_h__2_2203_){
_start:
{
if (lean_obj_tag(v_t_2201_) == 0)
{
lean_object* v_size_2204_; lean_object* v_k_2205_; lean_object* v_v_2206_; lean_object* v_l_2207_; lean_object* v_r_2208_; lean_object* v___x_2209_; 
lean_dec(v_h__1_2202_);
v_size_2204_ = lean_ctor_get(v_t_2201_, 0);
lean_inc(v_size_2204_);
v_k_2205_ = lean_ctor_get(v_t_2201_, 1);
lean_inc(v_k_2205_);
v_v_2206_ = lean_ctor_get(v_t_2201_, 2);
lean_inc(v_v_2206_);
v_l_2207_ = lean_ctor_get(v_t_2201_, 3);
lean_inc(v_l_2207_);
v_r_2208_ = lean_ctor_get(v_t_2201_, 4);
lean_inc(v_r_2208_);
lean_dec_ref(v_t_2201_);
v___x_2209_ = lean_apply_5(v_h__2_2203_, v_size_2204_, v_k_2205_, v_v_2206_, v_l_2207_, v_r_2208_);
return v___x_2209_;
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec(v_h__2_2203_);
v___x_2210_ = lean_box(0);
v___x_2211_ = lean_apply_1(v_h__1_2202_, v___x_2210_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object* v_x_2212_, lean_object* v_h__1_2213_, lean_object* v_h__2_2214_){
_start:
{
if (lean_obj_tag(v_x_2212_) == 0)
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec(v_h__2_2214_);
v___x_2215_ = lean_box(0);
v___x_2216_ = lean_apply_1(v_h__1_2213_, v___x_2215_);
return v___x_2216_;
}
else
{
lean_object* v_val_2217_; lean_object* v___x_2218_; 
lean_dec(v_h__1_2213_);
v_val_2217_ = lean_ctor_get(v_x_2212_, 0);
lean_inc(v_val_2217_);
lean_dec_ref(v_x_2212_);
v___x_2218_ = lean_apply_1(v_h__2_2214_, v_val_2217_);
return v___x_2218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_2219_, lean_object* v_00_u03b2_2220_, lean_object* v_motive_2221_, lean_object* v_x_2222_, lean_object* v_h__1_2223_, lean_object* v_h__2_2224_){
_start:
{
if (lean_obj_tag(v_x_2222_) == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec(v_h__2_2224_);
v___x_2225_ = lean_box(0);
v___x_2226_ = lean_apply_1(v_h__1_2223_, v___x_2225_);
return v___x_2226_;
}
else
{
lean_object* v_val_2227_; lean_object* v___x_2228_; 
lean_dec(v_h__1_2223_);
v_val_2227_ = lean_ctor_get(v_x_2222_, 0);
lean_inc(v_val_2227_);
lean_dec_ref(v_x_2222_);
v___x_2228_ = lean_apply_1(v_h__2_2224_, v_val_2227_);
return v___x_2228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___redArg(lean_object* v_t_2229_, lean_object* v_h__1_2230_){
_start:
{
lean_object* v_size_2231_; lean_object* v_k_2232_; lean_object* v_v_2233_; lean_object* v_l_2234_; lean_object* v_r_2235_; lean_object* v___x_2236_; 
v_size_2231_ = lean_ctor_get(v_t_2229_, 0);
lean_inc(v_size_2231_);
v_k_2232_ = lean_ctor_get(v_t_2229_, 1);
lean_inc(v_k_2232_);
v_v_2233_ = lean_ctor_get(v_t_2229_, 2);
lean_inc(v_v_2233_);
v_l_2234_ = lean_ctor_get(v_t_2229_, 3);
lean_inc(v_l_2234_);
v_r_2235_ = lean_ctor_get(v_t_2229_, 4);
lean_inc(v_r_2235_);
lean_dec(v_t_2229_);
v___x_2236_ = lean_apply_6(v_h__1_2230_, v_size_2231_, v_k_2232_, v_v_2233_, v_l_2234_, v_r_2235_, lean_box(0));
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(lean_object* v_00_u03b1_2237_, lean_object* v_00_u03b4_2238_, lean_object* v_inst_2239_, lean_object* v_k_2240_, lean_object* v_motive_2241_, lean_object* v_t_2242_, lean_object* v_hlk_2243_, lean_object* v_h__1_2244_){
_start:
{
lean_object* v_size_2245_; lean_object* v_k_2246_; lean_object* v_v_2247_; lean_object* v_l_2248_; lean_object* v_r_2249_; lean_object* v___x_2250_; 
v_size_2245_ = lean_ctor_get(v_t_2242_, 0);
lean_inc(v_size_2245_);
v_k_2246_ = lean_ctor_get(v_t_2242_, 1);
lean_inc(v_k_2246_);
v_v_2247_ = lean_ctor_get(v_t_2242_, 2);
lean_inc(v_v_2247_);
v_l_2248_ = lean_ctor_get(v_t_2242_, 3);
lean_inc(v_l_2248_);
v_r_2249_ = lean_ctor_get(v_t_2242_, 4);
lean_inc(v_r_2249_);
lean_dec(v_t_2242_);
v___x_2250_ = lean_apply_6(v_h__1_2244_, v_size_2245_, v_k_2246_, v_v_2247_, v_l_2248_, v_r_2249_, lean_box(0));
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___boxed(lean_object* v_00_u03b1_2251_, lean_object* v_00_u03b4_2252_, lean_object* v_inst_2253_, lean_object* v_k_2254_, lean_object* v_motive_2255_, lean_object* v_t_2256_, lean_object* v_hlk_2257_, lean_object* v_h__1_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(v_00_u03b1_2251_, v_00_u03b4_2252_, v_inst_2253_, v_k_2254_, v_motive_2255_, v_t_2256_, v_hlk_2257_, v_h__1_2258_);
lean_dec(v_k_2254_);
lean_dec_ref(v_inst_2253_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(lean_object* v_x_2260_, lean_object* v_x_2261_, lean_object* v_h__1_2262_){
_start:
{
lean_object* v_size_2263_; lean_object* v_k_2264_; lean_object* v_v_2265_; lean_object* v_l_2266_; lean_object* v_r_2267_; lean_object* v___x_2268_; 
v_size_2263_ = lean_ctor_get(v_x_2260_, 0);
lean_inc(v_size_2263_);
v_k_2264_ = lean_ctor_get(v_x_2260_, 1);
lean_inc(v_k_2264_);
v_v_2265_ = lean_ctor_get(v_x_2260_, 2);
lean_inc(v_v_2265_);
v_l_2266_ = lean_ctor_get(v_x_2260_, 3);
lean_inc(v_l_2266_);
v_r_2267_ = lean_ctor_get(v_x_2260_, 4);
lean_inc(v_r_2267_);
lean_dec(v_x_2260_);
v___x_2268_ = lean_apply_8(v_h__1_2262_, v_size_2263_, v_k_2264_, v_v_2265_, v_l_2266_, v_r_2267_, lean_box(0), v_x_2261_, lean_box(0));
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter(lean_object* v_00_u03b1_2269_, lean_object* v_00_u03b2_2270_, lean_object* v_motive_2271_, lean_object* v_x_2272_, lean_object* v_x_2273_, lean_object* v_x_2274_, lean_object* v_x_2275_, lean_object* v_h__1_2276_){
_start:
{
lean_object* v_size_2277_; lean_object* v_k_2278_; lean_object* v_v_2279_; lean_object* v_l_2280_; lean_object* v_r_2281_; lean_object* v___x_2282_; 
v_size_2277_ = lean_ctor_get(v_x_2272_, 0);
lean_inc(v_size_2277_);
v_k_2278_ = lean_ctor_get(v_x_2272_, 1);
lean_inc(v_k_2278_);
v_v_2279_ = lean_ctor_get(v_x_2272_, 2);
lean_inc(v_v_2279_);
v_l_2280_ = lean_ctor_get(v_x_2272_, 3);
lean_inc(v_l_2280_);
v_r_2281_ = lean_ctor_get(v_x_2272_, 4);
lean_inc(v_r_2281_);
lean_dec(v_x_2272_);
v___x_2282_ = lean_apply_8(v_h__1_2276_, v_size_2277_, v_k_2278_, v_v_2279_, v_l_2280_, v_r_2281_, lean_box(0), v_x_2274_, lean_box(0));
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(uint8_t v_x_2283_, lean_object* v_h__1_2284_, lean_object* v_h__2_2285_, lean_object* v_h__3_2286_){
_start:
{
switch(v_x_2283_)
{
case 0:
{
lean_object* v___x_2287_; 
lean_dec(v_h__3_2286_);
lean_dec(v_h__2_2285_);
v___x_2287_ = lean_apply_1(v_h__1_2284_, lean_box(0));
return v___x_2287_;
}
case 1:
{
lean_object* v___x_2288_; 
lean_dec(v_h__3_2286_);
lean_dec(v_h__1_2284_);
v___x_2288_ = lean_apply_1(v_h__2_2285_, lean_box(0));
return v___x_2288_;
}
default: 
{
lean_object* v___x_2289_; 
lean_dec(v_h__2_2285_);
lean_dec(v_h__1_2284_);
v___x_2289_ = lean_apply_1(v_h__3_2286_, lean_box(0));
return v___x_2289_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg___boxed(lean_object* v_x_2290_, lean_object* v_h__1_2291_, lean_object* v_h__2_2292_, lean_object* v_h__3_2293_){
_start:
{
uint8_t v_x_33__boxed_2294_; lean_object* v_res_2295_; 
v_x_33__boxed_2294_ = lean_unbox(v_x_2290_);
v_res_2295_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(v_x_33__boxed_2294_, v_h__1_2291_, v_h__2_2292_, v_h__3_2293_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(lean_object* v_motive_2296_, uint8_t v_x_2297_, lean_object* v_h__1_2298_, lean_object* v_h__2_2299_, lean_object* v_h__3_2300_){
_start:
{
switch(v_x_2297_)
{
case 0:
{
lean_object* v___x_2301_; 
lean_dec(v_h__3_2300_);
lean_dec(v_h__2_2299_);
v___x_2301_ = lean_apply_1(v_h__1_2298_, lean_box(0));
return v___x_2301_;
}
case 1:
{
lean_object* v___x_2302_; 
lean_dec(v_h__3_2300_);
lean_dec(v_h__1_2298_);
v___x_2302_ = lean_apply_1(v_h__2_2299_, lean_box(0));
return v___x_2302_;
}
default: 
{
lean_object* v___x_2303_; 
lean_dec(v_h__2_2299_);
lean_dec(v_h__1_2298_);
v___x_2303_ = lean_apply_1(v_h__3_2300_, lean_box(0));
return v___x_2303_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___boxed(lean_object* v_motive_2304_, lean_object* v_x_2305_, lean_object* v_h__1_2306_, lean_object* v_h__2_2307_, lean_object* v_h__3_2308_){
_start:
{
uint8_t v_x_42__boxed_2309_; lean_object* v_res_2310_; 
v_x_42__boxed_2309_ = lean_unbox(v_x_2305_);
v_res_2310_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(v_motive_2304_, v_x_42__boxed_2309_, v_h__1_2306_, v_h__2_2307_, v_h__3_2308_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object* v_x_2311_, lean_object* v_x_2312_, lean_object* v_h__1_2313_, lean_object* v_h__2_2314_){
_start:
{
if (lean_obj_tag(v_x_2311_) == 0)
{
lean_object* v_size_2315_; lean_object* v_k_2316_; lean_object* v_v_2317_; lean_object* v_l_2318_; lean_object* v_r_2319_; lean_object* v___x_2320_; 
lean_dec(v_h__1_2313_);
v_size_2315_ = lean_ctor_get(v_x_2311_, 0);
lean_inc(v_size_2315_);
v_k_2316_ = lean_ctor_get(v_x_2311_, 1);
lean_inc(v_k_2316_);
v_v_2317_ = lean_ctor_get(v_x_2311_, 2);
lean_inc(v_v_2317_);
v_l_2318_ = lean_ctor_get(v_x_2311_, 3);
lean_inc(v_l_2318_);
v_r_2319_ = lean_ctor_get(v_x_2311_, 4);
lean_inc(v_r_2319_);
lean_dec_ref(v_x_2311_);
v___x_2320_ = lean_apply_6(v_h__2_2314_, v_size_2315_, v_k_2316_, v_v_2317_, v_l_2318_, v_r_2319_, v_x_2312_);
return v___x_2320_;
}
else
{
lean_object* v___x_2321_; 
lean_dec(v_h__2_2314_);
v___x_2321_ = lean_apply_1(v_h__1_2313_, v_x_2312_);
return v___x_2321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object* v_00_u03b1_2322_, lean_object* v_00_u03b2_2323_, lean_object* v_motive_2324_, lean_object* v_x_2325_, lean_object* v_x_2326_, lean_object* v_h__1_2327_, lean_object* v_h__2_2328_){
_start:
{
if (lean_obj_tag(v_x_2325_) == 0)
{
lean_object* v_size_2329_; lean_object* v_k_2330_; lean_object* v_v_2331_; lean_object* v_l_2332_; lean_object* v_r_2333_; lean_object* v___x_2334_; 
lean_dec(v_h__1_2327_);
v_size_2329_ = lean_ctor_get(v_x_2325_, 0);
lean_inc(v_size_2329_);
v_k_2330_ = lean_ctor_get(v_x_2325_, 1);
lean_inc(v_k_2330_);
v_v_2331_ = lean_ctor_get(v_x_2325_, 2);
lean_inc(v_v_2331_);
v_l_2332_ = lean_ctor_get(v_x_2325_, 3);
lean_inc(v_l_2332_);
v_r_2333_ = lean_ctor_get(v_x_2325_, 4);
lean_inc(v_r_2333_);
lean_dec_ref(v_x_2325_);
v___x_2334_ = lean_apply_6(v_h__2_2328_, v_size_2329_, v_k_2330_, v_v_2331_, v_l_2332_, v_r_2333_, v_x_2326_);
return v___x_2334_;
}
else
{
lean_object* v___x_2335_; 
lean_dec(v_h__2_2328_);
v___x_2335_ = lean_apply_1(v_h__1_2327_, v_x_2326_);
return v___x_2335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t v_x_2336_, lean_object* v_h__1_2337_, lean_object* v_h__2_2338_, lean_object* v_h__3_2339_){
_start:
{
switch(v_x_2336_)
{
case 0:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_dec(v_h__3_2339_);
lean_dec(v_h__2_2338_);
v___x_2340_ = lean_box(0);
v___x_2341_ = lean_apply_1(v_h__1_2337_, v___x_2340_);
return v___x_2341_;
}
case 1:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
lean_dec(v_h__3_2339_);
lean_dec(v_h__1_2337_);
v___x_2342_ = lean_box(0);
v___x_2343_ = lean_apply_1(v_h__2_2338_, v___x_2342_);
return v___x_2343_;
}
default: 
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_dec(v_h__2_2338_);
lean_dec(v_h__1_2337_);
v___x_2344_ = lean_box(0);
v___x_2345_ = lean_apply_1(v_h__3_2339_, v___x_2344_);
return v___x_2345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_2346_, lean_object* v_h__1_2347_, lean_object* v_h__2_2348_, lean_object* v_h__3_2349_){
_start:
{
uint8_t v_x_36__boxed_2350_; lean_object* v_res_2351_; 
v_x_36__boxed_2350_ = lean_unbox(v_x_2346_);
v_res_2351_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_36__boxed_2350_, v_h__1_2347_, v_h__2_2348_, v_h__3_2349_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object* v_motive_2352_, uint8_t v_x_2353_, lean_object* v_h__1_2354_, lean_object* v_h__2_2355_, lean_object* v_h__3_2356_){
_start:
{
switch(v_x_2353_)
{
case 0:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_dec(v_h__3_2356_);
lean_dec(v_h__2_2355_);
v___x_2357_ = lean_box(0);
v___x_2358_ = lean_apply_1(v_h__1_2354_, v___x_2357_);
return v___x_2358_;
}
case 1:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
lean_dec(v_h__3_2356_);
lean_dec(v_h__1_2354_);
v___x_2359_ = lean_box(0);
v___x_2360_ = lean_apply_1(v_h__2_2355_, v___x_2359_);
return v___x_2360_;
}
default: 
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec(v_h__2_2355_);
lean_dec(v_h__1_2354_);
v___x_2361_ = lean_box(0);
v___x_2362_ = lean_apply_1(v_h__3_2356_, v___x_2361_);
return v___x_2362_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object* v_motive_2363_, lean_object* v_x_2364_, lean_object* v_h__1_2365_, lean_object* v_h__2_2366_, lean_object* v_h__3_2367_){
_start:
{
uint8_t v_x_51__boxed_2368_; lean_object* v_res_2369_; 
v_x_51__boxed_2368_ = lean_unbox(v_x_2364_);
v_res_2369_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(v_motive_2363_, v_x_51__boxed_2368_, v_h__1_2365_, v_h__2_2366_, v_h__3_2367_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter___redArg(lean_object* v_x_2370_, lean_object* v_x_2371_, lean_object* v_x_2372_, lean_object* v_h__1_2373_, lean_object* v_h__2_2374_){
_start:
{
if (lean_obj_tag(v_x_2370_) == 0)
{
lean_object* v_size_2375_; lean_object* v_k_2376_; lean_object* v_v_2377_; lean_object* v_l_2378_; lean_object* v_r_2379_; lean_object* v___x_2380_; 
lean_dec(v_h__1_2373_);
v_size_2375_ = lean_ctor_get(v_x_2370_, 0);
lean_inc(v_size_2375_);
v_k_2376_ = lean_ctor_get(v_x_2370_, 1);
lean_inc(v_k_2376_);
v_v_2377_ = lean_ctor_get(v_x_2370_, 2);
lean_inc(v_v_2377_);
v_l_2378_ = lean_ctor_get(v_x_2370_, 3);
lean_inc(v_l_2378_);
v_r_2379_ = lean_ctor_get(v_x_2370_, 4);
lean_inc(v_r_2379_);
lean_dec_ref(v_x_2370_);
v___x_2380_ = lean_apply_7(v_h__2_2374_, v_size_2375_, v_k_2376_, v_v_2377_, v_l_2378_, v_r_2379_, v_x_2371_, v_x_2372_);
return v___x_2380_;
}
else
{
lean_object* v___x_2381_; 
lean_dec(v_h__2_2374_);
v___x_2381_ = lean_apply_2(v_h__1_2373_, v_x_2371_, v_x_2372_);
return v___x_2381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2382_, lean_object* v_00_u03b2_2383_, lean_object* v_motive_2384_, lean_object* v_x_2385_, lean_object* v_x_2386_, lean_object* v_x_2387_, lean_object* v_h__1_2388_, lean_object* v_h__2_2389_){
_start:
{
if (lean_obj_tag(v_x_2385_) == 0)
{
lean_object* v_size_2390_; lean_object* v_k_2391_; lean_object* v_v_2392_; lean_object* v_l_2393_; lean_object* v_r_2394_; lean_object* v___x_2395_; 
lean_dec(v_h__1_2388_);
v_size_2390_ = lean_ctor_get(v_x_2385_, 0);
lean_inc(v_size_2390_);
v_k_2391_ = lean_ctor_get(v_x_2385_, 1);
lean_inc(v_k_2391_);
v_v_2392_ = lean_ctor_get(v_x_2385_, 2);
lean_inc(v_v_2392_);
v_l_2393_ = lean_ctor_get(v_x_2385_, 3);
lean_inc(v_l_2393_);
v_r_2394_ = lean_ctor_get(v_x_2385_, 4);
lean_inc(v_r_2394_);
lean_dec_ref(v_x_2385_);
v___x_2395_ = lean_apply_7(v_h__2_2389_, v_size_2390_, v_k_2391_, v_v_2392_, v_l_2393_, v_r_2394_, v_x_2386_, v_x_2387_);
return v___x_2395_;
}
else
{
lean_object* v___x_2396_; 
lean_dec(v_h__2_2389_);
v___x_2396_ = lean_apply_2(v_h__1_2388_, v_x_2386_, v_x_2387_);
return v___x_2396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter___redArg(lean_object* v_x_2397_, lean_object* v_x_2398_, lean_object* v_x_2399_, lean_object* v_h__1_2400_, lean_object* v_h__2_2401_){
_start:
{
if (lean_obj_tag(v_x_2397_) == 0)
{
lean_object* v_size_2402_; lean_object* v_k_2403_; lean_object* v_v_2404_; lean_object* v_l_2405_; lean_object* v_r_2406_; lean_object* v___x_2407_; 
lean_dec(v_h__1_2400_);
v_size_2402_ = lean_ctor_get(v_x_2397_, 0);
lean_inc(v_size_2402_);
v_k_2403_ = lean_ctor_get(v_x_2397_, 1);
lean_inc(v_k_2403_);
v_v_2404_ = lean_ctor_get(v_x_2397_, 2);
lean_inc(v_v_2404_);
v_l_2405_ = lean_ctor_get(v_x_2397_, 3);
lean_inc(v_l_2405_);
v_r_2406_ = lean_ctor_get(v_x_2397_, 4);
lean_inc(v_r_2406_);
lean_dec_ref(v_x_2397_);
v___x_2407_ = lean_apply_7(v_h__2_2401_, v_size_2402_, v_k_2403_, v_v_2404_, v_l_2405_, v_r_2406_, v_x_2398_, v_x_2399_);
return v___x_2407_;
}
else
{
lean_object* v___x_2408_; 
lean_dec(v_h__2_2401_);
v___x_2408_ = lean_apply_2(v_h__1_2400_, v_x_2398_, v_x_2399_);
return v___x_2408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2409_, lean_object* v_00_u03b2_2410_, lean_object* v_motive_2411_, lean_object* v_x_2412_, lean_object* v_x_2413_, lean_object* v_x_2414_, lean_object* v_h__1_2415_, lean_object* v_h__2_2416_){
_start:
{
if (lean_obj_tag(v_x_2412_) == 0)
{
lean_object* v_size_2417_; lean_object* v_k_2418_; lean_object* v_v_2419_; lean_object* v_l_2420_; lean_object* v_r_2421_; lean_object* v___x_2422_; 
lean_dec(v_h__1_2415_);
v_size_2417_ = lean_ctor_get(v_x_2412_, 0);
lean_inc(v_size_2417_);
v_k_2418_ = lean_ctor_get(v_x_2412_, 1);
lean_inc(v_k_2418_);
v_v_2419_ = lean_ctor_get(v_x_2412_, 2);
lean_inc(v_v_2419_);
v_l_2420_ = lean_ctor_get(v_x_2412_, 3);
lean_inc(v_l_2420_);
v_r_2421_ = lean_ctor_get(v_x_2412_, 4);
lean_inc(v_r_2421_);
lean_dec_ref(v_x_2412_);
v___x_2422_ = lean_apply_7(v_h__2_2416_, v_size_2417_, v_k_2418_, v_v_2419_, v_l_2420_, v_r_2421_, v_x_2413_, v_x_2414_);
return v___x_2422_;
}
else
{
lean_object* v___x_2423_; 
lean_dec(v_h__2_2416_);
v___x_2423_ = lean_apply_2(v_h__1_2415_, v_x_2413_, v_x_2414_);
return v___x_2423_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(lean_object* v_x_2424_, lean_object* v_c_2425_, lean_object* v_x_2426_, lean_object* v_r_2427_){
_start:
{
if (lean_obj_tag(v_c_2425_) == 0)
{
lean_object* v___x_2428_; 
v___x_2428_ = l_List_head_x3f___redArg(v_r_2427_);
return v___x_2428_;
}
else
{
lean_object* v_val_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
v_val_2429_ = lean_ctor_get(v_c_2425_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v_c_2425_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v_c_2425_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_val_2429_);
lean_dec(v_c_2425_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_val_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed(lean_object* v_x_2437_, lean_object* v_c_2438_, lean_object* v_x_2439_, lean_object* v_r_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(v_x_2437_, v_c_2438_, v_x_2439_, v_r_2440_);
lean_dec(v_r_2440_);
lean_dec(v_x_2437_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(lean_object* v_inst_2443_, lean_object* v_k_2444_, lean_object* v_t_2445_){
_start:
{
lean_object* v___f_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___f_2446_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0));
v___x_2447_ = lean_apply_1(v_inst_2443_, v_k_2444_);
v___x_2448_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___x_2447_, v_t_2445_, v___f_2446_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098(lean_object* v_00_u03b1_2449_, lean_object* v_00_u03b2_2450_, lean_object* v_inst_2451_, lean_object* v_k_2452_, lean_object* v_t_2453_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(v_inst_2451_, v_k_2452_, v_t_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(lean_object* v_x_2455_, lean_object* v_x_2456_){
_start:
{
switch(lean_obj_tag(v_x_2456_))
{
case 0:
{
lean_object* v_a_2457_; lean_object* v_a_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_a_2457_ = lean_ctor_get(v_x_2456_, 0);
lean_inc(v_a_2457_);
v_a_2458_ = lean_ctor_get(v_x_2456_, 1);
lean_inc(v_a_2458_);
lean_dec_ref(v_x_2456_);
v___x_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2459_, 0, v_a_2457_);
lean_ctor_set(v___x_2459_, 1, v_a_2458_);
v___x_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
return v___x_2460_;
}
case 1:
{
lean_object* v_a_2461_; 
v_a_2461_ = lean_ctor_get(v_x_2456_, 1);
lean_inc(v_a_2461_);
if (lean_obj_tag(v_a_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2463_; 
v_a_2462_ = lean_ctor_get(v_x_2456_, 2);
lean_inc(v_a_2462_);
lean_dec_ref(v_x_2456_);
v___x_2463_ = l_List_head_x3f___redArg(v_a_2462_);
lean_dec(v_a_2462_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_inc(v_x_2455_);
return v_x_2455_;
}
else
{
return v___x_2463_;
}
}
else
{
lean_object* v_val_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec_ref(v_x_2456_);
v_val_2464_ = lean_ctor_get(v_a_2461_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_a_2461_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v_a_2461_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_val_2464_);
lean_dec(v_a_2461_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_val_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
default: 
{
lean_dec_ref(v_x_2456_);
lean_inc(v_x_2455_);
return v_x_2455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* v_x_2472_, lean_object* v_x_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(v_x_2472_, v_x_2473_);
lean_dec(v_x_2472_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(lean_object* v_inst_2476_, lean_object* v_k_2477_, lean_object* v_t_2478_){
_start:
{
lean_object* v___f_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___f_2479_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0));
v___x_2480_ = lean_apply_1(v_inst_2476_, v_k_2477_);
v___x_2481_ = lean_box(0);
v___x_2482_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___x_2480_, v___x_2481_, v___f_2479_, v_t_2478_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27(lean_object* v_00_u03b1_2483_, lean_object* v_00_u03b2_2484_, lean_object* v_inst_2485_, lean_object* v_k_2486_, lean_object* v_t_2487_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(v_inst_2485_, v_k_2486_, v_t_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_x_2489_, lean_object* v_x_2490_, lean_object* v_h__1_2491_, lean_object* v_h__2_2492_, lean_object* v_h__3_2493_){
_start:
{
switch(lean_obj_tag(v_x_2490_))
{
case 0:
{
lean_object* v_a_2494_; lean_object* v_a_2495_; lean_object* v_a_2496_; lean_object* v___x_2497_; 
lean_dec(v_h__3_2493_);
lean_dec(v_h__2_2492_);
v_a_2494_ = lean_ctor_get(v_x_2490_, 0);
lean_inc(v_a_2494_);
v_a_2495_ = lean_ctor_get(v_x_2490_, 1);
lean_inc(v_a_2495_);
v_a_2496_ = lean_ctor_get(v_x_2490_, 2);
lean_inc(v_a_2496_);
lean_dec_ref(v_x_2490_);
v___x_2497_ = lean_apply_5(v_h__1_2491_, v_x_2489_, v_a_2494_, lean_box(0), v_a_2495_, v_a_2496_);
return v___x_2497_;
}
case 1:
{
lean_object* v_a_2498_; lean_object* v_a_2499_; lean_object* v_a_2500_; lean_object* v___x_2501_; 
lean_dec(v_h__3_2493_);
lean_dec(v_h__1_2491_);
v_a_2498_ = lean_ctor_get(v_x_2490_, 0);
lean_inc(v_a_2498_);
v_a_2499_ = lean_ctor_get(v_x_2490_, 1);
lean_inc(v_a_2499_);
v_a_2500_ = lean_ctor_get(v_x_2490_, 2);
lean_inc(v_a_2500_);
lean_dec_ref(v_x_2490_);
v___x_2501_ = lean_apply_4(v_h__2_2492_, v_x_2489_, v_a_2498_, v_a_2499_, v_a_2500_);
return v___x_2501_;
}
default: 
{
lean_object* v_a_2502_; lean_object* v_a_2503_; lean_object* v_a_2504_; lean_object* v___x_2505_; 
lean_dec(v_h__2_2492_);
lean_dec(v_h__1_2491_);
v_a_2502_ = lean_ctor_get(v_x_2490_, 0);
lean_inc(v_a_2502_);
v_a_2503_ = lean_ctor_get(v_x_2490_, 1);
lean_inc(v_a_2503_);
v_a_2504_ = lean_ctor_get(v_x_2490_, 2);
lean_inc(v_a_2504_);
lean_dec_ref(v_x_2490_);
v___x_2505_ = lean_apply_5(v_h__3_2493_, v_x_2489_, v_a_2502_, v_a_2503_, lean_box(0), v_a_2504_);
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_2506_, lean_object* v_00_u03b2_2507_, lean_object* v_inst_2508_, lean_object* v_k_2509_, lean_object* v_motive_2510_, lean_object* v_x_2511_, lean_object* v_x_2512_, lean_object* v_h__1_2513_, lean_object* v_h__2_2514_, lean_object* v_h__3_2515_){
_start:
{
switch(lean_obj_tag(v_x_2512_))
{
case 0:
{
lean_object* v_a_2516_; lean_object* v_a_2517_; lean_object* v_a_2518_; lean_object* v___x_2519_; 
lean_dec(v_h__3_2515_);
lean_dec(v_h__2_2514_);
v_a_2516_ = lean_ctor_get(v_x_2512_, 0);
lean_inc(v_a_2516_);
v_a_2517_ = lean_ctor_get(v_x_2512_, 1);
lean_inc(v_a_2517_);
v_a_2518_ = lean_ctor_get(v_x_2512_, 2);
lean_inc(v_a_2518_);
lean_dec_ref(v_x_2512_);
v___x_2519_ = lean_apply_5(v_h__1_2513_, v_x_2511_, v_a_2516_, lean_box(0), v_a_2517_, v_a_2518_);
return v___x_2519_;
}
case 1:
{
lean_object* v_a_2520_; lean_object* v_a_2521_; lean_object* v_a_2522_; lean_object* v___x_2523_; 
lean_dec(v_h__3_2515_);
lean_dec(v_h__1_2513_);
v_a_2520_ = lean_ctor_get(v_x_2512_, 0);
lean_inc(v_a_2520_);
v_a_2521_ = lean_ctor_get(v_x_2512_, 1);
lean_inc(v_a_2521_);
v_a_2522_ = lean_ctor_get(v_x_2512_, 2);
lean_inc(v_a_2522_);
lean_dec_ref(v_x_2512_);
v___x_2523_ = lean_apply_4(v_h__2_2514_, v_x_2511_, v_a_2520_, v_a_2521_, v_a_2522_);
return v___x_2523_;
}
default: 
{
lean_object* v_a_2524_; lean_object* v_a_2525_; lean_object* v_a_2526_; lean_object* v___x_2527_; 
lean_dec(v_h__2_2514_);
lean_dec(v_h__1_2513_);
v_a_2524_ = lean_ctor_get(v_x_2512_, 0);
lean_inc(v_a_2524_);
v_a_2525_ = lean_ctor_get(v_x_2512_, 1);
lean_inc(v_a_2525_);
v_a_2526_ = lean_ctor_get(v_x_2512_, 2);
lean_inc(v_a_2526_);
lean_dec_ref(v_x_2512_);
v___x_2527_ = lean_apply_5(v_h__3_2515_, v_x_2511_, v_a_2524_, v_a_2525_, lean_box(0), v_a_2526_);
return v___x_2527_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_2528_, lean_object* v_00_u03b2_2529_, lean_object* v_inst_2530_, lean_object* v_k_2531_, lean_object* v_motive_2532_, lean_object* v_x_2533_, lean_object* v_x_2534_, lean_object* v_h__1_2535_, lean_object* v_h__2_2536_, lean_object* v_h__3_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(v_00_u03b1_2528_, v_00_u03b2_2529_, v_inst_2530_, v_k_2531_, v_motive_2532_, v_x_2533_, v_x_2534_, v_h__1_2535_, v_h__2_2536_, v_h__3_2537_);
lean_dec(v_k_2531_);
lean_dec_ref(v_inst_2530_);
return v_res_2538_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(lean_object* v_inst_2539_, lean_object* v_k_2540_, lean_object* v_k_x27_2541_){
_start:
{
lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2542_ = lean_apply_2(v_inst_2539_, v_k_2540_, v_k_x27_2541_);
v___x_2543_ = lean_unbox(v___x_2542_);
if (v___x_2543_ == 1)
{
uint8_t v___x_2544_; 
v___x_2544_ = 2;
return v___x_2544_;
}
else
{
uint8_t v___x_2545_; 
v___x_2545_ = lean_unbox(v___x_2542_);
return v___x_2545_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed(lean_object* v_inst_2546_, lean_object* v_k_2547_, lean_object* v_k_x27_2548_){
_start:
{
uint8_t v_res_2549_; lean_object* v_r_2550_; 
v_res_2549_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(v_inst_2546_, v_k_2547_, v_k_x27_2548_);
v_r_2550_ = lean_box(v_res_2549_);
return v_r_2550_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(lean_object* v_inst_2551_, lean_object* v_k_2552_, lean_object* v_t_2553_){
_start:
{
lean_object* v___f_2554_; lean_object* v___f_2555_; lean_object* v___x_2556_; 
v___f_2554_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2554_, 0, v_inst_2551_);
lean_closure_set(v___f_2554_, 1, v_k_2552_);
v___f_2555_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0));
v___x_2556_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_2554_, v_t_2553_, v___f_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098(lean_object* v_00_u03b1_2557_, lean_object* v_00_u03b2_2558_, lean_object* v_inst_2559_, lean_object* v_k_2560_, lean_object* v_t_2561_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(v_inst_2559_, v_k_2560_, v_t_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(lean_object* v_x_2563_, lean_object* v_x_2564_){
_start:
{
switch(lean_obj_tag(v_x_2564_))
{
case 0:
{
lean_object* v_a_2565_; lean_object* v_a_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v_a_2565_ = lean_ctor_get(v_x_2564_, 0);
v_a_2566_ = lean_ctor_get(v_x_2564_, 1);
lean_inc(v_a_2566_);
lean_inc(v_a_2565_);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v_a_2565_);
lean_ctor_set(v___x_2567_, 1, v_a_2566_);
v___x_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
return v___x_2568_;
}
case 1:
{
lean_object* v_a_2569_; lean_object* v___x_2570_; 
v_a_2569_ = lean_ctor_get(v_x_2564_, 2);
v___x_2570_ = l_List_head_x3f___redArg(v_a_2569_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_inc(v_x_2563_);
return v_x_2563_;
}
else
{
return v___x_2570_;
}
}
default: 
{
lean_inc(v_x_2563_);
return v_x_2563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* v_x_2571_, lean_object* v_x_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(v_x_2571_, v_x_2572_);
lean_dec_ref(v_x_2572_);
lean_dec(v_x_2571_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(lean_object* v_inst_2575_, lean_object* v_k_2576_, lean_object* v_t_2577_){
_start:
{
lean_object* v___f_2578_; lean_object* v___f_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___f_2578_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2578_, 0, v_inst_2575_);
lean_closure_set(v___f_2578_, 1, v_k_2576_);
v___f_2579_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0));
v___x_2580_ = lean_box(0);
v___x_2581_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___f_2578_, v___x_2580_, v___f_2579_, v_t_2577_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27(lean_object* v_00_u03b1_2582_, lean_object* v_00_u03b2_2583_, lean_object* v_inst_2584_, lean_object* v_k_2585_, lean_object* v_t_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(v_inst_2584_, v_k_2585_, v_t_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(uint8_t v_x_2588_, lean_object* v_h__1_2589_, lean_object* v_h__2_2590_){
_start:
{
if (v_x_2588_ == 0)
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_dec(v_h__2_2590_);
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_apply_1(v_h__1_2589_, v___x_2591_);
return v___x_2592_;
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_dec(v_h__1_2589_);
v___x_2593_ = lean_box(v_x_2588_);
v___x_2594_ = lean_apply_2(v_h__2_2590_, v___x_2593_, lean_box(0));
return v___x_2594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg___boxed(lean_object* v_x_2595_, lean_object* v_h__1_2596_, lean_object* v_h__2_2597_){
_start:
{
uint8_t v_x_17__boxed_2598_; lean_object* v_res_2599_; 
v_x_17__boxed_2598_ = lean_unbox(v_x_2595_);
v_res_2599_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(v_x_17__boxed_2598_, v_h__1_2596_, v_h__2_2597_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(lean_object* v_motive_2600_, uint8_t v_x_2601_, lean_object* v_h__1_2602_, lean_object* v_h__2_2603_){
_start:
{
if (v_x_2601_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
lean_dec(v_h__2_2603_);
v___x_2604_ = lean_box(0);
v___x_2605_ = lean_apply_1(v_h__1_2602_, v___x_2604_);
return v___x_2605_;
}
else
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_dec(v_h__1_2602_);
v___x_2606_ = lean_box(v_x_2601_);
v___x_2607_ = lean_apply_2(v_h__2_2603_, v___x_2606_, lean_box(0));
return v___x_2607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___boxed(lean_object* v_motive_2608_, lean_object* v_x_2609_, lean_object* v_h__1_2610_, lean_object* v_h__2_2611_){
_start:
{
uint8_t v_x_28__boxed_2612_; lean_object* v_res_2613_; 
v_x_28__boxed_2612_ = lean_unbox(v_x_2609_);
v_res_2613_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(v_motive_2608_, v_x_28__boxed_2612_, v_h__1_2610_, v_h__2_2611_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_x_2614_, lean_object* v_x_2615_, lean_object* v_h__1_2616_, lean_object* v_h__2_2617_, lean_object* v_h__3_2618_){
_start:
{
switch(lean_obj_tag(v_x_2615_))
{
case 0:
{
lean_object* v_a_2619_; lean_object* v_a_2620_; lean_object* v_a_2621_; lean_object* v___x_2622_; 
lean_dec(v_h__3_2618_);
lean_dec(v_h__2_2617_);
v_a_2619_ = lean_ctor_get(v_x_2615_, 0);
lean_inc(v_a_2619_);
v_a_2620_ = lean_ctor_get(v_x_2615_, 1);
lean_inc(v_a_2620_);
v_a_2621_ = lean_ctor_get(v_x_2615_, 2);
lean_inc(v_a_2621_);
lean_dec_ref(v_x_2615_);
v___x_2622_ = lean_apply_5(v_h__1_2616_, v_x_2614_, v_a_2619_, lean_box(0), v_a_2620_, v_a_2621_);
return v___x_2622_;
}
case 1:
{
lean_object* v_a_2623_; lean_object* v_a_2624_; lean_object* v_a_2625_; lean_object* v___x_2626_; 
lean_dec(v_h__3_2618_);
lean_dec(v_h__1_2616_);
v_a_2623_ = lean_ctor_get(v_x_2615_, 0);
lean_inc(v_a_2623_);
v_a_2624_ = lean_ctor_get(v_x_2615_, 1);
lean_inc(v_a_2624_);
v_a_2625_ = lean_ctor_get(v_x_2615_, 2);
lean_inc(v_a_2625_);
lean_dec_ref(v_x_2615_);
v___x_2626_ = lean_apply_4(v_h__2_2617_, v_x_2614_, v_a_2623_, v_a_2624_, v_a_2625_);
return v___x_2626_;
}
default: 
{
lean_object* v_a_2627_; lean_object* v_a_2628_; lean_object* v_a_2629_; lean_object* v___x_2630_; 
lean_dec(v_h__2_2617_);
lean_dec(v_h__1_2616_);
v_a_2627_ = lean_ctor_get(v_x_2615_, 0);
lean_inc(v_a_2627_);
v_a_2628_ = lean_ctor_get(v_x_2615_, 1);
lean_inc(v_a_2628_);
v_a_2629_ = lean_ctor_get(v_x_2615_, 2);
lean_inc(v_a_2629_);
lean_dec_ref(v_x_2615_);
v___x_2630_ = lean_apply_5(v_h__3_2618_, v_x_2614_, v_a_2627_, v_a_2628_, lean_box(0), v_a_2629_);
return v___x_2630_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_2631_, lean_object* v_00_u03b2_2632_, lean_object* v_inst_2633_, lean_object* v_k_2634_, lean_object* v_motive_2635_, lean_object* v_x_2636_, lean_object* v_x_2637_, lean_object* v_h__1_2638_, lean_object* v_h__2_2639_, lean_object* v_h__3_2640_){
_start:
{
switch(lean_obj_tag(v_x_2637_))
{
case 0:
{
lean_object* v_a_2641_; lean_object* v_a_2642_; lean_object* v_a_2643_; lean_object* v___x_2644_; 
lean_dec(v_h__3_2640_);
lean_dec(v_h__2_2639_);
v_a_2641_ = lean_ctor_get(v_x_2637_, 0);
lean_inc(v_a_2641_);
v_a_2642_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_a_2642_);
v_a_2643_ = lean_ctor_get(v_x_2637_, 2);
lean_inc(v_a_2643_);
lean_dec_ref(v_x_2637_);
v___x_2644_ = lean_apply_5(v_h__1_2638_, v_x_2636_, v_a_2641_, lean_box(0), v_a_2642_, v_a_2643_);
return v___x_2644_;
}
case 1:
{
lean_object* v_a_2645_; lean_object* v_a_2646_; lean_object* v_a_2647_; lean_object* v___x_2648_; 
lean_dec(v_h__3_2640_);
lean_dec(v_h__1_2638_);
v_a_2645_ = lean_ctor_get(v_x_2637_, 0);
lean_inc(v_a_2645_);
v_a_2646_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_a_2646_);
v_a_2647_ = lean_ctor_get(v_x_2637_, 2);
lean_inc(v_a_2647_);
lean_dec_ref(v_x_2637_);
v___x_2648_ = lean_apply_4(v_h__2_2639_, v_x_2636_, v_a_2645_, v_a_2646_, v_a_2647_);
return v___x_2648_;
}
default: 
{
lean_object* v_a_2649_; lean_object* v_a_2650_; lean_object* v_a_2651_; lean_object* v___x_2652_; 
lean_dec(v_h__2_2639_);
lean_dec(v_h__1_2638_);
v_a_2649_ = lean_ctor_get(v_x_2637_, 0);
lean_inc(v_a_2649_);
v_a_2650_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_a_2650_);
v_a_2651_ = lean_ctor_get(v_x_2637_, 2);
lean_inc(v_a_2651_);
lean_dec_ref(v_x_2637_);
v___x_2652_ = lean_apply_5(v_h__3_2640_, v_x_2636_, v_a_2649_, v_a_2650_, lean_box(0), v_a_2651_);
return v___x_2652_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_2653_, lean_object* v_00_u03b2_2654_, lean_object* v_inst_2655_, lean_object* v_k_2656_, lean_object* v_motive_2657_, lean_object* v_x_2658_, lean_object* v_x_2659_, lean_object* v_h__1_2660_, lean_object* v_h__2_2661_, lean_object* v_h__3_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(v_00_u03b1_2653_, v_00_u03b2_2654_, v_inst_2655_, v_k_2656_, v_motive_2657_, v_x_2658_, v_x_2659_, v_h__1_2660_, v_h__2_2661_, v_h__3_2662_);
lean_dec(v_k_2656_);
lean_dec_ref(v_inst_2655_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(uint8_t v_x_2664_, lean_object* v_h__1_2665_, lean_object* v_h__2_2666_){
_start:
{
if (v_x_2664_ == 2)
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
lean_dec(v_h__2_2666_);
v___x_2667_ = lean_box(0);
v___x_2668_ = lean_apply_1(v_h__1_2665_, v___x_2667_);
return v___x_2668_;
}
else
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
lean_dec(v_h__1_2665_);
v___x_2669_ = lean_box(v_x_2664_);
v___x_2670_ = lean_apply_2(v_h__2_2666_, v___x_2669_, lean_box(0));
return v___x_2670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg___boxed(lean_object* v_x_2671_, lean_object* v_h__1_2672_, lean_object* v_h__2_2673_){
_start:
{
uint8_t v_x_17__boxed_2674_; lean_object* v_res_2675_; 
v_x_17__boxed_2674_ = lean_unbox(v_x_2671_);
v_res_2675_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(v_x_17__boxed_2674_, v_h__1_2672_, v_h__2_2673_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(lean_object* v_motive_2676_, uint8_t v_x_2677_, lean_object* v_h__1_2678_, lean_object* v_h__2_2679_){
_start:
{
if (v_x_2677_ == 2)
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
lean_dec(v_h__2_2679_);
v___x_2680_ = lean_box(0);
v___x_2681_ = lean_apply_1(v_h__1_2678_, v___x_2680_);
return v___x_2681_;
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
lean_dec(v_h__1_2678_);
v___x_2682_ = lean_box(v_x_2677_);
v___x_2683_ = lean_apply_2(v_h__2_2679_, v___x_2682_, lean_box(0));
return v___x_2683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___boxed(lean_object* v_motive_2684_, lean_object* v_x_2685_, lean_object* v_h__1_2686_, lean_object* v_h__2_2687_){
_start:
{
uint8_t v_x_28__boxed_2688_; lean_object* v_res_2689_; 
v_x_28__boxed_2688_ = lean_unbox(v_x_2685_);
v_res_2689_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(v_motive_2684_, v_x_28__boxed_2688_, v_h__1_2686_, v_h__2_2687_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(uint8_t v_x_2690_, lean_object* v_h__1_2691_, lean_object* v_h__2_2692_, lean_object* v_h__3_2693_){
_start:
{
switch(v_x_2690_)
{
case 0:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
lean_dec(v_h__3_2693_);
lean_dec(v_h__2_2692_);
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_apply_1(v_h__1_2691_, v___x_2694_);
return v___x_2695_;
}
case 1:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_dec(v_h__3_2693_);
lean_dec(v_h__1_2691_);
v___x_2696_ = lean_box(0);
v___x_2697_ = lean_apply_1(v_h__2_2692_, v___x_2696_);
return v___x_2697_;
}
default: 
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
lean_dec(v_h__2_2692_);
lean_dec(v_h__1_2691_);
v___x_2698_ = lean_box(0);
v___x_2699_ = lean_apply_1(v_h__3_2693_, v___x_2698_);
return v___x_2699_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object* v_x_2700_, lean_object* v_h__1_2701_, lean_object* v_h__2_2702_, lean_object* v_h__3_2703_){
_start:
{
uint8_t v_x_36__boxed_2704_; lean_object* v_res_2705_; 
v_x_36__boxed_2704_ = lean_unbox(v_x_2700_);
v_res_2705_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(v_x_36__boxed_2704_, v_h__1_2701_, v_h__2_2702_, v_h__3_2703_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(lean_object* v_motive_2706_, uint8_t v_x_2707_, lean_object* v_h__1_2708_, lean_object* v_h__2_2709_, lean_object* v_h__3_2710_){
_start:
{
switch(v_x_2707_)
{
case 0:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
lean_dec(v_h__3_2710_);
lean_dec(v_h__2_2709_);
v___x_2711_ = lean_box(0);
v___x_2712_ = lean_apply_1(v_h__1_2708_, v___x_2711_);
return v___x_2712_;
}
case 1:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_dec(v_h__3_2710_);
lean_dec(v_h__1_2708_);
v___x_2713_ = lean_box(0);
v___x_2714_ = lean_apply_1(v_h__2_2709_, v___x_2713_);
return v___x_2714_;
}
default: 
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_dec(v_h__2_2709_);
lean_dec(v_h__1_2708_);
v___x_2715_ = lean_box(0);
v___x_2716_ = lean_apply_1(v_h__3_2710_, v___x_2715_);
return v___x_2716_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___boxed(lean_object* v_motive_2717_, lean_object* v_x_2718_, lean_object* v_h__1_2719_, lean_object* v_h__2_2720_, lean_object* v_h__3_2721_){
_start:
{
uint8_t v_x_51__boxed_2722_; lean_object* v_res_2723_; 
v_x_51__boxed_2722_ = lean_unbox(v_x_2718_);
v_res_2723_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(v_motive_2717_, v_x_51__boxed_2722_, v_h__1_2719_, v_h__2_2720_, v_h__3_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___redArg(lean_object* v_x_2724_, lean_object* v_h__1_2725_, lean_object* v_h__2_2726_){
_start:
{
if (lean_obj_tag(v_x_2724_) == 0)
{
lean_object* v_size_2727_; lean_object* v_k_2728_; lean_object* v_v_2729_; lean_object* v_l_2730_; lean_object* v_r_2731_; lean_object* v___x_2732_; 
lean_dec(v_h__1_2725_);
v_size_2727_ = lean_ctor_get(v_x_2724_, 0);
lean_inc(v_size_2727_);
v_k_2728_ = lean_ctor_get(v_x_2724_, 1);
lean_inc(v_k_2728_);
v_v_2729_ = lean_ctor_get(v_x_2724_, 2);
lean_inc(v_v_2729_);
v_l_2730_ = lean_ctor_get(v_x_2724_, 3);
lean_inc(v_l_2730_);
v_r_2731_ = lean_ctor_get(v_x_2724_, 4);
lean_inc(v_r_2731_);
lean_dec_ref(v_x_2724_);
v___x_2732_ = lean_apply_7(v_h__2_2726_, v_size_2727_, v_k_2728_, v_v_2729_, v_l_2730_, v_r_2731_, lean_box(0), lean_box(0));
return v___x_2732_;
}
else
{
lean_object* v___x_2733_; 
lean_dec(v_h__2_2726_);
v___x_2733_ = lean_apply_2(v_h__1_2725_, lean_box(0), lean_box(0));
return v___x_2733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(lean_object* v_00_u03b1_2734_, lean_object* v_00_u03b2_2735_, lean_object* v_inst_2736_, lean_object* v_k_2737_, lean_object* v_motive_2738_, lean_object* v_x_2739_, lean_object* v_x_2740_, lean_object* v_x_2741_, lean_object* v_h__1_2742_, lean_object* v_h__2_2743_){
_start:
{
if (lean_obj_tag(v_x_2739_) == 0)
{
lean_object* v_size_2744_; lean_object* v_k_2745_; lean_object* v_v_2746_; lean_object* v_l_2747_; lean_object* v_r_2748_; lean_object* v___x_2749_; 
lean_dec(v_h__1_2742_);
v_size_2744_ = lean_ctor_get(v_x_2739_, 0);
lean_inc(v_size_2744_);
v_k_2745_ = lean_ctor_get(v_x_2739_, 1);
lean_inc(v_k_2745_);
v_v_2746_ = lean_ctor_get(v_x_2739_, 2);
lean_inc(v_v_2746_);
v_l_2747_ = lean_ctor_get(v_x_2739_, 3);
lean_inc(v_l_2747_);
v_r_2748_ = lean_ctor_get(v_x_2739_, 4);
lean_inc(v_r_2748_);
lean_dec_ref(v_x_2739_);
v___x_2749_ = lean_apply_7(v_h__2_2743_, v_size_2744_, v_k_2745_, v_v_2746_, v_l_2747_, v_r_2748_, lean_box(0), lean_box(0));
return v___x_2749_;
}
else
{
lean_object* v___x_2750_; 
lean_dec(v_h__2_2743_);
v___x_2750_ = lean_apply_2(v_h__1_2742_, lean_box(0), lean_box(0));
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___boxed(lean_object* v_00_u03b1_2751_, lean_object* v_00_u03b2_2752_, lean_object* v_inst_2753_, lean_object* v_k_2754_, lean_object* v_motive_2755_, lean_object* v_x_2756_, lean_object* v_x_2757_, lean_object* v_x_2758_, lean_object* v_h__1_2759_, lean_object* v_h__2_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(v_00_u03b1_2751_, v_00_u03b2_2752_, v_inst_2753_, v_k_2754_, v_motive_2755_, v_x_2756_, v_x_2757_, v_x_2758_, v_h__1_2759_, v_h__2_2760_);
lean_dec(v_k_2754_);
lean_dec_ref(v_inst_2753_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___redArg(lean_object* v_x_2762_, lean_object* v_h__1_2763_, lean_object* v_h__2_2764_){
_start:
{
if (lean_obj_tag(v_x_2762_) == 0)
{
lean_object* v_size_2765_; lean_object* v_k_2766_; lean_object* v_v_2767_; lean_object* v_l_2768_; lean_object* v_r_2769_; lean_object* v___x_2770_; 
lean_dec(v_h__1_2763_);
v_size_2765_ = lean_ctor_get(v_x_2762_, 0);
lean_inc(v_size_2765_);
v_k_2766_ = lean_ctor_get(v_x_2762_, 1);
lean_inc(v_k_2766_);
v_v_2767_ = lean_ctor_get(v_x_2762_, 2);
lean_inc(v_v_2767_);
v_l_2768_ = lean_ctor_get(v_x_2762_, 3);
lean_inc(v_l_2768_);
v_r_2769_ = lean_ctor_get(v_x_2762_, 4);
lean_inc(v_r_2769_);
lean_dec_ref(v_x_2762_);
v___x_2770_ = lean_apply_7(v_h__2_2764_, v_size_2765_, v_k_2766_, v_v_2767_, v_l_2768_, v_r_2769_, lean_box(0), lean_box(0));
return v___x_2770_;
}
else
{
lean_object* v___x_2771_; 
lean_dec(v_h__2_2764_);
v___x_2771_ = lean_apply_2(v_h__1_2763_, lean_box(0), lean_box(0));
return v___x_2771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(lean_object* v_00_u03b1_2772_, lean_object* v_00_u03b2_2773_, lean_object* v_inst_2774_, lean_object* v_k_2775_, lean_object* v_motive_2776_, lean_object* v_x_2777_, lean_object* v_x_2778_, lean_object* v_x_2779_, lean_object* v_h__1_2780_, lean_object* v_h__2_2781_){
_start:
{
if (lean_obj_tag(v_x_2777_) == 0)
{
lean_object* v_size_2782_; lean_object* v_k_2783_; lean_object* v_v_2784_; lean_object* v_l_2785_; lean_object* v_r_2786_; lean_object* v___x_2787_; 
lean_dec(v_h__1_2780_);
v_size_2782_ = lean_ctor_get(v_x_2777_, 0);
lean_inc(v_size_2782_);
v_k_2783_ = lean_ctor_get(v_x_2777_, 1);
lean_inc(v_k_2783_);
v_v_2784_ = lean_ctor_get(v_x_2777_, 2);
lean_inc(v_v_2784_);
v_l_2785_ = lean_ctor_get(v_x_2777_, 3);
lean_inc(v_l_2785_);
v_r_2786_ = lean_ctor_get(v_x_2777_, 4);
lean_inc(v_r_2786_);
lean_dec_ref(v_x_2777_);
v___x_2787_ = lean_apply_7(v_h__2_2781_, v_size_2782_, v_k_2783_, v_v_2784_, v_l_2785_, v_r_2786_, lean_box(0), lean_box(0));
return v___x_2787_;
}
else
{
lean_object* v___x_2788_; 
lean_dec(v_h__2_2781_);
v___x_2788_ = lean_apply_2(v_h__1_2780_, lean_box(0), lean_box(0));
return v___x_2788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___boxed(lean_object* v_00_u03b1_2789_, lean_object* v_00_u03b2_2790_, lean_object* v_inst_2791_, lean_object* v_k_2792_, lean_object* v_motive_2793_, lean_object* v_x_2794_, lean_object* v_x_2795_, lean_object* v_x_2796_, lean_object* v_h__1_2797_, lean_object* v_h__2_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(v_00_u03b1_2789_, v_00_u03b2_2790_, v_inst_2791_, v_k_2792_, v_motive_2793_, v_x_2794_, v_x_2795_, v_x_2796_, v_h__1_2797_, v_h__2_2798_);
lean_dec(v_k_2792_);
lean_dec_ref(v_inst_2791_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___redArg(lean_object* v_x_2800_, lean_object* v_h__1_2801_, lean_object* v_h__2_2802_){
_start:
{
if (lean_obj_tag(v_x_2800_) == 0)
{
lean_object* v_size_2803_; lean_object* v_k_2804_; lean_object* v_v_2805_; lean_object* v_l_2806_; lean_object* v_r_2807_; lean_object* v___x_2808_; 
lean_dec(v_h__1_2801_);
v_size_2803_ = lean_ctor_get(v_x_2800_, 0);
lean_inc(v_size_2803_);
v_k_2804_ = lean_ctor_get(v_x_2800_, 1);
lean_inc(v_k_2804_);
v_v_2805_ = lean_ctor_get(v_x_2800_, 2);
lean_inc(v_v_2805_);
v_l_2806_ = lean_ctor_get(v_x_2800_, 3);
lean_inc(v_l_2806_);
v_r_2807_ = lean_ctor_get(v_x_2800_, 4);
lean_inc(v_r_2807_);
lean_dec_ref(v_x_2800_);
v___x_2808_ = lean_apply_7(v_h__2_2802_, v_size_2803_, v_k_2804_, v_v_2805_, v_l_2806_, v_r_2807_, lean_box(0), lean_box(0));
return v___x_2808_;
}
else
{
lean_object* v___x_2809_; 
lean_dec(v_h__2_2802_);
v___x_2809_ = lean_apply_2(v_h__1_2801_, lean_box(0), lean_box(0));
return v___x_2809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(lean_object* v_00_u03b1_2810_, lean_object* v_00_u03b2_2811_, lean_object* v_inst_2812_, lean_object* v_k_2813_, lean_object* v_motive_2814_, lean_object* v_x_2815_, lean_object* v_x_2816_, lean_object* v_x_2817_, lean_object* v_h__1_2818_, lean_object* v_h__2_2819_){
_start:
{
if (lean_obj_tag(v_x_2815_) == 0)
{
lean_object* v_size_2820_; lean_object* v_k_2821_; lean_object* v_v_2822_; lean_object* v_l_2823_; lean_object* v_r_2824_; lean_object* v___x_2825_; 
lean_dec(v_h__1_2818_);
v_size_2820_ = lean_ctor_get(v_x_2815_, 0);
lean_inc(v_size_2820_);
v_k_2821_ = lean_ctor_get(v_x_2815_, 1);
lean_inc(v_k_2821_);
v_v_2822_ = lean_ctor_get(v_x_2815_, 2);
lean_inc(v_v_2822_);
v_l_2823_ = lean_ctor_get(v_x_2815_, 3);
lean_inc(v_l_2823_);
v_r_2824_ = lean_ctor_get(v_x_2815_, 4);
lean_inc(v_r_2824_);
lean_dec_ref(v_x_2815_);
v___x_2825_ = lean_apply_7(v_h__2_2819_, v_size_2820_, v_k_2821_, v_v_2822_, v_l_2823_, v_r_2824_, lean_box(0), lean_box(0));
return v___x_2825_;
}
else
{
lean_object* v___x_2826_; 
lean_dec(v_h__2_2819_);
v___x_2826_ = lean_apply_2(v_h__1_2818_, lean_box(0), lean_box(0));
return v___x_2826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___boxed(lean_object* v_00_u03b1_2827_, lean_object* v_00_u03b2_2828_, lean_object* v_inst_2829_, lean_object* v_k_2830_, lean_object* v_motive_2831_, lean_object* v_x_2832_, lean_object* v_x_2833_, lean_object* v_x_2834_, lean_object* v_h__1_2835_, lean_object* v_h__2_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(v_00_u03b1_2827_, v_00_u03b2_2828_, v_inst_2829_, v_k_2830_, v_motive_2831_, v_x_2832_, v_x_2833_, v_x_2834_, v_h__1_2835_, v_h__2_2836_);
lean_dec(v_k_2830_);
lean_dec_ref(v_inst_2829_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(uint8_t v_x_2838_, lean_object* v_h__1_2839_, lean_object* v_h__2_2840_, lean_object* v_h__3_2841_){
_start:
{
switch(v_x_2838_)
{
case 0:
{
lean_object* v___x_2842_; 
lean_dec(v_h__2_2840_);
lean_dec(v_h__1_2839_);
v___x_2842_ = lean_apply_1(v_h__3_2841_, lean_box(0));
return v___x_2842_;
}
case 1:
{
lean_object* v___x_2843_; 
lean_dec(v_h__3_2841_);
lean_dec(v_h__1_2839_);
v___x_2843_ = lean_apply_1(v_h__2_2840_, lean_box(0));
return v___x_2843_;
}
default: 
{
lean_object* v___x_2844_; 
lean_dec(v_h__3_2841_);
lean_dec(v_h__2_2840_);
v___x_2844_ = lean_apply_1(v_h__1_2839_, lean_box(0));
return v___x_2844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg___boxed(lean_object* v_x_2845_, lean_object* v_h__1_2846_, lean_object* v_h__2_2847_, lean_object* v_h__3_2848_){
_start:
{
uint8_t v_x_33__boxed_2849_; lean_object* v_res_2850_; 
v_x_33__boxed_2849_ = lean_unbox(v_x_2845_);
v_res_2850_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(v_x_33__boxed_2849_, v_h__1_2846_, v_h__2_2847_, v_h__3_2848_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(lean_object* v_motive_2851_, uint8_t v_x_2852_, lean_object* v_h__1_2853_, lean_object* v_h__2_2854_, lean_object* v_h__3_2855_){
_start:
{
switch(v_x_2852_)
{
case 0:
{
lean_object* v___x_2856_; 
lean_dec(v_h__2_2854_);
lean_dec(v_h__1_2853_);
v___x_2856_ = lean_apply_1(v_h__3_2855_, lean_box(0));
return v___x_2856_;
}
case 1:
{
lean_object* v___x_2857_; 
lean_dec(v_h__3_2855_);
lean_dec(v_h__1_2853_);
v___x_2857_ = lean_apply_1(v_h__2_2854_, lean_box(0));
return v___x_2857_;
}
default: 
{
lean_object* v___x_2858_; 
lean_dec(v_h__3_2855_);
lean_dec(v_h__2_2854_);
v___x_2858_ = lean_apply_1(v_h__1_2853_, lean_box(0));
return v___x_2858_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___boxed(lean_object* v_motive_2859_, lean_object* v_x_2860_, lean_object* v_h__1_2861_, lean_object* v_h__2_2862_, lean_object* v_h__3_2863_){
_start:
{
uint8_t v_x_42__boxed_2864_; lean_object* v_res_2865_; 
v_x_42__boxed_2864_ = lean_unbox(v_x_2860_);
v_res_2865_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(v_motive_2859_, v_x_42__boxed_2864_, v_h__1_2861_, v_h__2_2862_, v_h__3_2863_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___redArg(lean_object* v_x_2866_, lean_object* v_h__1_2867_, lean_object* v_h__2_2868_){
_start:
{
if (lean_obj_tag(v_x_2866_) == 0)
{
lean_object* v_size_2869_; lean_object* v_k_2870_; lean_object* v_v_2871_; lean_object* v_l_2872_; lean_object* v_r_2873_; lean_object* v___x_2874_; 
lean_dec(v_h__1_2867_);
v_size_2869_ = lean_ctor_get(v_x_2866_, 0);
lean_inc(v_size_2869_);
v_k_2870_ = lean_ctor_get(v_x_2866_, 1);
lean_inc(v_k_2870_);
v_v_2871_ = lean_ctor_get(v_x_2866_, 2);
lean_inc(v_v_2871_);
v_l_2872_ = lean_ctor_get(v_x_2866_, 3);
lean_inc(v_l_2872_);
v_r_2873_ = lean_ctor_get(v_x_2866_, 4);
lean_inc(v_r_2873_);
lean_dec_ref(v_x_2866_);
v___x_2874_ = lean_apply_7(v_h__2_2868_, v_size_2869_, v_k_2870_, v_v_2871_, v_l_2872_, v_r_2873_, lean_box(0), lean_box(0));
return v___x_2874_;
}
else
{
lean_object* v___x_2875_; 
lean_dec(v_h__2_2868_);
v___x_2875_ = lean_apply_2(v_h__1_2867_, lean_box(0), lean_box(0));
return v___x_2875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(lean_object* v_00_u03b1_2876_, lean_object* v_00_u03b2_2877_, lean_object* v_inst_2878_, lean_object* v_k_2879_, lean_object* v_motive_2880_, lean_object* v_x_2881_, lean_object* v_x_2882_, lean_object* v_x_2883_, lean_object* v_h__1_2884_, lean_object* v_h__2_2885_){
_start:
{
if (lean_obj_tag(v_x_2881_) == 0)
{
lean_object* v_size_2886_; lean_object* v_k_2887_; lean_object* v_v_2888_; lean_object* v_l_2889_; lean_object* v_r_2890_; lean_object* v___x_2891_; 
lean_dec(v_h__1_2884_);
v_size_2886_ = lean_ctor_get(v_x_2881_, 0);
lean_inc(v_size_2886_);
v_k_2887_ = lean_ctor_get(v_x_2881_, 1);
lean_inc(v_k_2887_);
v_v_2888_ = lean_ctor_get(v_x_2881_, 2);
lean_inc(v_v_2888_);
v_l_2889_ = lean_ctor_get(v_x_2881_, 3);
lean_inc(v_l_2889_);
v_r_2890_ = lean_ctor_get(v_x_2881_, 4);
lean_inc(v_r_2890_);
lean_dec_ref(v_x_2881_);
v___x_2891_ = lean_apply_7(v_h__2_2885_, v_size_2886_, v_k_2887_, v_v_2888_, v_l_2889_, v_r_2890_, lean_box(0), lean_box(0));
return v___x_2891_;
}
else
{
lean_object* v___x_2892_; 
lean_dec(v_h__2_2885_);
v___x_2892_ = lean_apply_2(v_h__1_2884_, lean_box(0), lean_box(0));
return v___x_2892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___boxed(lean_object* v_00_u03b1_2893_, lean_object* v_00_u03b2_2894_, lean_object* v_inst_2895_, lean_object* v_k_2896_, lean_object* v_motive_2897_, lean_object* v_x_2898_, lean_object* v_x_2899_, lean_object* v_x_2900_, lean_object* v_h__1_2901_, lean_object* v_h__2_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(v_00_u03b1_2893_, v_00_u03b2_2894_, v_inst_2895_, v_k_2896_, v_motive_2897_, v_x_2898_, v_x_2899_, v_x_2900_, v_h__1_2901_, v_h__2_2902_);
lean_dec(v_k_2896_);
lean_dec_ref(v_inst_2895_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(lean_object* v_x_2904_, lean_object* v_x_2905_, lean_object* v_h__1_2906_, lean_object* v_h__2_2907_){
_start:
{
if (lean_obj_tag(v_x_2904_) == 0)
{
lean_object* v_size_2908_; lean_object* v_k_2909_; lean_object* v_v_2910_; lean_object* v_l_2911_; lean_object* v_r_2912_; lean_object* v___x_2913_; 
lean_dec(v_h__1_2906_);
v_size_2908_ = lean_ctor_get(v_x_2904_, 0);
lean_inc(v_size_2908_);
v_k_2909_ = lean_ctor_get(v_x_2904_, 1);
lean_inc(v_k_2909_);
v_v_2910_ = lean_ctor_get(v_x_2904_, 2);
lean_inc(v_v_2910_);
v_l_2911_ = lean_ctor_get(v_x_2904_, 3);
lean_inc(v_l_2911_);
v_r_2912_ = lean_ctor_get(v_x_2904_, 4);
lean_inc(v_r_2912_);
lean_dec_ref(v_x_2904_);
v___x_2913_ = lean_apply_6(v_h__2_2907_, v_size_2908_, v_k_2909_, v_v_2910_, v_l_2911_, v_r_2912_, v_x_2905_);
return v___x_2913_;
}
else
{
lean_object* v___x_2914_; 
lean_dec(v_h__2_2907_);
v___x_2914_ = lean_apply_1(v_h__1_2906_, v_x_2905_);
return v___x_2914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter(lean_object* v_00_u03b1_2915_, lean_object* v_00_u03b2_2916_, lean_object* v_motive_2917_, lean_object* v_x_2918_, lean_object* v_x_2919_, lean_object* v_h__1_2920_, lean_object* v_h__2_2921_){
_start:
{
if (lean_obj_tag(v_x_2918_) == 0)
{
lean_object* v_size_2922_; lean_object* v_k_2923_; lean_object* v_v_2924_; lean_object* v_l_2925_; lean_object* v_r_2926_; lean_object* v___x_2927_; 
lean_dec(v_h__1_2920_);
v_size_2922_ = lean_ctor_get(v_x_2918_, 0);
lean_inc(v_size_2922_);
v_k_2923_ = lean_ctor_get(v_x_2918_, 1);
lean_inc(v_k_2923_);
v_v_2924_ = lean_ctor_get(v_x_2918_, 2);
lean_inc(v_v_2924_);
v_l_2925_ = lean_ctor_get(v_x_2918_, 3);
lean_inc(v_l_2925_);
v_r_2926_ = lean_ctor_get(v_x_2918_, 4);
lean_inc(v_r_2926_);
lean_dec_ref(v_x_2918_);
v___x_2927_ = lean_apply_6(v_h__2_2921_, v_size_2922_, v_k_2923_, v_v_2924_, v_l_2925_, v_r_2926_, v_x_2919_);
return v___x_2927_;
}
else
{
lean_object* v___x_2928_; 
lean_dec(v_h__2_2921_);
v___x_2928_ = lean_apply_1(v_h__1_2920_, v_x_2919_);
return v___x_2928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(lean_object* v_x_2929_, lean_object* v_x_2930_, lean_object* v_h__1_2931_){
_start:
{
lean_object* v_size_2932_; lean_object* v_k_2933_; lean_object* v_v_2934_; lean_object* v_l_2935_; lean_object* v_r_2936_; lean_object* v___x_2937_; 
v_size_2932_ = lean_ctor_get(v_x_2929_, 0);
lean_inc(v_size_2932_);
v_k_2933_ = lean_ctor_get(v_x_2929_, 1);
lean_inc(v_k_2933_);
v_v_2934_ = lean_ctor_get(v_x_2929_, 2);
lean_inc(v_v_2934_);
v_l_2935_ = lean_ctor_get(v_x_2929_, 3);
lean_inc(v_l_2935_);
v_r_2936_ = lean_ctor_get(v_x_2929_, 4);
lean_inc(v_r_2936_);
lean_dec(v_x_2929_);
v___x_2937_ = lean_apply_8(v_h__1_2931_, v_size_2932_, v_k_2933_, v_v_2934_, v_l_2935_, v_r_2936_, lean_box(0), v_x_2930_, lean_box(0));
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter(lean_object* v_00_u03b1_2938_, lean_object* v_00_u03b2_2939_, lean_object* v_motive_2940_, lean_object* v_x_2941_, lean_object* v_x_2942_, lean_object* v_x_2943_, lean_object* v_x_2944_, lean_object* v_h__1_2945_){
_start:
{
lean_object* v_size_2946_; lean_object* v_k_2947_; lean_object* v_v_2948_; lean_object* v_l_2949_; lean_object* v_r_2950_; lean_object* v___x_2951_; 
v_size_2946_ = lean_ctor_get(v_x_2941_, 0);
lean_inc(v_size_2946_);
v_k_2947_ = lean_ctor_get(v_x_2941_, 1);
lean_inc(v_k_2947_);
v_v_2948_ = lean_ctor_get(v_x_2941_, 2);
lean_inc(v_v_2948_);
v_l_2949_ = lean_ctor_get(v_x_2941_, 3);
lean_inc(v_l_2949_);
v_r_2950_ = lean_ctor_get(v_x_2941_, 4);
lean_inc(v_r_2950_);
lean_dec(v_x_2941_);
v___x_2951_ = lean_apply_8(v_h__1_2945_, v_size_2946_, v_k_2947_, v_v_2948_, v_l_2949_, v_r_2950_, lean_box(0), v_x_2943_, lean_box(0));
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter___redArg(lean_object* v_x_2952_, lean_object* v_x_2953_, lean_object* v_x_2954_, lean_object* v_h__1_2955_, lean_object* v_h__2_2956_){
_start:
{
if (lean_obj_tag(v_x_2952_) == 0)
{
lean_object* v_size_2957_; lean_object* v_k_2958_; lean_object* v_v_2959_; lean_object* v_l_2960_; lean_object* v_r_2961_; lean_object* v___x_2962_; 
lean_dec(v_h__1_2955_);
v_size_2957_ = lean_ctor_get(v_x_2952_, 0);
lean_inc(v_size_2957_);
v_k_2958_ = lean_ctor_get(v_x_2952_, 1);
lean_inc(v_k_2958_);
v_v_2959_ = lean_ctor_get(v_x_2952_, 2);
lean_inc(v_v_2959_);
v_l_2960_ = lean_ctor_get(v_x_2952_, 3);
lean_inc(v_l_2960_);
v_r_2961_ = lean_ctor_get(v_x_2952_, 4);
lean_inc(v_r_2961_);
lean_dec_ref(v_x_2952_);
v___x_2962_ = lean_apply_7(v_h__2_2956_, v_size_2957_, v_k_2958_, v_v_2959_, v_l_2960_, v_r_2961_, v_x_2953_, v_x_2954_);
return v___x_2962_;
}
else
{
lean_object* v___x_2963_; 
lean_dec(v_h__2_2956_);
v___x_2963_ = lean_apply_2(v_h__1_2955_, v_x_2953_, v_x_2954_);
return v___x_2963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2964_, lean_object* v_00_u03b2_2965_, lean_object* v_motive_2966_, lean_object* v_x_2967_, lean_object* v_x_2968_, lean_object* v_x_2969_, lean_object* v_h__1_2970_, lean_object* v_h__2_2971_){
_start:
{
if (lean_obj_tag(v_x_2967_) == 0)
{
lean_object* v_size_2972_; lean_object* v_k_2973_; lean_object* v_v_2974_; lean_object* v_l_2975_; lean_object* v_r_2976_; lean_object* v___x_2977_; 
lean_dec(v_h__1_2970_);
v_size_2972_ = lean_ctor_get(v_x_2967_, 0);
lean_inc(v_size_2972_);
v_k_2973_ = lean_ctor_get(v_x_2967_, 1);
lean_inc(v_k_2973_);
v_v_2974_ = lean_ctor_get(v_x_2967_, 2);
lean_inc(v_v_2974_);
v_l_2975_ = lean_ctor_get(v_x_2967_, 3);
lean_inc(v_l_2975_);
v_r_2976_ = lean_ctor_get(v_x_2967_, 4);
lean_inc(v_r_2976_);
lean_dec_ref(v_x_2967_);
v___x_2977_ = lean_apply_7(v_h__2_2971_, v_size_2972_, v_k_2973_, v_v_2974_, v_l_2975_, v_r_2976_, v_x_2968_, v_x_2969_);
return v___x_2977_;
}
else
{
lean_object* v___x_2978_; 
lean_dec(v_h__2_2971_);
v___x_2978_ = lean_apply_2(v_h__1_2970_, v_x_2968_, v_x_2969_);
return v___x_2978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___redArg(lean_object* v_x_2979_, lean_object* v_h__1_2980_, lean_object* v_h__2_2981_){
_start:
{
if (lean_obj_tag(v_x_2979_) == 0)
{
lean_object* v_size_2982_; lean_object* v_k_2983_; lean_object* v_v_2984_; lean_object* v_l_2985_; lean_object* v_r_2986_; lean_object* v___x_2987_; 
lean_dec(v_h__1_2980_);
v_size_2982_ = lean_ctor_get(v_x_2979_, 0);
lean_inc(v_size_2982_);
v_k_2983_ = lean_ctor_get(v_x_2979_, 1);
lean_inc(v_k_2983_);
v_v_2984_ = lean_ctor_get(v_x_2979_, 2);
lean_inc(v_v_2984_);
v_l_2985_ = lean_ctor_get(v_x_2979_, 3);
lean_inc(v_l_2985_);
v_r_2986_ = lean_ctor_get(v_x_2979_, 4);
lean_inc(v_r_2986_);
lean_dec_ref(v_x_2979_);
v___x_2987_ = lean_apply_7(v_h__2_2981_, v_size_2982_, v_k_2983_, v_v_2984_, v_l_2985_, v_r_2986_, lean_box(0), lean_box(0));
return v___x_2987_;
}
else
{
lean_object* v___x_2988_; 
lean_dec(v_h__2_2981_);
v___x_2988_ = lean_apply_2(v_h__1_2980_, lean_box(0), lean_box(0));
return v___x_2988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(lean_object* v_00_u03b1_2989_, lean_object* v_00_u03b2_2990_, lean_object* v_inst_2991_, lean_object* v_k_2992_, lean_object* v_motive_2993_, lean_object* v_x_2994_, lean_object* v_x_2995_, lean_object* v_x_2996_, lean_object* v_h__1_2997_, lean_object* v_h__2_2998_){
_start:
{
if (lean_obj_tag(v_x_2994_) == 0)
{
lean_object* v_size_2999_; lean_object* v_k_3000_; lean_object* v_v_3001_; lean_object* v_l_3002_; lean_object* v_r_3003_; lean_object* v___x_3004_; 
lean_dec(v_h__1_2997_);
v_size_2999_ = lean_ctor_get(v_x_2994_, 0);
lean_inc(v_size_2999_);
v_k_3000_ = lean_ctor_get(v_x_2994_, 1);
lean_inc(v_k_3000_);
v_v_3001_ = lean_ctor_get(v_x_2994_, 2);
lean_inc(v_v_3001_);
v_l_3002_ = lean_ctor_get(v_x_2994_, 3);
lean_inc(v_l_3002_);
v_r_3003_ = lean_ctor_get(v_x_2994_, 4);
lean_inc(v_r_3003_);
lean_dec_ref(v_x_2994_);
v___x_3004_ = lean_apply_7(v_h__2_2998_, v_size_2999_, v_k_3000_, v_v_3001_, v_l_3002_, v_r_3003_, lean_box(0), lean_box(0));
return v___x_3004_;
}
else
{
lean_object* v___x_3005_; 
lean_dec(v_h__2_2998_);
v___x_3005_ = lean_apply_2(v_h__1_2997_, lean_box(0), lean_box(0));
return v___x_3005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___boxed(lean_object* v_00_u03b1_3006_, lean_object* v_00_u03b2_3007_, lean_object* v_inst_3008_, lean_object* v_k_3009_, lean_object* v_motive_3010_, lean_object* v_x_3011_, lean_object* v_x_3012_, lean_object* v_x_3013_, lean_object* v_h__1_3014_, lean_object* v_h__2_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(v_00_u03b1_3006_, v_00_u03b2_3007_, v_inst_3008_, v_k_3009_, v_motive_3010_, v_x_3011_, v_x_3012_, v_x_3013_, v_h__1_3014_, v_h__2_3015_);
lean_dec(v_k_3009_);
lean_dec_ref(v_inst_3008_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___redArg(lean_object* v_x_3017_, lean_object* v_h__1_3018_, lean_object* v_h__2_3019_){
_start:
{
if (lean_obj_tag(v_x_3017_) == 0)
{
lean_object* v_size_3020_; lean_object* v_k_3021_; lean_object* v_v_3022_; lean_object* v_l_3023_; lean_object* v_r_3024_; lean_object* v___x_3025_; 
lean_dec(v_h__1_3018_);
v_size_3020_ = lean_ctor_get(v_x_3017_, 0);
lean_inc(v_size_3020_);
v_k_3021_ = lean_ctor_get(v_x_3017_, 1);
lean_inc(v_k_3021_);
v_v_3022_ = lean_ctor_get(v_x_3017_, 2);
lean_inc(v_v_3022_);
v_l_3023_ = lean_ctor_get(v_x_3017_, 3);
lean_inc(v_l_3023_);
v_r_3024_ = lean_ctor_get(v_x_3017_, 4);
lean_inc(v_r_3024_);
lean_dec_ref(v_x_3017_);
v___x_3025_ = lean_apply_7(v_h__2_3019_, v_size_3020_, v_k_3021_, v_v_3022_, v_l_3023_, v_r_3024_, lean_box(0), lean_box(0));
return v___x_3025_;
}
else
{
lean_object* v___x_3026_; 
lean_dec(v_h__2_3019_);
v___x_3026_ = lean_apply_2(v_h__1_3018_, lean_box(0), lean_box(0));
return v___x_3026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(lean_object* v_00_u03b1_3027_, lean_object* v_00_u03b2_3028_, lean_object* v_inst_3029_, lean_object* v_k_3030_, lean_object* v_motive_3031_, lean_object* v_x_3032_, lean_object* v_x_3033_, lean_object* v_x_3034_, lean_object* v_h__1_3035_, lean_object* v_h__2_3036_){
_start:
{
if (lean_obj_tag(v_x_3032_) == 0)
{
lean_object* v_size_3037_; lean_object* v_k_3038_; lean_object* v_v_3039_; lean_object* v_l_3040_; lean_object* v_r_3041_; lean_object* v___x_3042_; 
lean_dec(v_h__1_3035_);
v_size_3037_ = lean_ctor_get(v_x_3032_, 0);
lean_inc(v_size_3037_);
v_k_3038_ = lean_ctor_get(v_x_3032_, 1);
lean_inc(v_k_3038_);
v_v_3039_ = lean_ctor_get(v_x_3032_, 2);
lean_inc(v_v_3039_);
v_l_3040_ = lean_ctor_get(v_x_3032_, 3);
lean_inc(v_l_3040_);
v_r_3041_ = lean_ctor_get(v_x_3032_, 4);
lean_inc(v_r_3041_);
lean_dec_ref(v_x_3032_);
v___x_3042_ = lean_apply_7(v_h__2_3036_, v_size_3037_, v_k_3038_, v_v_3039_, v_l_3040_, v_r_3041_, lean_box(0), lean_box(0));
return v___x_3042_;
}
else
{
lean_object* v___x_3043_; 
lean_dec(v_h__2_3036_);
v___x_3043_ = lean_apply_2(v_h__1_3035_, lean_box(0), lean_box(0));
return v___x_3043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___boxed(lean_object* v_00_u03b1_3044_, lean_object* v_00_u03b2_3045_, lean_object* v_inst_3046_, lean_object* v_k_3047_, lean_object* v_motive_3048_, lean_object* v_x_3049_, lean_object* v_x_3050_, lean_object* v_x_3051_, lean_object* v_h__1_3052_, lean_object* v_h__2_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(v_00_u03b1_3044_, v_00_u03b2_3045_, v_inst_3046_, v_k_3047_, v_motive_3048_, v_x_3049_, v_x_3050_, v_x_3051_, v_h__1_3052_, v_h__2_3053_);
lean_dec(v_k_3047_);
lean_dec_ref(v_inst_3046_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___redArg(lean_object* v_x_3055_, lean_object* v_h__1_3056_, lean_object* v_h__2_3057_){
_start:
{
if (lean_obj_tag(v_x_3055_) == 0)
{
lean_object* v_size_3058_; lean_object* v_k_3059_; lean_object* v_v_3060_; lean_object* v_l_3061_; lean_object* v_r_3062_; lean_object* v___x_3063_; 
lean_dec(v_h__1_3056_);
v_size_3058_ = lean_ctor_get(v_x_3055_, 0);
lean_inc(v_size_3058_);
v_k_3059_ = lean_ctor_get(v_x_3055_, 1);
lean_inc(v_k_3059_);
v_v_3060_ = lean_ctor_get(v_x_3055_, 2);
lean_inc(v_v_3060_);
v_l_3061_ = lean_ctor_get(v_x_3055_, 3);
lean_inc(v_l_3061_);
v_r_3062_ = lean_ctor_get(v_x_3055_, 4);
lean_inc(v_r_3062_);
lean_dec_ref(v_x_3055_);
v___x_3063_ = lean_apply_7(v_h__2_3057_, v_size_3058_, v_k_3059_, v_v_3060_, v_l_3061_, v_r_3062_, lean_box(0), lean_box(0));
return v___x_3063_;
}
else
{
lean_object* v___x_3064_; 
lean_dec(v_h__2_3057_);
v___x_3064_ = lean_apply_2(v_h__1_3056_, lean_box(0), lean_box(0));
return v___x_3064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(lean_object* v_00_u03b1_3065_, lean_object* v_00_u03b2_3066_, lean_object* v_inst_3067_, lean_object* v_k_3068_, lean_object* v_motive_3069_, lean_object* v_x_3070_, lean_object* v_x_3071_, lean_object* v_x_3072_, lean_object* v_h__1_3073_, lean_object* v_h__2_3074_){
_start:
{
if (lean_obj_tag(v_x_3070_) == 0)
{
lean_object* v_size_3075_; lean_object* v_k_3076_; lean_object* v_v_3077_; lean_object* v_l_3078_; lean_object* v_r_3079_; lean_object* v___x_3080_; 
lean_dec(v_h__1_3073_);
v_size_3075_ = lean_ctor_get(v_x_3070_, 0);
lean_inc(v_size_3075_);
v_k_3076_ = lean_ctor_get(v_x_3070_, 1);
lean_inc(v_k_3076_);
v_v_3077_ = lean_ctor_get(v_x_3070_, 2);
lean_inc(v_v_3077_);
v_l_3078_ = lean_ctor_get(v_x_3070_, 3);
lean_inc(v_l_3078_);
v_r_3079_ = lean_ctor_get(v_x_3070_, 4);
lean_inc(v_r_3079_);
lean_dec_ref(v_x_3070_);
v___x_3080_ = lean_apply_7(v_h__2_3074_, v_size_3075_, v_k_3076_, v_v_3077_, v_l_3078_, v_r_3079_, lean_box(0), lean_box(0));
return v___x_3080_;
}
else
{
lean_object* v___x_3081_; 
lean_dec(v_h__2_3074_);
v___x_3081_ = lean_apply_2(v_h__1_3073_, lean_box(0), lean_box(0));
return v___x_3081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___boxed(lean_object* v_00_u03b1_3082_, lean_object* v_00_u03b2_3083_, lean_object* v_inst_3084_, lean_object* v_k_3085_, lean_object* v_motive_3086_, lean_object* v_x_3087_, lean_object* v_x_3088_, lean_object* v_x_3089_, lean_object* v_h__1_3090_, lean_object* v_h__2_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(v_00_u03b1_3082_, v_00_u03b2_3083_, v_inst_3084_, v_k_3085_, v_motive_3086_, v_x_3087_, v_x_3088_, v_x_3089_, v_h__1_3090_, v_h__2_3091_);
lean_dec(v_k_3085_);
lean_dec_ref(v_inst_3084_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___redArg(lean_object* v_x_3093_, lean_object* v_h__1_3094_, lean_object* v_h__2_3095_){
_start:
{
if (lean_obj_tag(v_x_3093_) == 0)
{
lean_object* v_size_3096_; lean_object* v_k_3097_; lean_object* v_v_3098_; lean_object* v_l_3099_; lean_object* v_r_3100_; lean_object* v___x_3101_; 
lean_dec(v_h__1_3094_);
v_size_3096_ = lean_ctor_get(v_x_3093_, 0);
lean_inc(v_size_3096_);
v_k_3097_ = lean_ctor_get(v_x_3093_, 1);
lean_inc(v_k_3097_);
v_v_3098_ = lean_ctor_get(v_x_3093_, 2);
lean_inc(v_v_3098_);
v_l_3099_ = lean_ctor_get(v_x_3093_, 3);
lean_inc(v_l_3099_);
v_r_3100_ = lean_ctor_get(v_x_3093_, 4);
lean_inc(v_r_3100_);
lean_dec_ref(v_x_3093_);
v___x_3101_ = lean_apply_7(v_h__2_3095_, v_size_3096_, v_k_3097_, v_v_3098_, v_l_3099_, v_r_3100_, lean_box(0), lean_box(0));
return v___x_3101_;
}
else
{
lean_object* v___x_3102_; 
lean_dec(v_h__2_3095_);
v___x_3102_ = lean_apply_2(v_h__1_3094_, lean_box(0), lean_box(0));
return v___x_3102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(lean_object* v_00_u03b1_3103_, lean_object* v_00_u03b2_3104_, lean_object* v_inst_3105_, lean_object* v_k_3106_, lean_object* v_motive_3107_, lean_object* v_x_3108_, lean_object* v_x_3109_, lean_object* v_x_3110_, lean_object* v_h__1_3111_, lean_object* v_h__2_3112_){
_start:
{
if (lean_obj_tag(v_x_3108_) == 0)
{
lean_object* v_size_3113_; lean_object* v_k_3114_; lean_object* v_v_3115_; lean_object* v_l_3116_; lean_object* v_r_3117_; lean_object* v___x_3118_; 
lean_dec(v_h__1_3111_);
v_size_3113_ = lean_ctor_get(v_x_3108_, 0);
lean_inc(v_size_3113_);
v_k_3114_ = lean_ctor_get(v_x_3108_, 1);
lean_inc(v_k_3114_);
v_v_3115_ = lean_ctor_get(v_x_3108_, 2);
lean_inc(v_v_3115_);
v_l_3116_ = lean_ctor_get(v_x_3108_, 3);
lean_inc(v_l_3116_);
v_r_3117_ = lean_ctor_get(v_x_3108_, 4);
lean_inc(v_r_3117_);
lean_dec_ref(v_x_3108_);
v___x_3118_ = lean_apply_7(v_h__2_3112_, v_size_3113_, v_k_3114_, v_v_3115_, v_l_3116_, v_r_3117_, lean_box(0), lean_box(0));
return v___x_3118_;
}
else
{
lean_object* v___x_3119_; 
lean_dec(v_h__2_3112_);
v___x_3119_ = lean_apply_2(v_h__1_3111_, lean_box(0), lean_box(0));
return v___x_3119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___boxed(lean_object* v_00_u03b1_3120_, lean_object* v_00_u03b2_3121_, lean_object* v_inst_3122_, lean_object* v_k_3123_, lean_object* v_motive_3124_, lean_object* v_x_3125_, lean_object* v_x_3126_, lean_object* v_x_3127_, lean_object* v_h__1_3128_, lean_object* v_h__2_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(v_00_u03b1_3120_, v_00_u03b2_3121_, v_inst_3122_, v_k_3123_, v_motive_3124_, v_x_3125_, v_x_3126_, v_x_3127_, v_h__1_3128_, v_h__2_3129_);
lean_dec(v_k_3123_);
lean_dec_ref(v_inst_3122_);
return v_res_3130_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_WF_Defs(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Cell(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Model(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Linear(builtin);
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
