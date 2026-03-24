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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_k_127_);
v_v_128_ = lean_ctor_get(v_m_125_, 2);
lean_inc(v_v_128_);
v_l_129_ = lean_ctor_get(v_m_125_, 3);
lean_inc(v_l_129_);
v_r_130_ = lean_ctor_get(v_m_125_, 4);
lean_inc(v_r_130_);
lean_dec_ref(v_m_125_);
lean_inc_ref(v_k_122_);
lean_inc(v_k_127_);
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
lean_inc(v_k_206_);
v_v_207_ = lean_ctor_get(v_l_204_, 2);
lean_inc(v_v_207_);
v_l_208_ = lean_ctor_get(v_l_204_, 3);
lean_inc(v_l_208_);
v_r_209_ = lean_ctor_get(v_l_204_, 4);
lean_inc(v_r_209_);
lean_dec_ref(v_l_204_);
lean_inc_ref(v_inst_202_);
lean_inc(v_k_206_);
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
lean_inc(v_k_455_);
v_v_456_ = lean_ctor_get(v_l_454_, 2);
lean_inc(v_v_456_);
v_l_457_ = lean_ctor_get(v_l_454_, 3);
lean_inc(v_l_457_);
v_r_458_ = lean_ctor_get(v_l_454_, 4);
lean_inc(v_r_458_);
lean_dec_ref(v_l_454_);
lean_inc_ref(v_k_451_);
lean_inc(v_k_455_);
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
lean_dec(v_inst_569_);
v_val_573_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_val_573_);
lean_dec_ref(v___x_570_);
return v_val_573_;
}
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(lean_object* v_inst_583_, lean_object* v_k_584_, lean_object* v_l_585_, lean_object* v_fallback_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_583_, v_l_585_, v_k_584_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_inc(v_fallback_586_);
return v_fallback_586_;
}
else
{
lean_object* v_val_588_; 
v_val_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_val_588_);
lean_dec_ref(v___x_587_);
return v_val_588_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg___boxed(lean_object* v_inst_589_, lean_object* v_k_590_, lean_object* v_l_591_, lean_object* v_fallback_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(v_inst_589_, v_k_590_, v_l_591_, v_fallback_592_);
lean_dec(v_fallback_592_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098(lean_object* v_00_u03b1_594_, lean_object* v_00_u03b2_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_k_599_, lean_object* v_l_600_, lean_object* v_fallback_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(v_inst_596_, v_k_599_, v_l_600_, v_fallback_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___boxed(lean_object* v_00_u03b1_603_, lean_object* v_00_u03b2_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_k_608_, lean_object* v_l_609_, lean_object* v_fallback_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_DTreeMap_Internal_Impl_getD_u2098(v_00_u03b1_603_, v_00_u03b2_604_, v_inst_605_, v_inst_606_, v_inst_607_, v_k_608_, v_l_609_, v_fallback_610_);
lean_dec(v_fallback_610_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___lam__0(lean_object* v_c_612_, lean_object* v_x_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(v_c_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(lean_object* v_inst_616_, lean_object* v_l_617_, lean_object* v_k_618_){
_start:
{
lean_object* v___f_619_; lean_object* v___x_620_; 
v___f_619_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0));
v___x_620_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_616_, v_k_618_, v_l_617_, v___f_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098(lean_object* v_00_u03b1_621_, lean_object* v_00_u03b2_622_, lean_object* v_inst_623_, lean_object* v_l_624_, lean_object* v_k_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_623_, v_l_624_, v_k_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(lean_object* v_inst_627_, lean_object* v_l_628_, lean_object* v_k_629_){
_start:
{
lean_object* v___x_630_; lean_object* v_val_631_; 
v___x_630_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_627_, v_l_628_, v_k_629_);
v_val_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_val_631_);
lean_dec(v___x_630_);
return v_val_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098(lean_object* v_00_u03b1_632_, lean_object* v_00_u03b2_633_, lean_object* v_inst_634_, lean_object* v_l_635_, lean_object* v_k_636_, lean_object* v_h_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(v_inst_634_, v_l_635_, v_k_636_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_l_641_, lean_object* v_k_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_639_, v_l_641_, v_k_642_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_645_ = l_panic___redArg(v_inst_640_, v___x_644_);
return v___x_645_;
}
else
{
lean_object* v_val_646_; 
lean_dec_ref(v_inst_640_);
v_val_646_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_val_646_);
lean_dec_ref(v___x_643_);
return v_val_646_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(lean_object* v_00_u03b1_647_, lean_object* v_00_u03b2_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_l_651_, lean_object* v_k_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(v_inst_649_, v_inst_650_, v_l_651_, v_k_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(lean_object* v_inst_654_, lean_object* v_k_655_, lean_object* v_l_656_, lean_object* v_fallback_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_654_, v_l_656_, v_k_655_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_inc_ref(v_fallback_657_);
return v_fallback_657_;
}
else
{
lean_object* v_val_659_; 
v_val_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_val_659_);
lean_dec_ref(v___x_658_);
return v_val_659_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg___boxed(lean_object* v_inst_660_, lean_object* v_k_661_, lean_object* v_l_662_, lean_object* v_fallback_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(v_inst_660_, v_k_661_, v_l_662_, v_fallback_663_);
lean_dec_ref(v_fallback_663_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(lean_object* v_00_u03b1_665_, lean_object* v_00_u03b2_666_, lean_object* v_inst_667_, lean_object* v_k_668_, lean_object* v_l_669_, lean_object* v_fallback_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(v_inst_667_, v_k_668_, v_l_669_, v_fallback_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___boxed(lean_object* v_00_u03b1_672_, lean_object* v_00_u03b2_673_, lean_object* v_inst_674_, lean_object* v_k_675_, lean_object* v_l_676_, lean_object* v_fallback_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(v_00_u03b1_672_, v_00_u03b2_673_, v_inst_674_, v_k_675_, v_l_676_, v_fallback_677_);
lean_dec_ref(v_fallback_677_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0(lean_object* v_c_679_, lean_object* v_x_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(v_c_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(lean_object* v_inst_683_, lean_object* v_l_684_, lean_object* v_k_685_){
_start:
{
lean_object* v___f_686_; lean_object* v___x_687_; 
v___f_686_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0));
v___x_687_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_683_, v_k_685_, v_l_684_, v___f_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098(lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_inst_690_, lean_object* v_l_691_, lean_object* v_k_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_690_, v_l_691_, v_k_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(lean_object* v_inst_694_, lean_object* v_l_695_, lean_object* v_k_696_){
_start:
{
lean_object* v___x_697_; lean_object* v_val_698_; 
v___x_697_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_694_, v_l_695_, v_k_696_);
v_val_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_val_698_);
lean_dec(v___x_697_);
return v_val_698_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_inst_701_, lean_object* v_l_702_, lean_object* v_k_703_, lean_object* v_h_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(v_inst_701_, v_l_702_, v_k_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(lean_object* v_inst_706_, lean_object* v_l_707_, lean_object* v_k_708_, lean_object* v_inst_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_706_, v_l_707_, v_k_708_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_712_ = l_panic___redArg(v_inst_709_, v___x_711_);
return v___x_712_;
}
else
{
lean_object* v_val_713_; 
lean_dec(v_inst_709_);
v_val_713_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_val_713_);
lean_dec_ref(v___x_710_);
return v_val_713_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(lean_object* v_00_u03b1_714_, lean_object* v_00_u03b2_715_, lean_object* v_inst_716_, lean_object* v_l_717_, lean_object* v_k_718_, lean_object* v_inst_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(v_inst_716_, v_l_717_, v_k_718_, v_inst_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(lean_object* v_inst_721_, lean_object* v_k_722_, lean_object* v_l_723_, lean_object* v_fallback_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_721_, v_l_723_, v_k_722_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_inc(v_fallback_724_);
return v_fallback_724_;
}
else
{
lean_object* v_val_726_; 
v_val_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_val_726_);
lean_dec_ref(v___x_725_);
return v_val_726_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg___boxed(lean_object* v_inst_727_, lean_object* v_k_728_, lean_object* v_l_729_, lean_object* v_fallback_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(v_inst_727_, v_k_728_, v_l_729_, v_fallback_730_);
lean_dec(v_fallback_730_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(lean_object* v_00_u03b1_732_, lean_object* v_00_u03b2_733_, lean_object* v_inst_734_, lean_object* v_k_735_, lean_object* v_l_736_, lean_object* v_fallback_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(v_inst_734_, v_k_735_, v_l_736_, v_fallback_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___boxed(lean_object* v_00_u03b1_739_, lean_object* v_00_u03b2_740_, lean_object* v_inst_741_, lean_object* v_k_742_, lean_object* v_l_743_, lean_object* v_fallback_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(v_00_u03b1_739_, v_00_u03b2_740_, v_inst_741_, v_k_742_, v_l_743_, v_fallback_744_);
lean_dec(v_fallback_744_);
return v_res_745_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(lean_object* v_x_746_){
_start:
{
uint8_t v___x_747_; 
v___x_747_ = 0;
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* v_x_748_){
_start:
{
uint8_t v_res_749_; lean_object* v_r_750_; 
v_res_749_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(v_x_748_);
lean_dec(v_x_748_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(lean_object* v_sofar_751_, lean_object* v_step_752_){
_start:
{
if (lean_obj_tag(v_step_752_) == 0)
{
lean_object* v_a_753_; lean_object* v_a_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_a_753_ = lean_ctor_get(v_step_752_, 0);
v_a_754_ = lean_ctor_get(v_step_752_, 1);
lean_inc(v_a_754_);
lean_inc(v_a_753_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_a_753_);
lean_ctor_set(v___x_755_, 1, v_a_754_);
v___x_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
else
{
lean_object* v_a_757_; lean_object* v___x_758_; 
v_a_757_ = lean_ctor_get(v_step_752_, 2);
v___x_758_ = l_List_head_x3f___redArg(v_a_757_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_inc(v_sofar_751_);
return v_sofar_751_;
}
else
{
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* v_sofar_759_, lean_object* v_step_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(v_sofar_759_, v_step_760_);
lean_dec_ref(v_step_760_);
lean_dec(v_sofar_759_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(lean_object* v_l_764_){
_start:
{
lean_object* v___f_765_; lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___f_765_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0));
v___f_766_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1));
v___x_767_ = lean_box(0);
v___x_768_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___f_765_, v___x_767_, v___f_766_, v_l_764_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(lean_object* v_00_u03b1_769_, lean_object* v_00_u03b2_770_, lean_object* v_inst_771_, lean_object* v_l_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(v_l_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___boxed(lean_object* v_00_u03b1_774_, lean_object* v_00_u03b2_775_, lean_object* v_inst_776_, lean_object* v_l_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(v_00_u03b1_774_, v_00_u03b2_775_, v_inst_776_, v_l_777_);
lean_dec_ref(v_inst_776_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v_x_781_, lean_object* v_r_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_List_head_x3f___redArg(v_r_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed(lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v_r_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(v_x_784_, v_x_785_, v_x_786_, v_r_787_);
lean_dec(v_r_787_);
lean_dec(v_x_785_);
lean_dec(v_x_784_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(lean_object* v_l_790_){
_start:
{
lean_object* v___f_791_; lean_object* v___f_792_; lean_object* v___x_793_; 
v___f_791_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0));
v___f_792_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0));
v___x_793_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_791_, v_l_790_, v___f_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(lean_object* v_00_u03b1_794_, lean_object* v_00_u03b2_795_, lean_object* v_inst_796_, lean_object* v_l_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(v_l_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___boxed(lean_object* v_00_u03b1_799_, lean_object* v_00_u03b2_800_, lean_object* v_inst_801_, lean_object* v_l_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(v_00_u03b1_799_, v_00_u03b2_800_, v_inst_801_, v_l_802_);
lean_dec_ref(v_inst_801_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse___redArg(lean_object* v_x_804_){
_start:
{
if (lean_obj_tag(v_x_804_) == 0)
{
lean_object* v_size_805_; lean_object* v_k_806_; lean_object* v_v_807_; lean_object* v_l_808_; lean_object* v_r_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_818_; 
v_size_805_ = lean_ctor_get(v_x_804_, 0);
v_k_806_ = lean_ctor_get(v_x_804_, 1);
v_v_807_ = lean_ctor_get(v_x_804_, 2);
v_l_808_ = lean_ctor_get(v_x_804_, 3);
v_r_809_ = lean_ctor_get(v_x_804_, 4);
v_isSharedCheck_818_ = !lean_is_exclusive(v_x_804_);
if (v_isSharedCheck_818_ == 0)
{
v___x_811_ = v_x_804_;
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_r_809_);
lean_inc(v_l_808_);
lean_inc(v_v_807_);
lean_inc(v_k_806_);
lean_inc(v_size_805_);
lean_dec(v_x_804_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_813_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_r_809_);
v___x_814_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_l_808_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 4, v___x_814_);
lean_ctor_set(v___x_811_, 3, v___x_813_);
v___x_816_ = v___x_811_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_size_805_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_k_806_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_v_807_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
else
{
return v_x_804_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse(lean_object* v_00_u03b1_819_, lean_object* v_00_u03b2_820_, lean_object* v_x_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0(lean_object* v_c_823_, lean_object* v_x_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(v_c_823_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(lean_object* v_inst_827_, lean_object* v_l_828_, lean_object* v_k_829_){
_start:
{
lean_object* v___f_830_; lean_object* v___x_831_; 
v___f_830_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0));
v___x_831_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_827_, v_k_829_, v_l_828_, v___f_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098(lean_object* v_00_u03b1_832_, lean_object* v_00_u03b2_833_, lean_object* v_inst_834_, lean_object* v_l_835_, lean_object* v_k_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_834_, v_l_835_, v_k_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(lean_object* v_inst_838_, lean_object* v_l_839_, lean_object* v_k_840_){
_start:
{
lean_object* v___x_841_; lean_object* v_val_842_; 
v___x_841_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_838_, v_l_839_, v_k_840_);
v_val_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_val_842_);
lean_dec(v___x_841_);
return v_val_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098(lean_object* v_00_u03b1_843_, lean_object* v_00_u03b2_844_, lean_object* v_inst_845_, lean_object* v_l_846_, lean_object* v_k_847_, lean_object* v_h_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(v_inst_845_, v_l_846_, v_k_847_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(lean_object* v_inst_850_, lean_object* v_l_851_, lean_object* v_k_852_, lean_object* v_inst_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_850_, v_l_851_, v_k_852_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_856_ = l_panic___redArg(v_inst_853_, v___x_855_);
return v___x_856_;
}
else
{
lean_object* v_val_857_; 
lean_dec(v_inst_853_);
v_val_857_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_val_857_);
lean_dec_ref(v___x_854_);
return v_val_857_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(lean_object* v_00_u03b1_858_, lean_object* v_00_u03b2_859_, lean_object* v_inst_860_, lean_object* v_l_861_, lean_object* v_k_862_, lean_object* v_inst_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(v_inst_860_, v_l_861_, v_k_862_, v_inst_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(lean_object* v_inst_865_, lean_object* v_l_866_, lean_object* v_k_867_, lean_object* v_fallback_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_865_, v_l_866_, v_k_867_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_inc(v_fallback_868_);
return v_fallback_868_;
}
else
{
lean_object* v_val_870_; 
v_val_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_val_870_);
lean_dec_ref(v___x_869_);
return v_val_870_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg___boxed(lean_object* v_inst_871_, lean_object* v_l_872_, lean_object* v_k_873_, lean_object* v_fallback_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(v_inst_871_, v_l_872_, v_k_873_, v_fallback_874_);
lean_dec(v_fallback_874_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(lean_object* v_00_u03b1_876_, lean_object* v_00_u03b2_877_, lean_object* v_inst_878_, lean_object* v_l_879_, lean_object* v_k_880_, lean_object* v_fallback_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(v_inst_878_, v_l_879_, v_k_880_, v_fallback_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___boxed(lean_object* v_00_u03b1_883_, lean_object* v_00_u03b2_884_, lean_object* v_inst_885_, lean_object* v_l_886_, lean_object* v_k_887_, lean_object* v_fallback_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(v_00_u03b1_883_, v_00_u03b2_884_, v_inst_885_, v_l_886_, v_k_887_, v_fallback_888_);
lean_dec(v_fallback_888_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object* v_t_890_, lean_object* v_h__1_891_, lean_object* v_h__2_892_){
_start:
{
if (lean_obj_tag(v_t_890_) == 0)
{
lean_object* v_size_893_; lean_object* v_k_894_; lean_object* v_v_895_; lean_object* v_l_896_; lean_object* v_r_897_; lean_object* v___x_898_; 
lean_dec(v_h__1_891_);
v_size_893_ = lean_ctor_get(v_t_890_, 0);
lean_inc(v_size_893_);
v_k_894_ = lean_ctor_get(v_t_890_, 1);
lean_inc(v_k_894_);
v_v_895_ = lean_ctor_get(v_t_890_, 2);
lean_inc(v_v_895_);
v_l_896_ = lean_ctor_get(v_t_890_, 3);
lean_inc(v_l_896_);
v_r_897_ = lean_ctor_get(v_t_890_, 4);
lean_inc(v_r_897_);
lean_dec_ref(v_t_890_);
v___x_898_ = lean_apply_5(v_h__2_892_, v_size_893_, v_k_894_, v_v_895_, v_l_896_, v_r_897_);
return v___x_898_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; 
lean_dec(v_h__2_892_);
v___x_899_ = lean_box(0);
v___x_900_ = lean_apply_1(v_h__1_891_, v___x_899_);
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object* v_00_u03b1_901_, lean_object* v_00_u03b2_902_, lean_object* v_motive_903_, lean_object* v_t_904_, lean_object* v_h__1_905_, lean_object* v_h__2_906_){
_start:
{
if (lean_obj_tag(v_t_904_) == 0)
{
lean_object* v_size_907_; lean_object* v_k_908_; lean_object* v_v_909_; lean_object* v_l_910_; lean_object* v_r_911_; lean_object* v___x_912_; 
lean_dec(v_h__1_905_);
v_size_907_ = lean_ctor_get(v_t_904_, 0);
lean_inc(v_size_907_);
v_k_908_ = lean_ctor_get(v_t_904_, 1);
lean_inc(v_k_908_);
v_v_909_ = lean_ctor_get(v_t_904_, 2);
lean_inc(v_v_909_);
v_l_910_ = lean_ctor_get(v_t_904_, 3);
lean_inc(v_l_910_);
v_r_911_ = lean_ctor_get(v_t_904_, 4);
lean_inc(v_r_911_);
lean_dec_ref(v_t_904_);
v___x_912_ = lean_apply_5(v_h__2_906_, v_size_907_, v_k_908_, v_v_909_, v_l_910_, v_r_911_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v_h__2_906_);
v___x_913_ = lean_box(0);
v___x_914_ = lean_apply_1(v_h__1_905_, v___x_913_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(uint8_t v_x_915_, lean_object* v_h__1_916_, lean_object* v_h__2_917_, lean_object* v_h__3_918_){
_start:
{
switch(v_x_915_)
{
case 0:
{
lean_object* v___x_919_; 
lean_dec(v_h__3_918_);
lean_dec(v_h__2_917_);
v___x_919_ = lean_apply_1(v_h__1_916_, lean_box(0));
return v___x_919_;
}
case 1:
{
lean_object* v___x_920_; 
lean_dec(v_h__2_917_);
lean_dec(v_h__1_916_);
v___x_920_ = lean_apply_1(v_h__3_918_, lean_box(0));
return v___x_920_;
}
default: 
{
lean_object* v___x_921_; 
lean_dec(v_h__3_918_);
lean_dec(v_h__1_916_);
v___x_921_ = lean_apply_1(v_h__2_917_, lean_box(0));
return v___x_921_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_922_, lean_object* v_h__1_923_, lean_object* v_h__2_924_, lean_object* v_h__3_925_){
_start:
{
uint8_t v_x_33__boxed_926_; lean_object* v_res_927_; 
v_x_33__boxed_926_ = lean_unbox(v_x_922_);
v_res_927_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(v_x_33__boxed_926_, v_h__1_923_, v_h__2_924_, v_h__3_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(lean_object* v_motive_928_, uint8_t v_x_929_, lean_object* v_h__1_930_, lean_object* v_h__2_931_, lean_object* v_h__3_932_){
_start:
{
switch(v_x_929_)
{
case 0:
{
lean_object* v___x_933_; 
lean_dec(v_h__3_932_);
lean_dec(v_h__2_931_);
v___x_933_ = lean_apply_1(v_h__1_930_, lean_box(0));
return v___x_933_;
}
case 1:
{
lean_object* v___x_934_; 
lean_dec(v_h__2_931_);
lean_dec(v_h__1_930_);
v___x_934_ = lean_apply_1(v_h__3_932_, lean_box(0));
return v___x_934_;
}
default: 
{
lean_object* v___x_935_; 
lean_dec(v_h__3_932_);
lean_dec(v_h__1_930_);
v___x_935_ = lean_apply_1(v_h__2_931_, lean_box(0));
return v___x_935_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___boxed(lean_object* v_motive_936_, lean_object* v_x_937_, lean_object* v_h__1_938_, lean_object* v_h__2_939_, lean_object* v_h__3_940_){
_start:
{
uint8_t v_x_42__boxed_941_; lean_object* v_res_942_; 
v_x_42__boxed_941_ = lean_unbox(v_x_937_);
v_res_942_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(v_motive_936_, v_x_42__boxed_941_, v_h__1_938_, v_h__2_939_, v_h__3_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object* v_x_943_, lean_object* v_h__1_944_, lean_object* v_h__2_945_){
_start:
{
if (lean_obj_tag(v_x_943_) == 0)
{
lean_object* v___x_946_; 
lean_dec(v_h__2_945_);
v___x_946_ = lean_apply_1(v_h__1_944_, lean_box(0));
return v___x_946_;
}
else
{
lean_object* v_val_947_; lean_object* v___x_948_; 
lean_dec(v_h__1_944_);
v_val_947_ = lean_ctor_get(v_x_943_, 0);
lean_inc(v_val_947_);
lean_dec_ref(v_x_943_);
v___x_948_ = lean_apply_2(v_h__2_945_, v_val_947_, lean_box(0));
return v___x_948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object* v_00_u03b1_949_, lean_object* v_00_u03b2_950_, lean_object* v_motive_951_, lean_object* v_x_952_, lean_object* v_h__1_953_, lean_object* v_h__2_954_){
_start:
{
if (lean_obj_tag(v_x_952_) == 0)
{
lean_object* v___x_955_; 
lean_dec(v_h__2_954_);
v___x_955_ = lean_apply_1(v_h__1_953_, lean_box(0));
return v___x_955_;
}
else
{
lean_object* v_val_956_; lean_object* v___x_957_; 
lean_dec(v_h__1_953_);
v_val_956_ = lean_ctor_get(v_x_952_, 0);
lean_inc(v_val_956_);
lean_dec_ref(v_x_952_);
v___x_957_ = lean_apply_2(v_h__2_954_, v_val_956_, lean_box(0));
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___redArg(lean_object* v_t_958_, lean_object* v_h__1_959_){
_start:
{
lean_object* v_size_960_; lean_object* v_k_961_; lean_object* v_v_962_; lean_object* v_l_963_; lean_object* v_r_964_; lean_object* v___x_965_; 
v_size_960_ = lean_ctor_get(v_t_958_, 0);
lean_inc(v_size_960_);
v_k_961_ = lean_ctor_get(v_t_958_, 1);
lean_inc(v_k_961_);
v_v_962_ = lean_ctor_get(v_t_958_, 2);
lean_inc(v_v_962_);
v_l_963_ = lean_ctor_get(v_t_958_, 3);
lean_inc(v_l_963_);
v_r_964_ = lean_ctor_get(v_t_958_, 4);
lean_inc(v_r_964_);
lean_dec(v_t_958_);
v___x_965_ = lean_apply_6(v_h__1_959_, v_size_960_, v_k_961_, v_v_962_, v_l_963_, v_r_964_, lean_box(0));
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(lean_object* v_00_u03b1_966_, lean_object* v_00_u03b2_967_, lean_object* v_inst_968_, lean_object* v_k_969_, lean_object* v_motive_970_, lean_object* v_t_971_, lean_object* v_hlk_972_, lean_object* v_h__1_973_){
_start:
{
lean_object* v_size_974_; lean_object* v_k_975_; lean_object* v_v_976_; lean_object* v_l_977_; lean_object* v_r_978_; lean_object* v___x_979_; 
v_size_974_ = lean_ctor_get(v_t_971_, 0);
lean_inc(v_size_974_);
v_k_975_ = lean_ctor_get(v_t_971_, 1);
lean_inc(v_k_975_);
v_v_976_ = lean_ctor_get(v_t_971_, 2);
lean_inc(v_v_976_);
v_l_977_ = lean_ctor_get(v_t_971_, 3);
lean_inc(v_l_977_);
v_r_978_ = lean_ctor_get(v_t_971_, 4);
lean_inc(v_r_978_);
lean_dec(v_t_971_);
v___x_979_ = lean_apply_6(v_h__1_973_, v_size_974_, v_k_975_, v_v_976_, v_l_977_, v_r_978_, lean_box(0));
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___boxed(lean_object* v_00_u03b1_980_, lean_object* v_00_u03b2_981_, lean_object* v_inst_982_, lean_object* v_k_983_, lean_object* v_motive_984_, lean_object* v_t_985_, lean_object* v_hlk_986_, lean_object* v_h__1_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(v_00_u03b1_980_, v_00_u03b2_981_, v_inst_982_, v_k_983_, v_motive_984_, v_t_985_, v_hlk_986_, v_h__1_987_);
lean_dec(v_k_983_);
lean_dec_ref(v_inst_982_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_989_, lean_object* v_h__1_990_, lean_object* v_h__2_991_){
_start:
{
if (lean_obj_tag(v_x_989_) == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec(v_h__2_991_);
v___x_992_ = lean_box(0);
v___x_993_ = lean_apply_1(v_h__1_990_, v___x_992_);
return v___x_993_;
}
else
{
lean_object* v_val_994_; lean_object* v___x_995_; 
lean_dec(v_h__1_990_);
v_val_994_ = lean_ctor_get(v_x_989_, 0);
lean_inc(v_val_994_);
lean_dec_ref(v_x_989_);
v___x_995_ = lean_apply_1(v_h__2_991_, v_val_994_);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_996_, lean_object* v_00_u03b2_997_, lean_object* v_motive_998_, lean_object* v_x_999_, lean_object* v_h__1_1000_, lean_object* v_h__2_1001_){
_start:
{
if (lean_obj_tag(v_x_999_) == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec(v_h__2_1001_);
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_apply_1(v_h__1_1000_, v___x_1002_);
return v___x_1003_;
}
else
{
lean_object* v_val_1004_; lean_object* v___x_1005_; 
lean_dec(v_h__1_1000_);
v_val_1004_ = lean_ctor_get(v_x_999_, 0);
lean_inc(v_val_1004_);
lean_dec_ref(v_x_999_);
v___x_1005_ = lean_apply_1(v_h__2_1001_, v_val_1004_);
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___redArg(lean_object* v_t_1006_, lean_object* v_h__1_1007_){
_start:
{
lean_object* v_size_1008_; lean_object* v_k_1009_; lean_object* v_v_1010_; lean_object* v_l_1011_; lean_object* v_r_1012_; lean_object* v___x_1013_; 
v_size_1008_ = lean_ctor_get(v_t_1006_, 0);
lean_inc(v_size_1008_);
v_k_1009_ = lean_ctor_get(v_t_1006_, 1);
lean_inc(v_k_1009_);
v_v_1010_ = lean_ctor_get(v_t_1006_, 2);
lean_inc(v_v_1010_);
v_l_1011_ = lean_ctor_get(v_t_1006_, 3);
lean_inc(v_l_1011_);
v_r_1012_ = lean_ctor_get(v_t_1006_, 4);
lean_inc(v_r_1012_);
lean_dec(v_t_1006_);
v___x_1013_ = lean_apply_6(v_h__1_1007_, v_size_1008_, v_k_1009_, v_v_1010_, v_l_1011_, v_r_1012_, lean_box(0));
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(lean_object* v_00_u03b1_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_inst_1016_, lean_object* v_k_1017_, lean_object* v_motive_1018_, lean_object* v_t_1019_, lean_object* v_hlk_1020_, lean_object* v_h__1_1021_){
_start:
{
lean_object* v_size_1022_; lean_object* v_k_1023_; lean_object* v_v_1024_; lean_object* v_l_1025_; lean_object* v_r_1026_; lean_object* v___x_1027_; 
v_size_1022_ = lean_ctor_get(v_t_1019_, 0);
lean_inc(v_size_1022_);
v_k_1023_ = lean_ctor_get(v_t_1019_, 1);
lean_inc(v_k_1023_);
v_v_1024_ = lean_ctor_get(v_t_1019_, 2);
lean_inc(v_v_1024_);
v_l_1025_ = lean_ctor_get(v_t_1019_, 3);
lean_inc(v_l_1025_);
v_r_1026_ = lean_ctor_get(v_t_1019_, 4);
lean_inc(v_r_1026_);
lean_dec(v_t_1019_);
v___x_1027_ = lean_apply_6(v_h__1_1021_, v_size_1022_, v_k_1023_, v_v_1024_, v_l_1025_, v_r_1026_, lean_box(0));
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___boxed(lean_object* v_00_u03b1_1028_, lean_object* v_00_u03b2_1029_, lean_object* v_inst_1030_, lean_object* v_k_1031_, lean_object* v_motive_1032_, lean_object* v_t_1033_, lean_object* v_hlk_1034_, lean_object* v_h__1_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(v_00_u03b1_1028_, v_00_u03b2_1029_, v_inst_1030_, v_k_1031_, v_motive_1032_, v_t_1033_, v_hlk_1034_, v_h__1_1035_);
lean_dec(v_k_1031_);
lean_dec_ref(v_inst_1030_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1037_, lean_object* v_h__1_1038_, lean_object* v_h__2_1039_, lean_object* v_h__3_1040_){
_start:
{
if (lean_obj_tag(v_x_1037_) == 0)
{
lean_object* v_l_1041_; 
lean_dec(v_h__1_1038_);
v_l_1041_ = lean_ctor_get(v_x_1037_, 3);
if (lean_obj_tag(v_l_1041_) == 0)
{
lean_object* v_size_1042_; lean_object* v_k_1043_; lean_object* v_v_1044_; lean_object* v_r_1045_; lean_object* v_size_1046_; lean_object* v_k_1047_; lean_object* v_v_1048_; lean_object* v_l_1049_; lean_object* v_r_1050_; lean_object* v___x_1051_; 
lean_inc_ref(v_l_1041_);
lean_dec(v_h__2_1039_);
v_size_1042_ = lean_ctor_get(v_x_1037_, 0);
lean_inc(v_size_1042_);
v_k_1043_ = lean_ctor_get(v_x_1037_, 1);
lean_inc(v_k_1043_);
v_v_1044_ = lean_ctor_get(v_x_1037_, 2);
lean_inc(v_v_1044_);
v_r_1045_ = lean_ctor_get(v_x_1037_, 4);
lean_inc(v_r_1045_);
lean_dec_ref(v_x_1037_);
v_size_1046_ = lean_ctor_get(v_l_1041_, 0);
lean_inc(v_size_1046_);
v_k_1047_ = lean_ctor_get(v_l_1041_, 1);
lean_inc(v_k_1047_);
v_v_1048_ = lean_ctor_get(v_l_1041_, 2);
lean_inc(v_v_1048_);
v_l_1049_ = lean_ctor_get(v_l_1041_, 3);
lean_inc(v_l_1049_);
v_r_1050_ = lean_ctor_get(v_l_1041_, 4);
lean_inc(v_r_1050_);
lean_dec_ref(v_l_1041_);
v___x_1051_ = lean_apply_9(v_h__3_1040_, v_size_1042_, v_k_1043_, v_v_1044_, v_size_1046_, v_k_1047_, v_v_1048_, v_l_1049_, v_r_1050_, v_r_1045_);
return v___x_1051_;
}
else
{
lean_object* v_size_1052_; lean_object* v_k_1053_; lean_object* v_v_1054_; lean_object* v_r_1055_; lean_object* v___x_1056_; 
lean_dec(v_h__3_1040_);
v_size_1052_ = lean_ctor_get(v_x_1037_, 0);
lean_inc(v_size_1052_);
v_k_1053_ = lean_ctor_get(v_x_1037_, 1);
lean_inc(v_k_1053_);
v_v_1054_ = lean_ctor_get(v_x_1037_, 2);
lean_inc(v_v_1054_);
v_r_1055_ = lean_ctor_get(v_x_1037_, 4);
lean_inc(v_r_1055_);
lean_dec_ref(v_x_1037_);
v___x_1056_ = lean_apply_4(v_h__2_1039_, v_size_1052_, v_k_1053_, v_v_1054_, v_r_1055_);
return v___x_1056_;
}
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec(v_h__3_1040_);
lean_dec(v_h__2_1039_);
v___x_1057_ = lean_box(0);
v___x_1058_ = lean_apply_1(v_h__1_1038_, v___x_1057_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1059_, lean_object* v_00_u03b2_1060_, lean_object* v_motive_1061_, lean_object* v_x_1062_, lean_object* v_h__1_1063_, lean_object* v_h__2_1064_, lean_object* v_h__3_1065_){
_start:
{
if (lean_obj_tag(v_x_1062_) == 0)
{
lean_object* v_l_1066_; 
lean_dec(v_h__1_1063_);
v_l_1066_ = lean_ctor_get(v_x_1062_, 3);
if (lean_obj_tag(v_l_1066_) == 0)
{
lean_object* v_size_1067_; lean_object* v_k_1068_; lean_object* v_v_1069_; lean_object* v_r_1070_; lean_object* v_size_1071_; lean_object* v_k_1072_; lean_object* v_v_1073_; lean_object* v_l_1074_; lean_object* v_r_1075_; lean_object* v___x_1076_; 
lean_inc_ref(v_l_1066_);
lean_dec(v_h__2_1064_);
v_size_1067_ = lean_ctor_get(v_x_1062_, 0);
lean_inc(v_size_1067_);
v_k_1068_ = lean_ctor_get(v_x_1062_, 1);
lean_inc(v_k_1068_);
v_v_1069_ = lean_ctor_get(v_x_1062_, 2);
lean_inc(v_v_1069_);
v_r_1070_ = lean_ctor_get(v_x_1062_, 4);
lean_inc(v_r_1070_);
lean_dec_ref(v_x_1062_);
v_size_1071_ = lean_ctor_get(v_l_1066_, 0);
lean_inc(v_size_1071_);
v_k_1072_ = lean_ctor_get(v_l_1066_, 1);
lean_inc(v_k_1072_);
v_v_1073_ = lean_ctor_get(v_l_1066_, 2);
lean_inc(v_v_1073_);
v_l_1074_ = lean_ctor_get(v_l_1066_, 3);
lean_inc(v_l_1074_);
v_r_1075_ = lean_ctor_get(v_l_1066_, 4);
lean_inc(v_r_1075_);
lean_dec_ref(v_l_1066_);
v___x_1076_ = lean_apply_9(v_h__3_1065_, v_size_1067_, v_k_1068_, v_v_1069_, v_size_1071_, v_k_1072_, v_v_1073_, v_l_1074_, v_r_1075_, v_r_1070_);
return v___x_1076_;
}
else
{
lean_object* v_size_1077_; lean_object* v_k_1078_; lean_object* v_v_1079_; lean_object* v_r_1080_; lean_object* v___x_1081_; 
lean_dec(v_h__3_1065_);
v_size_1077_ = lean_ctor_get(v_x_1062_, 0);
lean_inc(v_size_1077_);
v_k_1078_ = lean_ctor_get(v_x_1062_, 1);
lean_inc(v_k_1078_);
v_v_1079_ = lean_ctor_get(v_x_1062_, 2);
lean_inc(v_v_1079_);
v_r_1080_ = lean_ctor_get(v_x_1062_, 4);
lean_inc(v_r_1080_);
lean_dec_ref(v_x_1062_);
v___x_1081_ = lean_apply_4(v_h__2_1064_, v_size_1077_, v_k_1078_, v_v_1079_, v_r_1080_);
return v___x_1081_;
}
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec(v_h__3_1065_);
lean_dec(v_h__2_1064_);
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_apply_1(v_h__1_1063_, v___x_1082_);
return v___x_1083_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_step_1084_, lean_object* v_h__1_1085_, lean_object* v_h__2_1086_){
_start:
{
if (lean_obj_tag(v_step_1084_) == 0)
{
lean_object* v_a_1087_; lean_object* v_a_1088_; lean_object* v_a_1089_; lean_object* v___x_1090_; 
lean_dec(v_h__2_1086_);
v_a_1087_ = lean_ctor_get(v_step_1084_, 0);
lean_inc(v_a_1087_);
v_a_1088_ = lean_ctor_get(v_step_1084_, 1);
lean_inc(v_a_1088_);
v_a_1089_ = lean_ctor_get(v_step_1084_, 2);
lean_inc(v_a_1089_);
lean_dec_ref(v_step_1084_);
v___x_1090_ = lean_apply_4(v_h__1_1085_, v_a_1087_, lean_box(0), v_a_1088_, v_a_1089_);
return v___x_1090_;
}
else
{
lean_object* v_a_1091_; lean_object* v_a_1092_; lean_object* v_a_1093_; lean_object* v___x_1094_; 
lean_dec(v_h__1_1085_);
v_a_1091_ = lean_ctor_get(v_step_1084_, 0);
lean_inc(v_a_1091_);
v_a_1092_ = lean_ctor_get(v_step_1084_, 1);
lean_inc(v_a_1092_);
v_a_1093_ = lean_ctor_get(v_step_1084_, 2);
lean_inc(v_a_1093_);
lean_dec_ref(v_step_1084_);
v___x_1094_ = lean_apply_3(v_h__2_1086_, v_a_1091_, v_a_1092_, v_a_1093_);
return v___x_1094_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_1095_, lean_object* v_00_u03b2_1096_, lean_object* v_inst_1097_, lean_object* v_motive_1098_, lean_object* v_step_1099_, lean_object* v_h__1_1100_, lean_object* v_h__2_1101_){
_start:
{
if (lean_obj_tag(v_step_1099_) == 0)
{
lean_object* v_a_1102_; lean_object* v_a_1103_; lean_object* v_a_1104_; lean_object* v___x_1105_; 
lean_dec(v_h__2_1101_);
v_a_1102_ = lean_ctor_get(v_step_1099_, 0);
lean_inc(v_a_1102_);
v_a_1103_ = lean_ctor_get(v_step_1099_, 1);
lean_inc(v_a_1103_);
v_a_1104_ = lean_ctor_get(v_step_1099_, 2);
lean_inc(v_a_1104_);
lean_dec_ref(v_step_1099_);
v___x_1105_ = lean_apply_4(v_h__1_1100_, v_a_1102_, lean_box(0), v_a_1103_, v_a_1104_);
return v___x_1105_;
}
else
{
lean_object* v_a_1106_; lean_object* v_a_1107_; lean_object* v_a_1108_; lean_object* v___x_1109_; 
lean_dec(v_h__1_1100_);
v_a_1106_ = lean_ctor_get(v_step_1099_, 0);
lean_inc(v_a_1106_);
v_a_1107_ = lean_ctor_get(v_step_1099_, 1);
lean_inc(v_a_1107_);
v_a_1108_ = lean_ctor_get(v_step_1099_, 2);
lean_inc(v_a_1108_);
lean_dec_ref(v_step_1099_);
v___x_1109_ = lean_apply_3(v_h__2_1101_, v_a_1106_, v_a_1107_, v_a_1108_);
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_1110_, lean_object* v_00_u03b2_1111_, lean_object* v_inst_1112_, lean_object* v_motive_1113_, lean_object* v_step_1114_, lean_object* v_h__1_1115_, lean_object* v_h__2_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(v_00_u03b1_1110_, v_00_u03b2_1111_, v_inst_1112_, v_motive_1113_, v_step_1114_, v_h__1_1115_, v_h__2_1116_);
lean_dec_ref(v_inst_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object* v_x_1118_, lean_object* v_x_1119_, lean_object* v_h__1_1120_, lean_object* v_h__2_1121_, lean_object* v_h__3_1122_){
_start:
{
if (lean_obj_tag(v_x_1118_) == 0)
{
lean_object* v_l_1123_; 
lean_dec(v_h__1_1120_);
v_l_1123_ = lean_ctor_get(v_x_1118_, 3);
if (lean_obj_tag(v_l_1123_) == 0)
{
lean_object* v_size_1124_; lean_object* v_k_1125_; lean_object* v_v_1126_; lean_object* v_r_1127_; lean_object* v_size_1128_; lean_object* v_k_1129_; lean_object* v_v_1130_; lean_object* v_l_1131_; lean_object* v_r_1132_; lean_object* v___x_1133_; 
lean_inc_ref(v_l_1123_);
lean_dec(v_h__2_1121_);
v_size_1124_ = lean_ctor_get(v_x_1118_, 0);
lean_inc(v_size_1124_);
v_k_1125_ = lean_ctor_get(v_x_1118_, 1);
lean_inc(v_k_1125_);
v_v_1126_ = lean_ctor_get(v_x_1118_, 2);
lean_inc(v_v_1126_);
v_r_1127_ = lean_ctor_get(v_x_1118_, 4);
lean_inc(v_r_1127_);
lean_dec_ref(v_x_1118_);
v_size_1128_ = lean_ctor_get(v_l_1123_, 0);
lean_inc(v_size_1128_);
v_k_1129_ = lean_ctor_get(v_l_1123_, 1);
lean_inc(v_k_1129_);
v_v_1130_ = lean_ctor_get(v_l_1123_, 2);
lean_inc(v_v_1130_);
v_l_1131_ = lean_ctor_get(v_l_1123_, 3);
lean_inc(v_l_1131_);
v_r_1132_ = lean_ctor_get(v_l_1123_, 4);
lean_inc(v_r_1132_);
lean_dec_ref(v_l_1123_);
v___x_1133_ = lean_apply_10(v_h__3_1122_, v_size_1124_, v_k_1125_, v_v_1126_, v_size_1128_, v_k_1129_, v_v_1130_, v_l_1131_, v_r_1132_, v_r_1127_, v_x_1119_);
return v___x_1133_;
}
else
{
lean_object* v_size_1134_; lean_object* v_k_1135_; lean_object* v_v_1136_; lean_object* v_r_1137_; lean_object* v___x_1138_; 
lean_dec(v_h__3_1122_);
v_size_1134_ = lean_ctor_get(v_x_1118_, 0);
lean_inc(v_size_1134_);
v_k_1135_ = lean_ctor_get(v_x_1118_, 1);
lean_inc(v_k_1135_);
v_v_1136_ = lean_ctor_get(v_x_1118_, 2);
lean_inc(v_v_1136_);
v_r_1137_ = lean_ctor_get(v_x_1118_, 4);
lean_inc(v_r_1137_);
lean_dec_ref(v_x_1118_);
v___x_1138_ = lean_apply_5(v_h__2_1121_, v_size_1134_, v_k_1135_, v_v_1136_, v_r_1137_, v_x_1119_);
return v___x_1138_;
}
}
else
{
lean_object* v___x_1139_; 
lean_dec(v_h__3_1122_);
lean_dec(v_h__2_1121_);
v___x_1139_ = lean_apply_1(v_h__1_1120_, v_x_1119_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1140_, lean_object* v_00_u03b2_1141_, lean_object* v_motive_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_, lean_object* v_h__1_1145_, lean_object* v_h__2_1146_, lean_object* v_h__3_1147_){
_start:
{
if (lean_obj_tag(v_x_1143_) == 0)
{
lean_object* v_l_1148_; 
lean_dec(v_h__1_1145_);
v_l_1148_ = lean_ctor_get(v_x_1143_, 3);
if (lean_obj_tag(v_l_1148_) == 0)
{
lean_object* v_size_1149_; lean_object* v_k_1150_; lean_object* v_v_1151_; lean_object* v_r_1152_; lean_object* v_size_1153_; lean_object* v_k_1154_; lean_object* v_v_1155_; lean_object* v_l_1156_; lean_object* v_r_1157_; lean_object* v___x_1158_; 
lean_inc_ref(v_l_1148_);
lean_dec(v_h__2_1146_);
v_size_1149_ = lean_ctor_get(v_x_1143_, 0);
lean_inc(v_size_1149_);
v_k_1150_ = lean_ctor_get(v_x_1143_, 1);
lean_inc(v_k_1150_);
v_v_1151_ = lean_ctor_get(v_x_1143_, 2);
lean_inc(v_v_1151_);
v_r_1152_ = lean_ctor_get(v_x_1143_, 4);
lean_inc(v_r_1152_);
lean_dec_ref(v_x_1143_);
v_size_1153_ = lean_ctor_get(v_l_1148_, 0);
lean_inc(v_size_1153_);
v_k_1154_ = lean_ctor_get(v_l_1148_, 1);
lean_inc(v_k_1154_);
v_v_1155_ = lean_ctor_get(v_l_1148_, 2);
lean_inc(v_v_1155_);
v_l_1156_ = lean_ctor_get(v_l_1148_, 3);
lean_inc(v_l_1156_);
v_r_1157_ = lean_ctor_get(v_l_1148_, 4);
lean_inc(v_r_1157_);
lean_dec_ref(v_l_1148_);
v___x_1158_ = lean_apply_10(v_h__3_1147_, v_size_1149_, v_k_1150_, v_v_1151_, v_size_1153_, v_k_1154_, v_v_1155_, v_l_1156_, v_r_1157_, v_r_1152_, v_x_1144_);
return v___x_1158_;
}
else
{
lean_object* v_size_1159_; lean_object* v_k_1160_; lean_object* v_v_1161_; lean_object* v_r_1162_; lean_object* v___x_1163_; 
lean_dec(v_h__3_1147_);
v_size_1159_ = lean_ctor_get(v_x_1143_, 0);
lean_inc(v_size_1159_);
v_k_1160_ = lean_ctor_get(v_x_1143_, 1);
lean_inc(v_k_1160_);
v_v_1161_ = lean_ctor_get(v_x_1143_, 2);
lean_inc(v_v_1161_);
v_r_1162_ = lean_ctor_get(v_x_1143_, 4);
lean_inc(v_r_1162_);
lean_dec_ref(v_x_1143_);
v___x_1163_ = lean_apply_5(v_h__2_1146_, v_size_1159_, v_k_1160_, v_v_1161_, v_r_1162_, v_x_1144_);
return v___x_1163_;
}
}
else
{
lean_object* v___x_1164_; 
lean_dec(v_h__3_1147_);
lean_dec(v_h__2_1146_);
v___x_1164_ = lean_apply_1(v_h__1_1145_, v_x_1144_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object* v_x_1165_, lean_object* v_h__1_1166_, lean_object* v_h__2_1167_){
_start:
{
lean_object* v_l_1168_; 
v_l_1168_ = lean_ctor_get(v_x_1165_, 3);
if (lean_obj_tag(v_l_1168_) == 0)
{
lean_object* v_size_1169_; lean_object* v_k_1170_; lean_object* v_v_1171_; lean_object* v_r_1172_; lean_object* v_size_1173_; lean_object* v_k_1174_; lean_object* v_v_1175_; lean_object* v_l_1176_; lean_object* v_r_1177_; lean_object* v___x_1178_; 
lean_inc_ref(v_l_1168_);
lean_dec(v_h__1_1166_);
v_size_1169_ = lean_ctor_get(v_x_1165_, 0);
lean_inc(v_size_1169_);
v_k_1170_ = lean_ctor_get(v_x_1165_, 1);
lean_inc(v_k_1170_);
v_v_1171_ = lean_ctor_get(v_x_1165_, 2);
lean_inc(v_v_1171_);
v_r_1172_ = lean_ctor_get(v_x_1165_, 4);
lean_inc(v_r_1172_);
lean_dec(v_x_1165_);
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
lean_dec_ref(v_l_1168_);
v___x_1178_ = lean_apply_10(v_h__2_1167_, v_size_1169_, v_k_1170_, v_v_1171_, v_size_1173_, v_k_1174_, v_v_1175_, v_l_1176_, v_r_1177_, v_r_1172_, lean_box(0));
return v___x_1178_;
}
else
{
lean_object* v_size_1179_; lean_object* v_k_1180_; lean_object* v_v_1181_; lean_object* v_r_1182_; lean_object* v___x_1183_; 
lean_dec(v_h__2_1167_);
v_size_1179_ = lean_ctor_get(v_x_1165_, 0);
lean_inc(v_size_1179_);
v_k_1180_ = lean_ctor_get(v_x_1165_, 1);
lean_inc(v_k_1180_);
v_v_1181_ = lean_ctor_get(v_x_1165_, 2);
lean_inc(v_v_1181_);
v_r_1182_ = lean_ctor_get(v_x_1165_, 4);
lean_inc(v_r_1182_);
lean_dec(v_x_1165_);
v___x_1183_ = lean_apply_5(v_h__1_1166_, v_size_1179_, v_k_1180_, v_v_1181_, v_r_1182_, lean_box(0));
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* v_00_u03b1_1184_, lean_object* v_00_u03b2_1185_, lean_object* v_motive_1186_, lean_object* v_x_1187_, lean_object* v_x_1188_, lean_object* v_h__1_1189_, lean_object* v_h__2_1190_){
_start:
{
lean_object* v_l_1191_; 
v_l_1191_ = lean_ctor_get(v_x_1187_, 3);
if (lean_obj_tag(v_l_1191_) == 0)
{
lean_object* v_size_1192_; lean_object* v_k_1193_; lean_object* v_v_1194_; lean_object* v_r_1195_; lean_object* v_size_1196_; lean_object* v_k_1197_; lean_object* v_v_1198_; lean_object* v_l_1199_; lean_object* v_r_1200_; lean_object* v___x_1201_; 
lean_inc_ref(v_l_1191_);
lean_dec(v_h__1_1189_);
v_size_1192_ = lean_ctor_get(v_x_1187_, 0);
lean_inc(v_size_1192_);
v_k_1193_ = lean_ctor_get(v_x_1187_, 1);
lean_inc(v_k_1193_);
v_v_1194_ = lean_ctor_get(v_x_1187_, 2);
lean_inc(v_v_1194_);
v_r_1195_ = lean_ctor_get(v_x_1187_, 4);
lean_inc(v_r_1195_);
lean_dec(v_x_1187_);
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
lean_dec_ref(v_l_1191_);
v___x_1201_ = lean_apply_10(v_h__2_1190_, v_size_1192_, v_k_1193_, v_v_1194_, v_size_1196_, v_k_1197_, v_v_1198_, v_l_1199_, v_r_1200_, v_r_1195_, lean_box(0));
return v___x_1201_;
}
else
{
lean_object* v_size_1202_; lean_object* v_k_1203_; lean_object* v_v_1204_; lean_object* v_r_1205_; lean_object* v___x_1206_; 
lean_dec(v_h__2_1190_);
v_size_1202_ = lean_ctor_get(v_x_1187_, 0);
lean_inc(v_size_1202_);
v_k_1203_ = lean_ctor_get(v_x_1187_, 1);
lean_inc(v_k_1203_);
v_v_1204_ = lean_ctor_get(v_x_1187_, 2);
lean_inc(v_v_1204_);
v_r_1205_ = lean_ctor_get(v_x_1187_, 4);
lean_inc(v_r_1205_);
lean_dec(v_x_1187_);
v___x_1206_ = lean_apply_5(v_h__1_1189_, v_size_1202_, v_k_1203_, v_v_1204_, v_r_1205_, lean_box(0));
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1207_, lean_object* v_h__1_1208_, lean_object* v_h__2_1209_, lean_object* v_h__3_1210_){
_start:
{
if (lean_obj_tag(v_x_1207_) == 0)
{
lean_object* v_r_1211_; 
lean_dec(v_h__1_1208_);
v_r_1211_ = lean_ctor_get(v_x_1207_, 4);
if (lean_obj_tag(v_r_1211_) == 0)
{
lean_object* v_size_1212_; lean_object* v_k_1213_; lean_object* v_v_1214_; lean_object* v_l_1215_; lean_object* v_size_1216_; lean_object* v_k_1217_; lean_object* v_v_1218_; lean_object* v_l_1219_; lean_object* v_r_1220_; lean_object* v___x_1221_; 
lean_inc_ref(v_r_1211_);
lean_dec(v_h__2_1209_);
v_size_1212_ = lean_ctor_get(v_x_1207_, 0);
lean_inc(v_size_1212_);
v_k_1213_ = lean_ctor_get(v_x_1207_, 1);
lean_inc(v_k_1213_);
v_v_1214_ = lean_ctor_get(v_x_1207_, 2);
lean_inc(v_v_1214_);
v_l_1215_ = lean_ctor_get(v_x_1207_, 3);
lean_inc(v_l_1215_);
lean_dec_ref(v_x_1207_);
v_size_1216_ = lean_ctor_get(v_r_1211_, 0);
lean_inc(v_size_1216_);
v_k_1217_ = lean_ctor_get(v_r_1211_, 1);
lean_inc(v_k_1217_);
v_v_1218_ = lean_ctor_get(v_r_1211_, 2);
lean_inc(v_v_1218_);
v_l_1219_ = lean_ctor_get(v_r_1211_, 3);
lean_inc(v_l_1219_);
v_r_1220_ = lean_ctor_get(v_r_1211_, 4);
lean_inc(v_r_1220_);
lean_dec_ref(v_r_1211_);
v___x_1221_ = lean_apply_9(v_h__3_1210_, v_size_1212_, v_k_1213_, v_v_1214_, v_l_1215_, v_size_1216_, v_k_1217_, v_v_1218_, v_l_1219_, v_r_1220_);
return v___x_1221_;
}
else
{
lean_object* v_size_1222_; lean_object* v_k_1223_; lean_object* v_v_1224_; lean_object* v_l_1225_; lean_object* v___x_1226_; 
lean_dec(v_h__3_1210_);
v_size_1222_ = lean_ctor_get(v_x_1207_, 0);
lean_inc(v_size_1222_);
v_k_1223_ = lean_ctor_get(v_x_1207_, 1);
lean_inc(v_k_1223_);
v_v_1224_ = lean_ctor_get(v_x_1207_, 2);
lean_inc(v_v_1224_);
v_l_1225_ = lean_ctor_get(v_x_1207_, 3);
lean_inc(v_l_1225_);
lean_dec_ref(v_x_1207_);
v___x_1226_ = lean_apply_4(v_h__2_1209_, v_size_1222_, v_k_1223_, v_v_1224_, v_l_1225_);
return v___x_1226_;
}
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec(v_h__3_1210_);
lean_dec(v_h__2_1209_);
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_apply_1(v_h__1_1208_, v___x_1227_);
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1229_, lean_object* v_00_u03b2_1230_, lean_object* v_motive_1231_, lean_object* v_x_1232_, lean_object* v_h__1_1233_, lean_object* v_h__2_1234_, lean_object* v_h__3_1235_){
_start:
{
if (lean_obj_tag(v_x_1232_) == 0)
{
lean_object* v_r_1236_; 
lean_dec(v_h__1_1233_);
v_r_1236_ = lean_ctor_get(v_x_1232_, 4);
if (lean_obj_tag(v_r_1236_) == 0)
{
lean_object* v_size_1237_; lean_object* v_k_1238_; lean_object* v_v_1239_; lean_object* v_l_1240_; lean_object* v_size_1241_; lean_object* v_k_1242_; lean_object* v_v_1243_; lean_object* v_l_1244_; lean_object* v_r_1245_; lean_object* v___x_1246_; 
lean_inc_ref(v_r_1236_);
lean_dec(v_h__2_1234_);
v_size_1237_ = lean_ctor_get(v_x_1232_, 0);
lean_inc(v_size_1237_);
v_k_1238_ = lean_ctor_get(v_x_1232_, 1);
lean_inc(v_k_1238_);
v_v_1239_ = lean_ctor_get(v_x_1232_, 2);
lean_inc(v_v_1239_);
v_l_1240_ = lean_ctor_get(v_x_1232_, 3);
lean_inc(v_l_1240_);
lean_dec_ref(v_x_1232_);
v_size_1241_ = lean_ctor_get(v_r_1236_, 0);
lean_inc(v_size_1241_);
v_k_1242_ = lean_ctor_get(v_r_1236_, 1);
lean_inc(v_k_1242_);
v_v_1243_ = lean_ctor_get(v_r_1236_, 2);
lean_inc(v_v_1243_);
v_l_1244_ = lean_ctor_get(v_r_1236_, 3);
lean_inc(v_l_1244_);
v_r_1245_ = lean_ctor_get(v_r_1236_, 4);
lean_inc(v_r_1245_);
lean_dec_ref(v_r_1236_);
v___x_1246_ = lean_apply_9(v_h__3_1235_, v_size_1237_, v_k_1238_, v_v_1239_, v_l_1240_, v_size_1241_, v_k_1242_, v_v_1243_, v_l_1244_, v_r_1245_);
return v___x_1246_;
}
else
{
lean_object* v_size_1247_; lean_object* v_k_1248_; lean_object* v_v_1249_; lean_object* v_l_1250_; lean_object* v___x_1251_; 
lean_dec(v_h__3_1235_);
v_size_1247_ = lean_ctor_get(v_x_1232_, 0);
lean_inc(v_size_1247_);
v_k_1248_ = lean_ctor_get(v_x_1232_, 1);
lean_inc(v_k_1248_);
v_v_1249_ = lean_ctor_get(v_x_1232_, 2);
lean_inc(v_v_1249_);
v_l_1250_ = lean_ctor_get(v_x_1232_, 3);
lean_inc(v_l_1250_);
lean_dec_ref(v_x_1232_);
v___x_1251_ = lean_apply_4(v_h__2_1234_, v_size_1247_, v_k_1248_, v_v_1249_, v_l_1250_);
return v___x_1251_;
}
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec(v_h__3_1235_);
lean_dec(v_h__2_1234_);
v___x_1252_ = lean_box(0);
v___x_1253_ = lean_apply_1(v_h__1_1233_, v___x_1252_);
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1254_, lean_object* v_x_1255_, lean_object* v_h__1_1256_, lean_object* v_h__2_1257_, lean_object* v_h__3_1258_){
_start:
{
if (lean_obj_tag(v_x_1254_) == 0)
{
lean_object* v_r_1259_; 
lean_dec(v_h__1_1256_);
v_r_1259_ = lean_ctor_get(v_x_1254_, 4);
if (lean_obj_tag(v_r_1259_) == 0)
{
lean_object* v_size_1260_; lean_object* v_k_1261_; lean_object* v_v_1262_; lean_object* v_l_1263_; lean_object* v_size_1264_; lean_object* v_k_1265_; lean_object* v_v_1266_; lean_object* v_l_1267_; lean_object* v_r_1268_; lean_object* v___x_1269_; 
lean_inc_ref(v_r_1259_);
lean_dec(v_h__2_1257_);
v_size_1260_ = lean_ctor_get(v_x_1254_, 0);
lean_inc(v_size_1260_);
v_k_1261_ = lean_ctor_get(v_x_1254_, 1);
lean_inc(v_k_1261_);
v_v_1262_ = lean_ctor_get(v_x_1254_, 2);
lean_inc(v_v_1262_);
v_l_1263_ = lean_ctor_get(v_x_1254_, 3);
lean_inc(v_l_1263_);
lean_dec_ref(v_x_1254_);
v_size_1264_ = lean_ctor_get(v_r_1259_, 0);
lean_inc(v_size_1264_);
v_k_1265_ = lean_ctor_get(v_r_1259_, 1);
lean_inc(v_k_1265_);
v_v_1266_ = lean_ctor_get(v_r_1259_, 2);
lean_inc(v_v_1266_);
v_l_1267_ = lean_ctor_get(v_r_1259_, 3);
lean_inc(v_l_1267_);
v_r_1268_ = lean_ctor_get(v_r_1259_, 4);
lean_inc(v_r_1268_);
lean_dec_ref(v_r_1259_);
v___x_1269_ = lean_apply_10(v_h__3_1258_, v_size_1260_, v_k_1261_, v_v_1262_, v_l_1263_, v_size_1264_, v_k_1265_, v_v_1266_, v_l_1267_, v_r_1268_, v_x_1255_);
return v___x_1269_;
}
else
{
lean_object* v_size_1270_; lean_object* v_k_1271_; lean_object* v_v_1272_; lean_object* v_l_1273_; lean_object* v___x_1274_; 
lean_dec(v_h__3_1258_);
v_size_1270_ = lean_ctor_get(v_x_1254_, 0);
lean_inc(v_size_1270_);
v_k_1271_ = lean_ctor_get(v_x_1254_, 1);
lean_inc(v_k_1271_);
v_v_1272_ = lean_ctor_get(v_x_1254_, 2);
lean_inc(v_v_1272_);
v_l_1273_ = lean_ctor_get(v_x_1254_, 3);
lean_inc(v_l_1273_);
lean_dec_ref(v_x_1254_);
v___x_1274_ = lean_apply_5(v_h__2_1257_, v_size_1270_, v_k_1271_, v_v_1272_, v_l_1273_, v_x_1255_);
return v___x_1274_;
}
}
else
{
lean_object* v___x_1275_; 
lean_dec(v_h__3_1258_);
lean_dec(v_h__2_1257_);
v___x_1275_ = lean_apply_1(v_h__1_1256_, v_x_1255_);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1276_, lean_object* v_00_u03b2_1277_, lean_object* v_motive_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_h__1_1281_, lean_object* v_h__2_1282_, lean_object* v_h__3_1283_){
_start:
{
if (lean_obj_tag(v_x_1279_) == 0)
{
lean_object* v_r_1284_; 
lean_dec(v_h__1_1281_);
v_r_1284_ = lean_ctor_get(v_x_1279_, 4);
if (lean_obj_tag(v_r_1284_) == 0)
{
lean_object* v_size_1285_; lean_object* v_k_1286_; lean_object* v_v_1287_; lean_object* v_l_1288_; lean_object* v_size_1289_; lean_object* v_k_1290_; lean_object* v_v_1291_; lean_object* v_l_1292_; lean_object* v_r_1293_; lean_object* v___x_1294_; 
lean_inc_ref(v_r_1284_);
lean_dec(v_h__2_1282_);
v_size_1285_ = lean_ctor_get(v_x_1279_, 0);
lean_inc(v_size_1285_);
v_k_1286_ = lean_ctor_get(v_x_1279_, 1);
lean_inc(v_k_1286_);
v_v_1287_ = lean_ctor_get(v_x_1279_, 2);
lean_inc(v_v_1287_);
v_l_1288_ = lean_ctor_get(v_x_1279_, 3);
lean_inc(v_l_1288_);
lean_dec_ref(v_x_1279_);
v_size_1289_ = lean_ctor_get(v_r_1284_, 0);
lean_inc(v_size_1289_);
v_k_1290_ = lean_ctor_get(v_r_1284_, 1);
lean_inc(v_k_1290_);
v_v_1291_ = lean_ctor_get(v_r_1284_, 2);
lean_inc(v_v_1291_);
v_l_1292_ = lean_ctor_get(v_r_1284_, 3);
lean_inc(v_l_1292_);
v_r_1293_ = lean_ctor_get(v_r_1284_, 4);
lean_inc(v_r_1293_);
lean_dec_ref(v_r_1284_);
v___x_1294_ = lean_apply_10(v_h__3_1283_, v_size_1285_, v_k_1286_, v_v_1287_, v_l_1288_, v_size_1289_, v_k_1290_, v_v_1291_, v_l_1292_, v_r_1293_, v_x_1280_);
return v___x_1294_;
}
else
{
lean_object* v_size_1295_; lean_object* v_k_1296_; lean_object* v_v_1297_; lean_object* v_l_1298_; lean_object* v___x_1299_; 
lean_dec(v_h__3_1283_);
v_size_1295_ = lean_ctor_get(v_x_1279_, 0);
lean_inc(v_size_1295_);
v_k_1296_ = lean_ctor_get(v_x_1279_, 1);
lean_inc(v_k_1296_);
v_v_1297_ = lean_ctor_get(v_x_1279_, 2);
lean_inc(v_v_1297_);
v_l_1298_ = lean_ctor_get(v_x_1279_, 3);
lean_inc(v_l_1298_);
lean_dec_ref(v_x_1279_);
v___x_1299_ = lean_apply_5(v_h__2_1282_, v_size_1295_, v_k_1296_, v_v_1297_, v_l_1298_, v_x_1280_);
return v___x_1299_;
}
}
else
{
lean_object* v___x_1300_; 
lean_dec(v_h__3_1283_);
lean_dec(v_h__2_1282_);
v___x_1300_ = lean_apply_1(v_h__1_1281_, v_x_1280_);
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object* v_x_1301_, lean_object* v_h__1_1302_, lean_object* v_h__2_1303_){
_start:
{
lean_object* v_r_1304_; 
v_r_1304_ = lean_ctor_get(v_x_1301_, 4);
if (lean_obj_tag(v_r_1304_) == 0)
{
lean_object* v_size_1305_; lean_object* v_k_1306_; lean_object* v_v_1307_; lean_object* v_l_1308_; lean_object* v_size_1309_; lean_object* v_k_1310_; lean_object* v_v_1311_; lean_object* v_l_1312_; lean_object* v_r_1313_; lean_object* v___x_1314_; 
lean_inc_ref(v_r_1304_);
lean_dec(v_h__1_1302_);
v_size_1305_ = lean_ctor_get(v_x_1301_, 0);
lean_inc(v_size_1305_);
v_k_1306_ = lean_ctor_get(v_x_1301_, 1);
lean_inc(v_k_1306_);
v_v_1307_ = lean_ctor_get(v_x_1301_, 2);
lean_inc(v_v_1307_);
v_l_1308_ = lean_ctor_get(v_x_1301_, 3);
lean_inc(v_l_1308_);
lean_dec(v_x_1301_);
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
lean_dec_ref(v_r_1304_);
v___x_1314_ = lean_apply_10(v_h__2_1303_, v_size_1305_, v_k_1306_, v_v_1307_, v_l_1308_, v_size_1309_, v_k_1310_, v_v_1311_, v_l_1312_, v_r_1313_, lean_box(0));
return v___x_1314_;
}
else
{
lean_object* v_size_1315_; lean_object* v_k_1316_; lean_object* v_v_1317_; lean_object* v_l_1318_; lean_object* v___x_1319_; 
lean_dec(v_h__2_1303_);
v_size_1315_ = lean_ctor_get(v_x_1301_, 0);
lean_inc(v_size_1315_);
v_k_1316_ = lean_ctor_get(v_x_1301_, 1);
lean_inc(v_k_1316_);
v_v_1317_ = lean_ctor_get(v_x_1301_, 2);
lean_inc(v_v_1317_);
v_l_1318_ = lean_ctor_get(v_x_1301_, 3);
lean_inc(v_l_1318_);
lean_dec(v_x_1301_);
v___x_1319_ = lean_apply_5(v_h__1_1302_, v_size_1315_, v_k_1316_, v_v_1317_, v_l_1318_, lean_box(0));
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1320_, lean_object* v_00_u03b2_1321_, lean_object* v_motive_1322_, lean_object* v_x_1323_, lean_object* v_x_1324_, lean_object* v_h__1_1325_, lean_object* v_h__2_1326_){
_start:
{
lean_object* v_r_1327_; 
v_r_1327_ = lean_ctor_get(v_x_1323_, 4);
if (lean_obj_tag(v_r_1327_) == 0)
{
lean_object* v_size_1328_; lean_object* v_k_1329_; lean_object* v_v_1330_; lean_object* v_l_1331_; lean_object* v_size_1332_; lean_object* v_k_1333_; lean_object* v_v_1334_; lean_object* v_l_1335_; lean_object* v_r_1336_; lean_object* v___x_1337_; 
lean_inc_ref(v_r_1327_);
lean_dec(v_h__1_1325_);
v_size_1328_ = lean_ctor_get(v_x_1323_, 0);
lean_inc(v_size_1328_);
v_k_1329_ = lean_ctor_get(v_x_1323_, 1);
lean_inc(v_k_1329_);
v_v_1330_ = lean_ctor_get(v_x_1323_, 2);
lean_inc(v_v_1330_);
v_l_1331_ = lean_ctor_get(v_x_1323_, 3);
lean_inc(v_l_1331_);
lean_dec(v_x_1323_);
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
lean_dec_ref(v_r_1327_);
v___x_1337_ = lean_apply_10(v_h__2_1326_, v_size_1328_, v_k_1329_, v_v_1330_, v_l_1331_, v_size_1332_, v_k_1333_, v_v_1334_, v_l_1335_, v_r_1336_, lean_box(0));
return v___x_1337_;
}
else
{
lean_object* v_size_1338_; lean_object* v_k_1339_; lean_object* v_v_1340_; lean_object* v_l_1341_; lean_object* v___x_1342_; 
lean_dec(v_h__2_1326_);
v_size_1338_ = lean_ctor_get(v_x_1323_, 0);
lean_inc(v_size_1338_);
v_k_1339_ = lean_ctor_get(v_x_1323_, 1);
lean_inc(v_k_1339_);
v_v_1340_ = lean_ctor_get(v_x_1323_, 2);
lean_inc(v_v_1340_);
v_l_1341_ = lean_ctor_get(v_x_1323_, 3);
lean_inc(v_l_1341_);
lean_dec(v_x_1323_);
v___x_1342_ = lean_apply_5(v_h__1_1325_, v_size_1338_, v_k_1339_, v_v_1340_, v_l_1341_, lean_box(0));
return v___x_1342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object* v_x_1343_, lean_object* v_x_1344_, lean_object* v_h__1_1345_, lean_object* v_h__2_1346_, lean_object* v_h__3_1347_){
_start:
{
if (lean_obj_tag(v_x_1343_) == 0)
{
lean_object* v_l_1348_; 
lean_dec(v_h__1_1345_);
v_l_1348_ = lean_ctor_get(v_x_1343_, 3);
if (lean_obj_tag(v_l_1348_) == 0)
{
lean_object* v_size_1349_; lean_object* v_k_1350_; lean_object* v_v_1351_; lean_object* v_r_1352_; lean_object* v_size_1353_; lean_object* v_k_1354_; lean_object* v_v_1355_; lean_object* v_l_1356_; lean_object* v_r_1357_; lean_object* v___x_1358_; 
lean_inc_ref(v_l_1348_);
lean_dec(v_h__2_1346_);
v_size_1349_ = lean_ctor_get(v_x_1343_, 0);
lean_inc(v_size_1349_);
v_k_1350_ = lean_ctor_get(v_x_1343_, 1);
lean_inc(v_k_1350_);
v_v_1351_ = lean_ctor_get(v_x_1343_, 2);
lean_inc(v_v_1351_);
v_r_1352_ = lean_ctor_get(v_x_1343_, 4);
lean_inc(v_r_1352_);
lean_dec_ref(v_x_1343_);
v_size_1353_ = lean_ctor_get(v_l_1348_, 0);
lean_inc(v_size_1353_);
v_k_1354_ = lean_ctor_get(v_l_1348_, 1);
lean_inc(v_k_1354_);
v_v_1355_ = lean_ctor_get(v_l_1348_, 2);
lean_inc(v_v_1355_);
v_l_1356_ = lean_ctor_get(v_l_1348_, 3);
lean_inc(v_l_1356_);
v_r_1357_ = lean_ctor_get(v_l_1348_, 4);
lean_inc(v_r_1357_);
lean_dec_ref(v_l_1348_);
v___x_1358_ = lean_apply_10(v_h__3_1347_, v_size_1349_, v_k_1350_, v_v_1351_, v_size_1353_, v_k_1354_, v_v_1355_, v_l_1356_, v_r_1357_, v_r_1352_, v_x_1344_);
return v___x_1358_;
}
else
{
lean_object* v_size_1359_; lean_object* v_k_1360_; lean_object* v_v_1361_; lean_object* v_r_1362_; lean_object* v___x_1363_; 
lean_dec(v_h__3_1347_);
v_size_1359_ = lean_ctor_get(v_x_1343_, 0);
lean_inc(v_size_1359_);
v_k_1360_ = lean_ctor_get(v_x_1343_, 1);
lean_inc(v_k_1360_);
v_v_1361_ = lean_ctor_get(v_x_1343_, 2);
lean_inc(v_v_1361_);
v_r_1362_ = lean_ctor_get(v_x_1343_, 4);
lean_inc(v_r_1362_);
lean_dec_ref(v_x_1343_);
v___x_1363_ = lean_apply_5(v_h__2_1346_, v_size_1359_, v_k_1360_, v_v_1361_, v_r_1362_, v_x_1344_);
return v___x_1363_;
}
}
else
{
lean_object* v___x_1364_; 
lean_dec(v_h__3_1347_);
lean_dec(v_h__2_1346_);
v___x_1364_ = lean_apply_1(v_h__1_1345_, v_x_1344_);
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* v_00_u03b1_1365_, lean_object* v_00_u03b2_1366_, lean_object* v_motive_1367_, lean_object* v_x_1368_, lean_object* v_x_1369_, lean_object* v_h__1_1370_, lean_object* v_h__2_1371_, lean_object* v_h__3_1372_){
_start:
{
if (lean_obj_tag(v_x_1368_) == 0)
{
lean_object* v_l_1373_; 
lean_dec(v_h__1_1370_);
v_l_1373_ = lean_ctor_get(v_x_1368_, 3);
if (lean_obj_tag(v_l_1373_) == 0)
{
lean_object* v_size_1374_; lean_object* v_k_1375_; lean_object* v_v_1376_; lean_object* v_r_1377_; lean_object* v_size_1378_; lean_object* v_k_1379_; lean_object* v_v_1380_; lean_object* v_l_1381_; lean_object* v_r_1382_; lean_object* v___x_1383_; 
lean_inc_ref(v_l_1373_);
lean_dec(v_h__2_1371_);
v_size_1374_ = lean_ctor_get(v_x_1368_, 0);
lean_inc(v_size_1374_);
v_k_1375_ = lean_ctor_get(v_x_1368_, 1);
lean_inc(v_k_1375_);
v_v_1376_ = lean_ctor_get(v_x_1368_, 2);
lean_inc(v_v_1376_);
v_r_1377_ = lean_ctor_get(v_x_1368_, 4);
lean_inc(v_r_1377_);
lean_dec_ref(v_x_1368_);
v_size_1378_ = lean_ctor_get(v_l_1373_, 0);
lean_inc(v_size_1378_);
v_k_1379_ = lean_ctor_get(v_l_1373_, 1);
lean_inc(v_k_1379_);
v_v_1380_ = lean_ctor_get(v_l_1373_, 2);
lean_inc(v_v_1380_);
v_l_1381_ = lean_ctor_get(v_l_1373_, 3);
lean_inc(v_l_1381_);
v_r_1382_ = lean_ctor_get(v_l_1373_, 4);
lean_inc(v_r_1382_);
lean_dec_ref(v_l_1373_);
v___x_1383_ = lean_apply_10(v_h__3_1372_, v_size_1374_, v_k_1375_, v_v_1376_, v_size_1378_, v_k_1379_, v_v_1380_, v_l_1381_, v_r_1382_, v_r_1377_, v_x_1369_);
return v___x_1383_;
}
else
{
lean_object* v_size_1384_; lean_object* v_k_1385_; lean_object* v_v_1386_; lean_object* v_r_1387_; lean_object* v___x_1388_; 
lean_dec(v_h__3_1372_);
v_size_1384_ = lean_ctor_get(v_x_1368_, 0);
lean_inc(v_size_1384_);
v_k_1385_ = lean_ctor_get(v_x_1368_, 1);
lean_inc(v_k_1385_);
v_v_1386_ = lean_ctor_get(v_x_1368_, 2);
lean_inc(v_v_1386_);
v_r_1387_ = lean_ctor_get(v_x_1368_, 4);
lean_inc(v_r_1387_);
lean_dec_ref(v_x_1368_);
v___x_1388_ = lean_apply_5(v_h__2_1371_, v_size_1384_, v_k_1385_, v_v_1386_, v_r_1387_, v_x_1369_);
return v___x_1388_;
}
}
else
{
lean_object* v___x_1389_; 
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
v___x_1389_ = lean_apply_1(v_h__1_1370_, v_x_1369_);
return v___x_1389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object* v_x_1390_, lean_object* v_x_1391_, lean_object* v_h__1_1392_, lean_object* v_h__2_1393_, lean_object* v_h__3_1394_){
_start:
{
if (lean_obj_tag(v_x_1390_) == 0)
{
lean_object* v_r_1395_; 
lean_dec(v_h__1_1392_);
v_r_1395_ = lean_ctor_get(v_x_1390_, 4);
if (lean_obj_tag(v_r_1395_) == 0)
{
lean_object* v_size_1396_; lean_object* v_k_1397_; lean_object* v_v_1398_; lean_object* v_l_1399_; lean_object* v_size_1400_; lean_object* v_k_1401_; lean_object* v_v_1402_; lean_object* v_l_1403_; lean_object* v_r_1404_; lean_object* v___x_1405_; 
lean_inc_ref(v_r_1395_);
lean_dec(v_h__2_1393_);
v_size_1396_ = lean_ctor_get(v_x_1390_, 0);
lean_inc(v_size_1396_);
v_k_1397_ = lean_ctor_get(v_x_1390_, 1);
lean_inc(v_k_1397_);
v_v_1398_ = lean_ctor_get(v_x_1390_, 2);
lean_inc(v_v_1398_);
v_l_1399_ = lean_ctor_get(v_x_1390_, 3);
lean_inc(v_l_1399_);
lean_dec_ref(v_x_1390_);
v_size_1400_ = lean_ctor_get(v_r_1395_, 0);
lean_inc(v_size_1400_);
v_k_1401_ = lean_ctor_get(v_r_1395_, 1);
lean_inc(v_k_1401_);
v_v_1402_ = lean_ctor_get(v_r_1395_, 2);
lean_inc(v_v_1402_);
v_l_1403_ = lean_ctor_get(v_r_1395_, 3);
lean_inc(v_l_1403_);
v_r_1404_ = lean_ctor_get(v_r_1395_, 4);
lean_inc(v_r_1404_);
lean_dec_ref(v_r_1395_);
v___x_1405_ = lean_apply_10(v_h__3_1394_, v_size_1396_, v_k_1397_, v_v_1398_, v_l_1399_, v_size_1400_, v_k_1401_, v_v_1402_, v_l_1403_, v_r_1404_, v_x_1391_);
return v___x_1405_;
}
else
{
lean_object* v_size_1406_; lean_object* v_k_1407_; lean_object* v_v_1408_; lean_object* v_l_1409_; lean_object* v___x_1410_; 
lean_dec(v_h__3_1394_);
v_size_1406_ = lean_ctor_get(v_x_1390_, 0);
lean_inc(v_size_1406_);
v_k_1407_ = lean_ctor_get(v_x_1390_, 1);
lean_inc(v_k_1407_);
v_v_1408_ = lean_ctor_get(v_x_1390_, 2);
lean_inc(v_v_1408_);
v_l_1409_ = lean_ctor_get(v_x_1390_, 3);
lean_inc(v_l_1409_);
lean_dec_ref(v_x_1390_);
v___x_1410_ = lean_apply_5(v_h__2_1393_, v_size_1406_, v_k_1407_, v_v_1408_, v_l_1409_, v_x_1391_);
return v___x_1410_;
}
}
else
{
lean_object* v___x_1411_; 
lean_dec(v_h__3_1394_);
lean_dec(v_h__2_1393_);
v___x_1411_ = lean_apply_1(v_h__1_1392_, v_x_1391_);
return v___x_1411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object* v_00_u03b1_1412_, lean_object* v_00_u03b2_1413_, lean_object* v_motive_1414_, lean_object* v_x_1415_, lean_object* v_x_1416_, lean_object* v_h__1_1417_, lean_object* v_h__2_1418_, lean_object* v_h__3_1419_){
_start:
{
if (lean_obj_tag(v_x_1415_) == 0)
{
lean_object* v_r_1420_; 
lean_dec(v_h__1_1417_);
v_r_1420_ = lean_ctor_get(v_x_1415_, 4);
if (lean_obj_tag(v_r_1420_) == 0)
{
lean_object* v_size_1421_; lean_object* v_k_1422_; lean_object* v_v_1423_; lean_object* v_l_1424_; lean_object* v_size_1425_; lean_object* v_k_1426_; lean_object* v_v_1427_; lean_object* v_l_1428_; lean_object* v_r_1429_; lean_object* v___x_1430_; 
lean_inc_ref(v_r_1420_);
lean_dec(v_h__2_1418_);
v_size_1421_ = lean_ctor_get(v_x_1415_, 0);
lean_inc(v_size_1421_);
v_k_1422_ = lean_ctor_get(v_x_1415_, 1);
lean_inc(v_k_1422_);
v_v_1423_ = lean_ctor_get(v_x_1415_, 2);
lean_inc(v_v_1423_);
v_l_1424_ = lean_ctor_get(v_x_1415_, 3);
lean_inc(v_l_1424_);
lean_dec_ref(v_x_1415_);
v_size_1425_ = lean_ctor_get(v_r_1420_, 0);
lean_inc(v_size_1425_);
v_k_1426_ = lean_ctor_get(v_r_1420_, 1);
lean_inc(v_k_1426_);
v_v_1427_ = lean_ctor_get(v_r_1420_, 2);
lean_inc(v_v_1427_);
v_l_1428_ = lean_ctor_get(v_r_1420_, 3);
lean_inc(v_l_1428_);
v_r_1429_ = lean_ctor_get(v_r_1420_, 4);
lean_inc(v_r_1429_);
lean_dec_ref(v_r_1420_);
v___x_1430_ = lean_apply_10(v_h__3_1419_, v_size_1421_, v_k_1422_, v_v_1423_, v_l_1424_, v_size_1425_, v_k_1426_, v_v_1427_, v_l_1428_, v_r_1429_, v_x_1416_);
return v___x_1430_;
}
else
{
lean_object* v_size_1431_; lean_object* v_k_1432_; lean_object* v_v_1433_; lean_object* v_l_1434_; lean_object* v___x_1435_; 
lean_dec(v_h__3_1419_);
v_size_1431_ = lean_ctor_get(v_x_1415_, 0);
lean_inc(v_size_1431_);
v_k_1432_ = lean_ctor_get(v_x_1415_, 1);
lean_inc(v_k_1432_);
v_v_1433_ = lean_ctor_get(v_x_1415_, 2);
lean_inc(v_v_1433_);
v_l_1434_ = lean_ctor_get(v_x_1415_, 3);
lean_inc(v_l_1434_);
lean_dec_ref(v_x_1415_);
v___x_1435_ = lean_apply_5(v_h__2_1418_, v_size_1431_, v_k_1432_, v_v_1433_, v_l_1434_, v_x_1416_);
return v___x_1435_;
}
}
else
{
lean_object* v___x_1436_; 
lean_dec(v_h__3_1419_);
lean_dec(v_h__2_1418_);
v___x_1436_ = lean_apply_1(v_h__1_1417_, v_x_1416_);
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1437_, lean_object* v_h__1_1438_, lean_object* v_h__2_1439_, lean_object* v_h__3_1440_){
_start:
{
if (lean_obj_tag(v_x_1437_) == 0)
{
lean_object* v_l_1441_; 
lean_dec(v_h__1_1438_);
v_l_1441_ = lean_ctor_get(v_x_1437_, 3);
if (lean_obj_tag(v_l_1441_) == 0)
{
lean_object* v_size_1442_; lean_object* v_k_1443_; lean_object* v_v_1444_; lean_object* v_r_1445_; lean_object* v_size_1446_; lean_object* v_k_1447_; lean_object* v_v_1448_; lean_object* v_l_1449_; lean_object* v_r_1450_; lean_object* v___x_1451_; 
lean_inc_ref(v_l_1441_);
lean_dec(v_h__2_1439_);
v_size_1442_ = lean_ctor_get(v_x_1437_, 0);
lean_inc(v_size_1442_);
v_k_1443_ = lean_ctor_get(v_x_1437_, 1);
lean_inc(v_k_1443_);
v_v_1444_ = lean_ctor_get(v_x_1437_, 2);
lean_inc(v_v_1444_);
v_r_1445_ = lean_ctor_get(v_x_1437_, 4);
lean_inc(v_r_1445_);
lean_dec_ref(v_x_1437_);
v_size_1446_ = lean_ctor_get(v_l_1441_, 0);
lean_inc(v_size_1446_);
v_k_1447_ = lean_ctor_get(v_l_1441_, 1);
lean_inc(v_k_1447_);
v_v_1448_ = lean_ctor_get(v_l_1441_, 2);
lean_inc(v_v_1448_);
v_l_1449_ = lean_ctor_get(v_l_1441_, 3);
lean_inc(v_l_1449_);
v_r_1450_ = lean_ctor_get(v_l_1441_, 4);
lean_inc(v_r_1450_);
lean_dec_ref(v_l_1441_);
v___x_1451_ = lean_apply_9(v_h__3_1440_, v_size_1442_, v_k_1443_, v_v_1444_, v_size_1446_, v_k_1447_, v_v_1448_, v_l_1449_, v_r_1450_, v_r_1445_);
return v___x_1451_;
}
else
{
lean_object* v_size_1452_; lean_object* v_k_1453_; lean_object* v_v_1454_; lean_object* v_r_1455_; lean_object* v___x_1456_; 
lean_dec(v_h__3_1440_);
v_size_1452_ = lean_ctor_get(v_x_1437_, 0);
lean_inc(v_size_1452_);
v_k_1453_ = lean_ctor_get(v_x_1437_, 1);
lean_inc(v_k_1453_);
v_v_1454_ = lean_ctor_get(v_x_1437_, 2);
lean_inc(v_v_1454_);
v_r_1455_ = lean_ctor_get(v_x_1437_, 4);
lean_inc(v_r_1455_);
lean_dec_ref(v_x_1437_);
v___x_1456_ = lean_apply_4(v_h__2_1439_, v_size_1452_, v_k_1453_, v_v_1454_, v_r_1455_);
return v___x_1456_;
}
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec(v_h__3_1440_);
lean_dec(v_h__2_1439_);
v___x_1457_ = lean_box(0);
v___x_1458_ = lean_apply_1(v_h__1_1438_, v___x_1457_);
return v___x_1458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1459_, lean_object* v_00_u03b2_1460_, lean_object* v_motive_1461_, lean_object* v_x_1462_, lean_object* v_h__1_1463_, lean_object* v_h__2_1464_, lean_object* v_h__3_1465_){
_start:
{
if (lean_obj_tag(v_x_1462_) == 0)
{
lean_object* v_l_1466_; 
lean_dec(v_h__1_1463_);
v_l_1466_ = lean_ctor_get(v_x_1462_, 3);
if (lean_obj_tag(v_l_1466_) == 0)
{
lean_object* v_size_1467_; lean_object* v_k_1468_; lean_object* v_v_1469_; lean_object* v_r_1470_; lean_object* v_size_1471_; lean_object* v_k_1472_; lean_object* v_v_1473_; lean_object* v_l_1474_; lean_object* v_r_1475_; lean_object* v___x_1476_; 
lean_inc_ref(v_l_1466_);
lean_dec(v_h__2_1464_);
v_size_1467_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_size_1467_);
v_k_1468_ = lean_ctor_get(v_x_1462_, 1);
lean_inc(v_k_1468_);
v_v_1469_ = lean_ctor_get(v_x_1462_, 2);
lean_inc(v_v_1469_);
v_r_1470_ = lean_ctor_get(v_x_1462_, 4);
lean_inc(v_r_1470_);
lean_dec_ref(v_x_1462_);
v_size_1471_ = lean_ctor_get(v_l_1466_, 0);
lean_inc(v_size_1471_);
v_k_1472_ = lean_ctor_get(v_l_1466_, 1);
lean_inc(v_k_1472_);
v_v_1473_ = lean_ctor_get(v_l_1466_, 2);
lean_inc(v_v_1473_);
v_l_1474_ = lean_ctor_get(v_l_1466_, 3);
lean_inc(v_l_1474_);
v_r_1475_ = lean_ctor_get(v_l_1466_, 4);
lean_inc(v_r_1475_);
lean_dec_ref(v_l_1466_);
v___x_1476_ = lean_apply_9(v_h__3_1465_, v_size_1467_, v_k_1468_, v_v_1469_, v_size_1471_, v_k_1472_, v_v_1473_, v_l_1474_, v_r_1475_, v_r_1470_);
return v___x_1476_;
}
else
{
lean_object* v_size_1477_; lean_object* v_k_1478_; lean_object* v_v_1479_; lean_object* v_r_1480_; lean_object* v___x_1481_; 
lean_dec(v_h__3_1465_);
v_size_1477_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_size_1477_);
v_k_1478_ = lean_ctor_get(v_x_1462_, 1);
lean_inc(v_k_1478_);
v_v_1479_ = lean_ctor_get(v_x_1462_, 2);
lean_inc(v_v_1479_);
v_r_1480_ = lean_ctor_get(v_x_1462_, 4);
lean_inc(v_r_1480_);
lean_dec_ref(v_x_1462_);
v___x_1481_ = lean_apply_4(v_h__2_1464_, v_size_1477_, v_k_1478_, v_v_1479_, v_r_1480_);
return v___x_1481_;
}
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
v___x_1482_ = lean_box(0);
v___x_1483_ = lean_apply_1(v_h__1_1463_, v___x_1482_);
return v___x_1483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object* v_x_1484_, lean_object* v_x_1485_, lean_object* v_h__1_1486_, lean_object* v_h__2_1487_, lean_object* v_h__3_1488_){
_start:
{
if (lean_obj_tag(v_x_1484_) == 0)
{
lean_object* v_l_1489_; 
lean_dec(v_h__1_1486_);
v_l_1489_ = lean_ctor_get(v_x_1484_, 3);
if (lean_obj_tag(v_l_1489_) == 0)
{
lean_object* v_size_1490_; lean_object* v_k_1491_; lean_object* v_v_1492_; lean_object* v_r_1493_; lean_object* v_size_1494_; lean_object* v_k_1495_; lean_object* v_v_1496_; lean_object* v_l_1497_; lean_object* v_r_1498_; lean_object* v___x_1499_; 
lean_inc_ref(v_l_1489_);
lean_dec(v_h__2_1487_);
v_size_1490_ = lean_ctor_get(v_x_1484_, 0);
lean_inc(v_size_1490_);
v_k_1491_ = lean_ctor_get(v_x_1484_, 1);
lean_inc(v_k_1491_);
v_v_1492_ = lean_ctor_get(v_x_1484_, 2);
lean_inc(v_v_1492_);
v_r_1493_ = lean_ctor_get(v_x_1484_, 4);
lean_inc(v_r_1493_);
lean_dec_ref(v_x_1484_);
v_size_1494_ = lean_ctor_get(v_l_1489_, 0);
lean_inc(v_size_1494_);
v_k_1495_ = lean_ctor_get(v_l_1489_, 1);
lean_inc(v_k_1495_);
v_v_1496_ = lean_ctor_get(v_l_1489_, 2);
lean_inc(v_v_1496_);
v_l_1497_ = lean_ctor_get(v_l_1489_, 3);
lean_inc(v_l_1497_);
v_r_1498_ = lean_ctor_get(v_l_1489_, 4);
lean_inc(v_r_1498_);
lean_dec_ref(v_l_1489_);
v___x_1499_ = lean_apply_10(v_h__3_1488_, v_size_1490_, v_k_1491_, v_v_1492_, v_size_1494_, v_k_1495_, v_v_1496_, v_l_1497_, v_r_1498_, v_r_1493_, v_x_1485_);
return v___x_1499_;
}
else
{
lean_object* v_size_1500_; lean_object* v_k_1501_; lean_object* v_v_1502_; lean_object* v_r_1503_; lean_object* v___x_1504_; 
lean_dec(v_h__3_1488_);
v_size_1500_ = lean_ctor_get(v_x_1484_, 0);
lean_inc(v_size_1500_);
v_k_1501_ = lean_ctor_get(v_x_1484_, 1);
lean_inc(v_k_1501_);
v_v_1502_ = lean_ctor_get(v_x_1484_, 2);
lean_inc(v_v_1502_);
v_r_1503_ = lean_ctor_get(v_x_1484_, 4);
lean_inc(v_r_1503_);
lean_dec_ref(v_x_1484_);
v___x_1504_ = lean_apply_5(v_h__2_1487_, v_size_1500_, v_k_1501_, v_v_1502_, v_r_1503_, v_x_1485_);
return v___x_1504_;
}
}
else
{
lean_object* v___x_1505_; 
lean_dec(v_h__3_1488_);
lean_dec(v_h__2_1487_);
v___x_1505_ = lean_apply_1(v_h__1_1486_, v_x_1485_);
return v___x_1505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1506_, lean_object* v_00_u03b2_1507_, lean_object* v_motive_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_, lean_object* v_h__1_1511_, lean_object* v_h__2_1512_, lean_object* v_h__3_1513_){
_start:
{
if (lean_obj_tag(v_x_1509_) == 0)
{
lean_object* v_l_1514_; 
lean_dec(v_h__1_1511_);
v_l_1514_ = lean_ctor_get(v_x_1509_, 3);
if (lean_obj_tag(v_l_1514_) == 0)
{
lean_object* v_size_1515_; lean_object* v_k_1516_; lean_object* v_v_1517_; lean_object* v_r_1518_; lean_object* v_size_1519_; lean_object* v_k_1520_; lean_object* v_v_1521_; lean_object* v_l_1522_; lean_object* v_r_1523_; lean_object* v___x_1524_; 
lean_inc_ref(v_l_1514_);
lean_dec(v_h__2_1512_);
v_size_1515_ = lean_ctor_get(v_x_1509_, 0);
lean_inc(v_size_1515_);
v_k_1516_ = lean_ctor_get(v_x_1509_, 1);
lean_inc(v_k_1516_);
v_v_1517_ = lean_ctor_get(v_x_1509_, 2);
lean_inc(v_v_1517_);
v_r_1518_ = lean_ctor_get(v_x_1509_, 4);
lean_inc(v_r_1518_);
lean_dec_ref(v_x_1509_);
v_size_1519_ = lean_ctor_get(v_l_1514_, 0);
lean_inc(v_size_1519_);
v_k_1520_ = lean_ctor_get(v_l_1514_, 1);
lean_inc(v_k_1520_);
v_v_1521_ = lean_ctor_get(v_l_1514_, 2);
lean_inc(v_v_1521_);
v_l_1522_ = lean_ctor_get(v_l_1514_, 3);
lean_inc(v_l_1522_);
v_r_1523_ = lean_ctor_get(v_l_1514_, 4);
lean_inc(v_r_1523_);
lean_dec_ref(v_l_1514_);
v___x_1524_ = lean_apply_10(v_h__3_1513_, v_size_1515_, v_k_1516_, v_v_1517_, v_size_1519_, v_k_1520_, v_v_1521_, v_l_1522_, v_r_1523_, v_r_1518_, v_x_1510_);
return v___x_1524_;
}
else
{
lean_object* v_size_1525_; lean_object* v_k_1526_; lean_object* v_v_1527_; lean_object* v_r_1528_; lean_object* v___x_1529_; 
lean_dec(v_h__3_1513_);
v_size_1525_ = lean_ctor_get(v_x_1509_, 0);
lean_inc(v_size_1525_);
v_k_1526_ = lean_ctor_get(v_x_1509_, 1);
lean_inc(v_k_1526_);
v_v_1527_ = lean_ctor_get(v_x_1509_, 2);
lean_inc(v_v_1527_);
v_r_1528_ = lean_ctor_get(v_x_1509_, 4);
lean_inc(v_r_1528_);
lean_dec_ref(v_x_1509_);
v___x_1529_ = lean_apply_5(v_h__2_1512_, v_size_1525_, v_k_1526_, v_v_1527_, v_r_1528_, v_x_1510_);
return v___x_1529_;
}
}
else
{
lean_object* v___x_1530_; 
lean_dec(v_h__3_1513_);
lean_dec(v_h__2_1512_);
v___x_1530_ = lean_apply_1(v_h__1_1511_, v_x_1510_);
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* v_x_1531_, lean_object* v_h__1_1532_, lean_object* v_h__2_1533_){
_start:
{
lean_object* v_l_1534_; 
v_l_1534_ = lean_ctor_get(v_x_1531_, 3);
if (lean_obj_tag(v_l_1534_) == 0)
{
lean_object* v_size_1535_; lean_object* v_k_1536_; lean_object* v_v_1537_; lean_object* v_r_1538_; lean_object* v_size_1539_; lean_object* v_k_1540_; lean_object* v_v_1541_; lean_object* v_l_1542_; lean_object* v_r_1543_; lean_object* v___x_1544_; 
lean_inc_ref(v_l_1534_);
lean_dec(v_h__1_1532_);
v_size_1535_ = lean_ctor_get(v_x_1531_, 0);
lean_inc(v_size_1535_);
v_k_1536_ = lean_ctor_get(v_x_1531_, 1);
lean_inc(v_k_1536_);
v_v_1537_ = lean_ctor_get(v_x_1531_, 2);
lean_inc(v_v_1537_);
v_r_1538_ = lean_ctor_get(v_x_1531_, 4);
lean_inc(v_r_1538_);
lean_dec(v_x_1531_);
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
lean_dec_ref(v_l_1534_);
v___x_1544_ = lean_apply_10(v_h__2_1533_, v_size_1535_, v_k_1536_, v_v_1537_, v_size_1539_, v_k_1540_, v_v_1541_, v_l_1542_, v_r_1543_, v_r_1538_, lean_box(0));
return v___x_1544_;
}
else
{
lean_object* v_size_1545_; lean_object* v_k_1546_; lean_object* v_v_1547_; lean_object* v_r_1548_; lean_object* v___x_1549_; 
lean_dec(v_h__2_1533_);
v_size_1545_ = lean_ctor_get(v_x_1531_, 0);
lean_inc(v_size_1545_);
v_k_1546_ = lean_ctor_get(v_x_1531_, 1);
lean_inc(v_k_1546_);
v_v_1547_ = lean_ctor_get(v_x_1531_, 2);
lean_inc(v_v_1547_);
v_r_1548_ = lean_ctor_get(v_x_1531_, 4);
lean_inc(v_r_1548_);
lean_dec(v_x_1531_);
v___x_1549_ = lean_apply_5(v_h__1_1532_, v_size_1545_, v_k_1546_, v_v_1547_, v_r_1548_, lean_box(0));
return v___x_1549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* v_00_u03b1_1550_, lean_object* v_00_u03b2_1551_, lean_object* v_motive_1552_, lean_object* v_x_1553_, lean_object* v_x_1554_, lean_object* v_h__1_1555_, lean_object* v_h__2_1556_){
_start:
{
lean_object* v_l_1557_; 
v_l_1557_ = lean_ctor_get(v_x_1553_, 3);
if (lean_obj_tag(v_l_1557_) == 0)
{
lean_object* v_size_1558_; lean_object* v_k_1559_; lean_object* v_v_1560_; lean_object* v_r_1561_; lean_object* v_size_1562_; lean_object* v_k_1563_; lean_object* v_v_1564_; lean_object* v_l_1565_; lean_object* v_r_1566_; lean_object* v___x_1567_; 
lean_inc_ref(v_l_1557_);
lean_dec(v_h__1_1555_);
v_size_1558_ = lean_ctor_get(v_x_1553_, 0);
lean_inc(v_size_1558_);
v_k_1559_ = lean_ctor_get(v_x_1553_, 1);
lean_inc(v_k_1559_);
v_v_1560_ = lean_ctor_get(v_x_1553_, 2);
lean_inc(v_v_1560_);
v_r_1561_ = lean_ctor_get(v_x_1553_, 4);
lean_inc(v_r_1561_);
lean_dec(v_x_1553_);
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
lean_dec_ref(v_l_1557_);
v___x_1567_ = lean_apply_10(v_h__2_1556_, v_size_1558_, v_k_1559_, v_v_1560_, v_size_1562_, v_k_1563_, v_v_1564_, v_l_1565_, v_r_1566_, v_r_1561_, lean_box(0));
return v___x_1567_;
}
else
{
lean_object* v_size_1568_; lean_object* v_k_1569_; lean_object* v_v_1570_; lean_object* v_r_1571_; lean_object* v___x_1572_; 
lean_dec(v_h__2_1556_);
v_size_1568_ = lean_ctor_get(v_x_1553_, 0);
lean_inc(v_size_1568_);
v_k_1569_ = lean_ctor_get(v_x_1553_, 1);
lean_inc(v_k_1569_);
v_v_1570_ = lean_ctor_get(v_x_1553_, 2);
lean_inc(v_v_1570_);
v_r_1571_ = lean_ctor_get(v_x_1553_, 4);
lean_inc(v_r_1571_);
lean_dec(v_x_1553_);
v___x_1572_ = lean_apply_5(v_h__1_1555_, v_size_1568_, v_k_1569_, v_v_1570_, v_r_1571_, lean_box(0));
return v___x_1572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1573_, lean_object* v_h__1_1574_, lean_object* v_h__2_1575_, lean_object* v_h__3_1576_){
_start:
{
if (lean_obj_tag(v_x_1573_) == 0)
{
lean_object* v_r_1577_; 
lean_dec(v_h__1_1574_);
v_r_1577_ = lean_ctor_get(v_x_1573_, 4);
if (lean_obj_tag(v_r_1577_) == 0)
{
lean_object* v_size_1578_; lean_object* v_k_1579_; lean_object* v_v_1580_; lean_object* v_l_1581_; lean_object* v_size_1582_; lean_object* v_k_1583_; lean_object* v_v_1584_; lean_object* v_l_1585_; lean_object* v_r_1586_; lean_object* v___x_1587_; 
lean_inc_ref(v_r_1577_);
lean_dec(v_h__2_1575_);
v_size_1578_ = lean_ctor_get(v_x_1573_, 0);
lean_inc(v_size_1578_);
v_k_1579_ = lean_ctor_get(v_x_1573_, 1);
lean_inc(v_k_1579_);
v_v_1580_ = lean_ctor_get(v_x_1573_, 2);
lean_inc(v_v_1580_);
v_l_1581_ = lean_ctor_get(v_x_1573_, 3);
lean_inc(v_l_1581_);
lean_dec_ref(v_x_1573_);
v_size_1582_ = lean_ctor_get(v_r_1577_, 0);
lean_inc(v_size_1582_);
v_k_1583_ = lean_ctor_get(v_r_1577_, 1);
lean_inc(v_k_1583_);
v_v_1584_ = lean_ctor_get(v_r_1577_, 2);
lean_inc(v_v_1584_);
v_l_1585_ = lean_ctor_get(v_r_1577_, 3);
lean_inc(v_l_1585_);
v_r_1586_ = lean_ctor_get(v_r_1577_, 4);
lean_inc(v_r_1586_);
lean_dec_ref(v_r_1577_);
v___x_1587_ = lean_apply_9(v_h__3_1576_, v_size_1578_, v_k_1579_, v_v_1580_, v_l_1581_, v_size_1582_, v_k_1583_, v_v_1584_, v_l_1585_, v_r_1586_);
return v___x_1587_;
}
else
{
lean_object* v_size_1588_; lean_object* v_k_1589_; lean_object* v_v_1590_; lean_object* v_l_1591_; lean_object* v___x_1592_; 
lean_dec(v_h__3_1576_);
v_size_1588_ = lean_ctor_get(v_x_1573_, 0);
lean_inc(v_size_1588_);
v_k_1589_ = lean_ctor_get(v_x_1573_, 1);
lean_inc(v_k_1589_);
v_v_1590_ = lean_ctor_get(v_x_1573_, 2);
lean_inc(v_v_1590_);
v_l_1591_ = lean_ctor_get(v_x_1573_, 3);
lean_inc(v_l_1591_);
lean_dec_ref(v_x_1573_);
v___x_1592_ = lean_apply_4(v_h__2_1575_, v_size_1588_, v_k_1589_, v_v_1590_, v_l_1591_);
return v___x_1592_;
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec(v_h__3_1576_);
lean_dec(v_h__2_1575_);
v___x_1593_ = lean_box(0);
v___x_1594_ = lean_apply_1(v_h__1_1574_, v___x_1593_);
return v___x_1594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1595_, lean_object* v_00_u03b2_1596_, lean_object* v_motive_1597_, lean_object* v_x_1598_, lean_object* v_h__1_1599_, lean_object* v_h__2_1600_, lean_object* v_h__3_1601_){
_start:
{
if (lean_obj_tag(v_x_1598_) == 0)
{
lean_object* v_r_1602_; 
lean_dec(v_h__1_1599_);
v_r_1602_ = lean_ctor_get(v_x_1598_, 4);
if (lean_obj_tag(v_r_1602_) == 0)
{
lean_object* v_size_1603_; lean_object* v_k_1604_; lean_object* v_v_1605_; lean_object* v_l_1606_; lean_object* v_size_1607_; lean_object* v_k_1608_; lean_object* v_v_1609_; lean_object* v_l_1610_; lean_object* v_r_1611_; lean_object* v___x_1612_; 
lean_inc_ref(v_r_1602_);
lean_dec(v_h__2_1600_);
v_size_1603_ = lean_ctor_get(v_x_1598_, 0);
lean_inc(v_size_1603_);
v_k_1604_ = lean_ctor_get(v_x_1598_, 1);
lean_inc(v_k_1604_);
v_v_1605_ = lean_ctor_get(v_x_1598_, 2);
lean_inc(v_v_1605_);
v_l_1606_ = lean_ctor_get(v_x_1598_, 3);
lean_inc(v_l_1606_);
lean_dec_ref(v_x_1598_);
v_size_1607_ = lean_ctor_get(v_r_1602_, 0);
lean_inc(v_size_1607_);
v_k_1608_ = lean_ctor_get(v_r_1602_, 1);
lean_inc(v_k_1608_);
v_v_1609_ = lean_ctor_get(v_r_1602_, 2);
lean_inc(v_v_1609_);
v_l_1610_ = lean_ctor_get(v_r_1602_, 3);
lean_inc(v_l_1610_);
v_r_1611_ = lean_ctor_get(v_r_1602_, 4);
lean_inc(v_r_1611_);
lean_dec_ref(v_r_1602_);
v___x_1612_ = lean_apply_9(v_h__3_1601_, v_size_1603_, v_k_1604_, v_v_1605_, v_l_1606_, v_size_1607_, v_k_1608_, v_v_1609_, v_l_1610_, v_r_1611_);
return v___x_1612_;
}
else
{
lean_object* v_size_1613_; lean_object* v_k_1614_; lean_object* v_v_1615_; lean_object* v_l_1616_; lean_object* v___x_1617_; 
lean_dec(v_h__3_1601_);
v_size_1613_ = lean_ctor_get(v_x_1598_, 0);
lean_inc(v_size_1613_);
v_k_1614_ = lean_ctor_get(v_x_1598_, 1);
lean_inc(v_k_1614_);
v_v_1615_ = lean_ctor_get(v_x_1598_, 2);
lean_inc(v_v_1615_);
v_l_1616_ = lean_ctor_get(v_x_1598_, 3);
lean_inc(v_l_1616_);
lean_dec_ref(v_x_1598_);
v___x_1617_ = lean_apply_4(v_h__2_1600_, v_size_1613_, v_k_1614_, v_v_1615_, v_l_1616_);
return v___x_1617_;
}
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec(v_h__3_1601_);
lean_dec(v_h__2_1600_);
v___x_1618_ = lean_box(0);
v___x_1619_ = lean_apply_1(v_h__1_1599_, v___x_1618_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1620_, lean_object* v_x_1621_, lean_object* v_h__1_1622_, lean_object* v_h__2_1623_, lean_object* v_h__3_1624_){
_start:
{
if (lean_obj_tag(v_x_1620_) == 0)
{
lean_object* v_r_1625_; 
lean_dec(v_h__1_1622_);
v_r_1625_ = lean_ctor_get(v_x_1620_, 4);
if (lean_obj_tag(v_r_1625_) == 0)
{
lean_object* v_size_1626_; lean_object* v_k_1627_; lean_object* v_v_1628_; lean_object* v_l_1629_; lean_object* v_size_1630_; lean_object* v_k_1631_; lean_object* v_v_1632_; lean_object* v_l_1633_; lean_object* v_r_1634_; lean_object* v___x_1635_; 
lean_inc_ref(v_r_1625_);
lean_dec(v_h__2_1623_);
v_size_1626_ = lean_ctor_get(v_x_1620_, 0);
lean_inc(v_size_1626_);
v_k_1627_ = lean_ctor_get(v_x_1620_, 1);
lean_inc(v_k_1627_);
v_v_1628_ = lean_ctor_get(v_x_1620_, 2);
lean_inc(v_v_1628_);
v_l_1629_ = lean_ctor_get(v_x_1620_, 3);
lean_inc(v_l_1629_);
lean_dec_ref(v_x_1620_);
v_size_1630_ = lean_ctor_get(v_r_1625_, 0);
lean_inc(v_size_1630_);
v_k_1631_ = lean_ctor_get(v_r_1625_, 1);
lean_inc(v_k_1631_);
v_v_1632_ = lean_ctor_get(v_r_1625_, 2);
lean_inc(v_v_1632_);
v_l_1633_ = lean_ctor_get(v_r_1625_, 3);
lean_inc(v_l_1633_);
v_r_1634_ = lean_ctor_get(v_r_1625_, 4);
lean_inc(v_r_1634_);
lean_dec_ref(v_r_1625_);
v___x_1635_ = lean_apply_10(v_h__3_1624_, v_size_1626_, v_k_1627_, v_v_1628_, v_l_1629_, v_size_1630_, v_k_1631_, v_v_1632_, v_l_1633_, v_r_1634_, v_x_1621_);
return v___x_1635_;
}
else
{
lean_object* v_size_1636_; lean_object* v_k_1637_; lean_object* v_v_1638_; lean_object* v_l_1639_; lean_object* v___x_1640_; 
lean_dec(v_h__3_1624_);
v_size_1636_ = lean_ctor_get(v_x_1620_, 0);
lean_inc(v_size_1636_);
v_k_1637_ = lean_ctor_get(v_x_1620_, 1);
lean_inc(v_k_1637_);
v_v_1638_ = lean_ctor_get(v_x_1620_, 2);
lean_inc(v_v_1638_);
v_l_1639_ = lean_ctor_get(v_x_1620_, 3);
lean_inc(v_l_1639_);
lean_dec_ref(v_x_1620_);
v___x_1640_ = lean_apply_5(v_h__2_1623_, v_size_1636_, v_k_1637_, v_v_1638_, v_l_1639_, v_x_1621_);
return v___x_1640_;
}
}
else
{
lean_object* v___x_1641_; 
lean_dec(v_h__3_1624_);
lean_dec(v_h__2_1623_);
v___x_1641_ = lean_apply_1(v_h__1_1622_, v_x_1621_);
return v___x_1641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1642_, lean_object* v_00_u03b2_1643_, lean_object* v_motive_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_, lean_object* v_h__1_1647_, lean_object* v_h__2_1648_, lean_object* v_h__3_1649_){
_start:
{
if (lean_obj_tag(v_x_1645_) == 0)
{
lean_object* v_r_1650_; 
lean_dec(v_h__1_1647_);
v_r_1650_ = lean_ctor_get(v_x_1645_, 4);
if (lean_obj_tag(v_r_1650_) == 0)
{
lean_object* v_size_1651_; lean_object* v_k_1652_; lean_object* v_v_1653_; lean_object* v_l_1654_; lean_object* v_size_1655_; lean_object* v_k_1656_; lean_object* v_v_1657_; lean_object* v_l_1658_; lean_object* v_r_1659_; lean_object* v___x_1660_; 
lean_inc_ref(v_r_1650_);
lean_dec(v_h__2_1648_);
v_size_1651_ = lean_ctor_get(v_x_1645_, 0);
lean_inc(v_size_1651_);
v_k_1652_ = lean_ctor_get(v_x_1645_, 1);
lean_inc(v_k_1652_);
v_v_1653_ = lean_ctor_get(v_x_1645_, 2);
lean_inc(v_v_1653_);
v_l_1654_ = lean_ctor_get(v_x_1645_, 3);
lean_inc(v_l_1654_);
lean_dec_ref(v_x_1645_);
v_size_1655_ = lean_ctor_get(v_r_1650_, 0);
lean_inc(v_size_1655_);
v_k_1656_ = lean_ctor_get(v_r_1650_, 1);
lean_inc(v_k_1656_);
v_v_1657_ = lean_ctor_get(v_r_1650_, 2);
lean_inc(v_v_1657_);
v_l_1658_ = lean_ctor_get(v_r_1650_, 3);
lean_inc(v_l_1658_);
v_r_1659_ = lean_ctor_get(v_r_1650_, 4);
lean_inc(v_r_1659_);
lean_dec_ref(v_r_1650_);
v___x_1660_ = lean_apply_10(v_h__3_1649_, v_size_1651_, v_k_1652_, v_v_1653_, v_l_1654_, v_size_1655_, v_k_1656_, v_v_1657_, v_l_1658_, v_r_1659_, v_x_1646_);
return v___x_1660_;
}
else
{
lean_object* v_size_1661_; lean_object* v_k_1662_; lean_object* v_v_1663_; lean_object* v_l_1664_; lean_object* v___x_1665_; 
lean_dec(v_h__3_1649_);
v_size_1661_ = lean_ctor_get(v_x_1645_, 0);
lean_inc(v_size_1661_);
v_k_1662_ = lean_ctor_get(v_x_1645_, 1);
lean_inc(v_k_1662_);
v_v_1663_ = lean_ctor_get(v_x_1645_, 2);
lean_inc(v_v_1663_);
v_l_1664_ = lean_ctor_get(v_x_1645_, 3);
lean_inc(v_l_1664_);
lean_dec_ref(v_x_1645_);
v___x_1665_ = lean_apply_5(v_h__2_1648_, v_size_1661_, v_k_1662_, v_v_1663_, v_l_1664_, v_x_1646_);
return v___x_1665_;
}
}
else
{
lean_object* v___x_1666_; 
lean_dec(v_h__3_1649_);
lean_dec(v_h__2_1648_);
v___x_1666_ = lean_apply_1(v_h__1_1647_, v_x_1646_);
return v___x_1666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* v_x_1667_, lean_object* v_h__1_1668_, lean_object* v_h__2_1669_){
_start:
{
lean_object* v_r_1670_; 
v_r_1670_ = lean_ctor_get(v_x_1667_, 4);
if (lean_obj_tag(v_r_1670_) == 0)
{
lean_object* v_size_1671_; lean_object* v_k_1672_; lean_object* v_v_1673_; lean_object* v_l_1674_; lean_object* v_size_1675_; lean_object* v_k_1676_; lean_object* v_v_1677_; lean_object* v_l_1678_; lean_object* v_r_1679_; lean_object* v___x_1680_; 
lean_inc_ref(v_r_1670_);
lean_dec(v_h__1_1668_);
v_size_1671_ = lean_ctor_get(v_x_1667_, 0);
lean_inc(v_size_1671_);
v_k_1672_ = lean_ctor_get(v_x_1667_, 1);
lean_inc(v_k_1672_);
v_v_1673_ = lean_ctor_get(v_x_1667_, 2);
lean_inc(v_v_1673_);
v_l_1674_ = lean_ctor_get(v_x_1667_, 3);
lean_inc(v_l_1674_);
lean_dec(v_x_1667_);
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
lean_dec_ref(v_r_1670_);
v___x_1680_ = lean_apply_10(v_h__2_1669_, v_size_1671_, v_k_1672_, v_v_1673_, v_l_1674_, v_size_1675_, v_k_1676_, v_v_1677_, v_l_1678_, v_r_1679_, lean_box(0));
return v___x_1680_;
}
else
{
lean_object* v_size_1681_; lean_object* v_k_1682_; lean_object* v_v_1683_; lean_object* v_l_1684_; lean_object* v___x_1685_; 
lean_dec(v_h__2_1669_);
v_size_1681_ = lean_ctor_get(v_x_1667_, 0);
lean_inc(v_size_1681_);
v_k_1682_ = lean_ctor_get(v_x_1667_, 1);
lean_inc(v_k_1682_);
v_v_1683_ = lean_ctor_get(v_x_1667_, 2);
lean_inc(v_v_1683_);
v_l_1684_ = lean_ctor_get(v_x_1667_, 3);
lean_inc(v_l_1684_);
lean_dec(v_x_1667_);
v___x_1685_ = lean_apply_5(v_h__1_1668_, v_size_1681_, v_k_1682_, v_v_1683_, v_l_1684_, lean_box(0));
return v___x_1685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1686_, lean_object* v_00_u03b2_1687_, lean_object* v_motive_1688_, lean_object* v_x_1689_, lean_object* v_x_1690_, lean_object* v_h__1_1691_, lean_object* v_h__2_1692_){
_start:
{
lean_object* v_r_1693_; 
v_r_1693_ = lean_ctor_get(v_x_1689_, 4);
if (lean_obj_tag(v_r_1693_) == 0)
{
lean_object* v_size_1694_; lean_object* v_k_1695_; lean_object* v_v_1696_; lean_object* v_l_1697_; lean_object* v_size_1698_; lean_object* v_k_1699_; lean_object* v_v_1700_; lean_object* v_l_1701_; lean_object* v_r_1702_; lean_object* v___x_1703_; 
lean_inc_ref(v_r_1693_);
lean_dec(v_h__1_1691_);
v_size_1694_ = lean_ctor_get(v_x_1689_, 0);
lean_inc(v_size_1694_);
v_k_1695_ = lean_ctor_get(v_x_1689_, 1);
lean_inc(v_k_1695_);
v_v_1696_ = lean_ctor_get(v_x_1689_, 2);
lean_inc(v_v_1696_);
v_l_1697_ = lean_ctor_get(v_x_1689_, 3);
lean_inc(v_l_1697_);
lean_dec(v_x_1689_);
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
lean_dec_ref(v_r_1693_);
v___x_1703_ = lean_apply_10(v_h__2_1692_, v_size_1694_, v_k_1695_, v_v_1696_, v_l_1697_, v_size_1698_, v_k_1699_, v_v_1700_, v_l_1701_, v_r_1702_, lean_box(0));
return v___x_1703_;
}
else
{
lean_object* v_size_1704_; lean_object* v_k_1705_; lean_object* v_v_1706_; lean_object* v_l_1707_; lean_object* v___x_1708_; 
lean_dec(v_h__2_1692_);
v_size_1704_ = lean_ctor_get(v_x_1689_, 0);
lean_inc(v_size_1704_);
v_k_1705_ = lean_ctor_get(v_x_1689_, 1);
lean_inc(v_k_1705_);
v_v_1706_ = lean_ctor_get(v_x_1689_, 2);
lean_inc(v_v_1706_);
v_l_1707_ = lean_ctor_get(v_x_1689_, 3);
lean_inc(v_l_1707_);
lean_dec(v_x_1689_);
v___x_1708_ = lean_apply_5(v_h__1_1691_, v_size_1704_, v_k_1705_, v_v_1706_, v_l_1707_, lean_box(0));
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object* v_l_1709_, lean_object* v_h__1_1710_, lean_object* v_h__2_1711_){
_start:
{
if (lean_obj_tag(v_l_1709_) == 0)
{
lean_object* v_size_1712_; lean_object* v_k_1713_; lean_object* v_v_1714_; lean_object* v_l_1715_; lean_object* v_r_1716_; lean_object* v___x_1717_; 
lean_dec(v_h__1_1710_);
v_size_1712_ = lean_ctor_get(v_l_1709_, 0);
lean_inc(v_size_1712_);
v_k_1713_ = lean_ctor_get(v_l_1709_, 1);
lean_inc(v_k_1713_);
v_v_1714_ = lean_ctor_get(v_l_1709_, 2);
lean_inc(v_v_1714_);
v_l_1715_ = lean_ctor_get(v_l_1709_, 3);
lean_inc(v_l_1715_);
v_r_1716_ = lean_ctor_get(v_l_1709_, 4);
lean_inc(v_r_1716_);
lean_dec_ref(v_l_1709_);
v___x_1717_ = lean_apply_7(v_h__2_1711_, v_size_1712_, v_k_1713_, v_v_1714_, v_l_1715_, v_r_1716_, lean_box(0), lean_box(0));
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; 
lean_dec(v_h__2_1711_);
v___x_1718_ = lean_apply_2(v_h__1_1710_, lean_box(0), lean_box(0));
return v___x_1718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object* v_00_u03b1_1719_, lean_object* v_00_u03b2_1720_, lean_object* v_r_1721_, lean_object* v_motive_1722_, lean_object* v_l_1723_, lean_object* v_hl_1724_, lean_object* v_hlr_1725_, lean_object* v_h__1_1726_, lean_object* v_h__2_1727_){
_start:
{
if (lean_obj_tag(v_l_1723_) == 0)
{
lean_object* v_size_1728_; lean_object* v_k_1729_; lean_object* v_v_1730_; lean_object* v_l_1731_; lean_object* v_r_1732_; lean_object* v___x_1733_; 
lean_dec(v_h__1_1726_);
v_size_1728_ = lean_ctor_get(v_l_1723_, 0);
lean_inc(v_size_1728_);
v_k_1729_ = lean_ctor_get(v_l_1723_, 1);
lean_inc(v_k_1729_);
v_v_1730_ = lean_ctor_get(v_l_1723_, 2);
lean_inc(v_v_1730_);
v_l_1731_ = lean_ctor_get(v_l_1723_, 3);
lean_inc(v_l_1731_);
v_r_1732_ = lean_ctor_get(v_l_1723_, 4);
lean_inc(v_r_1732_);
lean_dec_ref(v_l_1723_);
v___x_1733_ = lean_apply_7(v_h__2_1727_, v_size_1728_, v_k_1729_, v_v_1730_, v_l_1731_, v_r_1732_, lean_box(0), lean_box(0));
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; 
lean_dec(v_h__2_1727_);
v___x_1734_ = lean_apply_2(v_h__1_1726_, lean_box(0), lean_box(0));
return v___x_1734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object* v_00_u03b1_1735_, lean_object* v_00_u03b2_1736_, lean_object* v_r_1737_, lean_object* v_motive_1738_, lean_object* v_l_1739_, lean_object* v_hl_1740_, lean_object* v_hlr_1741_, lean_object* v_h__1_1742_, lean_object* v_h__2_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(v_00_u03b1_1735_, v_00_u03b2_1736_, v_r_1737_, v_motive_1738_, v_l_1739_, v_hl_1740_, v_hlr_1741_, v_h__1_1742_, v_h__2_1743_);
lean_dec(v_r_1737_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(lean_object* v_x_1745_, lean_object* v_h__1_1746_){
_start:
{
lean_object* v_k_1747_; lean_object* v_v_1748_; lean_object* v_tree_1749_; lean_object* v___x_1750_; 
v_k_1747_ = lean_ctor_get(v_x_1745_, 0);
lean_inc(v_k_1747_);
v_v_1748_ = lean_ctor_get(v_x_1745_, 1);
lean_inc(v_v_1748_);
v_tree_1749_ = lean_ctor_get(v_x_1745_, 2);
lean_inc(v_tree_1749_);
lean_dec_ref(v_x_1745_);
v___x_1750_ = lean_apply_5(v_h__1_1746_, v_k_1747_, v_v_1748_, v_tree_1749_, lean_box(0), lean_box(0));
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object* v_00_u03b1_1751_, lean_object* v_00_u03b2_1752_, lean_object* v_l_x27_1753_, lean_object* v_r_x27_1754_, lean_object* v_motive_1755_, lean_object* v_x_1756_, lean_object* v_h__1_1757_){
_start:
{
lean_object* v_k_1758_; lean_object* v_v_1759_; lean_object* v_tree_1760_; lean_object* v___x_1761_; 
v_k_1758_ = lean_ctor_get(v_x_1756_, 0);
lean_inc(v_k_1758_);
v_v_1759_ = lean_ctor_get(v_x_1756_, 1);
lean_inc(v_v_1759_);
v_tree_1760_ = lean_ctor_get(v_x_1756_, 2);
lean_inc(v_tree_1760_);
lean_dec_ref(v_x_1756_);
v___x_1761_ = lean_apply_5(v_h__1_1757_, v_k_1758_, v_v_1759_, v_tree_1760_, lean_box(0), lean_box(0));
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object* v_00_u03b1_1762_, lean_object* v_00_u03b2_1763_, lean_object* v_l_x27_1764_, lean_object* v_r_x27_1765_, lean_object* v_motive_1766_, lean_object* v_x_1767_, lean_object* v_h__1_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(v_00_u03b1_1762_, v_00_u03b2_1763_, v_l_x27_1764_, v_r_x27_1765_, v_motive_1766_, v_x_1767_, v_h__1_1768_);
lean_dec(v_r_x27_1765_);
lean_dec(v_l_x27_1764_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object* v_l_1770_, lean_object* v_h__1_1771_, lean_object* v_h__2_1772_){
_start:
{
if (lean_obj_tag(v_l_1770_) == 0)
{
lean_object* v_size_1773_; lean_object* v_k_1774_; lean_object* v_v_1775_; lean_object* v_l_1776_; lean_object* v_r_1777_; lean_object* v___x_1778_; 
lean_dec(v_h__1_1771_);
v_size_1773_ = lean_ctor_get(v_l_1770_, 0);
lean_inc(v_size_1773_);
v_k_1774_ = lean_ctor_get(v_l_1770_, 1);
lean_inc(v_k_1774_);
v_v_1775_ = lean_ctor_get(v_l_1770_, 2);
lean_inc(v_v_1775_);
v_l_1776_ = lean_ctor_get(v_l_1770_, 3);
lean_inc(v_l_1776_);
v_r_1777_ = lean_ctor_get(v_l_1770_, 4);
lean_inc(v_r_1777_);
lean_dec_ref(v_l_1770_);
v___x_1778_ = lean_apply_5(v_h__2_1772_, v_size_1773_, v_k_1774_, v_v_1775_, v_l_1776_, v_r_1777_);
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec(v_h__2_1772_);
v___x_1779_ = lean_box(0);
v___x_1780_ = lean_apply_1(v_h__1_1771_, v___x_1779_);
return v___x_1780_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object* v_00_u03b1_1781_, lean_object* v_00_u03b2_1782_, lean_object* v_motive_1783_, lean_object* v_l_1784_, lean_object* v_h__1_1785_, lean_object* v_h__2_1786_){
_start:
{
if (lean_obj_tag(v_l_1784_) == 0)
{
lean_object* v_size_1787_; lean_object* v_k_1788_; lean_object* v_v_1789_; lean_object* v_l_1790_; lean_object* v_r_1791_; lean_object* v___x_1792_; 
lean_dec(v_h__1_1785_);
v_size_1787_ = lean_ctor_get(v_l_1784_, 0);
lean_inc(v_size_1787_);
v_k_1788_ = lean_ctor_get(v_l_1784_, 1);
lean_inc(v_k_1788_);
v_v_1789_ = lean_ctor_get(v_l_1784_, 2);
lean_inc(v_v_1789_);
v_l_1790_ = lean_ctor_get(v_l_1784_, 3);
lean_inc(v_l_1790_);
v_r_1791_ = lean_ctor_get(v_l_1784_, 4);
lean_inc(v_r_1791_);
lean_dec_ref(v_l_1784_);
v___x_1792_ = lean_apply_5(v_h__2_1786_, v_size_1787_, v_k_1788_, v_v_1789_, v_l_1790_, v_r_1791_);
return v___x_1792_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_dec(v_h__2_1786_);
v___x_1793_ = lean_box(0);
v___x_1794_ = lean_apply_1(v_h__1_1785_, v___x_1793_);
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(lean_object* v_r_1795_, lean_object* v_h__1_1796_, lean_object* v_h__2_1797_){
_start:
{
if (lean_obj_tag(v_r_1795_) == 0)
{
lean_object* v_size_1798_; lean_object* v_k_1799_; lean_object* v_v_1800_; lean_object* v_l_1801_; lean_object* v_r_1802_; lean_object* v___x_1803_; 
lean_dec(v_h__1_1796_);
v_size_1798_ = lean_ctor_get(v_r_1795_, 0);
lean_inc(v_size_1798_);
v_k_1799_ = lean_ctor_get(v_r_1795_, 1);
lean_inc(v_k_1799_);
v_v_1800_ = lean_ctor_get(v_r_1795_, 2);
lean_inc(v_v_1800_);
v_l_1801_ = lean_ctor_get(v_r_1795_, 3);
lean_inc(v_l_1801_);
v_r_1802_ = lean_ctor_get(v_r_1795_, 4);
lean_inc(v_r_1802_);
lean_dec_ref(v_r_1795_);
v___x_1803_ = lean_apply_7(v_h__2_1797_, v_size_1798_, v_k_1799_, v_v_1800_, v_l_1801_, v_r_1802_, lean_box(0), lean_box(0));
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; 
lean_dec(v_h__2_1797_);
v___x_1804_ = lean_apply_2(v_h__1_1796_, lean_box(0), lean_box(0));
return v___x_1804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object* v_00_u03b1_1805_, lean_object* v_00_u03b2_1806_, lean_object* v_l_1807_, lean_object* v_motive_1808_, lean_object* v_r_1809_, lean_object* v_hr_1810_, lean_object* v_hlr_1811_, lean_object* v_h__1_1812_, lean_object* v_h__2_1813_){
_start:
{
if (lean_obj_tag(v_r_1809_) == 0)
{
lean_object* v_size_1814_; lean_object* v_k_1815_; lean_object* v_v_1816_; lean_object* v_l_1817_; lean_object* v_r_1818_; lean_object* v___x_1819_; 
lean_dec(v_h__1_1812_);
v_size_1814_ = lean_ctor_get(v_r_1809_, 0);
lean_inc(v_size_1814_);
v_k_1815_ = lean_ctor_get(v_r_1809_, 1);
lean_inc(v_k_1815_);
v_v_1816_ = lean_ctor_get(v_r_1809_, 2);
lean_inc(v_v_1816_);
v_l_1817_ = lean_ctor_get(v_r_1809_, 3);
lean_inc(v_l_1817_);
v_r_1818_ = lean_ctor_get(v_r_1809_, 4);
lean_inc(v_r_1818_);
lean_dec_ref(v_r_1809_);
v___x_1819_ = lean_apply_7(v_h__2_1813_, v_size_1814_, v_k_1815_, v_v_1816_, v_l_1817_, v_r_1818_, lean_box(0), lean_box(0));
return v___x_1819_;
}
else
{
lean_object* v___x_1820_; 
lean_dec(v_h__2_1813_);
v___x_1820_ = lean_apply_2(v_h__1_1812_, lean_box(0), lean_box(0));
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object* v_00_u03b1_1821_, lean_object* v_00_u03b2_1822_, lean_object* v_l_1823_, lean_object* v_motive_1824_, lean_object* v_r_1825_, lean_object* v_hr_1826_, lean_object* v_hlr_1827_, lean_object* v_h__1_1828_, lean_object* v_h__2_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(v_00_u03b1_1821_, v_00_u03b2_1822_, v_l_1823_, v_motive_1824_, v_r_1825_, v_hr_1826_, v_hlr_1827_, v_h__1_1828_, v_h__2_1829_);
lean_dec(v_l_1823_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(lean_object* v_r_1831_, lean_object* v_h__1_1832_, lean_object* v_h__2_1833_){
_start:
{
if (lean_obj_tag(v_r_1831_) == 0)
{
lean_object* v_size_1834_; lean_object* v_k_1835_; lean_object* v_v_1836_; lean_object* v_l_1837_; lean_object* v_r_1838_; lean_object* v___x_1839_; 
lean_dec(v_h__1_1832_);
v_size_1834_ = lean_ctor_get(v_r_1831_, 0);
lean_inc(v_size_1834_);
v_k_1835_ = lean_ctor_get(v_r_1831_, 1);
lean_inc(v_k_1835_);
v_v_1836_ = lean_ctor_get(v_r_1831_, 2);
lean_inc(v_v_1836_);
v_l_1837_ = lean_ctor_get(v_r_1831_, 3);
lean_inc(v_l_1837_);
v_r_1838_ = lean_ctor_get(v_r_1831_, 4);
lean_inc(v_r_1838_);
lean_dec_ref(v_r_1831_);
v___x_1839_ = lean_apply_7(v_h__2_1833_, v_size_1834_, v_k_1835_, v_v_1836_, v_l_1837_, v_r_1838_, lean_box(0), lean_box(0));
return v___x_1839_;
}
else
{
lean_object* v___x_1840_; 
lean_dec(v_h__2_1833_);
v___x_1840_ = lean_apply_2(v_h__1_1832_, lean_box(0), lean_box(0));
return v___x_1840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object* v_00_u03b1_1841_, lean_object* v_00_u03b2_1842_, lean_object* v_sz_1843_, lean_object* v_k_1844_, lean_object* v_v_1845_, lean_object* v_l_x27_1846_, lean_object* v_r_x27_1847_, lean_object* v_motive_1848_, lean_object* v_r_1849_, lean_object* v_hr_1850_, lean_object* v_hlr_1851_, lean_object* v_h__1_1852_, lean_object* v_h__2_1853_){
_start:
{
if (lean_obj_tag(v_r_1849_) == 0)
{
lean_object* v_size_1854_; lean_object* v_k_1855_; lean_object* v_v_1856_; lean_object* v_l_1857_; lean_object* v_r_1858_; lean_object* v___x_1859_; 
lean_dec(v_h__1_1852_);
v_size_1854_ = lean_ctor_get(v_r_1849_, 0);
lean_inc(v_size_1854_);
v_k_1855_ = lean_ctor_get(v_r_1849_, 1);
lean_inc(v_k_1855_);
v_v_1856_ = lean_ctor_get(v_r_1849_, 2);
lean_inc(v_v_1856_);
v_l_1857_ = lean_ctor_get(v_r_1849_, 3);
lean_inc(v_l_1857_);
v_r_1858_ = lean_ctor_get(v_r_1849_, 4);
lean_inc(v_r_1858_);
lean_dec_ref(v_r_1849_);
v___x_1859_ = lean_apply_7(v_h__2_1853_, v_size_1854_, v_k_1855_, v_v_1856_, v_l_1857_, v_r_1858_, lean_box(0), lean_box(0));
return v___x_1859_;
}
else
{
lean_object* v___x_1860_; 
lean_dec(v_h__2_1853_);
v___x_1860_ = lean_apply_2(v_h__1_1852_, lean_box(0), lean_box(0));
return v___x_1860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object* v_00_u03b1_1861_, lean_object* v_00_u03b2_1862_, lean_object* v_sz_1863_, lean_object* v_k_1864_, lean_object* v_v_1865_, lean_object* v_l_x27_1866_, lean_object* v_r_x27_1867_, lean_object* v_motive_1868_, lean_object* v_r_1869_, lean_object* v_hr_1870_, lean_object* v_hlr_1871_, lean_object* v_h__1_1872_, lean_object* v_h__2_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(v_00_u03b1_1861_, v_00_u03b2_1862_, v_sz_1863_, v_k_1864_, v_v_1865_, v_l_x27_1866_, v_r_x27_1867_, v_motive_1868_, v_r_1869_, v_hr_1870_, v_hlr_1871_, v_h__1_1872_, v_h__2_1873_);
lean_dec(v_r_x27_1867_);
lean_dec(v_l_x27_1866_);
lean_dec(v_v_1865_);
lean_dec(v_k_1864_);
lean_dec(v_sz_1863_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object* v_t_1875_, lean_object* v_h__1_1876_, lean_object* v_h__2_1877_){
_start:
{
if (lean_obj_tag(v_t_1875_) == 0)
{
lean_object* v_size_1878_; lean_object* v_k_1879_; lean_object* v_v_1880_; lean_object* v_l_1881_; lean_object* v_r_1882_; lean_object* v___x_1883_; 
lean_dec(v_h__1_1876_);
v_size_1878_ = lean_ctor_get(v_t_1875_, 0);
lean_inc(v_size_1878_);
v_k_1879_ = lean_ctor_get(v_t_1875_, 1);
lean_inc(v_k_1879_);
v_v_1880_ = lean_ctor_get(v_t_1875_, 2);
lean_inc(v_v_1880_);
v_l_1881_ = lean_ctor_get(v_t_1875_, 3);
lean_inc(v_l_1881_);
v_r_1882_ = lean_ctor_get(v_t_1875_, 4);
lean_inc(v_r_1882_);
lean_dec_ref(v_t_1875_);
v___x_1883_ = lean_apply_6(v_h__2_1877_, v_size_1878_, v_k_1879_, v_v_1880_, v_l_1881_, v_r_1882_, lean_box(0));
return v___x_1883_;
}
else
{
lean_object* v___x_1884_; 
lean_dec(v_h__2_1877_);
v___x_1884_ = lean_apply_1(v_h__1_1876_, lean_box(0));
return v___x_1884_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object* v_00_u03b1_1885_, lean_object* v_00_u03b2_1886_, lean_object* v_motive_1887_, lean_object* v_t_1888_, lean_object* v_hr_1889_, lean_object* v_h__1_1890_, lean_object* v_h__2_1891_){
_start:
{
if (lean_obj_tag(v_t_1888_) == 0)
{
lean_object* v_size_1892_; lean_object* v_k_1893_; lean_object* v_v_1894_; lean_object* v_l_1895_; lean_object* v_r_1896_; lean_object* v___x_1897_; 
lean_dec(v_h__1_1890_);
v_size_1892_ = lean_ctor_get(v_t_1888_, 0);
lean_inc(v_size_1892_);
v_k_1893_ = lean_ctor_get(v_t_1888_, 1);
lean_inc(v_k_1893_);
v_v_1894_ = lean_ctor_get(v_t_1888_, 2);
lean_inc(v_v_1894_);
v_l_1895_ = lean_ctor_get(v_t_1888_, 3);
lean_inc(v_l_1895_);
v_r_1896_ = lean_ctor_get(v_t_1888_, 4);
lean_inc(v_r_1896_);
lean_dec_ref(v_t_1888_);
v___x_1897_ = lean_apply_6(v_h__2_1891_, v_size_1892_, v_k_1893_, v_v_1894_, v_l_1895_, v_r_1896_, lean_box(0));
return v___x_1897_;
}
else
{
lean_object* v___x_1898_; 
lean_dec(v_h__2_1891_);
v___x_1898_ = lean_apply_1(v_h__1_1890_, lean_box(0));
return v___x_1898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t v_x_1899_, lean_object* v_h__1_1900_, lean_object* v_h__2_1901_, lean_object* v_h__3_1902_){
_start:
{
switch(v_x_1899_)
{
case 0:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_dec(v_h__3_1902_);
lean_dec(v_h__2_1901_);
v___x_1903_ = lean_box(0);
v___x_1904_ = lean_apply_1(v_h__1_1900_, v___x_1903_);
return v___x_1904_;
}
case 1:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_dec(v_h__2_1901_);
lean_dec(v_h__1_1900_);
v___x_1905_ = lean_box(0);
v___x_1906_ = lean_apply_1(v_h__3_1902_, v___x_1905_);
return v___x_1906_;
}
default: 
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
lean_dec(v_h__3_1902_);
lean_dec(v_h__1_1900_);
v___x_1907_ = lean_box(0);
v___x_1908_ = lean_apply_1(v_h__2_1901_, v___x_1907_);
return v___x_1908_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object* v_x_1909_, lean_object* v_h__1_1910_, lean_object* v_h__2_1911_, lean_object* v_h__3_1912_){
_start:
{
uint8_t v_x_36__boxed_1913_; lean_object* v_res_1914_; 
v_x_36__boxed_1913_ = lean_unbox(v_x_1909_);
v_res_1914_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_36__boxed_1913_, v_h__1_1910_, v_h__2_1911_, v_h__3_1912_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object* v_motive_1915_, uint8_t v_x_1916_, lean_object* v_h__1_1917_, lean_object* v_h__2_1918_, lean_object* v_h__3_1919_){
_start:
{
switch(v_x_1916_)
{
case 0:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec(v_h__3_1919_);
lean_dec(v_h__2_1918_);
v___x_1920_ = lean_box(0);
v___x_1921_ = lean_apply_1(v_h__1_1917_, v___x_1920_);
return v___x_1921_;
}
case 1:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
lean_dec(v_h__2_1918_);
lean_dec(v_h__1_1917_);
v___x_1922_ = lean_box(0);
v___x_1923_ = lean_apply_1(v_h__3_1919_, v___x_1922_);
return v___x_1923_;
}
default: 
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
lean_dec(v_h__3_1919_);
lean_dec(v_h__1_1917_);
v___x_1924_ = lean_box(0);
v___x_1925_ = lean_apply_1(v_h__2_1918_, v___x_1924_);
return v___x_1925_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object* v_motive_1926_, lean_object* v_x_1927_, lean_object* v_h__1_1928_, lean_object* v_h__2_1929_, lean_object* v_h__3_1930_){
_start:
{
uint8_t v_x_51__boxed_1931_; lean_object* v_res_1932_; 
v_x_51__boxed_1931_ = lean_unbox(v_x_1927_);
v_res_1932_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_1926_, v_x_51__boxed_1931_, v_h__1_1928_, v_h__2_1929_, v_h__3_1930_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___redArg(lean_object* v_x_1933_, lean_object* v_h__1_1934_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_apply_4(v_h__1_1934_, v_x_1933_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(lean_object* v_00_u03b1_1936_, lean_object* v_00_u03b2_1937_, lean_object* v_l_x27_1938_, lean_object* v_motive_1939_, lean_object* v_x_1940_, lean_object* v_h__1_1941_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_apply_4(v_h__1_1941_, v_x_1940_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___boxed(lean_object* v_00_u03b1_1943_, lean_object* v_00_u03b2_1944_, lean_object* v_l_x27_1945_, lean_object* v_motive_1946_, lean_object* v_x_1947_, lean_object* v_h__1_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(v_00_u03b1_1943_, v_00_u03b2_1944_, v_l_x27_1945_, v_motive_1946_, v_x_1947_, v_h__1_1948_);
lean_dec(v_l_x27_1945_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(lean_object* v_l_1950_, lean_object* v_h__1_1951_, lean_object* v_h__2_1952_){
_start:
{
if (lean_obj_tag(v_l_1950_) == 0)
{
lean_object* v_size_1953_; lean_object* v_k_1954_; lean_object* v_v_1955_; lean_object* v_l_1956_; lean_object* v_r_1957_; lean_object* v___x_1958_; 
lean_dec(v_h__1_1951_);
v_size_1953_ = lean_ctor_get(v_l_1950_, 0);
lean_inc(v_size_1953_);
v_k_1954_ = lean_ctor_get(v_l_1950_, 1);
lean_inc(v_k_1954_);
v_v_1955_ = lean_ctor_get(v_l_1950_, 2);
lean_inc(v_v_1955_);
v_l_1956_ = lean_ctor_get(v_l_1950_, 3);
lean_inc(v_l_1956_);
v_r_1957_ = lean_ctor_get(v_l_1950_, 4);
lean_inc(v_r_1957_);
lean_dec_ref(v_l_1950_);
v___x_1958_ = lean_apply_6(v_h__2_1952_, v_size_1953_, v_k_1954_, v_v_1955_, v_l_1956_, v_r_1957_, lean_box(0));
return v___x_1958_;
}
else
{
lean_object* v___x_1959_; 
lean_dec(v_h__2_1952_);
v___x_1959_ = lean_apply_1(v_h__1_1951_, lean_box(0));
return v___x_1959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(lean_object* v_00_u03b1_1960_, lean_object* v_00_u03b2_1961_, lean_object* v_motive_1962_, lean_object* v_l_1963_, lean_object* v_hl_1964_, lean_object* v_h__1_1965_, lean_object* v_h__2_1966_){
_start:
{
if (lean_obj_tag(v_l_1963_) == 0)
{
lean_object* v_size_1967_; lean_object* v_k_1968_; lean_object* v_v_1969_; lean_object* v_l_1970_; lean_object* v_r_1971_; lean_object* v___x_1972_; 
lean_dec(v_h__1_1965_);
v_size_1967_ = lean_ctor_get(v_l_1963_, 0);
lean_inc(v_size_1967_);
v_k_1968_ = lean_ctor_get(v_l_1963_, 1);
lean_inc(v_k_1968_);
v_v_1969_ = lean_ctor_get(v_l_1963_, 2);
lean_inc(v_v_1969_);
v_l_1970_ = lean_ctor_get(v_l_1963_, 3);
lean_inc(v_l_1970_);
v_r_1971_ = lean_ctor_get(v_l_1963_, 4);
lean_inc(v_r_1971_);
lean_dec_ref(v_l_1963_);
v___x_1972_ = lean_apply_6(v_h__2_1966_, v_size_1967_, v_k_1968_, v_v_1969_, v_l_1970_, v_r_1971_, lean_box(0));
return v___x_1972_;
}
else
{
lean_object* v___x_1973_; 
lean_dec(v_h__2_1966_);
v___x_1973_ = lean_apply_1(v_h__1_1965_, lean_box(0));
return v___x_1973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object* v_x_1974_, lean_object* v_h__1_1975_, lean_object* v_h__2_1976_){
_start:
{
if (lean_obj_tag(v_x_1974_) == 0)
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_dec(v_h__2_1976_);
v___x_1977_ = lean_box(0);
v___x_1978_ = lean_apply_1(v_h__1_1975_, v___x_1977_);
return v___x_1978_;
}
else
{
lean_object* v_val_1979_; lean_object* v_fst_1980_; lean_object* v_snd_1981_; lean_object* v___x_1982_; 
lean_dec(v_h__1_1975_);
v_val_1979_ = lean_ctor_get(v_x_1974_, 0);
lean_inc(v_val_1979_);
lean_dec_ref(v_x_1974_);
v_fst_1980_ = lean_ctor_get(v_val_1979_, 0);
lean_inc(v_fst_1980_);
v_snd_1981_ = lean_ctor_get(v_val_1979_, 1);
lean_inc(v_snd_1981_);
lean_dec(v_val_1979_);
v___x_1982_ = lean_apply_2(v_h__2_1976_, v_fst_1980_, v_snd_1981_);
return v___x_1982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* v_00_u03b1_1983_, lean_object* v_00_u03b2_1984_, lean_object* v_motive_1985_, lean_object* v_x_1986_, lean_object* v_h__1_1987_, lean_object* v_h__2_1988_){
_start:
{
if (lean_obj_tag(v_x_1986_) == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_dec(v_h__2_1988_);
v___x_1989_ = lean_box(0);
v___x_1990_ = lean_apply_1(v_h__1_1987_, v___x_1989_);
return v___x_1990_;
}
else
{
lean_object* v_val_1991_; lean_object* v_fst_1992_; lean_object* v_snd_1993_; lean_object* v___x_1994_; 
lean_dec(v_h__1_1987_);
v_val_1991_ = lean_ctor_get(v_x_1986_, 0);
lean_inc(v_val_1991_);
lean_dec_ref(v_x_1986_);
v_fst_1992_ = lean_ctor_get(v_val_1991_, 0);
lean_inc(v_fst_1992_);
v_snd_1993_ = lean_ctor_get(v_val_1991_, 1);
lean_inc(v_snd_1993_);
lean_dec(v_val_1991_);
v___x_1994_ = lean_apply_2(v_h__2_1988_, v_fst_1992_, v_snd_1993_);
return v___x_1994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(lean_object* v_x_1995_, lean_object* v_h__1_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_apply_4(v_h__1_1996_, v_x_1995_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object* v_00_u03b1_1998_, lean_object* v_00_u03b2_1999_, lean_object* v_l_2000_, lean_object* v_motive_2001_, lean_object* v_x_2002_, lean_object* v_h__1_2003_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = lean_apply_4(v_h__1_2003_, v_x_2002_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(lean_object* v_00_u03b1_2005_, lean_object* v_00_u03b2_2006_, lean_object* v_l_2007_, lean_object* v_motive_2008_, lean_object* v_x_2009_, lean_object* v_h__1_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_2005_, v_00_u03b2_2006_, v_l_2007_, v_motive_2008_, v_x_2009_, v_h__1_2010_);
lean_dec(v_l_2007_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___redArg(lean_object* v_x_2012_, lean_object* v_h__1_2013_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_apply_4(v_h__1_2013_, v_x_2012_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(lean_object* v_00_u03b1_2015_, lean_object* v_00_u03b2_2016_, lean_object* v_l_2017_, lean_object* v_motive_2018_, lean_object* v_x_2019_, lean_object* v_h__1_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_apply_4(v_h__1_2020_, v_x_2019_, lean_box(0), lean_box(0), lean_box(0));
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_2022_, lean_object* v_00_u03b2_2023_, lean_object* v_l_2024_, lean_object* v_motive_2025_, lean_object* v_x_2026_, lean_object* v_h__1_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(v_00_u03b1_2022_, v_00_u03b2_2023_, v_l_2024_, v_motive_2025_, v_x_2026_, v_h__1_2027_);
lean_dec(v_l_2024_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___redArg(lean_object* v_x_2029_, lean_object* v_h__1_2030_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = lean_apply_3(v_h__1_2030_, v_x_2029_, lean_box(0), lean_box(0));
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(lean_object* v_00_u03b1_2032_, lean_object* v_00_u03b2_2033_, lean_object* v_l_x27_2034_, lean_object* v_motive_2035_, lean_object* v_x_2036_, lean_object* v_h__1_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = lean_apply_3(v_h__1_2037_, v_x_2036_, lean_box(0), lean_box(0));
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___boxed(lean_object* v_00_u03b1_2039_, lean_object* v_00_u03b2_2040_, lean_object* v_l_x27_2041_, lean_object* v_motive_2042_, lean_object* v_x_2043_, lean_object* v_h__1_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(v_00_u03b1_2039_, v_00_u03b2_2040_, v_l_x27_2041_, v_motive_2042_, v_x_2043_, v_h__1_2044_);
lean_dec(v_l_x27_2041_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___redArg(lean_object* v_x_2046_, lean_object* v_h__1_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_apply_3(v_h__1_2047_, v_x_2046_, lean_box(0), lean_box(0));
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(lean_object* v_00_u03b1_2049_, lean_object* v_00_u03b2_2050_, lean_object* v_r_x27_2051_, lean_object* v_motive_2052_, lean_object* v_x_2053_, lean_object* v_h__1_2054_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_apply_3(v_h__1_2054_, v_x_2053_, lean_box(0), lean_box(0));
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___boxed(lean_object* v_00_u03b1_2056_, lean_object* v_00_u03b2_2057_, lean_object* v_r_x27_2058_, lean_object* v_motive_2059_, lean_object* v_x_2060_, lean_object* v_h__1_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(v_00_u03b1_2056_, v_00_u03b2_2057_, v_r_x27_2058_, v_motive_2059_, v_x_2060_, v_h__1_2061_);
lean_dec(v_r_x27_2058_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(lean_object* v_r_2063_, lean_object* v_h__1_2064_, lean_object* v_h__2_2065_){
_start:
{
if (lean_obj_tag(v_r_2063_) == 0)
{
lean_object* v_size_2066_; lean_object* v_k_2067_; lean_object* v_v_2068_; lean_object* v_l_2069_; lean_object* v_r_2070_; lean_object* v___x_2071_; 
lean_dec(v_h__1_2064_);
v_size_2066_ = lean_ctor_get(v_r_2063_, 0);
lean_inc(v_size_2066_);
v_k_2067_ = lean_ctor_get(v_r_2063_, 1);
lean_inc(v_k_2067_);
v_v_2068_ = lean_ctor_get(v_r_2063_, 2);
lean_inc(v_v_2068_);
v_l_2069_ = lean_ctor_get(v_r_2063_, 3);
lean_inc(v_l_2069_);
v_r_2070_ = lean_ctor_get(v_r_2063_, 4);
lean_inc(v_r_2070_);
lean_dec_ref(v_r_2063_);
v___x_2071_ = lean_apply_5(v_h__2_2065_, v_size_2066_, v_k_2067_, v_v_2068_, v_l_2069_, v_r_2070_);
return v___x_2071_;
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec(v_h__2_2065_);
v___x_2072_ = lean_box(0);
v___x_2073_ = lean_apply_1(v_h__1_2064_, v___x_2072_);
return v___x_2073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object* v_00_u03b1_2074_, lean_object* v_00_u03b2_2075_, lean_object* v_motive_2076_, lean_object* v_r_2077_, lean_object* v_h__1_2078_, lean_object* v_h__2_2079_){
_start:
{
if (lean_obj_tag(v_r_2077_) == 0)
{
lean_object* v_size_2080_; lean_object* v_k_2081_; lean_object* v_v_2082_; lean_object* v_l_2083_; lean_object* v_r_2084_; lean_object* v___x_2085_; 
lean_dec(v_h__1_2078_);
v_size_2080_ = lean_ctor_get(v_r_2077_, 0);
lean_inc(v_size_2080_);
v_k_2081_ = lean_ctor_get(v_r_2077_, 1);
lean_inc(v_k_2081_);
v_v_2082_ = lean_ctor_get(v_r_2077_, 2);
lean_inc(v_v_2082_);
v_l_2083_ = lean_ctor_get(v_r_2077_, 3);
lean_inc(v_l_2083_);
v_r_2084_ = lean_ctor_get(v_r_2077_, 4);
lean_inc(v_r_2084_);
lean_dec_ref(v_r_2077_);
v___x_2085_ = lean_apply_5(v_h__2_2079_, v_size_2080_, v_k_2081_, v_v_2082_, v_l_2083_, v_r_2084_);
return v___x_2085_;
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec(v_h__2_2079_);
v___x_2086_ = lean_box(0);
v___x_2087_ = lean_apply_1(v_h__1_2078_, v___x_2086_);
return v___x_2087_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(lean_object* v_x_2088_, lean_object* v_h__1_2089_, lean_object* v_h__2_2090_){
_start:
{
if (lean_obj_tag(v_x_2088_) == 0)
{
lean_object* v_size_2091_; lean_object* v_k_2092_; lean_object* v_v_2093_; lean_object* v_l_2094_; lean_object* v_r_2095_; lean_object* v___x_2096_; 
lean_dec(v_h__2_2090_);
v_size_2091_ = lean_ctor_get(v_x_2088_, 0);
lean_inc(v_size_2091_);
v_k_2092_ = lean_ctor_get(v_x_2088_, 1);
lean_inc(v_k_2092_);
v_v_2093_ = lean_ctor_get(v_x_2088_, 2);
lean_inc(v_v_2093_);
v_l_2094_ = lean_ctor_get(v_x_2088_, 3);
lean_inc(v_l_2094_);
v_r_2095_ = lean_ctor_get(v_x_2088_, 4);
lean_inc(v_r_2095_);
lean_dec_ref(v_x_2088_);
v___x_2096_ = lean_apply_5(v_h__1_2089_, v_size_2091_, v_k_2092_, v_v_2093_, v_l_2094_, v_r_2095_);
return v___x_2096_;
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_dec(v_h__1_2089_);
v___x_2097_ = lean_box(0);
v___x_2098_ = lean_apply_1(v_h__2_2090_, v___x_2097_);
return v___x_2098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(lean_object* v_00_u03b1_2099_, lean_object* v_00_u03b2_2100_, lean_object* v_motive_2101_, lean_object* v_x_2102_, lean_object* v_h__1_2103_, lean_object* v_h__2_2104_){
_start:
{
if (lean_obj_tag(v_x_2102_) == 0)
{
lean_object* v_size_2105_; lean_object* v_k_2106_; lean_object* v_v_2107_; lean_object* v_l_2108_; lean_object* v_r_2109_; lean_object* v___x_2110_; 
lean_dec(v_h__2_2104_);
v_size_2105_ = lean_ctor_get(v_x_2102_, 0);
lean_inc(v_size_2105_);
v_k_2106_ = lean_ctor_get(v_x_2102_, 1);
lean_inc(v_k_2106_);
v_v_2107_ = lean_ctor_get(v_x_2102_, 2);
lean_inc(v_v_2107_);
v_l_2108_ = lean_ctor_get(v_x_2102_, 3);
lean_inc(v_l_2108_);
v_r_2109_ = lean_ctor_get(v_x_2102_, 4);
lean_inc(v_r_2109_);
lean_dec_ref(v_x_2102_);
v___x_2110_ = lean_apply_5(v_h__1_2103_, v_size_2105_, v_k_2106_, v_v_2107_, v_l_2108_, v_r_2109_);
return v___x_2110_;
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
lean_dec(v_h__1_2103_);
v___x_2111_ = lean_box(0);
v___x_2112_ = lean_apply_1(v_h__2_2104_, v___x_2111_);
return v___x_2112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object* v_r_2113_, lean_object* v_h__1_2114_, lean_object* v_h__2_2115_){
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
v___x_2121_ = lean_apply_7(v_h__2_2115_, v_size_2116_, v_k_2117_, v_v_2118_, v_l_2119_, v_r_2120_, lean_box(0), lean_box(0));
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; 
lean_dec(v_h__2_2115_);
v___x_2122_ = lean_apply_2(v_h__1_2114_, lean_box(0), lean_box(0));
return v___x_2122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object* v_00_u03b1_2123_, lean_object* v_00_u03b2_2124_, lean_object* v_motive_2125_, lean_object* v_r_2126_, lean_object* v_hr_2127_, lean_object* v_h__1_2128_, lean_object* v_h__2_2129_){
_start:
{
if (lean_obj_tag(v_r_2126_) == 0)
{
lean_object* v_size_2130_; lean_object* v_k_2131_; lean_object* v_v_2132_; lean_object* v_l_2133_; lean_object* v_r_2134_; lean_object* v___x_2135_; 
lean_dec(v_h__1_2128_);
v_size_2130_ = lean_ctor_get(v_r_2126_, 0);
lean_inc(v_size_2130_);
v_k_2131_ = lean_ctor_get(v_r_2126_, 1);
lean_inc(v_k_2131_);
v_v_2132_ = lean_ctor_get(v_r_2126_, 2);
lean_inc(v_v_2132_);
v_l_2133_ = lean_ctor_get(v_r_2126_, 3);
lean_inc(v_l_2133_);
v_r_2134_ = lean_ctor_get(v_r_2126_, 4);
lean_inc(v_r_2134_);
lean_dec_ref(v_r_2126_);
v___x_2135_ = lean_apply_7(v_h__2_2129_, v_size_2130_, v_k_2131_, v_v_2132_, v_l_2133_, v_r_2134_, lean_box(0), lean_box(0));
return v___x_2135_;
}
else
{
lean_object* v___x_2136_; 
lean_dec(v_h__2_2129_);
v___x_2136_ = lean_apply_2(v_h__1_2128_, lean_box(0), lean_box(0));
return v___x_2136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg(lean_object* v_t_2137_, lean_object* v_h__1_2138_, lean_object* v_h__2_2139_){
_start:
{
if (lean_obj_tag(v_t_2137_) == 0)
{
lean_object* v_size_2140_; lean_object* v_k_2141_; lean_object* v_v_2142_; lean_object* v_l_2143_; lean_object* v_r_2144_; lean_object* v___x_2145_; 
lean_dec(v_h__1_2138_);
v_size_2140_ = lean_ctor_get(v_t_2137_, 0);
lean_inc(v_size_2140_);
v_k_2141_ = lean_ctor_get(v_t_2137_, 1);
lean_inc(v_k_2141_);
v_v_2142_ = lean_ctor_get(v_t_2137_, 2);
lean_inc(v_v_2142_);
v_l_2143_ = lean_ctor_get(v_t_2137_, 3);
lean_inc(v_l_2143_);
v_r_2144_ = lean_ctor_get(v_t_2137_, 4);
lean_inc(v_r_2144_);
lean_dec_ref(v_t_2137_);
v___x_2145_ = lean_apply_5(v_h__2_2139_, v_size_2140_, v_k_2141_, v_v_2142_, v_l_2143_, v_r_2144_);
return v___x_2145_;
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
lean_dec(v_h__2_2139_);
v___x_2146_ = lean_box(0);
v___x_2147_ = lean_apply_1(v_h__1_2138_, v___x_2146_);
return v___x_2147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_2148_, lean_object* v_00_u03b4_2149_, lean_object* v_motive_2150_, lean_object* v_t_2151_, lean_object* v_h__1_2152_, lean_object* v_h__2_2153_){
_start:
{
if (lean_obj_tag(v_t_2151_) == 0)
{
lean_object* v_size_2154_; lean_object* v_k_2155_; lean_object* v_v_2156_; lean_object* v_l_2157_; lean_object* v_r_2158_; lean_object* v___x_2159_; 
lean_dec(v_h__1_2152_);
v_size_2154_ = lean_ctor_get(v_t_2151_, 0);
lean_inc(v_size_2154_);
v_k_2155_ = lean_ctor_get(v_t_2151_, 1);
lean_inc(v_k_2155_);
v_v_2156_ = lean_ctor_get(v_t_2151_, 2);
lean_inc(v_v_2156_);
v_l_2157_ = lean_ctor_get(v_t_2151_, 3);
lean_inc(v_l_2157_);
v_r_2158_ = lean_ctor_get(v_t_2151_, 4);
lean_inc(v_r_2158_);
lean_dec_ref(v_t_2151_);
v___x_2159_ = lean_apply_5(v_h__2_2153_, v_size_2154_, v_k_2155_, v_v_2156_, v_l_2157_, v_r_2158_);
return v___x_2159_;
}
else
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_dec(v_h__2_2153_);
v___x_2160_ = lean_box(0);
v___x_2161_ = lean_apply_1(v_h__1_2152_, v___x_2160_);
return v___x_2161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object* v_x_2162_, lean_object* v_h__1_2163_, lean_object* v_h__2_2164_){
_start:
{
if (lean_obj_tag(v_x_2162_) == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v_h__2_2164_);
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_apply_1(v_h__1_2163_, v___x_2165_);
return v___x_2166_;
}
else
{
lean_object* v_val_2167_; lean_object* v___x_2168_; 
lean_dec(v_h__1_2163_);
v_val_2167_ = lean_ctor_get(v_x_2162_, 0);
lean_inc(v_val_2167_);
lean_dec_ref(v_x_2162_);
v___x_2168_ = lean_apply_1(v_h__2_2164_, v_val_2167_);
return v___x_2168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_2169_, lean_object* v_00_u03b2_2170_, lean_object* v_motive_2171_, lean_object* v_x_2172_, lean_object* v_h__1_2173_, lean_object* v_h__2_2174_){
_start:
{
if (lean_obj_tag(v_x_2172_) == 0)
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec(v_h__2_2174_);
v___x_2175_ = lean_box(0);
v___x_2176_ = lean_apply_1(v_h__1_2173_, v___x_2175_);
return v___x_2176_;
}
else
{
lean_object* v_val_2177_; lean_object* v___x_2178_; 
lean_dec(v_h__1_2173_);
v_val_2177_ = lean_ctor_get(v_x_2172_, 0);
lean_inc(v_val_2177_);
lean_dec_ref(v_x_2172_);
v___x_2178_ = lean_apply_1(v_h__2_2174_, v_val_2177_);
return v___x_2178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___redArg(lean_object* v_t_2179_, lean_object* v_h__1_2180_){
_start:
{
lean_object* v_size_2181_; lean_object* v_k_2182_; lean_object* v_v_2183_; lean_object* v_l_2184_; lean_object* v_r_2185_; lean_object* v___x_2186_; 
v_size_2181_ = lean_ctor_get(v_t_2179_, 0);
lean_inc(v_size_2181_);
v_k_2182_ = lean_ctor_get(v_t_2179_, 1);
lean_inc(v_k_2182_);
v_v_2183_ = lean_ctor_get(v_t_2179_, 2);
lean_inc(v_v_2183_);
v_l_2184_ = lean_ctor_get(v_t_2179_, 3);
lean_inc(v_l_2184_);
v_r_2185_ = lean_ctor_get(v_t_2179_, 4);
lean_inc(v_r_2185_);
lean_dec(v_t_2179_);
v___x_2186_ = lean_apply_6(v_h__1_2180_, v_size_2181_, v_k_2182_, v_v_2183_, v_l_2184_, v_r_2185_, lean_box(0));
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(lean_object* v_00_u03b1_2187_, lean_object* v_00_u03b4_2188_, lean_object* v_inst_2189_, lean_object* v_k_2190_, lean_object* v_motive_2191_, lean_object* v_t_2192_, lean_object* v_hlk_2193_, lean_object* v_h__1_2194_){
_start:
{
lean_object* v_size_2195_; lean_object* v_k_2196_; lean_object* v_v_2197_; lean_object* v_l_2198_; lean_object* v_r_2199_; lean_object* v___x_2200_; 
v_size_2195_ = lean_ctor_get(v_t_2192_, 0);
lean_inc(v_size_2195_);
v_k_2196_ = lean_ctor_get(v_t_2192_, 1);
lean_inc(v_k_2196_);
v_v_2197_ = lean_ctor_get(v_t_2192_, 2);
lean_inc(v_v_2197_);
v_l_2198_ = lean_ctor_get(v_t_2192_, 3);
lean_inc(v_l_2198_);
v_r_2199_ = lean_ctor_get(v_t_2192_, 4);
lean_inc(v_r_2199_);
lean_dec(v_t_2192_);
v___x_2200_ = lean_apply_6(v_h__1_2194_, v_size_2195_, v_k_2196_, v_v_2197_, v_l_2198_, v_r_2199_, lean_box(0));
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___boxed(lean_object* v_00_u03b1_2201_, lean_object* v_00_u03b4_2202_, lean_object* v_inst_2203_, lean_object* v_k_2204_, lean_object* v_motive_2205_, lean_object* v_t_2206_, lean_object* v_hlk_2207_, lean_object* v_h__1_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(v_00_u03b1_2201_, v_00_u03b4_2202_, v_inst_2203_, v_k_2204_, v_motive_2205_, v_t_2206_, v_hlk_2207_, v_h__1_2208_);
lean_dec(v_k_2204_);
lean_dec_ref(v_inst_2203_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(lean_object* v_x_2210_, lean_object* v_x_2211_, lean_object* v_h__1_2212_){
_start:
{
lean_object* v_size_2213_; lean_object* v_k_2214_; lean_object* v_v_2215_; lean_object* v_l_2216_; lean_object* v_r_2217_; lean_object* v___x_2218_; 
v_size_2213_ = lean_ctor_get(v_x_2210_, 0);
lean_inc(v_size_2213_);
v_k_2214_ = lean_ctor_get(v_x_2210_, 1);
lean_inc(v_k_2214_);
v_v_2215_ = lean_ctor_get(v_x_2210_, 2);
lean_inc(v_v_2215_);
v_l_2216_ = lean_ctor_get(v_x_2210_, 3);
lean_inc(v_l_2216_);
v_r_2217_ = lean_ctor_get(v_x_2210_, 4);
lean_inc(v_r_2217_);
lean_dec(v_x_2210_);
v___x_2218_ = lean_apply_8(v_h__1_2212_, v_size_2213_, v_k_2214_, v_v_2215_, v_l_2216_, v_r_2217_, lean_box(0), v_x_2211_, lean_box(0));
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter(lean_object* v_00_u03b1_2219_, lean_object* v_00_u03b2_2220_, lean_object* v_motive_2221_, lean_object* v_x_2222_, lean_object* v_x_2223_, lean_object* v_x_2224_, lean_object* v_x_2225_, lean_object* v_h__1_2226_){
_start:
{
lean_object* v_size_2227_; lean_object* v_k_2228_; lean_object* v_v_2229_; lean_object* v_l_2230_; lean_object* v_r_2231_; lean_object* v___x_2232_; 
v_size_2227_ = lean_ctor_get(v_x_2222_, 0);
lean_inc(v_size_2227_);
v_k_2228_ = lean_ctor_get(v_x_2222_, 1);
lean_inc(v_k_2228_);
v_v_2229_ = lean_ctor_get(v_x_2222_, 2);
lean_inc(v_v_2229_);
v_l_2230_ = lean_ctor_get(v_x_2222_, 3);
lean_inc(v_l_2230_);
v_r_2231_ = lean_ctor_get(v_x_2222_, 4);
lean_inc(v_r_2231_);
lean_dec(v_x_2222_);
v___x_2232_ = lean_apply_8(v_h__1_2226_, v_size_2227_, v_k_2228_, v_v_2229_, v_l_2230_, v_r_2231_, lean_box(0), v_x_2224_, lean_box(0));
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(uint8_t v_x_2233_, lean_object* v_h__1_2234_, lean_object* v_h__2_2235_, lean_object* v_h__3_2236_){
_start:
{
switch(v_x_2233_)
{
case 0:
{
lean_object* v___x_2237_; 
lean_dec(v_h__3_2236_);
lean_dec(v_h__2_2235_);
v___x_2237_ = lean_apply_1(v_h__1_2234_, lean_box(0));
return v___x_2237_;
}
case 1:
{
lean_object* v___x_2238_; 
lean_dec(v_h__3_2236_);
lean_dec(v_h__1_2234_);
v___x_2238_ = lean_apply_1(v_h__2_2235_, lean_box(0));
return v___x_2238_;
}
default: 
{
lean_object* v___x_2239_; 
lean_dec(v_h__2_2235_);
lean_dec(v_h__1_2234_);
v___x_2239_ = lean_apply_1(v_h__3_2236_, lean_box(0));
return v___x_2239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg___boxed(lean_object* v_x_2240_, lean_object* v_h__1_2241_, lean_object* v_h__2_2242_, lean_object* v_h__3_2243_){
_start:
{
uint8_t v_x_33__boxed_2244_; lean_object* v_res_2245_; 
v_x_33__boxed_2244_ = lean_unbox(v_x_2240_);
v_res_2245_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(v_x_33__boxed_2244_, v_h__1_2241_, v_h__2_2242_, v_h__3_2243_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(lean_object* v_motive_2246_, uint8_t v_x_2247_, lean_object* v_h__1_2248_, lean_object* v_h__2_2249_, lean_object* v_h__3_2250_){
_start:
{
switch(v_x_2247_)
{
case 0:
{
lean_object* v___x_2251_; 
lean_dec(v_h__3_2250_);
lean_dec(v_h__2_2249_);
v___x_2251_ = lean_apply_1(v_h__1_2248_, lean_box(0));
return v___x_2251_;
}
case 1:
{
lean_object* v___x_2252_; 
lean_dec(v_h__3_2250_);
lean_dec(v_h__1_2248_);
v___x_2252_ = lean_apply_1(v_h__2_2249_, lean_box(0));
return v___x_2252_;
}
default: 
{
lean_object* v___x_2253_; 
lean_dec(v_h__2_2249_);
lean_dec(v_h__1_2248_);
v___x_2253_ = lean_apply_1(v_h__3_2250_, lean_box(0));
return v___x_2253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___boxed(lean_object* v_motive_2254_, lean_object* v_x_2255_, lean_object* v_h__1_2256_, lean_object* v_h__2_2257_, lean_object* v_h__3_2258_){
_start:
{
uint8_t v_x_42__boxed_2259_; lean_object* v_res_2260_; 
v_x_42__boxed_2259_ = lean_unbox(v_x_2255_);
v_res_2260_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(v_motive_2254_, v_x_42__boxed_2259_, v_h__1_2256_, v_h__2_2257_, v_h__3_2258_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object* v_x_2261_, lean_object* v_x_2262_, lean_object* v_h__1_2263_, lean_object* v_h__2_2264_){
_start:
{
if (lean_obj_tag(v_x_2261_) == 0)
{
lean_object* v_size_2265_; lean_object* v_k_2266_; lean_object* v_v_2267_; lean_object* v_l_2268_; lean_object* v_r_2269_; lean_object* v___x_2270_; 
lean_dec(v_h__1_2263_);
v_size_2265_ = lean_ctor_get(v_x_2261_, 0);
lean_inc(v_size_2265_);
v_k_2266_ = lean_ctor_get(v_x_2261_, 1);
lean_inc(v_k_2266_);
v_v_2267_ = lean_ctor_get(v_x_2261_, 2);
lean_inc(v_v_2267_);
v_l_2268_ = lean_ctor_get(v_x_2261_, 3);
lean_inc(v_l_2268_);
v_r_2269_ = lean_ctor_get(v_x_2261_, 4);
lean_inc(v_r_2269_);
lean_dec_ref(v_x_2261_);
v___x_2270_ = lean_apply_6(v_h__2_2264_, v_size_2265_, v_k_2266_, v_v_2267_, v_l_2268_, v_r_2269_, v_x_2262_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; 
lean_dec(v_h__2_2264_);
v___x_2271_ = lean_apply_1(v_h__1_2263_, v_x_2262_);
return v___x_2271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object* v_00_u03b1_2272_, lean_object* v_00_u03b2_2273_, lean_object* v_motive_2274_, lean_object* v_x_2275_, lean_object* v_x_2276_, lean_object* v_h__1_2277_, lean_object* v_h__2_2278_){
_start:
{
if (lean_obj_tag(v_x_2275_) == 0)
{
lean_object* v_size_2279_; lean_object* v_k_2280_; lean_object* v_v_2281_; lean_object* v_l_2282_; lean_object* v_r_2283_; lean_object* v___x_2284_; 
lean_dec(v_h__1_2277_);
v_size_2279_ = lean_ctor_get(v_x_2275_, 0);
lean_inc(v_size_2279_);
v_k_2280_ = lean_ctor_get(v_x_2275_, 1);
lean_inc(v_k_2280_);
v_v_2281_ = lean_ctor_get(v_x_2275_, 2);
lean_inc(v_v_2281_);
v_l_2282_ = lean_ctor_get(v_x_2275_, 3);
lean_inc(v_l_2282_);
v_r_2283_ = lean_ctor_get(v_x_2275_, 4);
lean_inc(v_r_2283_);
lean_dec_ref(v_x_2275_);
v___x_2284_ = lean_apply_6(v_h__2_2278_, v_size_2279_, v_k_2280_, v_v_2281_, v_l_2282_, v_r_2283_, v_x_2276_);
return v___x_2284_;
}
else
{
lean_object* v___x_2285_; 
lean_dec(v_h__2_2278_);
v___x_2285_ = lean_apply_1(v_h__1_2277_, v_x_2276_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t v_x_2286_, lean_object* v_h__1_2287_, lean_object* v_h__2_2288_, lean_object* v_h__3_2289_){
_start:
{
switch(v_x_2286_)
{
case 0:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
lean_dec(v_h__3_2289_);
lean_dec(v_h__2_2288_);
v___x_2290_ = lean_box(0);
v___x_2291_ = lean_apply_1(v_h__1_2287_, v___x_2290_);
return v___x_2291_;
}
case 1:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_dec(v_h__3_2289_);
lean_dec(v_h__1_2287_);
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_apply_1(v_h__2_2288_, v___x_2292_);
return v___x_2293_;
}
default: 
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_dec(v_h__2_2288_);
lean_dec(v_h__1_2287_);
v___x_2294_ = lean_box(0);
v___x_2295_ = lean_apply_1(v_h__3_2289_, v___x_2294_);
return v___x_2295_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_2296_, lean_object* v_h__1_2297_, lean_object* v_h__2_2298_, lean_object* v_h__3_2299_){
_start:
{
uint8_t v_x_36__boxed_2300_; lean_object* v_res_2301_; 
v_x_36__boxed_2300_ = lean_unbox(v_x_2296_);
v_res_2301_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_36__boxed_2300_, v_h__1_2297_, v_h__2_2298_, v_h__3_2299_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object* v_motive_2302_, uint8_t v_x_2303_, lean_object* v_h__1_2304_, lean_object* v_h__2_2305_, lean_object* v_h__3_2306_){
_start:
{
switch(v_x_2303_)
{
case 0:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_dec(v_h__3_2306_);
lean_dec(v_h__2_2305_);
v___x_2307_ = lean_box(0);
v___x_2308_ = lean_apply_1(v_h__1_2304_, v___x_2307_);
return v___x_2308_;
}
case 1:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
lean_dec(v_h__3_2306_);
lean_dec(v_h__1_2304_);
v___x_2309_ = lean_box(0);
v___x_2310_ = lean_apply_1(v_h__2_2305_, v___x_2309_);
return v___x_2310_;
}
default: 
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
lean_dec(v_h__2_2305_);
lean_dec(v_h__1_2304_);
v___x_2311_ = lean_box(0);
v___x_2312_ = lean_apply_1(v_h__3_2306_, v___x_2311_);
return v___x_2312_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object* v_motive_2313_, lean_object* v_x_2314_, lean_object* v_h__1_2315_, lean_object* v_h__2_2316_, lean_object* v_h__3_2317_){
_start:
{
uint8_t v_x_51__boxed_2318_; lean_object* v_res_2319_; 
v_x_51__boxed_2318_ = lean_unbox(v_x_2314_);
v_res_2319_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(v_motive_2313_, v_x_51__boxed_2318_, v_h__1_2315_, v_h__2_2316_, v_h__3_2317_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter___redArg(lean_object* v_x_2320_, lean_object* v_x_2321_, lean_object* v_x_2322_, lean_object* v_h__1_2323_, lean_object* v_h__2_2324_){
_start:
{
if (lean_obj_tag(v_x_2320_) == 0)
{
lean_object* v_size_2325_; lean_object* v_k_2326_; lean_object* v_v_2327_; lean_object* v_l_2328_; lean_object* v_r_2329_; lean_object* v___x_2330_; 
lean_dec(v_h__1_2323_);
v_size_2325_ = lean_ctor_get(v_x_2320_, 0);
lean_inc(v_size_2325_);
v_k_2326_ = lean_ctor_get(v_x_2320_, 1);
lean_inc(v_k_2326_);
v_v_2327_ = lean_ctor_get(v_x_2320_, 2);
lean_inc(v_v_2327_);
v_l_2328_ = lean_ctor_get(v_x_2320_, 3);
lean_inc(v_l_2328_);
v_r_2329_ = lean_ctor_get(v_x_2320_, 4);
lean_inc(v_r_2329_);
lean_dec_ref(v_x_2320_);
v___x_2330_ = lean_apply_7(v_h__2_2324_, v_size_2325_, v_k_2326_, v_v_2327_, v_l_2328_, v_r_2329_, v_x_2321_, v_x_2322_);
return v___x_2330_;
}
else
{
lean_object* v___x_2331_; 
lean_dec(v_h__2_2324_);
v___x_2331_ = lean_apply_2(v_h__1_2323_, v_x_2321_, v_x_2322_);
return v___x_2331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2332_, lean_object* v_00_u03b2_2333_, lean_object* v_motive_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_, lean_object* v_h__1_2338_, lean_object* v_h__2_2339_){
_start:
{
if (lean_obj_tag(v_x_2335_) == 0)
{
lean_object* v_size_2340_; lean_object* v_k_2341_; lean_object* v_v_2342_; lean_object* v_l_2343_; lean_object* v_r_2344_; lean_object* v___x_2345_; 
lean_dec(v_h__1_2338_);
v_size_2340_ = lean_ctor_get(v_x_2335_, 0);
lean_inc(v_size_2340_);
v_k_2341_ = lean_ctor_get(v_x_2335_, 1);
lean_inc(v_k_2341_);
v_v_2342_ = lean_ctor_get(v_x_2335_, 2);
lean_inc(v_v_2342_);
v_l_2343_ = lean_ctor_get(v_x_2335_, 3);
lean_inc(v_l_2343_);
v_r_2344_ = lean_ctor_get(v_x_2335_, 4);
lean_inc(v_r_2344_);
lean_dec_ref(v_x_2335_);
v___x_2345_ = lean_apply_7(v_h__2_2339_, v_size_2340_, v_k_2341_, v_v_2342_, v_l_2343_, v_r_2344_, v_x_2336_, v_x_2337_);
return v___x_2345_;
}
else
{
lean_object* v___x_2346_; 
lean_dec(v_h__2_2339_);
v___x_2346_ = lean_apply_2(v_h__1_2338_, v_x_2336_, v_x_2337_);
return v___x_2346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter___redArg(lean_object* v_x_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_, lean_object* v_h__1_2350_, lean_object* v_h__2_2351_){
_start:
{
if (lean_obj_tag(v_x_2347_) == 0)
{
lean_object* v_size_2352_; lean_object* v_k_2353_; lean_object* v_v_2354_; lean_object* v_l_2355_; lean_object* v_r_2356_; lean_object* v___x_2357_; 
lean_dec(v_h__1_2350_);
v_size_2352_ = lean_ctor_get(v_x_2347_, 0);
lean_inc(v_size_2352_);
v_k_2353_ = lean_ctor_get(v_x_2347_, 1);
lean_inc(v_k_2353_);
v_v_2354_ = lean_ctor_get(v_x_2347_, 2);
lean_inc(v_v_2354_);
v_l_2355_ = lean_ctor_get(v_x_2347_, 3);
lean_inc(v_l_2355_);
v_r_2356_ = lean_ctor_get(v_x_2347_, 4);
lean_inc(v_r_2356_);
lean_dec_ref(v_x_2347_);
v___x_2357_ = lean_apply_7(v_h__2_2351_, v_size_2352_, v_k_2353_, v_v_2354_, v_l_2355_, v_r_2356_, v_x_2348_, v_x_2349_);
return v___x_2357_;
}
else
{
lean_object* v___x_2358_; 
lean_dec(v_h__2_2351_);
v___x_2358_ = lean_apply_2(v_h__1_2350_, v_x_2348_, v_x_2349_);
return v___x_2358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2359_, lean_object* v_00_u03b2_2360_, lean_object* v_motive_2361_, lean_object* v_x_2362_, lean_object* v_x_2363_, lean_object* v_x_2364_, lean_object* v_h__1_2365_, lean_object* v_h__2_2366_){
_start:
{
if (lean_obj_tag(v_x_2362_) == 0)
{
lean_object* v_size_2367_; lean_object* v_k_2368_; lean_object* v_v_2369_; lean_object* v_l_2370_; lean_object* v_r_2371_; lean_object* v___x_2372_; 
lean_dec(v_h__1_2365_);
v_size_2367_ = lean_ctor_get(v_x_2362_, 0);
lean_inc(v_size_2367_);
v_k_2368_ = lean_ctor_get(v_x_2362_, 1);
lean_inc(v_k_2368_);
v_v_2369_ = lean_ctor_get(v_x_2362_, 2);
lean_inc(v_v_2369_);
v_l_2370_ = lean_ctor_get(v_x_2362_, 3);
lean_inc(v_l_2370_);
v_r_2371_ = lean_ctor_get(v_x_2362_, 4);
lean_inc(v_r_2371_);
lean_dec_ref(v_x_2362_);
v___x_2372_ = lean_apply_7(v_h__2_2366_, v_size_2367_, v_k_2368_, v_v_2369_, v_l_2370_, v_r_2371_, v_x_2363_, v_x_2364_);
return v___x_2372_;
}
else
{
lean_object* v___x_2373_; 
lean_dec(v_h__2_2366_);
v___x_2373_ = lean_apply_2(v_h__1_2365_, v_x_2363_, v_x_2364_);
return v___x_2373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(lean_object* v_x_2374_, lean_object* v_c_2375_, lean_object* v_x_2376_, lean_object* v_r_2377_){
_start:
{
if (lean_obj_tag(v_c_2375_) == 0)
{
lean_object* v___x_2378_; 
v___x_2378_ = l_List_head_x3f___redArg(v_r_2377_);
return v___x_2378_;
}
else
{
lean_object* v_val_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
v_val_2379_ = lean_ctor_get(v_c_2375_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_c_2375_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v_c_2375_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_val_2379_);
lean_dec(v_c_2375_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_val_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed(lean_object* v_x_2387_, lean_object* v_c_2388_, lean_object* v_x_2389_, lean_object* v_r_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(v_x_2387_, v_c_2388_, v_x_2389_, v_r_2390_);
lean_dec(v_r_2390_);
lean_dec(v_x_2387_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(lean_object* v_inst_2393_, lean_object* v_k_2394_, lean_object* v_t_2395_){
_start:
{
lean_object* v___f_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___f_2396_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0));
v___x_2397_ = lean_apply_1(v_inst_2393_, v_k_2394_);
v___x_2398_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___x_2397_, v_t_2395_, v___f_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098(lean_object* v_00_u03b1_2399_, lean_object* v_00_u03b2_2400_, lean_object* v_inst_2401_, lean_object* v_k_2402_, lean_object* v_t_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(v_inst_2401_, v_k_2402_, v_t_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(lean_object* v_x_2405_, lean_object* v_x_2406_){
_start:
{
switch(lean_obj_tag(v_x_2406_))
{
case 0:
{
lean_object* v_a_2407_; lean_object* v_a_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v_a_2407_ = lean_ctor_get(v_x_2406_, 0);
lean_inc(v_a_2407_);
v_a_2408_ = lean_ctor_get(v_x_2406_, 1);
lean_inc(v_a_2408_);
lean_dec_ref(v_x_2406_);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v_a_2407_);
lean_ctor_set(v___x_2409_, 1, v_a_2408_);
v___x_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
case 1:
{
lean_object* v_a_2411_; 
v_a_2411_ = lean_ctor_get(v_x_2406_, 1);
lean_inc(v_a_2411_);
if (lean_obj_tag(v_a_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2413_; 
v_a_2412_ = lean_ctor_get(v_x_2406_, 2);
lean_inc(v_a_2412_);
lean_dec_ref(v_x_2406_);
v___x_2413_ = l_List_head_x3f___redArg(v_a_2412_);
lean_dec(v_a_2412_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_inc(v_x_2405_);
return v_x_2405_;
}
else
{
return v___x_2413_;
}
}
else
{
lean_object* v_val_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec_ref(v_x_2406_);
v_val_2414_ = lean_ctor_get(v_a_2411_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_a_2411_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v_a_2411_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_val_2414_);
lean_dec(v_a_2411_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_val_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
default: 
{
lean_dec_ref(v_x_2406_);
lean_inc(v_x_2405_);
return v_x_2405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* v_x_2422_, lean_object* v_x_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(v_x_2422_, v_x_2423_);
lean_dec(v_x_2422_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(lean_object* v_inst_2426_, lean_object* v_k_2427_, lean_object* v_t_2428_){
_start:
{
lean_object* v___f_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___f_2429_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0));
v___x_2430_ = lean_apply_1(v_inst_2426_, v_k_2427_);
v___x_2431_ = lean_box(0);
v___x_2432_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___x_2430_, v___x_2431_, v___f_2429_, v_t_2428_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27(lean_object* v_00_u03b1_2433_, lean_object* v_00_u03b2_2434_, lean_object* v_inst_2435_, lean_object* v_k_2436_, lean_object* v_t_2437_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(v_inst_2435_, v_k_2436_, v_t_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_x_2439_, lean_object* v_x_2440_, lean_object* v_h__1_2441_, lean_object* v_h__2_2442_, lean_object* v_h__3_2443_){
_start:
{
switch(lean_obj_tag(v_x_2440_))
{
case 0:
{
lean_object* v_a_2444_; lean_object* v_a_2445_; lean_object* v_a_2446_; lean_object* v___x_2447_; 
lean_dec(v_h__3_2443_);
lean_dec(v_h__2_2442_);
v_a_2444_ = lean_ctor_get(v_x_2440_, 0);
lean_inc(v_a_2444_);
v_a_2445_ = lean_ctor_get(v_x_2440_, 1);
lean_inc(v_a_2445_);
v_a_2446_ = lean_ctor_get(v_x_2440_, 2);
lean_inc(v_a_2446_);
lean_dec_ref(v_x_2440_);
v___x_2447_ = lean_apply_5(v_h__1_2441_, v_x_2439_, v_a_2444_, lean_box(0), v_a_2445_, v_a_2446_);
return v___x_2447_;
}
case 1:
{
lean_object* v_a_2448_; lean_object* v_a_2449_; lean_object* v_a_2450_; lean_object* v___x_2451_; 
lean_dec(v_h__3_2443_);
lean_dec(v_h__1_2441_);
v_a_2448_ = lean_ctor_get(v_x_2440_, 0);
lean_inc(v_a_2448_);
v_a_2449_ = lean_ctor_get(v_x_2440_, 1);
lean_inc(v_a_2449_);
v_a_2450_ = lean_ctor_get(v_x_2440_, 2);
lean_inc(v_a_2450_);
lean_dec_ref(v_x_2440_);
v___x_2451_ = lean_apply_4(v_h__2_2442_, v_x_2439_, v_a_2448_, v_a_2449_, v_a_2450_);
return v___x_2451_;
}
default: 
{
lean_object* v_a_2452_; lean_object* v_a_2453_; lean_object* v_a_2454_; lean_object* v___x_2455_; 
lean_dec(v_h__2_2442_);
lean_dec(v_h__1_2441_);
v_a_2452_ = lean_ctor_get(v_x_2440_, 0);
lean_inc(v_a_2452_);
v_a_2453_ = lean_ctor_get(v_x_2440_, 1);
lean_inc(v_a_2453_);
v_a_2454_ = lean_ctor_get(v_x_2440_, 2);
lean_inc(v_a_2454_);
lean_dec_ref(v_x_2440_);
v___x_2455_ = lean_apply_5(v_h__3_2443_, v_x_2439_, v_a_2452_, v_a_2453_, lean_box(0), v_a_2454_);
return v___x_2455_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_2456_, lean_object* v_00_u03b2_2457_, lean_object* v_inst_2458_, lean_object* v_k_2459_, lean_object* v_motive_2460_, lean_object* v_x_2461_, lean_object* v_x_2462_, lean_object* v_h__1_2463_, lean_object* v_h__2_2464_, lean_object* v_h__3_2465_){
_start:
{
switch(lean_obj_tag(v_x_2462_))
{
case 0:
{
lean_object* v_a_2466_; lean_object* v_a_2467_; lean_object* v_a_2468_; lean_object* v___x_2469_; 
lean_dec(v_h__3_2465_);
lean_dec(v_h__2_2464_);
v_a_2466_ = lean_ctor_get(v_x_2462_, 0);
lean_inc(v_a_2466_);
v_a_2467_ = lean_ctor_get(v_x_2462_, 1);
lean_inc(v_a_2467_);
v_a_2468_ = lean_ctor_get(v_x_2462_, 2);
lean_inc(v_a_2468_);
lean_dec_ref(v_x_2462_);
v___x_2469_ = lean_apply_5(v_h__1_2463_, v_x_2461_, v_a_2466_, lean_box(0), v_a_2467_, v_a_2468_);
return v___x_2469_;
}
case 1:
{
lean_object* v_a_2470_; lean_object* v_a_2471_; lean_object* v_a_2472_; lean_object* v___x_2473_; 
lean_dec(v_h__3_2465_);
lean_dec(v_h__1_2463_);
v_a_2470_ = lean_ctor_get(v_x_2462_, 0);
lean_inc(v_a_2470_);
v_a_2471_ = lean_ctor_get(v_x_2462_, 1);
lean_inc(v_a_2471_);
v_a_2472_ = lean_ctor_get(v_x_2462_, 2);
lean_inc(v_a_2472_);
lean_dec_ref(v_x_2462_);
v___x_2473_ = lean_apply_4(v_h__2_2464_, v_x_2461_, v_a_2470_, v_a_2471_, v_a_2472_);
return v___x_2473_;
}
default: 
{
lean_object* v_a_2474_; lean_object* v_a_2475_; lean_object* v_a_2476_; lean_object* v___x_2477_; 
lean_dec(v_h__2_2464_);
lean_dec(v_h__1_2463_);
v_a_2474_ = lean_ctor_get(v_x_2462_, 0);
lean_inc(v_a_2474_);
v_a_2475_ = lean_ctor_get(v_x_2462_, 1);
lean_inc(v_a_2475_);
v_a_2476_ = lean_ctor_get(v_x_2462_, 2);
lean_inc(v_a_2476_);
lean_dec_ref(v_x_2462_);
v___x_2477_ = lean_apply_5(v_h__3_2465_, v_x_2461_, v_a_2474_, v_a_2475_, lean_box(0), v_a_2476_);
return v___x_2477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_2478_, lean_object* v_00_u03b2_2479_, lean_object* v_inst_2480_, lean_object* v_k_2481_, lean_object* v_motive_2482_, lean_object* v_x_2483_, lean_object* v_x_2484_, lean_object* v_h__1_2485_, lean_object* v_h__2_2486_, lean_object* v_h__3_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(v_00_u03b1_2478_, v_00_u03b2_2479_, v_inst_2480_, v_k_2481_, v_motive_2482_, v_x_2483_, v_x_2484_, v_h__1_2485_, v_h__2_2486_, v_h__3_2487_);
lean_dec(v_k_2481_);
lean_dec_ref(v_inst_2480_);
return v_res_2488_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(lean_object* v_inst_2489_, lean_object* v_k_2490_, lean_object* v_k_x27_2491_){
_start:
{
lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2492_ = lean_apply_2(v_inst_2489_, v_k_2490_, v_k_x27_2491_);
v___x_2493_ = lean_unbox(v___x_2492_);
if (v___x_2493_ == 1)
{
uint8_t v___x_2494_; 
v___x_2494_ = 2;
return v___x_2494_;
}
else
{
uint8_t v___x_2495_; 
v___x_2495_ = lean_unbox(v___x_2492_);
return v___x_2495_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed(lean_object* v_inst_2496_, lean_object* v_k_2497_, lean_object* v_k_x27_2498_){
_start:
{
uint8_t v_res_2499_; lean_object* v_r_2500_; 
v_res_2499_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(v_inst_2496_, v_k_2497_, v_k_x27_2498_);
v_r_2500_ = lean_box(v_res_2499_);
return v_r_2500_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(lean_object* v_inst_2501_, lean_object* v_k_2502_, lean_object* v_t_2503_){
_start:
{
lean_object* v___f_2504_; lean_object* v___f_2505_; lean_object* v___x_2506_; 
v___f_2504_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2504_, 0, v_inst_2501_);
lean_closure_set(v___f_2504_, 1, v_k_2502_);
v___f_2505_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0));
v___x_2506_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_2504_, v_t_2503_, v___f_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098(lean_object* v_00_u03b1_2507_, lean_object* v_00_u03b2_2508_, lean_object* v_inst_2509_, lean_object* v_k_2510_, lean_object* v_t_2511_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(v_inst_2509_, v_k_2510_, v_t_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(lean_object* v_x_2513_, lean_object* v_x_2514_){
_start:
{
switch(lean_obj_tag(v_x_2514_))
{
case 0:
{
lean_object* v_a_2515_; lean_object* v_a_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v_a_2515_ = lean_ctor_get(v_x_2514_, 0);
v_a_2516_ = lean_ctor_get(v_x_2514_, 1);
lean_inc(v_a_2516_);
lean_inc(v_a_2515_);
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v_a_2515_);
lean_ctor_set(v___x_2517_, 1, v_a_2516_);
v___x_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
return v___x_2518_;
}
case 1:
{
lean_object* v_a_2519_; lean_object* v___x_2520_; 
v_a_2519_ = lean_ctor_get(v_x_2514_, 2);
v___x_2520_ = l_List_head_x3f___redArg(v_a_2519_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_inc(v_x_2513_);
return v_x_2513_;
}
else
{
return v___x_2520_;
}
}
default: 
{
lean_inc(v_x_2513_);
return v_x_2513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* v_x_2521_, lean_object* v_x_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(v_x_2521_, v_x_2522_);
lean_dec_ref(v_x_2522_);
lean_dec(v_x_2521_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(lean_object* v_inst_2525_, lean_object* v_k_2526_, lean_object* v_t_2527_){
_start:
{
lean_object* v___f_2528_; lean_object* v___f_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___f_2528_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2528_, 0, v_inst_2525_);
lean_closure_set(v___f_2528_, 1, v_k_2526_);
v___f_2529_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0));
v___x_2530_ = lean_box(0);
v___x_2531_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___f_2528_, v___x_2530_, v___f_2529_, v_t_2527_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27(lean_object* v_00_u03b1_2532_, lean_object* v_00_u03b2_2533_, lean_object* v_inst_2534_, lean_object* v_k_2535_, lean_object* v_t_2536_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(v_inst_2534_, v_k_2535_, v_t_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(uint8_t v_x_2538_, lean_object* v_h__1_2539_, lean_object* v_h__2_2540_){
_start:
{
if (v_x_2538_ == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec(v_h__2_2540_);
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_apply_1(v_h__1_2539_, v___x_2541_);
return v___x_2542_;
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_dec(v_h__1_2539_);
v___x_2543_ = lean_box(v_x_2538_);
v___x_2544_ = lean_apply_2(v_h__2_2540_, v___x_2543_, lean_box(0));
return v___x_2544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg___boxed(lean_object* v_x_2545_, lean_object* v_h__1_2546_, lean_object* v_h__2_2547_){
_start:
{
uint8_t v_x_17__boxed_2548_; lean_object* v_res_2549_; 
v_x_17__boxed_2548_ = lean_unbox(v_x_2545_);
v_res_2549_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(v_x_17__boxed_2548_, v_h__1_2546_, v_h__2_2547_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(lean_object* v_motive_2550_, uint8_t v_x_2551_, lean_object* v_h__1_2552_, lean_object* v_h__2_2553_){
_start:
{
if (v_x_2551_ == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_dec(v_h__2_2553_);
v___x_2554_ = lean_box(0);
v___x_2555_ = lean_apply_1(v_h__1_2552_, v___x_2554_);
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_dec(v_h__1_2552_);
v___x_2556_ = lean_box(v_x_2551_);
v___x_2557_ = lean_apply_2(v_h__2_2553_, v___x_2556_, lean_box(0));
return v___x_2557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___boxed(lean_object* v_motive_2558_, lean_object* v_x_2559_, lean_object* v_h__1_2560_, lean_object* v_h__2_2561_){
_start:
{
uint8_t v_x_28__boxed_2562_; lean_object* v_res_2563_; 
v_x_28__boxed_2562_ = lean_unbox(v_x_2559_);
v_res_2563_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(v_motive_2558_, v_x_28__boxed_2562_, v_h__1_2560_, v_h__2_2561_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_x_2564_, lean_object* v_x_2565_, lean_object* v_h__1_2566_, lean_object* v_h__2_2567_, lean_object* v_h__3_2568_){
_start:
{
switch(lean_obj_tag(v_x_2565_))
{
case 0:
{
lean_object* v_a_2569_; lean_object* v_a_2570_; lean_object* v_a_2571_; lean_object* v___x_2572_; 
lean_dec(v_h__3_2568_);
lean_dec(v_h__2_2567_);
v_a_2569_ = lean_ctor_get(v_x_2565_, 0);
lean_inc(v_a_2569_);
v_a_2570_ = lean_ctor_get(v_x_2565_, 1);
lean_inc(v_a_2570_);
v_a_2571_ = lean_ctor_get(v_x_2565_, 2);
lean_inc(v_a_2571_);
lean_dec_ref(v_x_2565_);
v___x_2572_ = lean_apply_5(v_h__1_2566_, v_x_2564_, v_a_2569_, lean_box(0), v_a_2570_, v_a_2571_);
return v___x_2572_;
}
case 1:
{
lean_object* v_a_2573_; lean_object* v_a_2574_; lean_object* v_a_2575_; lean_object* v___x_2576_; 
lean_dec(v_h__3_2568_);
lean_dec(v_h__1_2566_);
v_a_2573_ = lean_ctor_get(v_x_2565_, 0);
lean_inc(v_a_2573_);
v_a_2574_ = lean_ctor_get(v_x_2565_, 1);
lean_inc(v_a_2574_);
v_a_2575_ = lean_ctor_get(v_x_2565_, 2);
lean_inc(v_a_2575_);
lean_dec_ref(v_x_2565_);
v___x_2576_ = lean_apply_4(v_h__2_2567_, v_x_2564_, v_a_2573_, v_a_2574_, v_a_2575_);
return v___x_2576_;
}
default: 
{
lean_object* v_a_2577_; lean_object* v_a_2578_; lean_object* v_a_2579_; lean_object* v___x_2580_; 
lean_dec(v_h__2_2567_);
lean_dec(v_h__1_2566_);
v_a_2577_ = lean_ctor_get(v_x_2565_, 0);
lean_inc(v_a_2577_);
v_a_2578_ = lean_ctor_get(v_x_2565_, 1);
lean_inc(v_a_2578_);
v_a_2579_ = lean_ctor_get(v_x_2565_, 2);
lean_inc(v_a_2579_);
lean_dec_ref(v_x_2565_);
v___x_2580_ = lean_apply_5(v_h__3_2568_, v_x_2564_, v_a_2577_, v_a_2578_, lean_box(0), v_a_2579_);
return v___x_2580_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_2581_, lean_object* v_00_u03b2_2582_, lean_object* v_inst_2583_, lean_object* v_k_2584_, lean_object* v_motive_2585_, lean_object* v_x_2586_, lean_object* v_x_2587_, lean_object* v_h__1_2588_, lean_object* v_h__2_2589_, lean_object* v_h__3_2590_){
_start:
{
switch(lean_obj_tag(v_x_2587_))
{
case 0:
{
lean_object* v_a_2591_; lean_object* v_a_2592_; lean_object* v_a_2593_; lean_object* v___x_2594_; 
lean_dec(v_h__3_2590_);
lean_dec(v_h__2_2589_);
v_a_2591_ = lean_ctor_get(v_x_2587_, 0);
lean_inc(v_a_2591_);
v_a_2592_ = lean_ctor_get(v_x_2587_, 1);
lean_inc(v_a_2592_);
v_a_2593_ = lean_ctor_get(v_x_2587_, 2);
lean_inc(v_a_2593_);
lean_dec_ref(v_x_2587_);
v___x_2594_ = lean_apply_5(v_h__1_2588_, v_x_2586_, v_a_2591_, lean_box(0), v_a_2592_, v_a_2593_);
return v___x_2594_;
}
case 1:
{
lean_object* v_a_2595_; lean_object* v_a_2596_; lean_object* v_a_2597_; lean_object* v___x_2598_; 
lean_dec(v_h__3_2590_);
lean_dec(v_h__1_2588_);
v_a_2595_ = lean_ctor_get(v_x_2587_, 0);
lean_inc(v_a_2595_);
v_a_2596_ = lean_ctor_get(v_x_2587_, 1);
lean_inc(v_a_2596_);
v_a_2597_ = lean_ctor_get(v_x_2587_, 2);
lean_inc(v_a_2597_);
lean_dec_ref(v_x_2587_);
v___x_2598_ = lean_apply_4(v_h__2_2589_, v_x_2586_, v_a_2595_, v_a_2596_, v_a_2597_);
return v___x_2598_;
}
default: 
{
lean_object* v_a_2599_; lean_object* v_a_2600_; lean_object* v_a_2601_; lean_object* v___x_2602_; 
lean_dec(v_h__2_2589_);
lean_dec(v_h__1_2588_);
v_a_2599_ = lean_ctor_get(v_x_2587_, 0);
lean_inc(v_a_2599_);
v_a_2600_ = lean_ctor_get(v_x_2587_, 1);
lean_inc(v_a_2600_);
v_a_2601_ = lean_ctor_get(v_x_2587_, 2);
lean_inc(v_a_2601_);
lean_dec_ref(v_x_2587_);
v___x_2602_ = lean_apply_5(v_h__3_2590_, v_x_2586_, v_a_2599_, v_a_2600_, lean_box(0), v_a_2601_);
return v___x_2602_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_2603_, lean_object* v_00_u03b2_2604_, lean_object* v_inst_2605_, lean_object* v_k_2606_, lean_object* v_motive_2607_, lean_object* v_x_2608_, lean_object* v_x_2609_, lean_object* v_h__1_2610_, lean_object* v_h__2_2611_, lean_object* v_h__3_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(v_00_u03b1_2603_, v_00_u03b2_2604_, v_inst_2605_, v_k_2606_, v_motive_2607_, v_x_2608_, v_x_2609_, v_h__1_2610_, v_h__2_2611_, v_h__3_2612_);
lean_dec(v_k_2606_);
lean_dec_ref(v_inst_2605_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(uint8_t v_x_2614_, lean_object* v_h__1_2615_, lean_object* v_h__2_2616_){
_start:
{
if (v_x_2614_ == 2)
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_dec(v_h__2_2616_);
v___x_2617_ = lean_box(0);
v___x_2618_ = lean_apply_1(v_h__1_2615_, v___x_2617_);
return v___x_2618_;
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
lean_dec(v_h__1_2615_);
v___x_2619_ = lean_box(v_x_2614_);
v___x_2620_ = lean_apply_2(v_h__2_2616_, v___x_2619_, lean_box(0));
return v___x_2620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg___boxed(lean_object* v_x_2621_, lean_object* v_h__1_2622_, lean_object* v_h__2_2623_){
_start:
{
uint8_t v_x_17__boxed_2624_; lean_object* v_res_2625_; 
v_x_17__boxed_2624_ = lean_unbox(v_x_2621_);
v_res_2625_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(v_x_17__boxed_2624_, v_h__1_2622_, v_h__2_2623_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(lean_object* v_motive_2626_, uint8_t v_x_2627_, lean_object* v_h__1_2628_, lean_object* v_h__2_2629_){
_start:
{
if (v_x_2627_ == 2)
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_dec(v_h__2_2629_);
v___x_2630_ = lean_box(0);
v___x_2631_ = lean_apply_1(v_h__1_2628_, v___x_2630_);
return v___x_2631_;
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_dec(v_h__1_2628_);
v___x_2632_ = lean_box(v_x_2627_);
v___x_2633_ = lean_apply_2(v_h__2_2629_, v___x_2632_, lean_box(0));
return v___x_2633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___boxed(lean_object* v_motive_2634_, lean_object* v_x_2635_, lean_object* v_h__1_2636_, lean_object* v_h__2_2637_){
_start:
{
uint8_t v_x_28__boxed_2638_; lean_object* v_res_2639_; 
v_x_28__boxed_2638_ = lean_unbox(v_x_2635_);
v_res_2639_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(v_motive_2634_, v_x_28__boxed_2638_, v_h__1_2636_, v_h__2_2637_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(uint8_t v_x_2640_, lean_object* v_h__1_2641_, lean_object* v_h__2_2642_, lean_object* v_h__3_2643_){
_start:
{
switch(v_x_2640_)
{
case 0:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
lean_dec(v_h__3_2643_);
lean_dec(v_h__2_2642_);
v___x_2644_ = lean_box(0);
v___x_2645_ = lean_apply_1(v_h__1_2641_, v___x_2644_);
return v___x_2645_;
}
case 1:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
lean_dec(v_h__3_2643_);
lean_dec(v_h__1_2641_);
v___x_2646_ = lean_box(0);
v___x_2647_ = lean_apply_1(v_h__2_2642_, v___x_2646_);
return v___x_2647_;
}
default: 
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_dec(v_h__2_2642_);
lean_dec(v_h__1_2641_);
v___x_2648_ = lean_box(0);
v___x_2649_ = lean_apply_1(v_h__3_2643_, v___x_2648_);
return v___x_2649_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object* v_x_2650_, lean_object* v_h__1_2651_, lean_object* v_h__2_2652_, lean_object* v_h__3_2653_){
_start:
{
uint8_t v_x_36__boxed_2654_; lean_object* v_res_2655_; 
v_x_36__boxed_2654_ = lean_unbox(v_x_2650_);
v_res_2655_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(v_x_36__boxed_2654_, v_h__1_2651_, v_h__2_2652_, v_h__3_2653_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(lean_object* v_motive_2656_, uint8_t v_x_2657_, lean_object* v_h__1_2658_, lean_object* v_h__2_2659_, lean_object* v_h__3_2660_){
_start:
{
switch(v_x_2657_)
{
case 0:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
lean_dec(v_h__3_2660_);
lean_dec(v_h__2_2659_);
v___x_2661_ = lean_box(0);
v___x_2662_ = lean_apply_1(v_h__1_2658_, v___x_2661_);
return v___x_2662_;
}
case 1:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
lean_dec(v_h__3_2660_);
lean_dec(v_h__1_2658_);
v___x_2663_ = lean_box(0);
v___x_2664_ = lean_apply_1(v_h__2_2659_, v___x_2663_);
return v___x_2664_;
}
default: 
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
lean_dec(v_h__2_2659_);
lean_dec(v_h__1_2658_);
v___x_2665_ = lean_box(0);
v___x_2666_ = lean_apply_1(v_h__3_2660_, v___x_2665_);
return v___x_2666_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___boxed(lean_object* v_motive_2667_, lean_object* v_x_2668_, lean_object* v_h__1_2669_, lean_object* v_h__2_2670_, lean_object* v_h__3_2671_){
_start:
{
uint8_t v_x_51__boxed_2672_; lean_object* v_res_2673_; 
v_x_51__boxed_2672_ = lean_unbox(v_x_2668_);
v_res_2673_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(v_motive_2667_, v_x_51__boxed_2672_, v_h__1_2669_, v_h__2_2670_, v_h__3_2671_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___redArg(lean_object* v_x_2674_, lean_object* v_h__1_2675_, lean_object* v_h__2_2676_){
_start:
{
if (lean_obj_tag(v_x_2674_) == 0)
{
lean_object* v_size_2677_; lean_object* v_k_2678_; lean_object* v_v_2679_; lean_object* v_l_2680_; lean_object* v_r_2681_; lean_object* v___x_2682_; 
lean_dec(v_h__1_2675_);
v_size_2677_ = lean_ctor_get(v_x_2674_, 0);
lean_inc(v_size_2677_);
v_k_2678_ = lean_ctor_get(v_x_2674_, 1);
lean_inc(v_k_2678_);
v_v_2679_ = lean_ctor_get(v_x_2674_, 2);
lean_inc(v_v_2679_);
v_l_2680_ = lean_ctor_get(v_x_2674_, 3);
lean_inc(v_l_2680_);
v_r_2681_ = lean_ctor_get(v_x_2674_, 4);
lean_inc(v_r_2681_);
lean_dec_ref(v_x_2674_);
v___x_2682_ = lean_apply_7(v_h__2_2676_, v_size_2677_, v_k_2678_, v_v_2679_, v_l_2680_, v_r_2681_, lean_box(0), lean_box(0));
return v___x_2682_;
}
else
{
lean_object* v___x_2683_; 
lean_dec(v_h__2_2676_);
v___x_2683_ = lean_apply_2(v_h__1_2675_, lean_box(0), lean_box(0));
return v___x_2683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(lean_object* v_00_u03b1_2684_, lean_object* v_00_u03b2_2685_, lean_object* v_inst_2686_, lean_object* v_k_2687_, lean_object* v_motive_2688_, lean_object* v_x_2689_, lean_object* v_x_2690_, lean_object* v_x_2691_, lean_object* v_h__1_2692_, lean_object* v_h__2_2693_){
_start:
{
if (lean_obj_tag(v_x_2689_) == 0)
{
lean_object* v_size_2694_; lean_object* v_k_2695_; lean_object* v_v_2696_; lean_object* v_l_2697_; lean_object* v_r_2698_; lean_object* v___x_2699_; 
lean_dec(v_h__1_2692_);
v_size_2694_ = lean_ctor_get(v_x_2689_, 0);
lean_inc(v_size_2694_);
v_k_2695_ = lean_ctor_get(v_x_2689_, 1);
lean_inc(v_k_2695_);
v_v_2696_ = lean_ctor_get(v_x_2689_, 2);
lean_inc(v_v_2696_);
v_l_2697_ = lean_ctor_get(v_x_2689_, 3);
lean_inc(v_l_2697_);
v_r_2698_ = lean_ctor_get(v_x_2689_, 4);
lean_inc(v_r_2698_);
lean_dec_ref(v_x_2689_);
v___x_2699_ = lean_apply_7(v_h__2_2693_, v_size_2694_, v_k_2695_, v_v_2696_, v_l_2697_, v_r_2698_, lean_box(0), lean_box(0));
return v___x_2699_;
}
else
{
lean_object* v___x_2700_; 
lean_dec(v_h__2_2693_);
v___x_2700_ = lean_apply_2(v_h__1_2692_, lean_box(0), lean_box(0));
return v___x_2700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___boxed(lean_object* v_00_u03b1_2701_, lean_object* v_00_u03b2_2702_, lean_object* v_inst_2703_, lean_object* v_k_2704_, lean_object* v_motive_2705_, lean_object* v_x_2706_, lean_object* v_x_2707_, lean_object* v_x_2708_, lean_object* v_h__1_2709_, lean_object* v_h__2_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(v_00_u03b1_2701_, v_00_u03b2_2702_, v_inst_2703_, v_k_2704_, v_motive_2705_, v_x_2706_, v_x_2707_, v_x_2708_, v_h__1_2709_, v_h__2_2710_);
lean_dec(v_k_2704_);
lean_dec_ref(v_inst_2703_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___redArg(lean_object* v_x_2712_, lean_object* v_h__1_2713_, lean_object* v_h__2_2714_){
_start:
{
if (lean_obj_tag(v_x_2712_) == 0)
{
lean_object* v_size_2715_; lean_object* v_k_2716_; lean_object* v_v_2717_; lean_object* v_l_2718_; lean_object* v_r_2719_; lean_object* v___x_2720_; 
lean_dec(v_h__1_2713_);
v_size_2715_ = lean_ctor_get(v_x_2712_, 0);
lean_inc(v_size_2715_);
v_k_2716_ = lean_ctor_get(v_x_2712_, 1);
lean_inc(v_k_2716_);
v_v_2717_ = lean_ctor_get(v_x_2712_, 2);
lean_inc(v_v_2717_);
v_l_2718_ = lean_ctor_get(v_x_2712_, 3);
lean_inc(v_l_2718_);
v_r_2719_ = lean_ctor_get(v_x_2712_, 4);
lean_inc(v_r_2719_);
lean_dec_ref(v_x_2712_);
v___x_2720_ = lean_apply_7(v_h__2_2714_, v_size_2715_, v_k_2716_, v_v_2717_, v_l_2718_, v_r_2719_, lean_box(0), lean_box(0));
return v___x_2720_;
}
else
{
lean_object* v___x_2721_; 
lean_dec(v_h__2_2714_);
v___x_2721_ = lean_apply_2(v_h__1_2713_, lean_box(0), lean_box(0));
return v___x_2721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(lean_object* v_00_u03b1_2722_, lean_object* v_00_u03b2_2723_, lean_object* v_inst_2724_, lean_object* v_k_2725_, lean_object* v_motive_2726_, lean_object* v_x_2727_, lean_object* v_x_2728_, lean_object* v_x_2729_, lean_object* v_h__1_2730_, lean_object* v_h__2_2731_){
_start:
{
if (lean_obj_tag(v_x_2727_) == 0)
{
lean_object* v_size_2732_; lean_object* v_k_2733_; lean_object* v_v_2734_; lean_object* v_l_2735_; lean_object* v_r_2736_; lean_object* v___x_2737_; 
lean_dec(v_h__1_2730_);
v_size_2732_ = lean_ctor_get(v_x_2727_, 0);
lean_inc(v_size_2732_);
v_k_2733_ = lean_ctor_get(v_x_2727_, 1);
lean_inc(v_k_2733_);
v_v_2734_ = lean_ctor_get(v_x_2727_, 2);
lean_inc(v_v_2734_);
v_l_2735_ = lean_ctor_get(v_x_2727_, 3);
lean_inc(v_l_2735_);
v_r_2736_ = lean_ctor_get(v_x_2727_, 4);
lean_inc(v_r_2736_);
lean_dec_ref(v_x_2727_);
v___x_2737_ = lean_apply_7(v_h__2_2731_, v_size_2732_, v_k_2733_, v_v_2734_, v_l_2735_, v_r_2736_, lean_box(0), lean_box(0));
return v___x_2737_;
}
else
{
lean_object* v___x_2738_; 
lean_dec(v_h__2_2731_);
v___x_2738_ = lean_apply_2(v_h__1_2730_, lean_box(0), lean_box(0));
return v___x_2738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___boxed(lean_object* v_00_u03b1_2739_, lean_object* v_00_u03b2_2740_, lean_object* v_inst_2741_, lean_object* v_k_2742_, lean_object* v_motive_2743_, lean_object* v_x_2744_, lean_object* v_x_2745_, lean_object* v_x_2746_, lean_object* v_h__1_2747_, lean_object* v_h__2_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(v_00_u03b1_2739_, v_00_u03b2_2740_, v_inst_2741_, v_k_2742_, v_motive_2743_, v_x_2744_, v_x_2745_, v_x_2746_, v_h__1_2747_, v_h__2_2748_);
lean_dec(v_k_2742_);
lean_dec_ref(v_inst_2741_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___redArg(lean_object* v_x_2750_, lean_object* v_h__1_2751_, lean_object* v_h__2_2752_){
_start:
{
if (lean_obj_tag(v_x_2750_) == 0)
{
lean_object* v_size_2753_; lean_object* v_k_2754_; lean_object* v_v_2755_; lean_object* v_l_2756_; lean_object* v_r_2757_; lean_object* v___x_2758_; 
lean_dec(v_h__1_2751_);
v_size_2753_ = lean_ctor_get(v_x_2750_, 0);
lean_inc(v_size_2753_);
v_k_2754_ = lean_ctor_get(v_x_2750_, 1);
lean_inc(v_k_2754_);
v_v_2755_ = lean_ctor_get(v_x_2750_, 2);
lean_inc(v_v_2755_);
v_l_2756_ = lean_ctor_get(v_x_2750_, 3);
lean_inc(v_l_2756_);
v_r_2757_ = lean_ctor_get(v_x_2750_, 4);
lean_inc(v_r_2757_);
lean_dec_ref(v_x_2750_);
v___x_2758_ = lean_apply_7(v_h__2_2752_, v_size_2753_, v_k_2754_, v_v_2755_, v_l_2756_, v_r_2757_, lean_box(0), lean_box(0));
return v___x_2758_;
}
else
{
lean_object* v___x_2759_; 
lean_dec(v_h__2_2752_);
v___x_2759_ = lean_apply_2(v_h__1_2751_, lean_box(0), lean_box(0));
return v___x_2759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(lean_object* v_00_u03b1_2760_, lean_object* v_00_u03b2_2761_, lean_object* v_inst_2762_, lean_object* v_k_2763_, lean_object* v_motive_2764_, lean_object* v_x_2765_, lean_object* v_x_2766_, lean_object* v_x_2767_, lean_object* v_h__1_2768_, lean_object* v_h__2_2769_){
_start:
{
if (lean_obj_tag(v_x_2765_) == 0)
{
lean_object* v_size_2770_; lean_object* v_k_2771_; lean_object* v_v_2772_; lean_object* v_l_2773_; lean_object* v_r_2774_; lean_object* v___x_2775_; 
lean_dec(v_h__1_2768_);
v_size_2770_ = lean_ctor_get(v_x_2765_, 0);
lean_inc(v_size_2770_);
v_k_2771_ = lean_ctor_get(v_x_2765_, 1);
lean_inc(v_k_2771_);
v_v_2772_ = lean_ctor_get(v_x_2765_, 2);
lean_inc(v_v_2772_);
v_l_2773_ = lean_ctor_get(v_x_2765_, 3);
lean_inc(v_l_2773_);
v_r_2774_ = lean_ctor_get(v_x_2765_, 4);
lean_inc(v_r_2774_);
lean_dec_ref(v_x_2765_);
v___x_2775_ = lean_apply_7(v_h__2_2769_, v_size_2770_, v_k_2771_, v_v_2772_, v_l_2773_, v_r_2774_, lean_box(0), lean_box(0));
return v___x_2775_;
}
else
{
lean_object* v___x_2776_; 
lean_dec(v_h__2_2769_);
v___x_2776_ = lean_apply_2(v_h__1_2768_, lean_box(0), lean_box(0));
return v___x_2776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___boxed(lean_object* v_00_u03b1_2777_, lean_object* v_00_u03b2_2778_, lean_object* v_inst_2779_, lean_object* v_k_2780_, lean_object* v_motive_2781_, lean_object* v_x_2782_, lean_object* v_x_2783_, lean_object* v_x_2784_, lean_object* v_h__1_2785_, lean_object* v_h__2_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(v_00_u03b1_2777_, v_00_u03b2_2778_, v_inst_2779_, v_k_2780_, v_motive_2781_, v_x_2782_, v_x_2783_, v_x_2784_, v_h__1_2785_, v_h__2_2786_);
lean_dec(v_k_2780_);
lean_dec_ref(v_inst_2779_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(uint8_t v_x_2788_, lean_object* v_h__1_2789_, lean_object* v_h__2_2790_, lean_object* v_h__3_2791_){
_start:
{
switch(v_x_2788_)
{
case 0:
{
lean_object* v___x_2792_; 
lean_dec(v_h__2_2790_);
lean_dec(v_h__1_2789_);
v___x_2792_ = lean_apply_1(v_h__3_2791_, lean_box(0));
return v___x_2792_;
}
case 1:
{
lean_object* v___x_2793_; 
lean_dec(v_h__3_2791_);
lean_dec(v_h__1_2789_);
v___x_2793_ = lean_apply_1(v_h__2_2790_, lean_box(0));
return v___x_2793_;
}
default: 
{
lean_object* v___x_2794_; 
lean_dec(v_h__3_2791_);
lean_dec(v_h__2_2790_);
v___x_2794_ = lean_apply_1(v_h__1_2789_, lean_box(0));
return v___x_2794_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg___boxed(lean_object* v_x_2795_, lean_object* v_h__1_2796_, lean_object* v_h__2_2797_, lean_object* v_h__3_2798_){
_start:
{
uint8_t v_x_33__boxed_2799_; lean_object* v_res_2800_; 
v_x_33__boxed_2799_ = lean_unbox(v_x_2795_);
v_res_2800_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(v_x_33__boxed_2799_, v_h__1_2796_, v_h__2_2797_, v_h__3_2798_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(lean_object* v_motive_2801_, uint8_t v_x_2802_, lean_object* v_h__1_2803_, lean_object* v_h__2_2804_, lean_object* v_h__3_2805_){
_start:
{
switch(v_x_2802_)
{
case 0:
{
lean_object* v___x_2806_; 
lean_dec(v_h__2_2804_);
lean_dec(v_h__1_2803_);
v___x_2806_ = lean_apply_1(v_h__3_2805_, lean_box(0));
return v___x_2806_;
}
case 1:
{
lean_object* v___x_2807_; 
lean_dec(v_h__3_2805_);
lean_dec(v_h__1_2803_);
v___x_2807_ = lean_apply_1(v_h__2_2804_, lean_box(0));
return v___x_2807_;
}
default: 
{
lean_object* v___x_2808_; 
lean_dec(v_h__3_2805_);
lean_dec(v_h__2_2804_);
v___x_2808_ = lean_apply_1(v_h__1_2803_, lean_box(0));
return v___x_2808_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___boxed(lean_object* v_motive_2809_, lean_object* v_x_2810_, lean_object* v_h__1_2811_, lean_object* v_h__2_2812_, lean_object* v_h__3_2813_){
_start:
{
uint8_t v_x_42__boxed_2814_; lean_object* v_res_2815_; 
v_x_42__boxed_2814_ = lean_unbox(v_x_2810_);
v_res_2815_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(v_motive_2809_, v_x_42__boxed_2814_, v_h__1_2811_, v_h__2_2812_, v_h__3_2813_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___redArg(lean_object* v_x_2816_, lean_object* v_h__1_2817_, lean_object* v_h__2_2818_){
_start:
{
if (lean_obj_tag(v_x_2816_) == 0)
{
lean_object* v_size_2819_; lean_object* v_k_2820_; lean_object* v_v_2821_; lean_object* v_l_2822_; lean_object* v_r_2823_; lean_object* v___x_2824_; 
lean_dec(v_h__1_2817_);
v_size_2819_ = lean_ctor_get(v_x_2816_, 0);
lean_inc(v_size_2819_);
v_k_2820_ = lean_ctor_get(v_x_2816_, 1);
lean_inc(v_k_2820_);
v_v_2821_ = lean_ctor_get(v_x_2816_, 2);
lean_inc(v_v_2821_);
v_l_2822_ = lean_ctor_get(v_x_2816_, 3);
lean_inc(v_l_2822_);
v_r_2823_ = lean_ctor_get(v_x_2816_, 4);
lean_inc(v_r_2823_);
lean_dec_ref(v_x_2816_);
v___x_2824_ = lean_apply_7(v_h__2_2818_, v_size_2819_, v_k_2820_, v_v_2821_, v_l_2822_, v_r_2823_, lean_box(0), lean_box(0));
return v___x_2824_;
}
else
{
lean_object* v___x_2825_; 
lean_dec(v_h__2_2818_);
v___x_2825_ = lean_apply_2(v_h__1_2817_, lean_box(0), lean_box(0));
return v___x_2825_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(lean_object* v_00_u03b1_2826_, lean_object* v_00_u03b2_2827_, lean_object* v_inst_2828_, lean_object* v_k_2829_, lean_object* v_motive_2830_, lean_object* v_x_2831_, lean_object* v_x_2832_, lean_object* v_x_2833_, lean_object* v_h__1_2834_, lean_object* v_h__2_2835_){
_start:
{
if (lean_obj_tag(v_x_2831_) == 0)
{
lean_object* v_size_2836_; lean_object* v_k_2837_; lean_object* v_v_2838_; lean_object* v_l_2839_; lean_object* v_r_2840_; lean_object* v___x_2841_; 
lean_dec(v_h__1_2834_);
v_size_2836_ = lean_ctor_get(v_x_2831_, 0);
lean_inc(v_size_2836_);
v_k_2837_ = lean_ctor_get(v_x_2831_, 1);
lean_inc(v_k_2837_);
v_v_2838_ = lean_ctor_get(v_x_2831_, 2);
lean_inc(v_v_2838_);
v_l_2839_ = lean_ctor_get(v_x_2831_, 3);
lean_inc(v_l_2839_);
v_r_2840_ = lean_ctor_get(v_x_2831_, 4);
lean_inc(v_r_2840_);
lean_dec_ref(v_x_2831_);
v___x_2841_ = lean_apply_7(v_h__2_2835_, v_size_2836_, v_k_2837_, v_v_2838_, v_l_2839_, v_r_2840_, lean_box(0), lean_box(0));
return v___x_2841_;
}
else
{
lean_object* v___x_2842_; 
lean_dec(v_h__2_2835_);
v___x_2842_ = lean_apply_2(v_h__1_2834_, lean_box(0), lean_box(0));
return v___x_2842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___boxed(lean_object* v_00_u03b1_2843_, lean_object* v_00_u03b2_2844_, lean_object* v_inst_2845_, lean_object* v_k_2846_, lean_object* v_motive_2847_, lean_object* v_x_2848_, lean_object* v_x_2849_, lean_object* v_x_2850_, lean_object* v_h__1_2851_, lean_object* v_h__2_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(v_00_u03b1_2843_, v_00_u03b2_2844_, v_inst_2845_, v_k_2846_, v_motive_2847_, v_x_2848_, v_x_2849_, v_x_2850_, v_h__1_2851_, v_h__2_2852_);
lean_dec(v_k_2846_);
lean_dec_ref(v_inst_2845_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(lean_object* v_x_2854_, lean_object* v_x_2855_, lean_object* v_h__1_2856_, lean_object* v_h__2_2857_){
_start:
{
if (lean_obj_tag(v_x_2854_) == 0)
{
lean_object* v_size_2858_; lean_object* v_k_2859_; lean_object* v_v_2860_; lean_object* v_l_2861_; lean_object* v_r_2862_; lean_object* v___x_2863_; 
lean_dec(v_h__1_2856_);
v_size_2858_ = lean_ctor_get(v_x_2854_, 0);
lean_inc(v_size_2858_);
v_k_2859_ = lean_ctor_get(v_x_2854_, 1);
lean_inc(v_k_2859_);
v_v_2860_ = lean_ctor_get(v_x_2854_, 2);
lean_inc(v_v_2860_);
v_l_2861_ = lean_ctor_get(v_x_2854_, 3);
lean_inc(v_l_2861_);
v_r_2862_ = lean_ctor_get(v_x_2854_, 4);
lean_inc(v_r_2862_);
lean_dec_ref(v_x_2854_);
v___x_2863_ = lean_apply_6(v_h__2_2857_, v_size_2858_, v_k_2859_, v_v_2860_, v_l_2861_, v_r_2862_, v_x_2855_);
return v___x_2863_;
}
else
{
lean_object* v___x_2864_; 
lean_dec(v_h__2_2857_);
v___x_2864_ = lean_apply_1(v_h__1_2856_, v_x_2855_);
return v___x_2864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter(lean_object* v_00_u03b1_2865_, lean_object* v_00_u03b2_2866_, lean_object* v_motive_2867_, lean_object* v_x_2868_, lean_object* v_x_2869_, lean_object* v_h__1_2870_, lean_object* v_h__2_2871_){
_start:
{
if (lean_obj_tag(v_x_2868_) == 0)
{
lean_object* v_size_2872_; lean_object* v_k_2873_; lean_object* v_v_2874_; lean_object* v_l_2875_; lean_object* v_r_2876_; lean_object* v___x_2877_; 
lean_dec(v_h__1_2870_);
v_size_2872_ = lean_ctor_get(v_x_2868_, 0);
lean_inc(v_size_2872_);
v_k_2873_ = lean_ctor_get(v_x_2868_, 1);
lean_inc(v_k_2873_);
v_v_2874_ = lean_ctor_get(v_x_2868_, 2);
lean_inc(v_v_2874_);
v_l_2875_ = lean_ctor_get(v_x_2868_, 3);
lean_inc(v_l_2875_);
v_r_2876_ = lean_ctor_get(v_x_2868_, 4);
lean_inc(v_r_2876_);
lean_dec_ref(v_x_2868_);
v___x_2877_ = lean_apply_6(v_h__2_2871_, v_size_2872_, v_k_2873_, v_v_2874_, v_l_2875_, v_r_2876_, v_x_2869_);
return v___x_2877_;
}
else
{
lean_object* v___x_2878_; 
lean_dec(v_h__2_2871_);
v___x_2878_ = lean_apply_1(v_h__1_2870_, v_x_2869_);
return v___x_2878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(lean_object* v_x_2879_, lean_object* v_x_2880_, lean_object* v_h__1_2881_){
_start:
{
lean_object* v_size_2882_; lean_object* v_k_2883_; lean_object* v_v_2884_; lean_object* v_l_2885_; lean_object* v_r_2886_; lean_object* v___x_2887_; 
v_size_2882_ = lean_ctor_get(v_x_2879_, 0);
lean_inc(v_size_2882_);
v_k_2883_ = lean_ctor_get(v_x_2879_, 1);
lean_inc(v_k_2883_);
v_v_2884_ = lean_ctor_get(v_x_2879_, 2);
lean_inc(v_v_2884_);
v_l_2885_ = lean_ctor_get(v_x_2879_, 3);
lean_inc(v_l_2885_);
v_r_2886_ = lean_ctor_get(v_x_2879_, 4);
lean_inc(v_r_2886_);
lean_dec(v_x_2879_);
v___x_2887_ = lean_apply_8(v_h__1_2881_, v_size_2882_, v_k_2883_, v_v_2884_, v_l_2885_, v_r_2886_, lean_box(0), v_x_2880_, lean_box(0));
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter(lean_object* v_00_u03b1_2888_, lean_object* v_00_u03b2_2889_, lean_object* v_motive_2890_, lean_object* v_x_2891_, lean_object* v_x_2892_, lean_object* v_x_2893_, lean_object* v_x_2894_, lean_object* v_h__1_2895_){
_start:
{
lean_object* v_size_2896_; lean_object* v_k_2897_; lean_object* v_v_2898_; lean_object* v_l_2899_; lean_object* v_r_2900_; lean_object* v___x_2901_; 
v_size_2896_ = lean_ctor_get(v_x_2891_, 0);
lean_inc(v_size_2896_);
v_k_2897_ = lean_ctor_get(v_x_2891_, 1);
lean_inc(v_k_2897_);
v_v_2898_ = lean_ctor_get(v_x_2891_, 2);
lean_inc(v_v_2898_);
v_l_2899_ = lean_ctor_get(v_x_2891_, 3);
lean_inc(v_l_2899_);
v_r_2900_ = lean_ctor_get(v_x_2891_, 4);
lean_inc(v_r_2900_);
lean_dec(v_x_2891_);
v___x_2901_ = lean_apply_8(v_h__1_2895_, v_size_2896_, v_k_2897_, v_v_2898_, v_l_2899_, v_r_2900_, lean_box(0), v_x_2893_, lean_box(0));
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter___redArg(lean_object* v_x_2902_, lean_object* v_x_2903_, lean_object* v_x_2904_, lean_object* v_h__1_2905_, lean_object* v_h__2_2906_){
_start:
{
if (lean_obj_tag(v_x_2902_) == 0)
{
lean_object* v_size_2907_; lean_object* v_k_2908_; lean_object* v_v_2909_; lean_object* v_l_2910_; lean_object* v_r_2911_; lean_object* v___x_2912_; 
lean_dec(v_h__1_2905_);
v_size_2907_ = lean_ctor_get(v_x_2902_, 0);
lean_inc(v_size_2907_);
v_k_2908_ = lean_ctor_get(v_x_2902_, 1);
lean_inc(v_k_2908_);
v_v_2909_ = lean_ctor_get(v_x_2902_, 2);
lean_inc(v_v_2909_);
v_l_2910_ = lean_ctor_get(v_x_2902_, 3);
lean_inc(v_l_2910_);
v_r_2911_ = lean_ctor_get(v_x_2902_, 4);
lean_inc(v_r_2911_);
lean_dec_ref(v_x_2902_);
v___x_2912_ = lean_apply_7(v_h__2_2906_, v_size_2907_, v_k_2908_, v_v_2909_, v_l_2910_, v_r_2911_, v_x_2903_, v_x_2904_);
return v___x_2912_;
}
else
{
lean_object* v___x_2913_; 
lean_dec(v_h__2_2906_);
v___x_2913_ = lean_apply_2(v_h__1_2905_, v_x_2903_, v_x_2904_);
return v___x_2913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2914_, lean_object* v_00_u03b2_2915_, lean_object* v_motive_2916_, lean_object* v_x_2917_, lean_object* v_x_2918_, lean_object* v_x_2919_, lean_object* v_h__1_2920_, lean_object* v_h__2_2921_){
_start:
{
if (lean_obj_tag(v_x_2917_) == 0)
{
lean_object* v_size_2922_; lean_object* v_k_2923_; lean_object* v_v_2924_; lean_object* v_l_2925_; lean_object* v_r_2926_; lean_object* v___x_2927_; 
lean_dec(v_h__1_2920_);
v_size_2922_ = lean_ctor_get(v_x_2917_, 0);
lean_inc(v_size_2922_);
v_k_2923_ = lean_ctor_get(v_x_2917_, 1);
lean_inc(v_k_2923_);
v_v_2924_ = lean_ctor_get(v_x_2917_, 2);
lean_inc(v_v_2924_);
v_l_2925_ = lean_ctor_get(v_x_2917_, 3);
lean_inc(v_l_2925_);
v_r_2926_ = lean_ctor_get(v_x_2917_, 4);
lean_inc(v_r_2926_);
lean_dec_ref(v_x_2917_);
v___x_2927_ = lean_apply_7(v_h__2_2921_, v_size_2922_, v_k_2923_, v_v_2924_, v_l_2925_, v_r_2926_, v_x_2918_, v_x_2919_);
return v___x_2927_;
}
else
{
lean_object* v___x_2928_; 
lean_dec(v_h__2_2921_);
v___x_2928_ = lean_apply_2(v_h__1_2920_, v_x_2918_, v_x_2919_);
return v___x_2928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___redArg(lean_object* v_x_2929_, lean_object* v_h__1_2930_, lean_object* v_h__2_2931_){
_start:
{
if (lean_obj_tag(v_x_2929_) == 0)
{
lean_object* v_size_2932_; lean_object* v_k_2933_; lean_object* v_v_2934_; lean_object* v_l_2935_; lean_object* v_r_2936_; lean_object* v___x_2937_; 
lean_dec(v_h__1_2930_);
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
lean_dec_ref(v_x_2929_);
v___x_2937_ = lean_apply_7(v_h__2_2931_, v_size_2932_, v_k_2933_, v_v_2934_, v_l_2935_, v_r_2936_, lean_box(0), lean_box(0));
return v___x_2937_;
}
else
{
lean_object* v___x_2938_; 
lean_dec(v_h__2_2931_);
v___x_2938_ = lean_apply_2(v_h__1_2930_, lean_box(0), lean_box(0));
return v___x_2938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(lean_object* v_00_u03b1_2939_, lean_object* v_00_u03b2_2940_, lean_object* v_inst_2941_, lean_object* v_k_2942_, lean_object* v_motive_2943_, lean_object* v_x_2944_, lean_object* v_x_2945_, lean_object* v_x_2946_, lean_object* v_h__1_2947_, lean_object* v_h__2_2948_){
_start:
{
if (lean_obj_tag(v_x_2944_) == 0)
{
lean_object* v_size_2949_; lean_object* v_k_2950_; lean_object* v_v_2951_; lean_object* v_l_2952_; lean_object* v_r_2953_; lean_object* v___x_2954_; 
lean_dec(v_h__1_2947_);
v_size_2949_ = lean_ctor_get(v_x_2944_, 0);
lean_inc(v_size_2949_);
v_k_2950_ = lean_ctor_get(v_x_2944_, 1);
lean_inc(v_k_2950_);
v_v_2951_ = lean_ctor_get(v_x_2944_, 2);
lean_inc(v_v_2951_);
v_l_2952_ = lean_ctor_get(v_x_2944_, 3);
lean_inc(v_l_2952_);
v_r_2953_ = lean_ctor_get(v_x_2944_, 4);
lean_inc(v_r_2953_);
lean_dec_ref(v_x_2944_);
v___x_2954_ = lean_apply_7(v_h__2_2948_, v_size_2949_, v_k_2950_, v_v_2951_, v_l_2952_, v_r_2953_, lean_box(0), lean_box(0));
return v___x_2954_;
}
else
{
lean_object* v___x_2955_; 
lean_dec(v_h__2_2948_);
v___x_2955_ = lean_apply_2(v_h__1_2947_, lean_box(0), lean_box(0));
return v___x_2955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___boxed(lean_object* v_00_u03b1_2956_, lean_object* v_00_u03b2_2957_, lean_object* v_inst_2958_, lean_object* v_k_2959_, lean_object* v_motive_2960_, lean_object* v_x_2961_, lean_object* v_x_2962_, lean_object* v_x_2963_, lean_object* v_h__1_2964_, lean_object* v_h__2_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(v_00_u03b1_2956_, v_00_u03b2_2957_, v_inst_2958_, v_k_2959_, v_motive_2960_, v_x_2961_, v_x_2962_, v_x_2963_, v_h__1_2964_, v_h__2_2965_);
lean_dec(v_k_2959_);
lean_dec_ref(v_inst_2958_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___redArg(lean_object* v_x_2967_, lean_object* v_h__1_2968_, lean_object* v_h__2_2969_){
_start:
{
if (lean_obj_tag(v_x_2967_) == 0)
{
lean_object* v_size_2970_; lean_object* v_k_2971_; lean_object* v_v_2972_; lean_object* v_l_2973_; lean_object* v_r_2974_; lean_object* v___x_2975_; 
lean_dec(v_h__1_2968_);
v_size_2970_ = lean_ctor_get(v_x_2967_, 0);
lean_inc(v_size_2970_);
v_k_2971_ = lean_ctor_get(v_x_2967_, 1);
lean_inc(v_k_2971_);
v_v_2972_ = lean_ctor_get(v_x_2967_, 2);
lean_inc(v_v_2972_);
v_l_2973_ = lean_ctor_get(v_x_2967_, 3);
lean_inc(v_l_2973_);
v_r_2974_ = lean_ctor_get(v_x_2967_, 4);
lean_inc(v_r_2974_);
lean_dec_ref(v_x_2967_);
v___x_2975_ = lean_apply_7(v_h__2_2969_, v_size_2970_, v_k_2971_, v_v_2972_, v_l_2973_, v_r_2974_, lean_box(0), lean_box(0));
return v___x_2975_;
}
else
{
lean_object* v___x_2976_; 
lean_dec(v_h__2_2969_);
v___x_2976_ = lean_apply_2(v_h__1_2968_, lean_box(0), lean_box(0));
return v___x_2976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(lean_object* v_00_u03b1_2977_, lean_object* v_00_u03b2_2978_, lean_object* v_inst_2979_, lean_object* v_k_2980_, lean_object* v_motive_2981_, lean_object* v_x_2982_, lean_object* v_x_2983_, lean_object* v_x_2984_, lean_object* v_h__1_2985_, lean_object* v_h__2_2986_){
_start:
{
if (lean_obj_tag(v_x_2982_) == 0)
{
lean_object* v_size_2987_; lean_object* v_k_2988_; lean_object* v_v_2989_; lean_object* v_l_2990_; lean_object* v_r_2991_; lean_object* v___x_2992_; 
lean_dec(v_h__1_2985_);
v_size_2987_ = lean_ctor_get(v_x_2982_, 0);
lean_inc(v_size_2987_);
v_k_2988_ = lean_ctor_get(v_x_2982_, 1);
lean_inc(v_k_2988_);
v_v_2989_ = lean_ctor_get(v_x_2982_, 2);
lean_inc(v_v_2989_);
v_l_2990_ = lean_ctor_get(v_x_2982_, 3);
lean_inc(v_l_2990_);
v_r_2991_ = lean_ctor_get(v_x_2982_, 4);
lean_inc(v_r_2991_);
lean_dec_ref(v_x_2982_);
v___x_2992_ = lean_apply_7(v_h__2_2986_, v_size_2987_, v_k_2988_, v_v_2989_, v_l_2990_, v_r_2991_, lean_box(0), lean_box(0));
return v___x_2992_;
}
else
{
lean_object* v___x_2993_; 
lean_dec(v_h__2_2986_);
v___x_2993_ = lean_apply_2(v_h__1_2985_, lean_box(0), lean_box(0));
return v___x_2993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___boxed(lean_object* v_00_u03b1_2994_, lean_object* v_00_u03b2_2995_, lean_object* v_inst_2996_, lean_object* v_k_2997_, lean_object* v_motive_2998_, lean_object* v_x_2999_, lean_object* v_x_3000_, lean_object* v_x_3001_, lean_object* v_h__1_3002_, lean_object* v_h__2_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(v_00_u03b1_2994_, v_00_u03b2_2995_, v_inst_2996_, v_k_2997_, v_motive_2998_, v_x_2999_, v_x_3000_, v_x_3001_, v_h__1_3002_, v_h__2_3003_);
lean_dec(v_k_2997_);
lean_dec_ref(v_inst_2996_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___redArg(lean_object* v_x_3005_, lean_object* v_h__1_3006_, lean_object* v_h__2_3007_){
_start:
{
if (lean_obj_tag(v_x_3005_) == 0)
{
lean_object* v_size_3008_; lean_object* v_k_3009_; lean_object* v_v_3010_; lean_object* v_l_3011_; lean_object* v_r_3012_; lean_object* v___x_3013_; 
lean_dec(v_h__1_3006_);
v_size_3008_ = lean_ctor_get(v_x_3005_, 0);
lean_inc(v_size_3008_);
v_k_3009_ = lean_ctor_get(v_x_3005_, 1);
lean_inc(v_k_3009_);
v_v_3010_ = lean_ctor_get(v_x_3005_, 2);
lean_inc(v_v_3010_);
v_l_3011_ = lean_ctor_get(v_x_3005_, 3);
lean_inc(v_l_3011_);
v_r_3012_ = lean_ctor_get(v_x_3005_, 4);
lean_inc(v_r_3012_);
lean_dec_ref(v_x_3005_);
v___x_3013_ = lean_apply_7(v_h__2_3007_, v_size_3008_, v_k_3009_, v_v_3010_, v_l_3011_, v_r_3012_, lean_box(0), lean_box(0));
return v___x_3013_;
}
else
{
lean_object* v___x_3014_; 
lean_dec(v_h__2_3007_);
v___x_3014_ = lean_apply_2(v_h__1_3006_, lean_box(0), lean_box(0));
return v___x_3014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(lean_object* v_00_u03b1_3015_, lean_object* v_00_u03b2_3016_, lean_object* v_inst_3017_, lean_object* v_k_3018_, lean_object* v_motive_3019_, lean_object* v_x_3020_, lean_object* v_x_3021_, lean_object* v_x_3022_, lean_object* v_h__1_3023_, lean_object* v_h__2_3024_){
_start:
{
if (lean_obj_tag(v_x_3020_) == 0)
{
lean_object* v_size_3025_; lean_object* v_k_3026_; lean_object* v_v_3027_; lean_object* v_l_3028_; lean_object* v_r_3029_; lean_object* v___x_3030_; 
lean_dec(v_h__1_3023_);
v_size_3025_ = lean_ctor_get(v_x_3020_, 0);
lean_inc(v_size_3025_);
v_k_3026_ = lean_ctor_get(v_x_3020_, 1);
lean_inc(v_k_3026_);
v_v_3027_ = lean_ctor_get(v_x_3020_, 2);
lean_inc(v_v_3027_);
v_l_3028_ = lean_ctor_get(v_x_3020_, 3);
lean_inc(v_l_3028_);
v_r_3029_ = lean_ctor_get(v_x_3020_, 4);
lean_inc(v_r_3029_);
lean_dec_ref(v_x_3020_);
v___x_3030_ = lean_apply_7(v_h__2_3024_, v_size_3025_, v_k_3026_, v_v_3027_, v_l_3028_, v_r_3029_, lean_box(0), lean_box(0));
return v___x_3030_;
}
else
{
lean_object* v___x_3031_; 
lean_dec(v_h__2_3024_);
v___x_3031_ = lean_apply_2(v_h__1_3023_, lean_box(0), lean_box(0));
return v___x_3031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___boxed(lean_object* v_00_u03b1_3032_, lean_object* v_00_u03b2_3033_, lean_object* v_inst_3034_, lean_object* v_k_3035_, lean_object* v_motive_3036_, lean_object* v_x_3037_, lean_object* v_x_3038_, lean_object* v_x_3039_, lean_object* v_h__1_3040_, lean_object* v_h__2_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(v_00_u03b1_3032_, v_00_u03b2_3033_, v_inst_3034_, v_k_3035_, v_motive_3036_, v_x_3037_, v_x_3038_, v_x_3039_, v_h__1_3040_, v_h__2_3041_);
lean_dec(v_k_3035_);
lean_dec_ref(v_inst_3034_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___redArg(lean_object* v_x_3043_, lean_object* v_h__1_3044_, lean_object* v_h__2_3045_){
_start:
{
if (lean_obj_tag(v_x_3043_) == 0)
{
lean_object* v_size_3046_; lean_object* v_k_3047_; lean_object* v_v_3048_; lean_object* v_l_3049_; lean_object* v_r_3050_; lean_object* v___x_3051_; 
lean_dec(v_h__1_3044_);
v_size_3046_ = lean_ctor_get(v_x_3043_, 0);
lean_inc(v_size_3046_);
v_k_3047_ = lean_ctor_get(v_x_3043_, 1);
lean_inc(v_k_3047_);
v_v_3048_ = lean_ctor_get(v_x_3043_, 2);
lean_inc(v_v_3048_);
v_l_3049_ = lean_ctor_get(v_x_3043_, 3);
lean_inc(v_l_3049_);
v_r_3050_ = lean_ctor_get(v_x_3043_, 4);
lean_inc(v_r_3050_);
lean_dec_ref(v_x_3043_);
v___x_3051_ = lean_apply_7(v_h__2_3045_, v_size_3046_, v_k_3047_, v_v_3048_, v_l_3049_, v_r_3050_, lean_box(0), lean_box(0));
return v___x_3051_;
}
else
{
lean_object* v___x_3052_; 
lean_dec(v_h__2_3045_);
v___x_3052_ = lean_apply_2(v_h__1_3044_, lean_box(0), lean_box(0));
return v___x_3052_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(lean_object* v_00_u03b1_3053_, lean_object* v_00_u03b2_3054_, lean_object* v_inst_3055_, lean_object* v_k_3056_, lean_object* v_motive_3057_, lean_object* v_x_3058_, lean_object* v_x_3059_, lean_object* v_x_3060_, lean_object* v_h__1_3061_, lean_object* v_h__2_3062_){
_start:
{
if (lean_obj_tag(v_x_3058_) == 0)
{
lean_object* v_size_3063_; lean_object* v_k_3064_; lean_object* v_v_3065_; lean_object* v_l_3066_; lean_object* v_r_3067_; lean_object* v___x_3068_; 
lean_dec(v_h__1_3061_);
v_size_3063_ = lean_ctor_get(v_x_3058_, 0);
lean_inc(v_size_3063_);
v_k_3064_ = lean_ctor_get(v_x_3058_, 1);
lean_inc(v_k_3064_);
v_v_3065_ = lean_ctor_get(v_x_3058_, 2);
lean_inc(v_v_3065_);
v_l_3066_ = lean_ctor_get(v_x_3058_, 3);
lean_inc(v_l_3066_);
v_r_3067_ = lean_ctor_get(v_x_3058_, 4);
lean_inc(v_r_3067_);
lean_dec_ref(v_x_3058_);
v___x_3068_ = lean_apply_7(v_h__2_3062_, v_size_3063_, v_k_3064_, v_v_3065_, v_l_3066_, v_r_3067_, lean_box(0), lean_box(0));
return v___x_3068_;
}
else
{
lean_object* v___x_3069_; 
lean_dec(v_h__2_3062_);
v___x_3069_ = lean_apply_2(v_h__1_3061_, lean_box(0), lean_box(0));
return v___x_3069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___boxed(lean_object* v_00_u03b1_3070_, lean_object* v_00_u03b2_3071_, lean_object* v_inst_3072_, lean_object* v_k_3073_, lean_object* v_motive_3074_, lean_object* v_x_3075_, lean_object* v_x_3076_, lean_object* v_x_3077_, lean_object* v_h__1_3078_, lean_object* v_h__2_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(v_00_u03b1_3070_, v_00_u03b2_3071_, v_inst_3072_, v_k_3073_, v_motive_3074_, v_x_3075_, v_x_3076_, v_x_3077_, v_h__1_3078_, v_h__2_3079_);
lean_dec(v_k_3073_);
lean_dec_ref(v_inst_3072_);
return v_res_3080_;
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
