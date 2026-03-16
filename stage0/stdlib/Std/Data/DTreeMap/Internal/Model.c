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
lean_object* v___x_46_; 
v___x_46_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___redArg(v_l_43_, v_h__1_44_, v_h__2_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(uint8_t v_x_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_, lean_object* v_h__3_50_){
_start:
{
switch(v_x_47_)
{
case 0:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec(v_h__3_50_);
lean_dec(v_h__2_49_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_apply_1(v_h__1_48_, v___x_51_);
return v___x_52_;
}
case 1:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec(v_h__2_49_);
lean_dec(v_h__1_48_);
v___x_53_ = lean_box(0);
v___x_54_ = lean_apply_1(v_h__3_50_, v___x_53_);
return v___x_54_;
}
default: 
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_h__3_50_);
lean_dec(v_h__1_48_);
v___x_55_ = lean_box(0);
v___x_56_ = lean_apply_1(v_h__2_49_, v___x_55_);
return v___x_56_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(lean_object* v_x_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_, lean_object* v_h__3_60_){
_start:
{
uint8_t v_x_30__boxed_61_; lean_object* v_res_62_; 
v_x_30__boxed_61_ = lean_unbox(v_x_57_);
v_res_62_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_30__boxed_61_, v_h__1_58_, v_h__2_59_, v_h__3_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object* v_motive_63_, uint8_t v_x_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_, lean_object* v_h__3_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_64_, v_h__1_65_, v_h__2_66_, v_h__3_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(lean_object* v_motive_69_, lean_object* v_x_70_, lean_object* v_h__1_71_, lean_object* v_h__2_72_, lean_object* v_h__3_73_){
_start:
{
uint8_t v_x_45__boxed_74_; lean_object* v_res_75_; 
v_x_45__boxed_74_ = lean_unbox(v_x_70_);
v_res_75_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_69_, v_x_45__boxed_74_, v_h__1_71_, v_h__2_72_, v_h__3_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(uint8_t v_x_76_, lean_object* v_h__1_77_, lean_object* v_h__2_78_, lean_object* v_h__3_79_){
_start:
{
switch(v_x_76_)
{
case 0:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_h__3_79_);
lean_dec(v_h__2_78_);
v___x_80_ = lean_box(0);
v___x_81_ = lean_apply_1(v_h__1_77_, v___x_80_);
return v___x_81_;
}
case 1:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_h__2_78_);
lean_dec(v_h__1_77_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_apply_1(v_h__3_79_, v___x_82_);
return v___x_83_;
}
default: 
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_h__3_79_);
lean_dec(v_h__1_77_);
v___x_84_ = lean_box(0);
v___x_85_ = lean_apply_1(v_h__2_78_, v___x_84_);
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(lean_object* v_x_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_, lean_object* v_h__3_89_){
_start:
{
uint8_t v_x_30__boxed_90_; lean_object* v_res_91_; 
v_x_30__boxed_90_ = lean_unbox(v_x_86_);
v_res_91_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_30__boxed_90_, v_h__1_87_, v_h__2_88_, v_h__3_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object* v_motive_92_, uint8_t v_x_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_, lean_object* v_h__3_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_93_, v_h__1_94_, v_h__2_95_, v_h__3_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(lean_object* v_motive_98_, lean_object* v_x_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_, lean_object* v_h__3_102_){
_start:
{
uint8_t v_x_45__boxed_103_; lean_object* v_res_104_; 
v_x_45__boxed_103_ = lean_unbox(v_x_99_);
v_res_104_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_98_, v_x_45__boxed_103_, v_h__1_100_, v_h__2_101_, v_h__3_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(lean_object* v_k_105_, lean_object* v_f_106_, lean_object* v_ll_107_, lean_object* v_m_108_, lean_object* v_rr_109_){
_start:
{
if (lean_obj_tag(v_m_108_) == 0)
{
lean_object* v_k_110_; lean_object* v_v_111_; lean_object* v_l_112_; lean_object* v_r_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_k_110_ = lean_ctor_get(v_m_108_, 1);
lean_inc(v_k_110_);
v_v_111_ = lean_ctor_get(v_m_108_, 2);
lean_inc(v_v_111_);
v_l_112_ = lean_ctor_get(v_m_108_, 3);
lean_inc(v_l_112_);
v_r_113_ = lean_ctor_get(v_m_108_, 4);
lean_inc(v_r_113_);
lean_dec_ref(v_m_108_);
lean_inc_ref(v_k_105_);
lean_inc(v_k_110_);
v___x_114_ = lean_apply_1(v_k_105_, v_k_110_);
v___x_115_ = lean_unbox(v___x_114_);
switch(v___x_115_)
{
case 0:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v_k_110_);
lean_ctor_set(v___x_116_, 1, v_v_111_);
v___x_117_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_113_);
lean_dec(v_r_113_);
v___x_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = l_List_appendTR___redArg(v___x_118_, v_rr_109_);
v_m_108_ = v_l_112_;
v_rr_109_ = v___x_119_;
goto _start;
}
case 1:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
lean_dec_ref(v_k_105_);
v___x_121_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_112_);
lean_dec(v_l_112_);
v___x_122_ = l_List_appendTR___redArg(v_ll_107_, v___x_121_);
v___x_123_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_110_, v_v_111_);
v___x_124_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_113_);
lean_dec(v_r_113_);
v___x_125_ = l_List_appendTR___redArg(v___x_124_, v_rr_109_);
v___x_126_ = lean_apply_4(v_f_106_, v___x_122_, v___x_123_, lean_box(0), v___x_125_);
return v___x_126_;
}
default: 
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_127_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_112_);
lean_dec(v_l_112_);
v___x_128_ = l_List_appendTR___redArg(v_ll_107_, v___x_127_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_k_110_);
lean_ctor_set(v___x_129_, 1, v_v_111_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = l_List_appendTR___redArg(v___x_128_, v___x_131_);
v_ll_107_ = v___x_132_;
v_m_108_ = v_r_113_;
goto _start;
}
}
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec_ref(v_k_105_);
v___x_134_ = lean_box(0);
v___x_135_ = lean_apply_4(v_f_106_, v_ll_107_, v___x_134_, lean_box(0), v_rr_109_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go(lean_object* v_00_u03b1_136_, lean_object* v_00_u03b2_137_, lean_object* v_00_u03b4_138_, lean_object* v_inst_139_, lean_object* v_k_140_, lean_object* v_l_141_, lean_object* v_f_142_, lean_object* v_ll_143_, lean_object* v_m_144_, lean_object* v_hm_145_, lean_object* v_rr_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(v_k_140_, v_f_142_, v_ll_143_, v_m_144_, v_rr_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___boxed(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v_00_u03b4_150_, lean_object* v_inst_151_, lean_object* v_k_152_, lean_object* v_l_153_, lean_object* v_f_154_, lean_object* v_ll_155_, lean_object* v_m_156_, lean_object* v_hm_157_, lean_object* v_rr_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go(v_00_u03b1_148_, v_00_u03b2_149_, v_00_u03b4_150_, v_inst_151_, v_k_152_, v_l_153_, v_f_154_, v_ll_155_, v_m_156_, v_hm_157_, v_rr_158_);
lean_dec(v_l_153_);
lean_dec_ref(v_inst_151_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(lean_object* v_k_160_, lean_object* v_l_161_, lean_object* v_f_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_box(0);
v___x_164_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(v_k_160_, v_f_162_, v___x_163_, v_l_161_, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition(lean_object* v_00_u03b1_165_, lean_object* v_00_u03b2_166_, lean_object* v_00_u03b4_167_, lean_object* v_inst_168_, lean_object* v_k_169_, lean_object* v_l_170_, lean_object* v_f_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v_k_169_, v_l_170_, v_f_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___boxed(lean_object* v_00_u03b1_173_, lean_object* v_00_u03b2_174_, lean_object* v_00_u03b4_175_, lean_object* v_inst_176_, lean_object* v_k_177_, lean_object* v_l_178_, lean_object* v_f_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_DTreeMap_Internal_Impl_applyPartition(v_00_u03b1_173_, v_00_u03b2_174_, v_00_u03b4_175_, v_inst_176_, v_k_177_, v_l_178_, v_f_179_);
lean_dec_ref(v_inst_176_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0(lean_object* v_f_181_, lean_object* v_c_182_, lean_object* v_h_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_apply_2(v_f_181_, v_c_182_, lean_box(0));
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___redArg(lean_object* v_inst_185_, lean_object* v_k_186_, lean_object* v_l_187_, lean_object* v_f_188_){
_start:
{
if (lean_obj_tag(v_l_187_) == 0)
{
lean_object* v_k_189_; lean_object* v_v_190_; lean_object* v_l_191_; lean_object* v_r_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_k_189_ = lean_ctor_get(v_l_187_, 1);
lean_inc(v_k_189_);
v_v_190_ = lean_ctor_get(v_l_187_, 2);
lean_inc(v_v_190_);
v_l_191_ = lean_ctor_get(v_l_187_, 3);
lean_inc(v_l_191_);
v_r_192_ = lean_ctor_get(v_l_187_, 4);
lean_inc(v_r_192_);
lean_dec_ref(v_l_187_);
lean_inc_ref(v_inst_185_);
lean_inc(v_k_189_);
lean_inc(v_k_186_);
v___x_193_ = lean_apply_2(v_inst_185_, v_k_186_, v_k_189_);
v___x_194_ = lean_unbox(v___x_193_);
switch(v___x_194_)
{
case 0:
{
lean_object* v___f_195_; 
lean_dec(v_r_192_);
lean_dec(v_v_190_);
lean_dec(v_k_189_);
v___f_195_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0), 3, 1);
lean_closure_set(v___f_195_, 0, v_f_188_);
v_l_187_ = v_l_191_;
v_f_188_ = v___f_195_;
goto _start;
}
case 1:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_r_192_);
lean_dec(v_l_191_);
lean_dec(v_k_186_);
lean_dec_ref(v_inst_185_);
v___x_197_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_189_, v_v_190_);
v___x_198_ = lean_apply_2(v_f_188_, v___x_197_, lean_box(0));
return v___x_198_;
}
default: 
{
lean_object* v___f_199_; 
lean_dec(v_l_191_);
lean_dec(v_v_190_);
lean_dec(v_k_189_);
v___f_199_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0), 3, 1);
lean_closure_set(v___f_199_, 0, v_f_188_);
v_l_187_ = v_r_192_;
v_f_188_ = v___f_199_;
goto _start;
}
}
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v_k_186_);
lean_dec_ref(v_inst_185_);
v___x_201_ = lean_box(0);
v___x_202_ = lean_apply_2(v_f_188_, v___x_201_, lean_box(0));
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell(lean_object* v_00_u03b1_203_, lean_object* v_00_u03b2_204_, lean_object* v_00_u03b4_205_, lean_object* v_inst_206_, lean_object* v_k_207_, lean_object* v_l_208_, lean_object* v_f_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_206_, v_k_207_, v_l_208_, v_f_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___redArg(lean_object* v_l_211_, lean_object* v_f_212_, lean_object* v_h__1_213_, lean_object* v_h__2_214_){
_start:
{
if (lean_obj_tag(v_l_211_) == 0)
{
lean_object* v_size_215_; lean_object* v_k_216_; lean_object* v_v_217_; lean_object* v_l_218_; lean_object* v_r_219_; lean_object* v___x_220_; 
lean_dec(v_h__1_213_);
v_size_215_ = lean_ctor_get(v_l_211_, 0);
lean_inc(v_size_215_);
v_k_216_ = lean_ctor_get(v_l_211_, 1);
lean_inc(v_k_216_);
v_v_217_ = lean_ctor_get(v_l_211_, 2);
lean_inc(v_v_217_);
v_l_218_ = lean_ctor_get(v_l_211_, 3);
lean_inc(v_l_218_);
v_r_219_ = lean_ctor_get(v_l_211_, 4);
lean_inc(v_r_219_);
lean_dec_ref(v_l_211_);
v___x_220_ = lean_apply_6(v_h__2_214_, v_size_215_, v_k_216_, v_v_217_, v_l_218_, v_r_219_, v_f_212_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; 
lean_dec(v_h__2_214_);
v___x_221_ = lean_apply_1(v_h__1_213_, v_f_212_);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(lean_object* v_00_u03b1_222_, lean_object* v_00_u03b2_223_, lean_object* v_00_u03b4_224_, lean_object* v_inst_225_, lean_object* v_k_226_, lean_object* v_motive_227_, lean_object* v_l_228_, lean_object* v_f_229_, lean_object* v_h__1_230_, lean_object* v_h__2_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___redArg(v_l_228_, v_f_229_, v_h__1_230_, v_h__2_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___boxed(lean_object* v_00_u03b1_233_, lean_object* v_00_u03b2_234_, lean_object* v_00_u03b4_235_, lean_object* v_inst_236_, lean_object* v_k_237_, lean_object* v_motive_238_, lean_object* v_l_239_, lean_object* v_f_240_, lean_object* v_h__1_241_, lean_object* v_h__2_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(v_00_u03b1_233_, v_00_u03b2_234_, v_00_u03b4_235_, v_inst_236_, v_k_237_, v_motive_238_, v_l_239_, v_f_240_, v_h__1_241_, v_h__2_242_);
lean_dec(v_k_237_);
lean_dec_ref(v_inst_236_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(uint8_t v_x_244_, lean_object* v_h__1_245_, lean_object* v_h__2_246_, lean_object* v_h__3_247_){
_start:
{
switch(v_x_244_)
{
case 0:
{
lean_object* v___x_248_; 
lean_dec(v_h__3_247_);
lean_dec(v_h__2_246_);
v___x_248_ = lean_apply_1(v_h__1_245_, lean_box(0));
return v___x_248_;
}
case 1:
{
lean_object* v___x_249_; 
lean_dec(v_h__3_247_);
lean_dec(v_h__1_245_);
v___x_249_ = lean_apply_1(v_h__2_246_, lean_box(0));
return v___x_249_;
}
default: 
{
lean_object* v___x_250_; 
lean_dec(v_h__2_246_);
lean_dec(v_h__1_245_);
v___x_250_ = lean_apply_1(v_h__3_247_, lean_box(0));
return v___x_250_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(lean_object* v_x_251_, lean_object* v_h__1_252_, lean_object* v_h__2_253_, lean_object* v_h__3_254_){
_start:
{
uint8_t v_x_30__boxed_255_; lean_object* v_res_256_; 
v_x_30__boxed_255_ = lean_unbox(v_x_251_);
v_res_256_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_30__boxed_255_, v_h__1_252_, v_h__2_253_, v_h__3_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object* v_motive_257_, uint8_t v_x_258_, lean_object* v_h__1_259_, lean_object* v_h__2_260_, lean_object* v_h__3_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_258_, v_h__1_259_, v_h__2_260_, v_h__3_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(lean_object* v_motive_263_, lean_object* v_x_264_, lean_object* v_h__1_265_, lean_object* v_h__2_266_, lean_object* v_h__3_267_){
_start:
{
uint8_t v_x_39__boxed_268_; lean_object* v_res_269_; 
v_x_39__boxed_268_ = lean_unbox(v_x_264_);
v_res_269_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(v_motive_263_, v_x_39__boxed_268_, v_h__1_265_, v_h__2_266_, v_h__3_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___redArg(lean_object* v_m_270_, lean_object* v_h__1_271_, lean_object* v_h__2_272_){
_start:
{
if (lean_obj_tag(v_m_270_) == 0)
{
lean_object* v_size_273_; lean_object* v_k_274_; lean_object* v_v_275_; lean_object* v_l_276_; lean_object* v_r_277_; lean_object* v___x_278_; 
lean_dec(v_h__1_271_);
v_size_273_ = lean_ctor_get(v_m_270_, 0);
lean_inc(v_size_273_);
v_k_274_ = lean_ctor_get(v_m_270_, 1);
lean_inc(v_k_274_);
v_v_275_ = lean_ctor_get(v_m_270_, 2);
lean_inc(v_v_275_);
v_l_276_ = lean_ctor_get(v_m_270_, 3);
lean_inc(v_l_276_);
v_r_277_ = lean_ctor_get(v_m_270_, 4);
lean_inc(v_r_277_);
lean_dec_ref(v_m_270_);
v___x_278_ = lean_apply_6(v_h__2_272_, v_size_273_, v_k_274_, v_v_275_, v_l_276_, v_r_277_, lean_box(0));
return v___x_278_;
}
else
{
lean_object* v___x_279_; 
lean_dec(v_h__2_272_);
v___x_279_ = lean_apply_1(v_h__1_271_, lean_box(0));
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_inst_282_, lean_object* v_k_283_, lean_object* v_l_284_, lean_object* v_motive_285_, lean_object* v_m_286_, lean_object* v_hm_287_, lean_object* v_h__1_288_, lean_object* v_h__2_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___redArg(v_m_286_, v_h__1_288_, v_h__2_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___boxed(lean_object* v_00_u03b1_291_, lean_object* v_00_u03b2_292_, lean_object* v_inst_293_, lean_object* v_k_294_, lean_object* v_l_295_, lean_object* v_motive_296_, lean_object* v_m_297_, lean_object* v_hm_298_, lean_object* v_h__1_299_, lean_object* v_h__2_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(v_00_u03b1_291_, v_00_u03b2_292_, v_inst_293_, v_k_294_, v_l_295_, v_motive_296_, v_m_297_, v_hm_298_, v_h__1_299_, v_h__2_300_);
lean_dec(v_l_295_);
lean_dec_ref(v_k_294_);
lean_dec_ref(v_inst_293_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg(lean_object* v_x_302_){
_start:
{
switch(lean_obj_tag(v_x_302_))
{
case 0:
{
lean_object* v___x_303_; 
v___x_303_ = lean_unsigned_to_nat(0u);
return v___x_303_;
}
case 1:
{
lean_object* v___x_304_; 
v___x_304_ = lean_unsigned_to_nat(1u);
return v___x_304_;
}
default: 
{
lean_object* v___x_305_; 
v___x_305_ = lean_unsigned_to_nat(2u);
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg___boxed(lean_object* v_x_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg(v_x_306_);
lean_dec_ref(v_x_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx(lean_object* v_00_u03b1_308_, lean_object* v_00_u03b2_309_, lean_object* v_inst_310_, lean_object* v_k_311_, lean_object* v_x_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg(v_x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___boxed(lean_object* v_00_u03b1_314_, lean_object* v_00_u03b2_315_, lean_object* v_inst_316_, lean_object* v_k_317_, lean_object* v_x_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx(v_00_u03b1_314_, v_00_u03b2_315_, v_inst_316_, v_k_317_, v_x_318_);
lean_dec_ref(v_x_318_);
lean_dec_ref(v_k_317_);
lean_dec_ref(v_inst_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(lean_object* v_t_320_, lean_object* v_k_321_){
_start:
{
switch(lean_obj_tag(v_t_320_))
{
case 0:
{
lean_object* v_a_322_; lean_object* v_a_323_; lean_object* v_a_324_; lean_object* v___x_325_; 
v_a_322_ = lean_ctor_get(v_t_320_, 0);
lean_inc(v_a_322_);
v_a_323_ = lean_ctor_get(v_t_320_, 1);
lean_inc(v_a_323_);
v_a_324_ = lean_ctor_get(v_t_320_, 2);
lean_inc(v_a_324_);
lean_dec_ref(v_t_320_);
v___x_325_ = lean_apply_4(v_k_321_, v_a_322_, lean_box(0), v_a_323_, v_a_324_);
return v___x_325_;
}
case 1:
{
lean_object* v_a_326_; lean_object* v_a_327_; lean_object* v_a_328_; lean_object* v___x_329_; 
v_a_326_ = lean_ctor_get(v_t_320_, 0);
lean_inc(v_a_326_);
v_a_327_ = lean_ctor_get(v_t_320_, 1);
lean_inc(v_a_327_);
v_a_328_ = lean_ctor_get(v_t_320_, 2);
lean_inc(v_a_328_);
lean_dec_ref(v_t_320_);
v___x_329_ = lean_apply_3(v_k_321_, v_a_326_, v_a_327_, v_a_328_);
return v___x_329_;
}
default: 
{
lean_object* v_a_330_; lean_object* v_a_331_; lean_object* v_a_332_; lean_object* v___x_333_; 
v_a_330_ = lean_ctor_get(v_t_320_, 0);
lean_inc(v_a_330_);
v_a_331_ = lean_ctor_get(v_t_320_, 1);
lean_inc(v_a_331_);
v_a_332_ = lean_ctor_get(v_t_320_, 2);
lean_inc(v_a_332_);
lean_dec_ref(v_t_320_);
v___x_333_ = lean_apply_4(v_k_321_, v_a_330_, v_a_331_, lean_box(0), v_a_332_);
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim(lean_object* v_00_u03b1_334_, lean_object* v_00_u03b2_335_, lean_object* v_inst_336_, lean_object* v_k_337_, lean_object* v_motive_338_, lean_object* v_ctorIdx_339_, lean_object* v_t_340_, lean_object* v_h_341_, lean_object* v_k_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_340_, v_k_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___boxed(lean_object* v_00_u03b1_344_, lean_object* v_00_u03b2_345_, lean_object* v_inst_346_, lean_object* v_k_347_, lean_object* v_motive_348_, lean_object* v_ctorIdx_349_, lean_object* v_t_350_, lean_object* v_h_351_, lean_object* v_k_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim(v_00_u03b1_344_, v_00_u03b2_345_, v_inst_346_, v_k_347_, v_motive_348_, v_ctorIdx_349_, v_t_350_, v_h_351_, v_k_352_);
lean_dec(v_ctorIdx_349_);
lean_dec_ref(v_k_347_);
lean_dec_ref(v_inst_346_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___redArg(lean_object* v_t_354_, lean_object* v_lt_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_354_, v_lt_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim(lean_object* v_00_u03b1_357_, lean_object* v_00_u03b2_358_, lean_object* v_inst_359_, lean_object* v_k_360_, lean_object* v_motive_361_, lean_object* v_t_362_, lean_object* v_h_363_, lean_object* v_lt_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_362_, v_lt_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___boxed(lean_object* v_00_u03b1_366_, lean_object* v_00_u03b2_367_, lean_object* v_inst_368_, lean_object* v_k_369_, lean_object* v_motive_370_, lean_object* v_t_371_, lean_object* v_h_372_, lean_object* v_lt_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim(v_00_u03b1_366_, v_00_u03b2_367_, v_inst_368_, v_k_369_, v_motive_370_, v_t_371_, v_h_372_, v_lt_373_);
lean_dec_ref(v_k_369_);
lean_dec_ref(v_inst_368_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___redArg(lean_object* v_t_375_, lean_object* v_eq_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_375_, v_eq_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim(lean_object* v_00_u03b1_378_, lean_object* v_00_u03b2_379_, lean_object* v_inst_380_, lean_object* v_k_381_, lean_object* v_motive_382_, lean_object* v_t_383_, lean_object* v_h_384_, lean_object* v_eq_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_383_, v_eq_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___boxed(lean_object* v_00_u03b1_387_, lean_object* v_00_u03b2_388_, lean_object* v_inst_389_, lean_object* v_k_390_, lean_object* v_motive_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_eq_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim(v_00_u03b1_387_, v_00_u03b2_388_, v_inst_389_, v_k_390_, v_motive_391_, v_t_392_, v_h_393_, v_eq_394_);
lean_dec_ref(v_k_390_);
lean_dec_ref(v_inst_389_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___redArg(lean_object* v_t_396_, lean_object* v_gt_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_396_, v_gt_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim(lean_object* v_00_u03b1_399_, lean_object* v_00_u03b2_400_, lean_object* v_inst_401_, lean_object* v_k_402_, lean_object* v_motive_403_, lean_object* v_t_404_, lean_object* v_h_405_, lean_object* v_gt_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_404_, v_gt_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___boxed(lean_object* v_00_u03b1_408_, lean_object* v_00_u03b2_409_, lean_object* v_inst_410_, lean_object* v_k_411_, lean_object* v_motive_412_, lean_object* v_t_413_, lean_object* v_h_414_, lean_object* v_gt_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim(v_00_u03b1_408_, v_00_u03b2_409_, v_inst_410_, v_k_411_, v_motive_412_, v_t_413_, v_h_414_, v_gt_415_);
lean_dec_ref(v_k_411_);
lean_dec_ref(v_inst_410_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___redArg(lean_object* v_k_420_, lean_object* v_init_421_, lean_object* v_inner_422_, lean_object* v_l_423_){
_start:
{
if (lean_obj_tag(v_l_423_) == 0)
{
lean_object* v_k_424_; lean_object* v_v_425_; lean_object* v_l_426_; lean_object* v_r_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_k_424_ = lean_ctor_get(v_l_423_, 1);
lean_inc(v_k_424_);
v_v_425_ = lean_ctor_get(v_l_423_, 2);
lean_inc(v_v_425_);
v_l_426_ = lean_ctor_get(v_l_423_, 3);
lean_inc(v_l_426_);
v_r_427_ = lean_ctor_get(v_l_423_, 4);
lean_inc(v_r_427_);
lean_dec_ref(v_l_423_);
lean_inc_ref(v_k_420_);
lean_inc(v_k_424_);
v___x_428_ = lean_apply_1(v_k_420_, v_k_424_);
v___x_429_ = lean_unbox(v___x_428_);
switch(v___x_429_)
{
case 0:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_427_);
lean_dec(v_r_427_);
v___x_431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_431_, 0, v_k_424_);
lean_ctor_set(v___x_431_, 1, v_v_425_);
lean_ctor_set(v___x_431_, 2, v___x_430_);
lean_inc(v_inner_422_);
v___x_432_ = lean_apply_2(v_inner_422_, v_init_421_, v___x_431_);
v_init_421_ = v___x_432_;
v_l_423_ = v_l_426_;
goto _start;
}
case 1:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec_ref(v_k_420_);
v___x_434_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_426_);
lean_dec(v_l_426_);
v___x_435_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_424_, v_v_425_);
v___x_436_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_427_);
lean_dec(v_r_427_);
v___x_437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_437_, 0, v___x_434_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
lean_ctor_set(v___x_437_, 2, v___x_436_);
v___x_438_ = lean_apply_2(v_inner_422_, v_init_421_, v___x_437_);
return v___x_438_;
}
default: 
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_426_);
lean_dec(v_l_426_);
v___x_440_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v_k_424_);
lean_ctor_set(v___x_440_, 2, v_v_425_);
lean_inc(v_inner_422_);
v___x_441_ = lean_apply_2(v_inner_422_, v_init_421_, v___x_440_);
v_init_421_ = v___x_441_;
v_l_423_ = v_r_427_;
goto _start;
}
}
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec_ref(v_k_420_);
v___x_443_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0));
v___x_444_ = lean_apply_2(v_inner_422_, v_init_421_, v___x_443_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore(lean_object* v_00_u03b1_445_, lean_object* v_00_u03b2_446_, lean_object* v_00_u03b3_447_, lean_object* v_inst_448_, lean_object* v_k_449_, lean_object* v_init_450_, lean_object* v_inner_451_, lean_object* v_l_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v_k_449_, v_init_450_, v_inner_451_, v_l_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___boxed(lean_object* v_00_u03b1_454_, lean_object* v_00_u03b2_455_, lean_object* v_00_u03b3_456_, lean_object* v_inst_457_, lean_object* v_k_458_, lean_object* v_init_459_, lean_object* v_inner_460_, lean_object* v_l_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_DTreeMap_Internal_Impl_explore(v_00_u03b1_454_, v_00_u03b2_455_, v_00_u03b3_456_, v_inst_457_, v_k_458_, v_init_459_, v_inner_460_, v_l_461_);
lean_dec_ref(v_inst_457_);
return v_res_462_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(lean_object* v_c_463_, lean_object* v_x_464_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0___boxed(lean_object* v_c_466_, lean_object* v_x_467_){
_start:
{
uint8_t v_res_468_; lean_object* v_r_469_; 
v_res_468_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(v_c_466_, v_x_467_);
lean_dec(v_c_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(lean_object* v_inst_471_, lean_object* v_l_472_, lean_object* v_k_473_){
_start:
{
lean_object* v___f_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___f_474_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0));
v___x_475_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_471_, v_k_473_, v_l_472_, v___f_474_);
v___x_476_ = lean_unbox(v___x_475_);
lean_dec(v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___boxed(lean_object* v_inst_477_, lean_object* v_l_478_, lean_object* v_k_479_){
_start:
{
uint8_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(v_inst_477_, v_l_478_, v_k_479_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098(lean_object* v_00_u03b1_482_, lean_object* v_00_u03b2_483_, lean_object* v_inst_484_, lean_object* v_l_485_, lean_object* v_k_486_){
_start:
{
uint8_t v___x_487_; 
v___x_487_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(v_inst_484_, v_l_485_, v_k_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___boxed(lean_object* v_00_u03b1_488_, lean_object* v_00_u03b2_489_, lean_object* v_inst_490_, lean_object* v_l_491_, lean_object* v_k_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_Std_DTreeMap_Internal_Impl_contains_u2098(v_00_u03b1_488_, v_00_u03b2_489_, v_inst_490_, v_l_491_, v_k_492_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0(lean_object* v_c_495_, lean_object* v_x_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(v_c_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(lean_object* v_inst_499_, lean_object* v_l_500_, lean_object* v_k_501_){
_start:
{
lean_object* v___f_502_; lean_object* v___x_503_; 
v___f_502_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0));
v___x_503_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_499_, v_k_501_, v_l_500_, v___f_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098(lean_object* v_00_u03b1_504_, lean_object* v_00_u03b2_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_l_509_, lean_object* v_k_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_506_, v_l_509_, v_k_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(lean_object* v_inst_512_, lean_object* v_l_513_, lean_object* v_k_514_){
_start:
{
lean_object* v___x_515_; lean_object* v_val_516_; 
v___x_515_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_512_, v_l_513_, v_k_514_);
v_val_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_val_516_);
lean_dec(v___x_515_);
return v_val_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098(lean_object* v_00_u03b1_517_, lean_object* v_00_u03b2_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_l_522_, lean_object* v_k_523_, lean_object* v_h_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(v_inst_519_, v_l_522_, v_k_523_);
return v___x_525_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_529_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2));
v___x_530_ = lean_unsigned_to_nat(14u);
v___x_531_ = lean_unsigned_to_nat(22u);
v___x_532_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1));
v___x_533_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0));
v___x_534_ = l_mkPanicMessageWithDecl(v___x_533_, v___x_532_, v___x_531_, v___x_530_, v___x_529_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(lean_object* v_inst_535_, lean_object* v_l_536_, lean_object* v_k_537_, lean_object* v_inst_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_535_, v_l_536_, v_k_537_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_541_ = l_panic___redArg(v_inst_538_, v___x_540_);
return v___x_541_;
}
else
{
lean_object* v_val_542_; 
lean_dec(v_inst_538_);
v_val_542_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_val_542_);
lean_dec_ref(v___x_539_);
return v_val_542_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098(lean_object* v_00_u03b1_543_, lean_object* v_00_u03b2_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_l_548_, lean_object* v_k_549_, lean_object* v_inst_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(v_inst_545_, v_l_548_, v_k_549_, v_inst_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(lean_object* v_inst_552_, lean_object* v_k_553_, lean_object* v_l_554_, lean_object* v_fallback_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_552_, v_l_554_, v_k_553_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_inc(v_fallback_555_);
return v_fallback_555_;
}
else
{
lean_object* v_val_557_; 
v_val_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_val_557_);
lean_dec_ref(v___x_556_);
return v_val_557_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg___boxed(lean_object* v_inst_558_, lean_object* v_k_559_, lean_object* v_l_560_, lean_object* v_fallback_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(v_inst_558_, v_k_559_, v_l_560_, v_fallback_561_);
lean_dec(v_fallback_561_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098(lean_object* v_00_u03b1_563_, lean_object* v_00_u03b2_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_k_568_, lean_object* v_l_569_, lean_object* v_fallback_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(v_inst_565_, v_k_568_, v_l_569_, v_fallback_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___boxed(lean_object* v_00_u03b1_572_, lean_object* v_00_u03b2_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_k_577_, lean_object* v_l_578_, lean_object* v_fallback_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_DTreeMap_Internal_Impl_getD_u2098(v_00_u03b1_572_, v_00_u03b2_573_, v_inst_574_, v_inst_575_, v_inst_576_, v_k_577_, v_l_578_, v_fallback_579_);
lean_dec(v_fallback_579_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___lam__0(lean_object* v_c_581_, lean_object* v_x_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(v_c_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(lean_object* v_inst_585_, lean_object* v_l_586_, lean_object* v_k_587_){
_start:
{
lean_object* v___f_588_; lean_object* v___x_589_; 
v___f_588_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0));
v___x_589_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_585_, v_k_587_, v_l_586_, v___f_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098(lean_object* v_00_u03b1_590_, lean_object* v_00_u03b2_591_, lean_object* v_inst_592_, lean_object* v_l_593_, lean_object* v_k_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_592_, v_l_593_, v_k_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(lean_object* v_inst_596_, lean_object* v_l_597_, lean_object* v_k_598_){
_start:
{
lean_object* v___x_599_; lean_object* v_val_600_; 
v___x_599_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_596_, v_l_597_, v_k_598_);
v_val_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_val_600_);
lean_dec(v___x_599_);
return v_val_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098(lean_object* v_00_u03b1_601_, lean_object* v_00_u03b2_602_, lean_object* v_inst_603_, lean_object* v_l_604_, lean_object* v_k_605_, lean_object* v_h_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(v_inst_603_, v_l_604_, v_k_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_l_610_, lean_object* v_k_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_608_, v_l_610_, v_k_611_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_614_ = l_panic___redArg(v_inst_609_, v___x_613_);
return v___x_614_;
}
else
{
lean_object* v_val_615_; 
lean_dec_ref(v_inst_609_);
v_val_615_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_val_615_);
lean_dec_ref(v___x_612_);
return v_val_615_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(lean_object* v_00_u03b1_616_, lean_object* v_00_u03b2_617_, lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_l_620_, lean_object* v_k_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(v_inst_618_, v_inst_619_, v_l_620_, v_k_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(lean_object* v_inst_623_, lean_object* v_k_624_, lean_object* v_l_625_, lean_object* v_fallback_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_623_, v_l_625_, v_k_624_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_inc_ref(v_fallback_626_);
return v_fallback_626_;
}
else
{
lean_object* v_val_628_; 
v_val_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_val_628_);
lean_dec_ref(v___x_627_);
return v_val_628_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg___boxed(lean_object* v_inst_629_, lean_object* v_k_630_, lean_object* v_l_631_, lean_object* v_fallback_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(v_inst_629_, v_k_630_, v_l_631_, v_fallback_632_);
lean_dec_ref(v_fallback_632_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(lean_object* v_00_u03b1_634_, lean_object* v_00_u03b2_635_, lean_object* v_inst_636_, lean_object* v_k_637_, lean_object* v_l_638_, lean_object* v_fallback_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(v_inst_636_, v_k_637_, v_l_638_, v_fallback_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___boxed(lean_object* v_00_u03b1_641_, lean_object* v_00_u03b2_642_, lean_object* v_inst_643_, lean_object* v_k_644_, lean_object* v_l_645_, lean_object* v_fallback_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(v_00_u03b1_641_, v_00_u03b2_642_, v_inst_643_, v_k_644_, v_l_645_, v_fallback_646_);
lean_dec_ref(v_fallback_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0(lean_object* v_c_648_, lean_object* v_x_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(v_c_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(lean_object* v_inst_652_, lean_object* v_l_653_, lean_object* v_k_654_){
_start:
{
lean_object* v___f_655_; lean_object* v___x_656_; 
v___f_655_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0));
v___x_656_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_652_, v_k_654_, v_l_653_, v___f_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098(lean_object* v_00_u03b1_657_, lean_object* v_00_u03b2_658_, lean_object* v_inst_659_, lean_object* v_l_660_, lean_object* v_k_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_659_, v_l_660_, v_k_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(lean_object* v_inst_663_, lean_object* v_l_664_, lean_object* v_k_665_){
_start:
{
lean_object* v___x_666_; lean_object* v_val_667_; 
v___x_666_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_663_, v_l_664_, v_k_665_);
v_val_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_val_667_);
lean_dec(v___x_666_);
return v_val_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098(lean_object* v_00_u03b1_668_, lean_object* v_00_u03b2_669_, lean_object* v_inst_670_, lean_object* v_l_671_, lean_object* v_k_672_, lean_object* v_h_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(v_inst_670_, v_l_671_, v_k_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(lean_object* v_inst_675_, lean_object* v_l_676_, lean_object* v_k_677_, lean_object* v_inst_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_675_, v_l_676_, v_k_677_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_681_ = l_panic___redArg(v_inst_678_, v___x_680_);
return v___x_681_;
}
else
{
lean_object* v_val_682_; 
lean_dec(v_inst_678_);
v_val_682_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_val_682_);
lean_dec_ref(v___x_679_);
return v_val_682_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(lean_object* v_00_u03b1_683_, lean_object* v_00_u03b2_684_, lean_object* v_inst_685_, lean_object* v_l_686_, lean_object* v_k_687_, lean_object* v_inst_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(v_inst_685_, v_l_686_, v_k_687_, v_inst_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(lean_object* v_inst_690_, lean_object* v_k_691_, lean_object* v_l_692_, lean_object* v_fallback_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_690_, v_l_692_, v_k_691_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_inc(v_fallback_693_);
return v_fallback_693_;
}
else
{
lean_object* v_val_695_; 
v_val_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_val_695_);
lean_dec_ref(v___x_694_);
return v_val_695_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg___boxed(lean_object* v_inst_696_, lean_object* v_k_697_, lean_object* v_l_698_, lean_object* v_fallback_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(v_inst_696_, v_k_697_, v_l_698_, v_fallback_699_);
lean_dec(v_fallback_699_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(lean_object* v_00_u03b1_701_, lean_object* v_00_u03b2_702_, lean_object* v_inst_703_, lean_object* v_k_704_, lean_object* v_l_705_, lean_object* v_fallback_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(v_inst_703_, v_k_704_, v_l_705_, v_fallback_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___boxed(lean_object* v_00_u03b1_708_, lean_object* v_00_u03b2_709_, lean_object* v_inst_710_, lean_object* v_k_711_, lean_object* v_l_712_, lean_object* v_fallback_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(v_00_u03b1_708_, v_00_u03b2_709_, v_inst_710_, v_k_711_, v_l_712_, v_fallback_713_);
lean_dec(v_fallback_713_);
return v_res_714_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(lean_object* v_x_715_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = 0;
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* v_x_717_){
_start:
{
uint8_t v_res_718_; lean_object* v_r_719_; 
v_res_718_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(v_x_717_);
lean_dec(v_x_717_);
v_r_719_ = lean_box(v_res_718_);
return v_r_719_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(lean_object* v_sofar_720_, lean_object* v_step_721_){
_start:
{
if (lean_obj_tag(v_step_721_) == 0)
{
lean_object* v_a_722_; lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_a_722_ = lean_ctor_get(v_step_721_, 0);
v_a_723_ = lean_ctor_get(v_step_721_, 1);
lean_inc(v_a_723_);
lean_inc(v_a_722_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v_a_722_);
lean_ctor_set(v___x_724_, 1, v_a_723_);
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
else
{
lean_object* v_a_726_; lean_object* v___x_727_; 
v_a_726_ = lean_ctor_get(v_step_721_, 2);
v___x_727_ = l_List_head_x3f___redArg(v_a_726_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_inc(v_sofar_720_);
return v_sofar_720_;
}
else
{
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* v_sofar_728_, lean_object* v_step_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(v_sofar_728_, v_step_729_);
lean_dec_ref(v_step_729_);
lean_dec(v_sofar_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(lean_object* v_l_733_){
_start:
{
lean_object* v___f_734_; lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___f_734_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0));
v___f_735_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1));
v___x_736_ = lean_box(0);
v___x_737_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___f_734_, v___x_736_, v___f_735_, v_l_733_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(lean_object* v_00_u03b1_738_, lean_object* v_00_u03b2_739_, lean_object* v_inst_740_, lean_object* v_l_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(v_l_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___boxed(lean_object* v_00_u03b1_743_, lean_object* v_00_u03b2_744_, lean_object* v_inst_745_, lean_object* v_l_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(v_00_u03b1_743_, v_00_u03b2_744_, v_inst_745_, v_l_746_);
lean_dec_ref(v_inst_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_r_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_List_head_x3f___redArg(v_r_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed(lean_object* v_x_753_, lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_r_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(v_x_753_, v_x_754_, v_x_755_, v_r_756_);
lean_dec(v_r_756_);
lean_dec(v_x_754_);
lean_dec(v_x_753_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(lean_object* v_l_759_){
_start:
{
lean_object* v___f_760_; lean_object* v___f_761_; lean_object* v___x_762_; 
v___f_760_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0));
v___f_761_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0));
v___x_762_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_760_, v_l_759_, v___f_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(lean_object* v_00_u03b1_763_, lean_object* v_00_u03b2_764_, lean_object* v_inst_765_, lean_object* v_l_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(v_l_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___boxed(lean_object* v_00_u03b1_768_, lean_object* v_00_u03b2_769_, lean_object* v_inst_770_, lean_object* v_l_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(v_00_u03b1_768_, v_00_u03b2_769_, v_inst_770_, v_l_771_);
lean_dec_ref(v_inst_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse___redArg(lean_object* v_x_773_){
_start:
{
if (lean_obj_tag(v_x_773_) == 0)
{
lean_object* v_size_774_; lean_object* v_k_775_; lean_object* v_v_776_; lean_object* v_l_777_; lean_object* v_r_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_787_; 
v_size_774_ = lean_ctor_get(v_x_773_, 0);
v_k_775_ = lean_ctor_get(v_x_773_, 1);
v_v_776_ = lean_ctor_get(v_x_773_, 2);
v_l_777_ = lean_ctor_get(v_x_773_, 3);
v_r_778_ = lean_ctor_get(v_x_773_, 4);
v_isSharedCheck_787_ = !lean_is_exclusive(v_x_773_);
if (v_isSharedCheck_787_ == 0)
{
v___x_780_ = v_x_773_;
v_isShared_781_ = v_isSharedCheck_787_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_r_778_);
lean_inc(v_l_777_);
lean_inc(v_v_776_);
lean_inc(v_k_775_);
lean_inc(v_size_774_);
lean_dec(v_x_773_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_787_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_782_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_r_778_);
v___x_783_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_l_777_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 4, v___x_783_);
lean_ctor_set(v___x_780_, 3, v___x_782_);
v___x_785_ = v___x_780_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_size_774_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_k_775_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_v_776_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
return v_x_773_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse(lean_object* v_00_u03b1_788_, lean_object* v_00_u03b2_789_, lean_object* v_x_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0(lean_object* v_c_792_, lean_object* v_x_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(v_c_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(lean_object* v_inst_796_, lean_object* v_l_797_, lean_object* v_k_798_){
_start:
{
lean_object* v___f_799_; lean_object* v___x_800_; 
v___f_799_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0));
v___x_800_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_796_, v_k_798_, v_l_797_, v___f_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098(lean_object* v_00_u03b1_801_, lean_object* v_00_u03b2_802_, lean_object* v_inst_803_, lean_object* v_l_804_, lean_object* v_k_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_803_, v_l_804_, v_k_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(lean_object* v_inst_807_, lean_object* v_l_808_, lean_object* v_k_809_){
_start:
{
lean_object* v___x_810_; lean_object* v_val_811_; 
v___x_810_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_807_, v_l_808_, v_k_809_);
v_val_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_val_811_);
lean_dec(v___x_810_);
return v_val_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098(lean_object* v_00_u03b1_812_, lean_object* v_00_u03b2_813_, lean_object* v_inst_814_, lean_object* v_l_815_, lean_object* v_k_816_, lean_object* v_h_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(v_inst_814_, v_l_815_, v_k_816_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(lean_object* v_inst_819_, lean_object* v_l_820_, lean_object* v_k_821_, lean_object* v_inst_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_819_, v_l_820_, v_k_821_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_825_ = l_panic___redArg(v_inst_822_, v___x_824_);
return v___x_825_;
}
else
{
lean_object* v_val_826_; 
lean_dec(v_inst_822_);
v_val_826_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_val_826_);
lean_dec_ref(v___x_823_);
return v_val_826_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(lean_object* v_00_u03b1_827_, lean_object* v_00_u03b2_828_, lean_object* v_inst_829_, lean_object* v_l_830_, lean_object* v_k_831_, lean_object* v_inst_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(v_inst_829_, v_l_830_, v_k_831_, v_inst_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(lean_object* v_inst_834_, lean_object* v_l_835_, lean_object* v_k_836_, lean_object* v_fallback_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_834_, v_l_835_, v_k_836_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_inc(v_fallback_837_);
return v_fallback_837_;
}
else
{
lean_object* v_val_839_; 
v_val_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_val_839_);
lean_dec_ref(v___x_838_);
return v_val_839_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg___boxed(lean_object* v_inst_840_, lean_object* v_l_841_, lean_object* v_k_842_, lean_object* v_fallback_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(v_inst_840_, v_l_841_, v_k_842_, v_fallback_843_);
lean_dec(v_fallback_843_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(lean_object* v_00_u03b1_845_, lean_object* v_00_u03b2_846_, lean_object* v_inst_847_, lean_object* v_l_848_, lean_object* v_k_849_, lean_object* v_fallback_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(v_inst_847_, v_l_848_, v_k_849_, v_fallback_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___boxed(lean_object* v_00_u03b1_852_, lean_object* v_00_u03b2_853_, lean_object* v_inst_854_, lean_object* v_l_855_, lean_object* v_k_856_, lean_object* v_fallback_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(v_00_u03b1_852_, v_00_u03b2_853_, v_inst_854_, v_l_855_, v_k_856_, v_fallback_857_);
lean_dec(v_fallback_857_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object* v_t_859_, lean_object* v_h__1_860_, lean_object* v_h__2_861_){
_start:
{
if (lean_obj_tag(v_t_859_) == 0)
{
lean_object* v_size_862_; lean_object* v_k_863_; lean_object* v_v_864_; lean_object* v_l_865_; lean_object* v_r_866_; lean_object* v___x_867_; 
lean_dec(v_h__1_860_);
v_size_862_ = lean_ctor_get(v_t_859_, 0);
lean_inc(v_size_862_);
v_k_863_ = lean_ctor_get(v_t_859_, 1);
lean_inc(v_k_863_);
v_v_864_ = lean_ctor_get(v_t_859_, 2);
lean_inc(v_v_864_);
v_l_865_ = lean_ctor_get(v_t_859_, 3);
lean_inc(v_l_865_);
v_r_866_ = lean_ctor_get(v_t_859_, 4);
lean_inc(v_r_866_);
lean_dec_ref(v_t_859_);
v___x_867_ = lean_apply_5(v_h__2_861_, v_size_862_, v_k_863_, v_v_864_, v_l_865_, v_r_866_);
return v___x_867_;
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_dec(v_h__2_861_);
v___x_868_ = lean_box(0);
v___x_869_ = lean_apply_1(v_h__1_860_, v___x_868_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object* v_00_u03b1_870_, lean_object* v_00_u03b2_871_, lean_object* v_motive_872_, lean_object* v_t_873_, lean_object* v_h__1_874_, lean_object* v_h__2_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(v_t_873_, v_h__1_874_, v_h__2_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(uint8_t v_x_877_, lean_object* v_h__1_878_, lean_object* v_h__2_879_, lean_object* v_h__3_880_){
_start:
{
switch(v_x_877_)
{
case 0:
{
lean_object* v___x_881_; 
lean_dec(v_h__3_880_);
lean_dec(v_h__2_879_);
v___x_881_ = lean_apply_1(v_h__1_878_, lean_box(0));
return v___x_881_;
}
case 1:
{
lean_object* v___x_882_; 
lean_dec(v_h__2_879_);
lean_dec(v_h__1_878_);
v___x_882_ = lean_apply_1(v_h__3_880_, lean_box(0));
return v___x_882_;
}
default: 
{
lean_object* v___x_883_; 
lean_dec(v_h__3_880_);
lean_dec(v_h__1_878_);
v___x_883_ = lean_apply_1(v_h__2_879_, lean_box(0));
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_884_, lean_object* v_h__1_885_, lean_object* v_h__2_886_, lean_object* v_h__3_887_){
_start:
{
uint8_t v_x_30__boxed_888_; lean_object* v_res_889_; 
v_x_30__boxed_888_ = lean_unbox(v_x_884_);
v_res_889_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(v_x_30__boxed_888_, v_h__1_885_, v_h__2_886_, v_h__3_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(lean_object* v_motive_890_, uint8_t v_x_891_, lean_object* v_h__1_892_, lean_object* v_h__2_893_, lean_object* v_h__3_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(v_x_891_, v_h__1_892_, v_h__2_893_, v_h__3_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___boxed(lean_object* v_motive_896_, lean_object* v_x_897_, lean_object* v_h__1_898_, lean_object* v_h__2_899_, lean_object* v_h__3_900_){
_start:
{
uint8_t v_x_39__boxed_901_; lean_object* v_res_902_; 
v_x_39__boxed_901_ = lean_unbox(v_x_897_);
v_res_902_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(v_motive_896_, v_x_39__boxed_901_, v_h__1_898_, v_h__2_899_, v_h__3_900_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object* v_x_903_, lean_object* v_h__1_904_, lean_object* v_h__2_905_){
_start:
{
if (lean_obj_tag(v_x_903_) == 0)
{
lean_object* v___x_906_; 
lean_dec(v_h__2_905_);
v___x_906_ = lean_apply_1(v_h__1_904_, lean_box(0));
return v___x_906_;
}
else
{
lean_object* v_val_907_; lean_object* v___x_908_; 
lean_dec(v_h__1_904_);
v_val_907_ = lean_ctor_get(v_x_903_, 0);
lean_inc(v_val_907_);
lean_dec_ref(v_x_903_);
v___x_908_ = lean_apply_2(v_h__2_905_, v_val_907_, lean_box(0));
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object* v_00_u03b1_909_, lean_object* v_00_u03b2_910_, lean_object* v_motive_911_, lean_object* v_x_912_, lean_object* v_h__1_913_, lean_object* v_h__2_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(v_x_912_, v_h__1_913_, v_h__2_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___redArg(lean_object* v_t_916_, lean_object* v_h__1_917_){
_start:
{
lean_object* v_size_918_; lean_object* v_k_919_; lean_object* v_v_920_; lean_object* v_l_921_; lean_object* v_r_922_; lean_object* v___x_923_; 
v_size_918_ = lean_ctor_get(v_t_916_, 0);
lean_inc(v_size_918_);
v_k_919_ = lean_ctor_get(v_t_916_, 1);
lean_inc(v_k_919_);
v_v_920_ = lean_ctor_get(v_t_916_, 2);
lean_inc(v_v_920_);
v_l_921_ = lean_ctor_get(v_t_916_, 3);
lean_inc(v_l_921_);
v_r_922_ = lean_ctor_get(v_t_916_, 4);
lean_inc(v_r_922_);
lean_dec(v_t_916_);
v___x_923_ = lean_apply_6(v_h__1_917_, v_size_918_, v_k_919_, v_v_920_, v_l_921_, v_r_922_, lean_box(0));
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(lean_object* v_00_u03b1_924_, lean_object* v_00_u03b2_925_, lean_object* v_inst_926_, lean_object* v_k_927_, lean_object* v_motive_928_, lean_object* v_t_929_, lean_object* v_hlk_930_, lean_object* v_h__1_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___redArg(v_t_929_, v_h__1_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___boxed(lean_object* v_00_u03b1_933_, lean_object* v_00_u03b2_934_, lean_object* v_inst_935_, lean_object* v_k_936_, lean_object* v_motive_937_, lean_object* v_t_938_, lean_object* v_hlk_939_, lean_object* v_h__1_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(v_00_u03b1_933_, v_00_u03b2_934_, v_inst_935_, v_k_936_, v_motive_937_, v_t_938_, v_hlk_939_, v_h__1_940_);
lean_dec(v_k_936_);
lean_dec_ref(v_inst_935_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_942_, lean_object* v_h__1_943_, lean_object* v_h__2_944_){
_start:
{
if (lean_obj_tag(v_x_942_) == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; 
lean_dec(v_h__2_944_);
v___x_945_ = lean_box(0);
v___x_946_ = lean_apply_1(v_h__1_943_, v___x_945_);
return v___x_946_;
}
else
{
lean_object* v_val_947_; lean_object* v___x_948_; 
lean_dec(v_h__1_943_);
v_val_947_ = lean_ctor_get(v_x_942_, 0);
lean_inc(v_val_947_);
lean_dec_ref(v_x_942_);
v___x_948_ = lean_apply_1(v_h__2_944_, v_val_947_);
return v___x_948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_949_, lean_object* v_00_u03b2_950_, lean_object* v_motive_951_, lean_object* v_x_952_, lean_object* v_h__1_953_, lean_object* v_h__2_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(v_x_952_, v_h__1_953_, v_h__2_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___redArg(lean_object* v_t_956_, lean_object* v_h__1_957_){
_start:
{
lean_object* v_size_958_; lean_object* v_k_959_; lean_object* v_v_960_; lean_object* v_l_961_; lean_object* v_r_962_; lean_object* v___x_963_; 
v_size_958_ = lean_ctor_get(v_t_956_, 0);
lean_inc(v_size_958_);
v_k_959_ = lean_ctor_get(v_t_956_, 1);
lean_inc(v_k_959_);
v_v_960_ = lean_ctor_get(v_t_956_, 2);
lean_inc(v_v_960_);
v_l_961_ = lean_ctor_get(v_t_956_, 3);
lean_inc(v_l_961_);
v_r_962_ = lean_ctor_get(v_t_956_, 4);
lean_inc(v_r_962_);
lean_dec(v_t_956_);
v___x_963_ = lean_apply_6(v_h__1_957_, v_size_958_, v_k_959_, v_v_960_, v_l_961_, v_r_962_, lean_box(0));
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(lean_object* v_00_u03b1_964_, lean_object* v_00_u03b2_965_, lean_object* v_inst_966_, lean_object* v_k_967_, lean_object* v_motive_968_, lean_object* v_t_969_, lean_object* v_hlk_970_, lean_object* v_h__1_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___redArg(v_t_969_, v_h__1_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___boxed(lean_object* v_00_u03b1_973_, lean_object* v_00_u03b2_974_, lean_object* v_inst_975_, lean_object* v_k_976_, lean_object* v_motive_977_, lean_object* v_t_978_, lean_object* v_hlk_979_, lean_object* v_h__1_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(v_00_u03b1_973_, v_00_u03b2_974_, v_inst_975_, v_k_976_, v_motive_977_, v_t_978_, v_hlk_979_, v_h__1_980_);
lean_dec(v_k_976_);
lean_dec_ref(v_inst_975_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_982_, lean_object* v_h__1_983_, lean_object* v_h__2_984_, lean_object* v_h__3_985_){
_start:
{
if (lean_obj_tag(v_x_982_) == 0)
{
lean_object* v_l_986_; 
lean_dec(v_h__1_983_);
v_l_986_ = lean_ctor_get(v_x_982_, 3);
if (lean_obj_tag(v_l_986_) == 0)
{
lean_object* v_size_987_; lean_object* v_k_988_; lean_object* v_v_989_; lean_object* v_r_990_; lean_object* v_size_991_; lean_object* v_k_992_; lean_object* v_v_993_; lean_object* v_l_994_; lean_object* v_r_995_; lean_object* v___x_996_; 
lean_inc_ref(v_l_986_);
lean_dec(v_h__2_984_);
v_size_987_ = lean_ctor_get(v_x_982_, 0);
lean_inc(v_size_987_);
v_k_988_ = lean_ctor_get(v_x_982_, 1);
lean_inc(v_k_988_);
v_v_989_ = lean_ctor_get(v_x_982_, 2);
lean_inc(v_v_989_);
v_r_990_ = lean_ctor_get(v_x_982_, 4);
lean_inc(v_r_990_);
lean_dec_ref(v_x_982_);
v_size_991_ = lean_ctor_get(v_l_986_, 0);
lean_inc(v_size_991_);
v_k_992_ = lean_ctor_get(v_l_986_, 1);
lean_inc(v_k_992_);
v_v_993_ = lean_ctor_get(v_l_986_, 2);
lean_inc(v_v_993_);
v_l_994_ = lean_ctor_get(v_l_986_, 3);
lean_inc(v_l_994_);
v_r_995_ = lean_ctor_get(v_l_986_, 4);
lean_inc(v_r_995_);
lean_dec_ref(v_l_986_);
v___x_996_ = lean_apply_9(v_h__3_985_, v_size_987_, v_k_988_, v_v_989_, v_size_991_, v_k_992_, v_v_993_, v_l_994_, v_r_995_, v_r_990_);
return v___x_996_;
}
else
{
lean_object* v_size_997_; lean_object* v_k_998_; lean_object* v_v_999_; lean_object* v_r_1000_; lean_object* v___x_1001_; 
lean_dec(v_h__3_985_);
v_size_997_ = lean_ctor_get(v_x_982_, 0);
lean_inc(v_size_997_);
v_k_998_ = lean_ctor_get(v_x_982_, 1);
lean_inc(v_k_998_);
v_v_999_ = lean_ctor_get(v_x_982_, 2);
lean_inc(v_v_999_);
v_r_1000_ = lean_ctor_get(v_x_982_, 4);
lean_inc(v_r_1000_);
lean_dec_ref(v_x_982_);
v___x_1001_ = lean_apply_4(v_h__2_984_, v_size_997_, v_k_998_, v_v_999_, v_r_1000_);
return v___x_1001_;
}
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec(v_h__3_985_);
lean_dec(v_h__2_984_);
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_apply_1(v_h__1_983_, v___x_1002_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_motive_1006_, lean_object* v_x_1007_, lean_object* v_h__1_1008_, lean_object* v_h__2_1009_, lean_object* v_h__3_1010_){
_start:
{
if (lean_obj_tag(v_x_1007_) == 0)
{
lean_object* v_l_1011_; 
lean_dec(v_h__1_1008_);
v_l_1011_ = lean_ctor_get(v_x_1007_, 3);
if (lean_obj_tag(v_l_1011_) == 0)
{
lean_object* v_size_1012_; lean_object* v_k_1013_; lean_object* v_v_1014_; lean_object* v_r_1015_; lean_object* v_size_1016_; lean_object* v_k_1017_; lean_object* v_v_1018_; lean_object* v_l_1019_; lean_object* v_r_1020_; lean_object* v___x_1021_; 
lean_inc_ref(v_l_1011_);
lean_dec(v_h__2_1009_);
v_size_1012_ = lean_ctor_get(v_x_1007_, 0);
lean_inc(v_size_1012_);
v_k_1013_ = lean_ctor_get(v_x_1007_, 1);
lean_inc(v_k_1013_);
v_v_1014_ = lean_ctor_get(v_x_1007_, 2);
lean_inc(v_v_1014_);
v_r_1015_ = lean_ctor_get(v_x_1007_, 4);
lean_inc(v_r_1015_);
lean_dec_ref(v_x_1007_);
v_size_1016_ = lean_ctor_get(v_l_1011_, 0);
lean_inc(v_size_1016_);
v_k_1017_ = lean_ctor_get(v_l_1011_, 1);
lean_inc(v_k_1017_);
v_v_1018_ = lean_ctor_get(v_l_1011_, 2);
lean_inc(v_v_1018_);
v_l_1019_ = lean_ctor_get(v_l_1011_, 3);
lean_inc(v_l_1019_);
v_r_1020_ = lean_ctor_get(v_l_1011_, 4);
lean_inc(v_r_1020_);
lean_dec_ref(v_l_1011_);
v___x_1021_ = lean_apply_9(v_h__3_1010_, v_size_1012_, v_k_1013_, v_v_1014_, v_size_1016_, v_k_1017_, v_v_1018_, v_l_1019_, v_r_1020_, v_r_1015_);
return v___x_1021_;
}
else
{
lean_object* v_size_1022_; lean_object* v_k_1023_; lean_object* v_v_1024_; lean_object* v_r_1025_; lean_object* v___x_1026_; 
lean_dec(v_h__3_1010_);
v_size_1022_ = lean_ctor_get(v_x_1007_, 0);
lean_inc(v_size_1022_);
v_k_1023_ = lean_ctor_get(v_x_1007_, 1);
lean_inc(v_k_1023_);
v_v_1024_ = lean_ctor_get(v_x_1007_, 2);
lean_inc(v_v_1024_);
v_r_1025_ = lean_ctor_get(v_x_1007_, 4);
lean_inc(v_r_1025_);
lean_dec_ref(v_x_1007_);
v___x_1026_ = lean_apply_4(v_h__2_1009_, v_size_1022_, v_k_1023_, v_v_1024_, v_r_1025_);
return v___x_1026_;
}
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec(v_h__3_1010_);
lean_dec(v_h__2_1009_);
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_apply_1(v_h__1_1008_, v___x_1027_);
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_step_1029_, lean_object* v_h__1_1030_, lean_object* v_h__2_1031_){
_start:
{
if (lean_obj_tag(v_step_1029_) == 0)
{
lean_object* v_a_1032_; lean_object* v_a_1033_; lean_object* v_a_1034_; lean_object* v___x_1035_; 
lean_dec(v_h__2_1031_);
v_a_1032_ = lean_ctor_get(v_step_1029_, 0);
lean_inc(v_a_1032_);
v_a_1033_ = lean_ctor_get(v_step_1029_, 1);
lean_inc(v_a_1033_);
v_a_1034_ = lean_ctor_get(v_step_1029_, 2);
lean_inc(v_a_1034_);
lean_dec_ref(v_step_1029_);
v___x_1035_ = lean_apply_4(v_h__1_1030_, v_a_1032_, lean_box(0), v_a_1033_, v_a_1034_);
return v___x_1035_;
}
else
{
lean_object* v_a_1036_; lean_object* v_a_1037_; lean_object* v_a_1038_; lean_object* v___x_1039_; 
lean_dec(v_h__1_1030_);
v_a_1036_ = lean_ctor_get(v_step_1029_, 0);
lean_inc(v_a_1036_);
v_a_1037_ = lean_ctor_get(v_step_1029_, 1);
lean_inc(v_a_1037_);
v_a_1038_ = lean_ctor_get(v_step_1029_, 2);
lean_inc(v_a_1038_);
lean_dec_ref(v_step_1029_);
v___x_1039_ = lean_apply_3(v_h__2_1031_, v_a_1036_, v_a_1037_, v_a_1038_);
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_1040_, lean_object* v_00_u03b2_1041_, lean_object* v_inst_1042_, lean_object* v_motive_1043_, lean_object* v_step_1044_, lean_object* v_h__1_1045_, lean_object* v_h__2_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(v_step_1044_, v_h__1_1045_, v_h__2_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_inst_1050_, lean_object* v_motive_1051_, lean_object* v_step_1052_, lean_object* v_h__1_1053_, lean_object* v_h__2_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(v_00_u03b1_1048_, v_00_u03b2_1049_, v_inst_1050_, v_motive_1051_, v_step_1052_, v_h__1_1053_, v_h__2_1054_);
lean_dec_ref(v_inst_1050_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object* v_x_1056_, lean_object* v_x_1057_, lean_object* v_h__1_1058_, lean_object* v_h__2_1059_, lean_object* v_h__3_1060_){
_start:
{
if (lean_obj_tag(v_x_1056_) == 0)
{
lean_object* v_l_1061_; 
lean_dec(v_h__1_1058_);
v_l_1061_ = lean_ctor_get(v_x_1056_, 3);
if (lean_obj_tag(v_l_1061_) == 0)
{
lean_object* v_size_1062_; lean_object* v_k_1063_; lean_object* v_v_1064_; lean_object* v_r_1065_; lean_object* v_size_1066_; lean_object* v_k_1067_; lean_object* v_v_1068_; lean_object* v_l_1069_; lean_object* v_r_1070_; lean_object* v___x_1071_; 
lean_inc_ref(v_l_1061_);
lean_dec(v_h__2_1059_);
v_size_1062_ = lean_ctor_get(v_x_1056_, 0);
lean_inc(v_size_1062_);
v_k_1063_ = lean_ctor_get(v_x_1056_, 1);
lean_inc(v_k_1063_);
v_v_1064_ = lean_ctor_get(v_x_1056_, 2);
lean_inc(v_v_1064_);
v_r_1065_ = lean_ctor_get(v_x_1056_, 4);
lean_inc(v_r_1065_);
lean_dec_ref(v_x_1056_);
v_size_1066_ = lean_ctor_get(v_l_1061_, 0);
lean_inc(v_size_1066_);
v_k_1067_ = lean_ctor_get(v_l_1061_, 1);
lean_inc(v_k_1067_);
v_v_1068_ = lean_ctor_get(v_l_1061_, 2);
lean_inc(v_v_1068_);
v_l_1069_ = lean_ctor_get(v_l_1061_, 3);
lean_inc(v_l_1069_);
v_r_1070_ = lean_ctor_get(v_l_1061_, 4);
lean_inc(v_r_1070_);
lean_dec_ref(v_l_1061_);
v___x_1071_ = lean_apply_10(v_h__3_1060_, v_size_1062_, v_k_1063_, v_v_1064_, v_size_1066_, v_k_1067_, v_v_1068_, v_l_1069_, v_r_1070_, v_r_1065_, v_x_1057_);
return v___x_1071_;
}
else
{
lean_object* v_size_1072_; lean_object* v_k_1073_; lean_object* v_v_1074_; lean_object* v_r_1075_; lean_object* v___x_1076_; 
lean_dec(v_h__3_1060_);
v_size_1072_ = lean_ctor_get(v_x_1056_, 0);
lean_inc(v_size_1072_);
v_k_1073_ = lean_ctor_get(v_x_1056_, 1);
lean_inc(v_k_1073_);
v_v_1074_ = lean_ctor_get(v_x_1056_, 2);
lean_inc(v_v_1074_);
v_r_1075_ = lean_ctor_get(v_x_1056_, 4);
lean_inc(v_r_1075_);
lean_dec_ref(v_x_1056_);
v___x_1076_ = lean_apply_5(v_h__2_1059_, v_size_1072_, v_k_1073_, v_v_1074_, v_r_1075_, v_x_1057_);
return v___x_1076_;
}
}
else
{
lean_object* v___x_1077_; 
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
v___x_1077_ = lean_apply_1(v_h__1_1058_, v_x_1057_);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_motive_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_h__1_1083_, lean_object* v_h__2_1084_, lean_object* v_h__3_1085_){
_start:
{
if (lean_obj_tag(v_x_1081_) == 0)
{
lean_object* v_l_1086_; 
lean_dec(v_h__1_1083_);
v_l_1086_ = lean_ctor_get(v_x_1081_, 3);
if (lean_obj_tag(v_l_1086_) == 0)
{
lean_object* v_size_1087_; lean_object* v_k_1088_; lean_object* v_v_1089_; lean_object* v_r_1090_; lean_object* v_size_1091_; lean_object* v_k_1092_; lean_object* v_v_1093_; lean_object* v_l_1094_; lean_object* v_r_1095_; lean_object* v___x_1096_; 
lean_inc_ref(v_l_1086_);
lean_dec(v_h__2_1084_);
v_size_1087_ = lean_ctor_get(v_x_1081_, 0);
lean_inc(v_size_1087_);
v_k_1088_ = lean_ctor_get(v_x_1081_, 1);
lean_inc(v_k_1088_);
v_v_1089_ = lean_ctor_get(v_x_1081_, 2);
lean_inc(v_v_1089_);
v_r_1090_ = lean_ctor_get(v_x_1081_, 4);
lean_inc(v_r_1090_);
lean_dec_ref(v_x_1081_);
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
lean_dec_ref(v_l_1086_);
v___x_1096_ = lean_apply_10(v_h__3_1085_, v_size_1087_, v_k_1088_, v_v_1089_, v_size_1091_, v_k_1092_, v_v_1093_, v_l_1094_, v_r_1095_, v_r_1090_, v_x_1082_);
return v___x_1096_;
}
else
{
lean_object* v_size_1097_; lean_object* v_k_1098_; lean_object* v_v_1099_; lean_object* v_r_1100_; lean_object* v___x_1101_; 
lean_dec(v_h__3_1085_);
v_size_1097_ = lean_ctor_get(v_x_1081_, 0);
lean_inc(v_size_1097_);
v_k_1098_ = lean_ctor_get(v_x_1081_, 1);
lean_inc(v_k_1098_);
v_v_1099_ = lean_ctor_get(v_x_1081_, 2);
lean_inc(v_v_1099_);
v_r_1100_ = lean_ctor_get(v_x_1081_, 4);
lean_inc(v_r_1100_);
lean_dec_ref(v_x_1081_);
v___x_1101_ = lean_apply_5(v_h__2_1084_, v_size_1097_, v_k_1098_, v_v_1099_, v_r_1100_, v_x_1082_);
return v___x_1101_;
}
}
else
{
lean_object* v___x_1102_; 
lean_dec(v_h__3_1085_);
lean_dec(v_h__2_1084_);
v___x_1102_ = lean_apply_1(v_h__1_1083_, v_x_1082_);
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object* v_x_1103_, lean_object* v_h__1_1104_, lean_object* v_h__2_1105_){
_start:
{
lean_object* v_l_1106_; 
v_l_1106_ = lean_ctor_get(v_x_1103_, 3);
if (lean_obj_tag(v_l_1106_) == 0)
{
lean_object* v_size_1107_; lean_object* v_k_1108_; lean_object* v_v_1109_; lean_object* v_r_1110_; lean_object* v_size_1111_; lean_object* v_k_1112_; lean_object* v_v_1113_; lean_object* v_l_1114_; lean_object* v_r_1115_; lean_object* v___x_1116_; 
lean_inc_ref(v_l_1106_);
lean_dec(v_h__1_1104_);
v_size_1107_ = lean_ctor_get(v_x_1103_, 0);
lean_inc(v_size_1107_);
v_k_1108_ = lean_ctor_get(v_x_1103_, 1);
lean_inc(v_k_1108_);
v_v_1109_ = lean_ctor_get(v_x_1103_, 2);
lean_inc(v_v_1109_);
v_r_1110_ = lean_ctor_get(v_x_1103_, 4);
lean_inc(v_r_1110_);
lean_dec(v_x_1103_);
v_size_1111_ = lean_ctor_get(v_l_1106_, 0);
lean_inc(v_size_1111_);
v_k_1112_ = lean_ctor_get(v_l_1106_, 1);
lean_inc(v_k_1112_);
v_v_1113_ = lean_ctor_get(v_l_1106_, 2);
lean_inc(v_v_1113_);
v_l_1114_ = lean_ctor_get(v_l_1106_, 3);
lean_inc(v_l_1114_);
v_r_1115_ = lean_ctor_get(v_l_1106_, 4);
lean_inc(v_r_1115_);
lean_dec_ref(v_l_1106_);
v___x_1116_ = lean_apply_10(v_h__2_1105_, v_size_1107_, v_k_1108_, v_v_1109_, v_size_1111_, v_k_1112_, v_v_1113_, v_l_1114_, v_r_1115_, v_r_1110_, lean_box(0));
return v___x_1116_;
}
else
{
lean_object* v_size_1117_; lean_object* v_k_1118_; lean_object* v_v_1119_; lean_object* v_r_1120_; lean_object* v___x_1121_; 
lean_dec(v_h__2_1105_);
v_size_1117_ = lean_ctor_get(v_x_1103_, 0);
lean_inc(v_size_1117_);
v_k_1118_ = lean_ctor_get(v_x_1103_, 1);
lean_inc(v_k_1118_);
v_v_1119_ = lean_ctor_get(v_x_1103_, 2);
lean_inc(v_v_1119_);
v_r_1120_ = lean_ctor_get(v_x_1103_, 4);
lean_inc(v_r_1120_);
lean_dec(v_x_1103_);
v___x_1121_ = lean_apply_5(v_h__1_1104_, v_size_1117_, v_k_1118_, v_v_1119_, v_r_1120_, lean_box(0));
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* v_00_u03b1_1122_, lean_object* v_00_u03b2_1123_, lean_object* v_motive_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_, lean_object* v_h__1_1127_, lean_object* v_h__2_1128_){
_start:
{
lean_object* v_l_1129_; 
v_l_1129_ = lean_ctor_get(v_x_1125_, 3);
if (lean_obj_tag(v_l_1129_) == 0)
{
lean_object* v_size_1130_; lean_object* v_k_1131_; lean_object* v_v_1132_; lean_object* v_r_1133_; lean_object* v_size_1134_; lean_object* v_k_1135_; lean_object* v_v_1136_; lean_object* v_l_1137_; lean_object* v_r_1138_; lean_object* v___x_1139_; 
lean_inc_ref(v_l_1129_);
lean_dec(v_h__1_1127_);
v_size_1130_ = lean_ctor_get(v_x_1125_, 0);
lean_inc(v_size_1130_);
v_k_1131_ = lean_ctor_get(v_x_1125_, 1);
lean_inc(v_k_1131_);
v_v_1132_ = lean_ctor_get(v_x_1125_, 2);
lean_inc(v_v_1132_);
v_r_1133_ = lean_ctor_get(v_x_1125_, 4);
lean_inc(v_r_1133_);
lean_dec(v_x_1125_);
v_size_1134_ = lean_ctor_get(v_l_1129_, 0);
lean_inc(v_size_1134_);
v_k_1135_ = lean_ctor_get(v_l_1129_, 1);
lean_inc(v_k_1135_);
v_v_1136_ = lean_ctor_get(v_l_1129_, 2);
lean_inc(v_v_1136_);
v_l_1137_ = lean_ctor_get(v_l_1129_, 3);
lean_inc(v_l_1137_);
v_r_1138_ = lean_ctor_get(v_l_1129_, 4);
lean_inc(v_r_1138_);
lean_dec_ref(v_l_1129_);
v___x_1139_ = lean_apply_10(v_h__2_1128_, v_size_1130_, v_k_1131_, v_v_1132_, v_size_1134_, v_k_1135_, v_v_1136_, v_l_1137_, v_r_1138_, v_r_1133_, lean_box(0));
return v___x_1139_;
}
else
{
lean_object* v_size_1140_; lean_object* v_k_1141_; lean_object* v_v_1142_; lean_object* v_r_1143_; lean_object* v___x_1144_; 
lean_dec(v_h__2_1128_);
v_size_1140_ = lean_ctor_get(v_x_1125_, 0);
lean_inc(v_size_1140_);
v_k_1141_ = lean_ctor_get(v_x_1125_, 1);
lean_inc(v_k_1141_);
v_v_1142_ = lean_ctor_get(v_x_1125_, 2);
lean_inc(v_v_1142_);
v_r_1143_ = lean_ctor_get(v_x_1125_, 4);
lean_inc(v_r_1143_);
lean_dec(v_x_1125_);
v___x_1144_ = lean_apply_5(v_h__1_1127_, v_size_1140_, v_k_1141_, v_v_1142_, v_r_1143_, lean_box(0));
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1145_, lean_object* v_h__1_1146_, lean_object* v_h__2_1147_, lean_object* v_h__3_1148_){
_start:
{
if (lean_obj_tag(v_x_1145_) == 0)
{
lean_object* v_r_1149_; 
lean_dec(v_h__1_1146_);
v_r_1149_ = lean_ctor_get(v_x_1145_, 4);
if (lean_obj_tag(v_r_1149_) == 0)
{
lean_object* v_size_1150_; lean_object* v_k_1151_; lean_object* v_v_1152_; lean_object* v_l_1153_; lean_object* v_size_1154_; lean_object* v_k_1155_; lean_object* v_v_1156_; lean_object* v_l_1157_; lean_object* v_r_1158_; lean_object* v___x_1159_; 
lean_inc_ref(v_r_1149_);
lean_dec(v_h__2_1147_);
v_size_1150_ = lean_ctor_get(v_x_1145_, 0);
lean_inc(v_size_1150_);
v_k_1151_ = lean_ctor_get(v_x_1145_, 1);
lean_inc(v_k_1151_);
v_v_1152_ = lean_ctor_get(v_x_1145_, 2);
lean_inc(v_v_1152_);
v_l_1153_ = lean_ctor_get(v_x_1145_, 3);
lean_inc(v_l_1153_);
lean_dec_ref(v_x_1145_);
v_size_1154_ = lean_ctor_get(v_r_1149_, 0);
lean_inc(v_size_1154_);
v_k_1155_ = lean_ctor_get(v_r_1149_, 1);
lean_inc(v_k_1155_);
v_v_1156_ = lean_ctor_get(v_r_1149_, 2);
lean_inc(v_v_1156_);
v_l_1157_ = lean_ctor_get(v_r_1149_, 3);
lean_inc(v_l_1157_);
v_r_1158_ = lean_ctor_get(v_r_1149_, 4);
lean_inc(v_r_1158_);
lean_dec_ref(v_r_1149_);
v___x_1159_ = lean_apply_9(v_h__3_1148_, v_size_1150_, v_k_1151_, v_v_1152_, v_l_1153_, v_size_1154_, v_k_1155_, v_v_1156_, v_l_1157_, v_r_1158_);
return v___x_1159_;
}
else
{
lean_object* v_size_1160_; lean_object* v_k_1161_; lean_object* v_v_1162_; lean_object* v_l_1163_; lean_object* v___x_1164_; 
lean_dec(v_h__3_1148_);
v_size_1160_ = lean_ctor_get(v_x_1145_, 0);
lean_inc(v_size_1160_);
v_k_1161_ = lean_ctor_get(v_x_1145_, 1);
lean_inc(v_k_1161_);
v_v_1162_ = lean_ctor_get(v_x_1145_, 2);
lean_inc(v_v_1162_);
v_l_1163_ = lean_ctor_get(v_x_1145_, 3);
lean_inc(v_l_1163_);
lean_dec_ref(v_x_1145_);
v___x_1164_ = lean_apply_4(v_h__2_1147_, v_size_1160_, v_k_1161_, v_v_1162_, v_l_1163_);
return v___x_1164_;
}
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec(v_h__3_1148_);
lean_dec(v_h__2_1147_);
v___x_1165_ = lean_box(0);
v___x_1166_ = lean_apply_1(v_h__1_1146_, v___x_1165_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1167_, lean_object* v_00_u03b2_1168_, lean_object* v_motive_1169_, lean_object* v_x_1170_, lean_object* v_h__1_1171_, lean_object* v_h__2_1172_, lean_object* v_h__3_1173_){
_start:
{
if (lean_obj_tag(v_x_1170_) == 0)
{
lean_object* v_r_1174_; 
lean_dec(v_h__1_1171_);
v_r_1174_ = lean_ctor_get(v_x_1170_, 4);
if (lean_obj_tag(v_r_1174_) == 0)
{
lean_object* v_size_1175_; lean_object* v_k_1176_; lean_object* v_v_1177_; lean_object* v_l_1178_; lean_object* v_size_1179_; lean_object* v_k_1180_; lean_object* v_v_1181_; lean_object* v_l_1182_; lean_object* v_r_1183_; lean_object* v___x_1184_; 
lean_inc_ref(v_r_1174_);
lean_dec(v_h__2_1172_);
v_size_1175_ = lean_ctor_get(v_x_1170_, 0);
lean_inc(v_size_1175_);
v_k_1176_ = lean_ctor_get(v_x_1170_, 1);
lean_inc(v_k_1176_);
v_v_1177_ = lean_ctor_get(v_x_1170_, 2);
lean_inc(v_v_1177_);
v_l_1178_ = lean_ctor_get(v_x_1170_, 3);
lean_inc(v_l_1178_);
lean_dec_ref(v_x_1170_);
v_size_1179_ = lean_ctor_get(v_r_1174_, 0);
lean_inc(v_size_1179_);
v_k_1180_ = lean_ctor_get(v_r_1174_, 1);
lean_inc(v_k_1180_);
v_v_1181_ = lean_ctor_get(v_r_1174_, 2);
lean_inc(v_v_1181_);
v_l_1182_ = lean_ctor_get(v_r_1174_, 3);
lean_inc(v_l_1182_);
v_r_1183_ = lean_ctor_get(v_r_1174_, 4);
lean_inc(v_r_1183_);
lean_dec_ref(v_r_1174_);
v___x_1184_ = lean_apply_9(v_h__3_1173_, v_size_1175_, v_k_1176_, v_v_1177_, v_l_1178_, v_size_1179_, v_k_1180_, v_v_1181_, v_l_1182_, v_r_1183_);
return v___x_1184_;
}
else
{
lean_object* v_size_1185_; lean_object* v_k_1186_; lean_object* v_v_1187_; lean_object* v_l_1188_; lean_object* v___x_1189_; 
lean_dec(v_h__3_1173_);
v_size_1185_ = lean_ctor_get(v_x_1170_, 0);
lean_inc(v_size_1185_);
v_k_1186_ = lean_ctor_get(v_x_1170_, 1);
lean_inc(v_k_1186_);
v_v_1187_ = lean_ctor_get(v_x_1170_, 2);
lean_inc(v_v_1187_);
v_l_1188_ = lean_ctor_get(v_x_1170_, 3);
lean_inc(v_l_1188_);
lean_dec_ref(v_x_1170_);
v___x_1189_ = lean_apply_4(v_h__2_1172_, v_size_1185_, v_k_1186_, v_v_1187_, v_l_1188_);
return v___x_1189_;
}
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec(v_h__3_1173_);
lean_dec(v_h__2_1172_);
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_apply_1(v_h__1_1171_, v___x_1190_);
return v___x_1191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1192_, lean_object* v_x_1193_, lean_object* v_h__1_1194_, lean_object* v_h__2_1195_, lean_object* v_h__3_1196_){
_start:
{
if (lean_obj_tag(v_x_1192_) == 0)
{
lean_object* v_r_1197_; 
lean_dec(v_h__1_1194_);
v_r_1197_ = lean_ctor_get(v_x_1192_, 4);
if (lean_obj_tag(v_r_1197_) == 0)
{
lean_object* v_size_1198_; lean_object* v_k_1199_; lean_object* v_v_1200_; lean_object* v_l_1201_; lean_object* v_size_1202_; lean_object* v_k_1203_; lean_object* v_v_1204_; lean_object* v_l_1205_; lean_object* v_r_1206_; lean_object* v___x_1207_; 
lean_inc_ref(v_r_1197_);
lean_dec(v_h__2_1195_);
v_size_1198_ = lean_ctor_get(v_x_1192_, 0);
lean_inc(v_size_1198_);
v_k_1199_ = lean_ctor_get(v_x_1192_, 1);
lean_inc(v_k_1199_);
v_v_1200_ = lean_ctor_get(v_x_1192_, 2);
lean_inc(v_v_1200_);
v_l_1201_ = lean_ctor_get(v_x_1192_, 3);
lean_inc(v_l_1201_);
lean_dec_ref(v_x_1192_);
v_size_1202_ = lean_ctor_get(v_r_1197_, 0);
lean_inc(v_size_1202_);
v_k_1203_ = lean_ctor_get(v_r_1197_, 1);
lean_inc(v_k_1203_);
v_v_1204_ = lean_ctor_get(v_r_1197_, 2);
lean_inc(v_v_1204_);
v_l_1205_ = lean_ctor_get(v_r_1197_, 3);
lean_inc(v_l_1205_);
v_r_1206_ = lean_ctor_get(v_r_1197_, 4);
lean_inc(v_r_1206_);
lean_dec_ref(v_r_1197_);
v___x_1207_ = lean_apply_10(v_h__3_1196_, v_size_1198_, v_k_1199_, v_v_1200_, v_l_1201_, v_size_1202_, v_k_1203_, v_v_1204_, v_l_1205_, v_r_1206_, v_x_1193_);
return v___x_1207_;
}
else
{
lean_object* v_size_1208_; lean_object* v_k_1209_; lean_object* v_v_1210_; lean_object* v_l_1211_; lean_object* v___x_1212_; 
lean_dec(v_h__3_1196_);
v_size_1208_ = lean_ctor_get(v_x_1192_, 0);
lean_inc(v_size_1208_);
v_k_1209_ = lean_ctor_get(v_x_1192_, 1);
lean_inc(v_k_1209_);
v_v_1210_ = lean_ctor_get(v_x_1192_, 2);
lean_inc(v_v_1210_);
v_l_1211_ = lean_ctor_get(v_x_1192_, 3);
lean_inc(v_l_1211_);
lean_dec_ref(v_x_1192_);
v___x_1212_ = lean_apply_5(v_h__2_1195_, v_size_1208_, v_k_1209_, v_v_1210_, v_l_1211_, v_x_1193_);
return v___x_1212_;
}
}
else
{
lean_object* v___x_1213_; 
lean_dec(v_h__3_1196_);
lean_dec(v_h__2_1195_);
v___x_1213_ = lean_apply_1(v_h__1_1194_, v_x_1193_);
return v___x_1213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1214_, lean_object* v_00_u03b2_1215_, lean_object* v_motive_1216_, lean_object* v_x_1217_, lean_object* v_x_1218_, lean_object* v_h__1_1219_, lean_object* v_h__2_1220_, lean_object* v_h__3_1221_){
_start:
{
if (lean_obj_tag(v_x_1217_) == 0)
{
lean_object* v_r_1222_; 
lean_dec(v_h__1_1219_);
v_r_1222_ = lean_ctor_get(v_x_1217_, 4);
if (lean_obj_tag(v_r_1222_) == 0)
{
lean_object* v_size_1223_; lean_object* v_k_1224_; lean_object* v_v_1225_; lean_object* v_l_1226_; lean_object* v_size_1227_; lean_object* v_k_1228_; lean_object* v_v_1229_; lean_object* v_l_1230_; lean_object* v_r_1231_; lean_object* v___x_1232_; 
lean_inc_ref(v_r_1222_);
lean_dec(v_h__2_1220_);
v_size_1223_ = lean_ctor_get(v_x_1217_, 0);
lean_inc(v_size_1223_);
v_k_1224_ = lean_ctor_get(v_x_1217_, 1);
lean_inc(v_k_1224_);
v_v_1225_ = lean_ctor_get(v_x_1217_, 2);
lean_inc(v_v_1225_);
v_l_1226_ = lean_ctor_get(v_x_1217_, 3);
lean_inc(v_l_1226_);
lean_dec_ref(v_x_1217_);
v_size_1227_ = lean_ctor_get(v_r_1222_, 0);
lean_inc(v_size_1227_);
v_k_1228_ = lean_ctor_get(v_r_1222_, 1);
lean_inc(v_k_1228_);
v_v_1229_ = lean_ctor_get(v_r_1222_, 2);
lean_inc(v_v_1229_);
v_l_1230_ = lean_ctor_get(v_r_1222_, 3);
lean_inc(v_l_1230_);
v_r_1231_ = lean_ctor_get(v_r_1222_, 4);
lean_inc(v_r_1231_);
lean_dec_ref(v_r_1222_);
v___x_1232_ = lean_apply_10(v_h__3_1221_, v_size_1223_, v_k_1224_, v_v_1225_, v_l_1226_, v_size_1227_, v_k_1228_, v_v_1229_, v_l_1230_, v_r_1231_, v_x_1218_);
return v___x_1232_;
}
else
{
lean_object* v_size_1233_; lean_object* v_k_1234_; lean_object* v_v_1235_; lean_object* v_l_1236_; lean_object* v___x_1237_; 
lean_dec(v_h__3_1221_);
v_size_1233_ = lean_ctor_get(v_x_1217_, 0);
lean_inc(v_size_1233_);
v_k_1234_ = lean_ctor_get(v_x_1217_, 1);
lean_inc(v_k_1234_);
v_v_1235_ = lean_ctor_get(v_x_1217_, 2);
lean_inc(v_v_1235_);
v_l_1236_ = lean_ctor_get(v_x_1217_, 3);
lean_inc(v_l_1236_);
lean_dec_ref(v_x_1217_);
v___x_1237_ = lean_apply_5(v_h__2_1220_, v_size_1233_, v_k_1234_, v_v_1235_, v_l_1236_, v_x_1218_);
return v___x_1237_;
}
}
else
{
lean_object* v___x_1238_; 
lean_dec(v_h__3_1221_);
lean_dec(v_h__2_1220_);
v___x_1238_ = lean_apply_1(v_h__1_1219_, v_x_1218_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object* v_x_1239_, lean_object* v_h__1_1240_, lean_object* v_h__2_1241_){
_start:
{
lean_object* v_r_1242_; 
v_r_1242_ = lean_ctor_get(v_x_1239_, 4);
if (lean_obj_tag(v_r_1242_) == 0)
{
lean_object* v_size_1243_; lean_object* v_k_1244_; lean_object* v_v_1245_; lean_object* v_l_1246_; lean_object* v_size_1247_; lean_object* v_k_1248_; lean_object* v_v_1249_; lean_object* v_l_1250_; lean_object* v_r_1251_; lean_object* v___x_1252_; 
lean_inc_ref(v_r_1242_);
lean_dec(v_h__1_1240_);
v_size_1243_ = lean_ctor_get(v_x_1239_, 0);
lean_inc(v_size_1243_);
v_k_1244_ = lean_ctor_get(v_x_1239_, 1);
lean_inc(v_k_1244_);
v_v_1245_ = lean_ctor_get(v_x_1239_, 2);
lean_inc(v_v_1245_);
v_l_1246_ = lean_ctor_get(v_x_1239_, 3);
lean_inc(v_l_1246_);
lean_dec(v_x_1239_);
v_size_1247_ = lean_ctor_get(v_r_1242_, 0);
lean_inc(v_size_1247_);
v_k_1248_ = lean_ctor_get(v_r_1242_, 1);
lean_inc(v_k_1248_);
v_v_1249_ = lean_ctor_get(v_r_1242_, 2);
lean_inc(v_v_1249_);
v_l_1250_ = lean_ctor_get(v_r_1242_, 3);
lean_inc(v_l_1250_);
v_r_1251_ = lean_ctor_get(v_r_1242_, 4);
lean_inc(v_r_1251_);
lean_dec_ref(v_r_1242_);
v___x_1252_ = lean_apply_10(v_h__2_1241_, v_size_1243_, v_k_1244_, v_v_1245_, v_l_1246_, v_size_1247_, v_k_1248_, v_v_1249_, v_l_1250_, v_r_1251_, lean_box(0));
return v___x_1252_;
}
else
{
lean_object* v_size_1253_; lean_object* v_k_1254_; lean_object* v_v_1255_; lean_object* v_l_1256_; lean_object* v___x_1257_; 
lean_dec(v_h__2_1241_);
v_size_1253_ = lean_ctor_get(v_x_1239_, 0);
lean_inc(v_size_1253_);
v_k_1254_ = lean_ctor_get(v_x_1239_, 1);
lean_inc(v_k_1254_);
v_v_1255_ = lean_ctor_get(v_x_1239_, 2);
lean_inc(v_v_1255_);
v_l_1256_ = lean_ctor_get(v_x_1239_, 3);
lean_inc(v_l_1256_);
lean_dec(v_x_1239_);
v___x_1257_ = lean_apply_5(v_h__1_1240_, v_size_1253_, v_k_1254_, v_v_1255_, v_l_1256_, lean_box(0));
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1258_, lean_object* v_00_u03b2_1259_, lean_object* v_motive_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_h__1_1263_, lean_object* v_h__2_1264_){
_start:
{
lean_object* v_r_1265_; 
v_r_1265_ = lean_ctor_get(v_x_1261_, 4);
if (lean_obj_tag(v_r_1265_) == 0)
{
lean_object* v_size_1266_; lean_object* v_k_1267_; lean_object* v_v_1268_; lean_object* v_l_1269_; lean_object* v_size_1270_; lean_object* v_k_1271_; lean_object* v_v_1272_; lean_object* v_l_1273_; lean_object* v_r_1274_; lean_object* v___x_1275_; 
lean_inc_ref(v_r_1265_);
lean_dec(v_h__1_1263_);
v_size_1266_ = lean_ctor_get(v_x_1261_, 0);
lean_inc(v_size_1266_);
v_k_1267_ = lean_ctor_get(v_x_1261_, 1);
lean_inc(v_k_1267_);
v_v_1268_ = lean_ctor_get(v_x_1261_, 2);
lean_inc(v_v_1268_);
v_l_1269_ = lean_ctor_get(v_x_1261_, 3);
lean_inc(v_l_1269_);
lean_dec(v_x_1261_);
v_size_1270_ = lean_ctor_get(v_r_1265_, 0);
lean_inc(v_size_1270_);
v_k_1271_ = lean_ctor_get(v_r_1265_, 1);
lean_inc(v_k_1271_);
v_v_1272_ = lean_ctor_get(v_r_1265_, 2);
lean_inc(v_v_1272_);
v_l_1273_ = lean_ctor_get(v_r_1265_, 3);
lean_inc(v_l_1273_);
v_r_1274_ = lean_ctor_get(v_r_1265_, 4);
lean_inc(v_r_1274_);
lean_dec_ref(v_r_1265_);
v___x_1275_ = lean_apply_10(v_h__2_1264_, v_size_1266_, v_k_1267_, v_v_1268_, v_l_1269_, v_size_1270_, v_k_1271_, v_v_1272_, v_l_1273_, v_r_1274_, lean_box(0));
return v___x_1275_;
}
else
{
lean_object* v_size_1276_; lean_object* v_k_1277_; lean_object* v_v_1278_; lean_object* v_l_1279_; lean_object* v___x_1280_; 
lean_dec(v_h__2_1264_);
v_size_1276_ = lean_ctor_get(v_x_1261_, 0);
lean_inc(v_size_1276_);
v_k_1277_ = lean_ctor_get(v_x_1261_, 1);
lean_inc(v_k_1277_);
v_v_1278_ = lean_ctor_get(v_x_1261_, 2);
lean_inc(v_v_1278_);
v_l_1279_ = lean_ctor_get(v_x_1261_, 3);
lean_inc(v_l_1279_);
lean_dec(v_x_1261_);
v___x_1280_ = lean_apply_5(v_h__1_1263_, v_size_1276_, v_k_1277_, v_v_1278_, v_l_1279_, lean_box(0));
return v___x_1280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object* v_x_1281_, lean_object* v_x_1282_, lean_object* v_h__1_1283_, lean_object* v_h__2_1284_, lean_object* v_h__3_1285_){
_start:
{
if (lean_obj_tag(v_x_1281_) == 0)
{
lean_object* v_l_1286_; 
lean_dec(v_h__1_1283_);
v_l_1286_ = lean_ctor_get(v_x_1281_, 3);
if (lean_obj_tag(v_l_1286_) == 0)
{
lean_object* v_size_1287_; lean_object* v_k_1288_; lean_object* v_v_1289_; lean_object* v_r_1290_; lean_object* v_size_1291_; lean_object* v_k_1292_; lean_object* v_v_1293_; lean_object* v_l_1294_; lean_object* v_r_1295_; lean_object* v___x_1296_; 
lean_inc_ref(v_l_1286_);
lean_dec(v_h__2_1284_);
v_size_1287_ = lean_ctor_get(v_x_1281_, 0);
lean_inc(v_size_1287_);
v_k_1288_ = lean_ctor_get(v_x_1281_, 1);
lean_inc(v_k_1288_);
v_v_1289_ = lean_ctor_get(v_x_1281_, 2);
lean_inc(v_v_1289_);
v_r_1290_ = lean_ctor_get(v_x_1281_, 4);
lean_inc(v_r_1290_);
lean_dec_ref(v_x_1281_);
v_size_1291_ = lean_ctor_get(v_l_1286_, 0);
lean_inc(v_size_1291_);
v_k_1292_ = lean_ctor_get(v_l_1286_, 1);
lean_inc(v_k_1292_);
v_v_1293_ = lean_ctor_get(v_l_1286_, 2);
lean_inc(v_v_1293_);
v_l_1294_ = lean_ctor_get(v_l_1286_, 3);
lean_inc(v_l_1294_);
v_r_1295_ = lean_ctor_get(v_l_1286_, 4);
lean_inc(v_r_1295_);
lean_dec_ref(v_l_1286_);
v___x_1296_ = lean_apply_10(v_h__3_1285_, v_size_1287_, v_k_1288_, v_v_1289_, v_size_1291_, v_k_1292_, v_v_1293_, v_l_1294_, v_r_1295_, v_r_1290_, v_x_1282_);
return v___x_1296_;
}
else
{
lean_object* v_size_1297_; lean_object* v_k_1298_; lean_object* v_v_1299_; lean_object* v_r_1300_; lean_object* v___x_1301_; 
lean_dec(v_h__3_1285_);
v_size_1297_ = lean_ctor_get(v_x_1281_, 0);
lean_inc(v_size_1297_);
v_k_1298_ = lean_ctor_get(v_x_1281_, 1);
lean_inc(v_k_1298_);
v_v_1299_ = lean_ctor_get(v_x_1281_, 2);
lean_inc(v_v_1299_);
v_r_1300_ = lean_ctor_get(v_x_1281_, 4);
lean_inc(v_r_1300_);
lean_dec_ref(v_x_1281_);
v___x_1301_ = lean_apply_5(v_h__2_1284_, v_size_1297_, v_k_1298_, v_v_1299_, v_r_1300_, v_x_1282_);
return v___x_1301_;
}
}
else
{
lean_object* v___x_1302_; 
lean_dec(v_h__3_1285_);
lean_dec(v_h__2_1284_);
v___x_1302_ = lean_apply_1(v_h__1_1283_, v_x_1282_);
return v___x_1302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* v_00_u03b1_1303_, lean_object* v_00_u03b2_1304_, lean_object* v_motive_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_, lean_object* v_h__1_1308_, lean_object* v_h__2_1309_, lean_object* v_h__3_1310_){
_start:
{
if (lean_obj_tag(v_x_1306_) == 0)
{
lean_object* v_l_1311_; 
lean_dec(v_h__1_1308_);
v_l_1311_ = lean_ctor_get(v_x_1306_, 3);
if (lean_obj_tag(v_l_1311_) == 0)
{
lean_object* v_size_1312_; lean_object* v_k_1313_; lean_object* v_v_1314_; lean_object* v_r_1315_; lean_object* v_size_1316_; lean_object* v_k_1317_; lean_object* v_v_1318_; lean_object* v_l_1319_; lean_object* v_r_1320_; lean_object* v___x_1321_; 
lean_inc_ref(v_l_1311_);
lean_dec(v_h__2_1309_);
v_size_1312_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_size_1312_);
v_k_1313_ = lean_ctor_get(v_x_1306_, 1);
lean_inc(v_k_1313_);
v_v_1314_ = lean_ctor_get(v_x_1306_, 2);
lean_inc(v_v_1314_);
v_r_1315_ = lean_ctor_get(v_x_1306_, 4);
lean_inc(v_r_1315_);
lean_dec_ref(v_x_1306_);
v_size_1316_ = lean_ctor_get(v_l_1311_, 0);
lean_inc(v_size_1316_);
v_k_1317_ = lean_ctor_get(v_l_1311_, 1);
lean_inc(v_k_1317_);
v_v_1318_ = lean_ctor_get(v_l_1311_, 2);
lean_inc(v_v_1318_);
v_l_1319_ = lean_ctor_get(v_l_1311_, 3);
lean_inc(v_l_1319_);
v_r_1320_ = lean_ctor_get(v_l_1311_, 4);
lean_inc(v_r_1320_);
lean_dec_ref(v_l_1311_);
v___x_1321_ = lean_apply_10(v_h__3_1310_, v_size_1312_, v_k_1313_, v_v_1314_, v_size_1316_, v_k_1317_, v_v_1318_, v_l_1319_, v_r_1320_, v_r_1315_, v_x_1307_);
return v___x_1321_;
}
else
{
lean_object* v_size_1322_; lean_object* v_k_1323_; lean_object* v_v_1324_; lean_object* v_r_1325_; lean_object* v___x_1326_; 
lean_dec(v_h__3_1310_);
v_size_1322_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_size_1322_);
v_k_1323_ = lean_ctor_get(v_x_1306_, 1);
lean_inc(v_k_1323_);
v_v_1324_ = lean_ctor_get(v_x_1306_, 2);
lean_inc(v_v_1324_);
v_r_1325_ = lean_ctor_get(v_x_1306_, 4);
lean_inc(v_r_1325_);
lean_dec_ref(v_x_1306_);
v___x_1326_ = lean_apply_5(v_h__2_1309_, v_size_1322_, v_k_1323_, v_v_1324_, v_r_1325_, v_x_1307_);
return v___x_1326_;
}
}
else
{
lean_object* v___x_1327_; 
lean_dec(v_h__3_1310_);
lean_dec(v_h__2_1309_);
v___x_1327_ = lean_apply_1(v_h__1_1308_, v_x_1307_);
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v_h__1_1330_, lean_object* v_h__2_1331_, lean_object* v_h__3_1332_){
_start:
{
if (lean_obj_tag(v_x_1328_) == 0)
{
lean_object* v_r_1333_; 
lean_dec(v_h__1_1330_);
v_r_1333_ = lean_ctor_get(v_x_1328_, 4);
if (lean_obj_tag(v_r_1333_) == 0)
{
lean_object* v_size_1334_; lean_object* v_k_1335_; lean_object* v_v_1336_; lean_object* v_l_1337_; lean_object* v_size_1338_; lean_object* v_k_1339_; lean_object* v_v_1340_; lean_object* v_l_1341_; lean_object* v_r_1342_; lean_object* v___x_1343_; 
lean_inc_ref(v_r_1333_);
lean_dec(v_h__2_1331_);
v_size_1334_ = lean_ctor_get(v_x_1328_, 0);
lean_inc(v_size_1334_);
v_k_1335_ = lean_ctor_get(v_x_1328_, 1);
lean_inc(v_k_1335_);
v_v_1336_ = lean_ctor_get(v_x_1328_, 2);
lean_inc(v_v_1336_);
v_l_1337_ = lean_ctor_get(v_x_1328_, 3);
lean_inc(v_l_1337_);
lean_dec_ref(v_x_1328_);
v_size_1338_ = lean_ctor_get(v_r_1333_, 0);
lean_inc(v_size_1338_);
v_k_1339_ = lean_ctor_get(v_r_1333_, 1);
lean_inc(v_k_1339_);
v_v_1340_ = lean_ctor_get(v_r_1333_, 2);
lean_inc(v_v_1340_);
v_l_1341_ = lean_ctor_get(v_r_1333_, 3);
lean_inc(v_l_1341_);
v_r_1342_ = lean_ctor_get(v_r_1333_, 4);
lean_inc(v_r_1342_);
lean_dec_ref(v_r_1333_);
v___x_1343_ = lean_apply_10(v_h__3_1332_, v_size_1334_, v_k_1335_, v_v_1336_, v_l_1337_, v_size_1338_, v_k_1339_, v_v_1340_, v_l_1341_, v_r_1342_, v_x_1329_);
return v___x_1343_;
}
else
{
lean_object* v_size_1344_; lean_object* v_k_1345_; lean_object* v_v_1346_; lean_object* v_l_1347_; lean_object* v___x_1348_; 
lean_dec(v_h__3_1332_);
v_size_1344_ = lean_ctor_get(v_x_1328_, 0);
lean_inc(v_size_1344_);
v_k_1345_ = lean_ctor_get(v_x_1328_, 1);
lean_inc(v_k_1345_);
v_v_1346_ = lean_ctor_get(v_x_1328_, 2);
lean_inc(v_v_1346_);
v_l_1347_ = lean_ctor_get(v_x_1328_, 3);
lean_inc(v_l_1347_);
lean_dec_ref(v_x_1328_);
v___x_1348_ = lean_apply_5(v_h__2_1331_, v_size_1344_, v_k_1345_, v_v_1346_, v_l_1347_, v_x_1329_);
return v___x_1348_;
}
}
else
{
lean_object* v___x_1349_; 
lean_dec(v_h__3_1332_);
lean_dec(v_h__2_1331_);
v___x_1349_ = lean_apply_1(v_h__1_1330_, v_x_1329_);
return v___x_1349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object* v_00_u03b1_1350_, lean_object* v_00_u03b2_1351_, lean_object* v_motive_1352_, lean_object* v_x_1353_, lean_object* v_x_1354_, lean_object* v_h__1_1355_, lean_object* v_h__2_1356_, lean_object* v_h__3_1357_){
_start:
{
if (lean_obj_tag(v_x_1353_) == 0)
{
lean_object* v_r_1358_; 
lean_dec(v_h__1_1355_);
v_r_1358_ = lean_ctor_get(v_x_1353_, 4);
if (lean_obj_tag(v_r_1358_) == 0)
{
lean_object* v_size_1359_; lean_object* v_k_1360_; lean_object* v_v_1361_; lean_object* v_l_1362_; lean_object* v_size_1363_; lean_object* v_k_1364_; lean_object* v_v_1365_; lean_object* v_l_1366_; lean_object* v_r_1367_; lean_object* v___x_1368_; 
lean_inc_ref(v_r_1358_);
lean_dec(v_h__2_1356_);
v_size_1359_ = lean_ctor_get(v_x_1353_, 0);
lean_inc(v_size_1359_);
v_k_1360_ = lean_ctor_get(v_x_1353_, 1);
lean_inc(v_k_1360_);
v_v_1361_ = lean_ctor_get(v_x_1353_, 2);
lean_inc(v_v_1361_);
v_l_1362_ = lean_ctor_get(v_x_1353_, 3);
lean_inc(v_l_1362_);
lean_dec_ref(v_x_1353_);
v_size_1363_ = lean_ctor_get(v_r_1358_, 0);
lean_inc(v_size_1363_);
v_k_1364_ = lean_ctor_get(v_r_1358_, 1);
lean_inc(v_k_1364_);
v_v_1365_ = lean_ctor_get(v_r_1358_, 2);
lean_inc(v_v_1365_);
v_l_1366_ = lean_ctor_get(v_r_1358_, 3);
lean_inc(v_l_1366_);
v_r_1367_ = lean_ctor_get(v_r_1358_, 4);
lean_inc(v_r_1367_);
lean_dec_ref(v_r_1358_);
v___x_1368_ = lean_apply_10(v_h__3_1357_, v_size_1359_, v_k_1360_, v_v_1361_, v_l_1362_, v_size_1363_, v_k_1364_, v_v_1365_, v_l_1366_, v_r_1367_, v_x_1354_);
return v___x_1368_;
}
else
{
lean_object* v_size_1369_; lean_object* v_k_1370_; lean_object* v_v_1371_; lean_object* v_l_1372_; lean_object* v___x_1373_; 
lean_dec(v_h__3_1357_);
v_size_1369_ = lean_ctor_get(v_x_1353_, 0);
lean_inc(v_size_1369_);
v_k_1370_ = lean_ctor_get(v_x_1353_, 1);
lean_inc(v_k_1370_);
v_v_1371_ = lean_ctor_get(v_x_1353_, 2);
lean_inc(v_v_1371_);
v_l_1372_ = lean_ctor_get(v_x_1353_, 3);
lean_inc(v_l_1372_);
lean_dec_ref(v_x_1353_);
v___x_1373_ = lean_apply_5(v_h__2_1356_, v_size_1369_, v_k_1370_, v_v_1371_, v_l_1372_, v_x_1354_);
return v___x_1373_;
}
}
else
{
lean_object* v___x_1374_; 
lean_dec(v_h__3_1357_);
lean_dec(v_h__2_1356_);
v___x_1374_ = lean_apply_1(v_h__1_1355_, v_x_1354_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1375_, lean_object* v_h__1_1376_, lean_object* v_h__2_1377_, lean_object* v_h__3_1378_){
_start:
{
if (lean_obj_tag(v_x_1375_) == 0)
{
lean_object* v_l_1379_; 
lean_dec(v_h__1_1376_);
v_l_1379_ = lean_ctor_get(v_x_1375_, 3);
if (lean_obj_tag(v_l_1379_) == 0)
{
lean_object* v_size_1380_; lean_object* v_k_1381_; lean_object* v_v_1382_; lean_object* v_r_1383_; lean_object* v_size_1384_; lean_object* v_k_1385_; lean_object* v_v_1386_; lean_object* v_l_1387_; lean_object* v_r_1388_; lean_object* v___x_1389_; 
lean_inc_ref(v_l_1379_);
lean_dec(v_h__2_1377_);
v_size_1380_ = lean_ctor_get(v_x_1375_, 0);
lean_inc(v_size_1380_);
v_k_1381_ = lean_ctor_get(v_x_1375_, 1);
lean_inc(v_k_1381_);
v_v_1382_ = lean_ctor_get(v_x_1375_, 2);
lean_inc(v_v_1382_);
v_r_1383_ = lean_ctor_get(v_x_1375_, 4);
lean_inc(v_r_1383_);
lean_dec_ref(v_x_1375_);
v_size_1384_ = lean_ctor_get(v_l_1379_, 0);
lean_inc(v_size_1384_);
v_k_1385_ = lean_ctor_get(v_l_1379_, 1);
lean_inc(v_k_1385_);
v_v_1386_ = lean_ctor_get(v_l_1379_, 2);
lean_inc(v_v_1386_);
v_l_1387_ = lean_ctor_get(v_l_1379_, 3);
lean_inc(v_l_1387_);
v_r_1388_ = lean_ctor_get(v_l_1379_, 4);
lean_inc(v_r_1388_);
lean_dec_ref(v_l_1379_);
v___x_1389_ = lean_apply_9(v_h__3_1378_, v_size_1380_, v_k_1381_, v_v_1382_, v_size_1384_, v_k_1385_, v_v_1386_, v_l_1387_, v_r_1388_, v_r_1383_);
return v___x_1389_;
}
else
{
lean_object* v_size_1390_; lean_object* v_k_1391_; lean_object* v_v_1392_; lean_object* v_r_1393_; lean_object* v___x_1394_; 
lean_dec(v_h__3_1378_);
v_size_1390_ = lean_ctor_get(v_x_1375_, 0);
lean_inc(v_size_1390_);
v_k_1391_ = lean_ctor_get(v_x_1375_, 1);
lean_inc(v_k_1391_);
v_v_1392_ = lean_ctor_get(v_x_1375_, 2);
lean_inc(v_v_1392_);
v_r_1393_ = lean_ctor_get(v_x_1375_, 4);
lean_inc(v_r_1393_);
lean_dec_ref(v_x_1375_);
v___x_1394_ = lean_apply_4(v_h__2_1377_, v_size_1390_, v_k_1391_, v_v_1392_, v_r_1393_);
return v___x_1394_;
}
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec(v_h__3_1378_);
lean_dec(v_h__2_1377_);
v___x_1395_ = lean_box(0);
v___x_1396_ = lean_apply_1(v_h__1_1376_, v___x_1395_);
return v___x_1396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1397_, lean_object* v_00_u03b2_1398_, lean_object* v_motive_1399_, lean_object* v_x_1400_, lean_object* v_h__1_1401_, lean_object* v_h__2_1402_, lean_object* v_h__3_1403_){
_start:
{
if (lean_obj_tag(v_x_1400_) == 0)
{
lean_object* v_l_1404_; 
lean_dec(v_h__1_1401_);
v_l_1404_ = lean_ctor_get(v_x_1400_, 3);
if (lean_obj_tag(v_l_1404_) == 0)
{
lean_object* v_size_1405_; lean_object* v_k_1406_; lean_object* v_v_1407_; lean_object* v_r_1408_; lean_object* v_size_1409_; lean_object* v_k_1410_; lean_object* v_v_1411_; lean_object* v_l_1412_; lean_object* v_r_1413_; lean_object* v___x_1414_; 
lean_inc_ref(v_l_1404_);
lean_dec(v_h__2_1402_);
v_size_1405_ = lean_ctor_get(v_x_1400_, 0);
lean_inc(v_size_1405_);
v_k_1406_ = lean_ctor_get(v_x_1400_, 1);
lean_inc(v_k_1406_);
v_v_1407_ = lean_ctor_get(v_x_1400_, 2);
lean_inc(v_v_1407_);
v_r_1408_ = lean_ctor_get(v_x_1400_, 4);
lean_inc(v_r_1408_);
lean_dec_ref(v_x_1400_);
v_size_1409_ = lean_ctor_get(v_l_1404_, 0);
lean_inc(v_size_1409_);
v_k_1410_ = lean_ctor_get(v_l_1404_, 1);
lean_inc(v_k_1410_);
v_v_1411_ = lean_ctor_get(v_l_1404_, 2);
lean_inc(v_v_1411_);
v_l_1412_ = lean_ctor_get(v_l_1404_, 3);
lean_inc(v_l_1412_);
v_r_1413_ = lean_ctor_get(v_l_1404_, 4);
lean_inc(v_r_1413_);
lean_dec_ref(v_l_1404_);
v___x_1414_ = lean_apply_9(v_h__3_1403_, v_size_1405_, v_k_1406_, v_v_1407_, v_size_1409_, v_k_1410_, v_v_1411_, v_l_1412_, v_r_1413_, v_r_1408_);
return v___x_1414_;
}
else
{
lean_object* v_size_1415_; lean_object* v_k_1416_; lean_object* v_v_1417_; lean_object* v_r_1418_; lean_object* v___x_1419_; 
lean_dec(v_h__3_1403_);
v_size_1415_ = lean_ctor_get(v_x_1400_, 0);
lean_inc(v_size_1415_);
v_k_1416_ = lean_ctor_get(v_x_1400_, 1);
lean_inc(v_k_1416_);
v_v_1417_ = lean_ctor_get(v_x_1400_, 2);
lean_inc(v_v_1417_);
v_r_1418_ = lean_ctor_get(v_x_1400_, 4);
lean_inc(v_r_1418_);
lean_dec_ref(v_x_1400_);
v___x_1419_ = lean_apply_4(v_h__2_1402_, v_size_1415_, v_k_1416_, v_v_1417_, v_r_1418_);
return v___x_1419_;
}
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_dec(v_h__3_1403_);
lean_dec(v_h__2_1402_);
v___x_1420_ = lean_box(0);
v___x_1421_ = lean_apply_1(v_h__1_1401_, v___x_1420_);
return v___x_1421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object* v_x_1422_, lean_object* v_x_1423_, lean_object* v_h__1_1424_, lean_object* v_h__2_1425_, lean_object* v_h__3_1426_){
_start:
{
if (lean_obj_tag(v_x_1422_) == 0)
{
lean_object* v_l_1427_; 
lean_dec(v_h__1_1424_);
v_l_1427_ = lean_ctor_get(v_x_1422_, 3);
if (lean_obj_tag(v_l_1427_) == 0)
{
lean_object* v_size_1428_; lean_object* v_k_1429_; lean_object* v_v_1430_; lean_object* v_r_1431_; lean_object* v_size_1432_; lean_object* v_k_1433_; lean_object* v_v_1434_; lean_object* v_l_1435_; lean_object* v_r_1436_; lean_object* v___x_1437_; 
lean_inc_ref(v_l_1427_);
lean_dec(v_h__2_1425_);
v_size_1428_ = lean_ctor_get(v_x_1422_, 0);
lean_inc(v_size_1428_);
v_k_1429_ = lean_ctor_get(v_x_1422_, 1);
lean_inc(v_k_1429_);
v_v_1430_ = lean_ctor_get(v_x_1422_, 2);
lean_inc(v_v_1430_);
v_r_1431_ = lean_ctor_get(v_x_1422_, 4);
lean_inc(v_r_1431_);
lean_dec_ref(v_x_1422_);
v_size_1432_ = lean_ctor_get(v_l_1427_, 0);
lean_inc(v_size_1432_);
v_k_1433_ = lean_ctor_get(v_l_1427_, 1);
lean_inc(v_k_1433_);
v_v_1434_ = lean_ctor_get(v_l_1427_, 2);
lean_inc(v_v_1434_);
v_l_1435_ = lean_ctor_get(v_l_1427_, 3);
lean_inc(v_l_1435_);
v_r_1436_ = lean_ctor_get(v_l_1427_, 4);
lean_inc(v_r_1436_);
lean_dec_ref(v_l_1427_);
v___x_1437_ = lean_apply_10(v_h__3_1426_, v_size_1428_, v_k_1429_, v_v_1430_, v_size_1432_, v_k_1433_, v_v_1434_, v_l_1435_, v_r_1436_, v_r_1431_, v_x_1423_);
return v___x_1437_;
}
else
{
lean_object* v_size_1438_; lean_object* v_k_1439_; lean_object* v_v_1440_; lean_object* v_r_1441_; lean_object* v___x_1442_; 
lean_dec(v_h__3_1426_);
v_size_1438_ = lean_ctor_get(v_x_1422_, 0);
lean_inc(v_size_1438_);
v_k_1439_ = lean_ctor_get(v_x_1422_, 1);
lean_inc(v_k_1439_);
v_v_1440_ = lean_ctor_get(v_x_1422_, 2);
lean_inc(v_v_1440_);
v_r_1441_ = lean_ctor_get(v_x_1422_, 4);
lean_inc(v_r_1441_);
lean_dec_ref(v_x_1422_);
v___x_1442_ = lean_apply_5(v_h__2_1425_, v_size_1438_, v_k_1439_, v_v_1440_, v_r_1441_, v_x_1423_);
return v___x_1442_;
}
}
else
{
lean_object* v___x_1443_; 
lean_dec(v_h__3_1426_);
lean_dec(v_h__2_1425_);
v___x_1443_ = lean_apply_1(v_h__1_1424_, v_x_1423_);
return v___x_1443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1444_, lean_object* v_00_u03b2_1445_, lean_object* v_motive_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_, lean_object* v_h__1_1449_, lean_object* v_h__2_1450_, lean_object* v_h__3_1451_){
_start:
{
if (lean_obj_tag(v_x_1447_) == 0)
{
lean_object* v_l_1452_; 
lean_dec(v_h__1_1449_);
v_l_1452_ = lean_ctor_get(v_x_1447_, 3);
if (lean_obj_tag(v_l_1452_) == 0)
{
lean_object* v_size_1453_; lean_object* v_k_1454_; lean_object* v_v_1455_; lean_object* v_r_1456_; lean_object* v_size_1457_; lean_object* v_k_1458_; lean_object* v_v_1459_; lean_object* v_l_1460_; lean_object* v_r_1461_; lean_object* v___x_1462_; 
lean_inc_ref(v_l_1452_);
lean_dec(v_h__2_1450_);
v_size_1453_ = lean_ctor_get(v_x_1447_, 0);
lean_inc(v_size_1453_);
v_k_1454_ = lean_ctor_get(v_x_1447_, 1);
lean_inc(v_k_1454_);
v_v_1455_ = lean_ctor_get(v_x_1447_, 2);
lean_inc(v_v_1455_);
v_r_1456_ = lean_ctor_get(v_x_1447_, 4);
lean_inc(v_r_1456_);
lean_dec_ref(v_x_1447_);
v_size_1457_ = lean_ctor_get(v_l_1452_, 0);
lean_inc(v_size_1457_);
v_k_1458_ = lean_ctor_get(v_l_1452_, 1);
lean_inc(v_k_1458_);
v_v_1459_ = lean_ctor_get(v_l_1452_, 2);
lean_inc(v_v_1459_);
v_l_1460_ = lean_ctor_get(v_l_1452_, 3);
lean_inc(v_l_1460_);
v_r_1461_ = lean_ctor_get(v_l_1452_, 4);
lean_inc(v_r_1461_);
lean_dec_ref(v_l_1452_);
v___x_1462_ = lean_apply_10(v_h__3_1451_, v_size_1453_, v_k_1454_, v_v_1455_, v_size_1457_, v_k_1458_, v_v_1459_, v_l_1460_, v_r_1461_, v_r_1456_, v_x_1448_);
return v___x_1462_;
}
else
{
lean_object* v_size_1463_; lean_object* v_k_1464_; lean_object* v_v_1465_; lean_object* v_r_1466_; lean_object* v___x_1467_; 
lean_dec(v_h__3_1451_);
v_size_1463_ = lean_ctor_get(v_x_1447_, 0);
lean_inc(v_size_1463_);
v_k_1464_ = lean_ctor_get(v_x_1447_, 1);
lean_inc(v_k_1464_);
v_v_1465_ = lean_ctor_get(v_x_1447_, 2);
lean_inc(v_v_1465_);
v_r_1466_ = lean_ctor_get(v_x_1447_, 4);
lean_inc(v_r_1466_);
lean_dec_ref(v_x_1447_);
v___x_1467_ = lean_apply_5(v_h__2_1450_, v_size_1463_, v_k_1464_, v_v_1465_, v_r_1466_, v_x_1448_);
return v___x_1467_;
}
}
else
{
lean_object* v___x_1468_; 
lean_dec(v_h__3_1451_);
lean_dec(v_h__2_1450_);
v___x_1468_ = lean_apply_1(v_h__1_1449_, v_x_1448_);
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* v_x_1469_, lean_object* v_h__1_1470_, lean_object* v_h__2_1471_){
_start:
{
lean_object* v_l_1472_; 
v_l_1472_ = lean_ctor_get(v_x_1469_, 3);
if (lean_obj_tag(v_l_1472_) == 0)
{
lean_object* v_size_1473_; lean_object* v_k_1474_; lean_object* v_v_1475_; lean_object* v_r_1476_; lean_object* v_size_1477_; lean_object* v_k_1478_; lean_object* v_v_1479_; lean_object* v_l_1480_; lean_object* v_r_1481_; lean_object* v___x_1482_; 
lean_inc_ref(v_l_1472_);
lean_dec(v_h__1_1470_);
v_size_1473_ = lean_ctor_get(v_x_1469_, 0);
lean_inc(v_size_1473_);
v_k_1474_ = lean_ctor_get(v_x_1469_, 1);
lean_inc(v_k_1474_);
v_v_1475_ = lean_ctor_get(v_x_1469_, 2);
lean_inc(v_v_1475_);
v_r_1476_ = lean_ctor_get(v_x_1469_, 4);
lean_inc(v_r_1476_);
lean_dec(v_x_1469_);
v_size_1477_ = lean_ctor_get(v_l_1472_, 0);
lean_inc(v_size_1477_);
v_k_1478_ = lean_ctor_get(v_l_1472_, 1);
lean_inc(v_k_1478_);
v_v_1479_ = lean_ctor_get(v_l_1472_, 2);
lean_inc(v_v_1479_);
v_l_1480_ = lean_ctor_get(v_l_1472_, 3);
lean_inc(v_l_1480_);
v_r_1481_ = lean_ctor_get(v_l_1472_, 4);
lean_inc(v_r_1481_);
lean_dec_ref(v_l_1472_);
v___x_1482_ = lean_apply_10(v_h__2_1471_, v_size_1473_, v_k_1474_, v_v_1475_, v_size_1477_, v_k_1478_, v_v_1479_, v_l_1480_, v_r_1481_, v_r_1476_, lean_box(0));
return v___x_1482_;
}
else
{
lean_object* v_size_1483_; lean_object* v_k_1484_; lean_object* v_v_1485_; lean_object* v_r_1486_; lean_object* v___x_1487_; 
lean_dec(v_h__2_1471_);
v_size_1483_ = lean_ctor_get(v_x_1469_, 0);
lean_inc(v_size_1483_);
v_k_1484_ = lean_ctor_get(v_x_1469_, 1);
lean_inc(v_k_1484_);
v_v_1485_ = lean_ctor_get(v_x_1469_, 2);
lean_inc(v_v_1485_);
v_r_1486_ = lean_ctor_get(v_x_1469_, 4);
lean_inc(v_r_1486_);
lean_dec(v_x_1469_);
v___x_1487_ = lean_apply_5(v_h__1_1470_, v_size_1483_, v_k_1484_, v_v_1485_, v_r_1486_, lean_box(0));
return v___x_1487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* v_00_u03b1_1488_, lean_object* v_00_u03b2_1489_, lean_object* v_motive_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v_h__1_1493_, lean_object* v_h__2_1494_){
_start:
{
lean_object* v_l_1495_; 
v_l_1495_ = lean_ctor_get(v_x_1491_, 3);
if (lean_obj_tag(v_l_1495_) == 0)
{
lean_object* v_size_1496_; lean_object* v_k_1497_; lean_object* v_v_1498_; lean_object* v_r_1499_; lean_object* v_size_1500_; lean_object* v_k_1501_; lean_object* v_v_1502_; lean_object* v_l_1503_; lean_object* v_r_1504_; lean_object* v___x_1505_; 
lean_inc_ref(v_l_1495_);
lean_dec(v_h__1_1493_);
v_size_1496_ = lean_ctor_get(v_x_1491_, 0);
lean_inc(v_size_1496_);
v_k_1497_ = lean_ctor_get(v_x_1491_, 1);
lean_inc(v_k_1497_);
v_v_1498_ = lean_ctor_get(v_x_1491_, 2);
lean_inc(v_v_1498_);
v_r_1499_ = lean_ctor_get(v_x_1491_, 4);
lean_inc(v_r_1499_);
lean_dec(v_x_1491_);
v_size_1500_ = lean_ctor_get(v_l_1495_, 0);
lean_inc(v_size_1500_);
v_k_1501_ = lean_ctor_get(v_l_1495_, 1);
lean_inc(v_k_1501_);
v_v_1502_ = lean_ctor_get(v_l_1495_, 2);
lean_inc(v_v_1502_);
v_l_1503_ = lean_ctor_get(v_l_1495_, 3);
lean_inc(v_l_1503_);
v_r_1504_ = lean_ctor_get(v_l_1495_, 4);
lean_inc(v_r_1504_);
lean_dec_ref(v_l_1495_);
v___x_1505_ = lean_apply_10(v_h__2_1494_, v_size_1496_, v_k_1497_, v_v_1498_, v_size_1500_, v_k_1501_, v_v_1502_, v_l_1503_, v_r_1504_, v_r_1499_, lean_box(0));
return v___x_1505_;
}
else
{
lean_object* v_size_1506_; lean_object* v_k_1507_; lean_object* v_v_1508_; lean_object* v_r_1509_; lean_object* v___x_1510_; 
lean_dec(v_h__2_1494_);
v_size_1506_ = lean_ctor_get(v_x_1491_, 0);
lean_inc(v_size_1506_);
v_k_1507_ = lean_ctor_get(v_x_1491_, 1);
lean_inc(v_k_1507_);
v_v_1508_ = lean_ctor_get(v_x_1491_, 2);
lean_inc(v_v_1508_);
v_r_1509_ = lean_ctor_get(v_x_1491_, 4);
lean_inc(v_r_1509_);
lean_dec(v_x_1491_);
v___x_1510_ = lean_apply_5(v_h__1_1493_, v_size_1506_, v_k_1507_, v_v_1508_, v_r_1509_, lean_box(0));
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1511_, lean_object* v_h__1_1512_, lean_object* v_h__2_1513_, lean_object* v_h__3_1514_){
_start:
{
if (lean_obj_tag(v_x_1511_) == 0)
{
lean_object* v_r_1515_; 
lean_dec(v_h__1_1512_);
v_r_1515_ = lean_ctor_get(v_x_1511_, 4);
if (lean_obj_tag(v_r_1515_) == 0)
{
lean_object* v_size_1516_; lean_object* v_k_1517_; lean_object* v_v_1518_; lean_object* v_l_1519_; lean_object* v_size_1520_; lean_object* v_k_1521_; lean_object* v_v_1522_; lean_object* v_l_1523_; lean_object* v_r_1524_; lean_object* v___x_1525_; 
lean_inc_ref(v_r_1515_);
lean_dec(v_h__2_1513_);
v_size_1516_ = lean_ctor_get(v_x_1511_, 0);
lean_inc(v_size_1516_);
v_k_1517_ = lean_ctor_get(v_x_1511_, 1);
lean_inc(v_k_1517_);
v_v_1518_ = lean_ctor_get(v_x_1511_, 2);
lean_inc(v_v_1518_);
v_l_1519_ = lean_ctor_get(v_x_1511_, 3);
lean_inc(v_l_1519_);
lean_dec_ref(v_x_1511_);
v_size_1520_ = lean_ctor_get(v_r_1515_, 0);
lean_inc(v_size_1520_);
v_k_1521_ = lean_ctor_get(v_r_1515_, 1);
lean_inc(v_k_1521_);
v_v_1522_ = lean_ctor_get(v_r_1515_, 2);
lean_inc(v_v_1522_);
v_l_1523_ = lean_ctor_get(v_r_1515_, 3);
lean_inc(v_l_1523_);
v_r_1524_ = lean_ctor_get(v_r_1515_, 4);
lean_inc(v_r_1524_);
lean_dec_ref(v_r_1515_);
v___x_1525_ = lean_apply_9(v_h__3_1514_, v_size_1516_, v_k_1517_, v_v_1518_, v_l_1519_, v_size_1520_, v_k_1521_, v_v_1522_, v_l_1523_, v_r_1524_);
return v___x_1525_;
}
else
{
lean_object* v_size_1526_; lean_object* v_k_1527_; lean_object* v_v_1528_; lean_object* v_l_1529_; lean_object* v___x_1530_; 
lean_dec(v_h__3_1514_);
v_size_1526_ = lean_ctor_get(v_x_1511_, 0);
lean_inc(v_size_1526_);
v_k_1527_ = lean_ctor_get(v_x_1511_, 1);
lean_inc(v_k_1527_);
v_v_1528_ = lean_ctor_get(v_x_1511_, 2);
lean_inc(v_v_1528_);
v_l_1529_ = lean_ctor_get(v_x_1511_, 3);
lean_inc(v_l_1529_);
lean_dec_ref(v_x_1511_);
v___x_1530_ = lean_apply_4(v_h__2_1513_, v_size_1526_, v_k_1527_, v_v_1528_, v_l_1529_);
return v___x_1530_;
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec(v_h__3_1514_);
lean_dec(v_h__2_1513_);
v___x_1531_ = lean_box(0);
v___x_1532_ = lean_apply_1(v_h__1_1512_, v___x_1531_);
return v___x_1532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1533_, lean_object* v_00_u03b2_1534_, lean_object* v_motive_1535_, lean_object* v_x_1536_, lean_object* v_h__1_1537_, lean_object* v_h__2_1538_, lean_object* v_h__3_1539_){
_start:
{
if (lean_obj_tag(v_x_1536_) == 0)
{
lean_object* v_r_1540_; 
lean_dec(v_h__1_1537_);
v_r_1540_ = lean_ctor_get(v_x_1536_, 4);
if (lean_obj_tag(v_r_1540_) == 0)
{
lean_object* v_size_1541_; lean_object* v_k_1542_; lean_object* v_v_1543_; lean_object* v_l_1544_; lean_object* v_size_1545_; lean_object* v_k_1546_; lean_object* v_v_1547_; lean_object* v_l_1548_; lean_object* v_r_1549_; lean_object* v___x_1550_; 
lean_inc_ref(v_r_1540_);
lean_dec(v_h__2_1538_);
v_size_1541_ = lean_ctor_get(v_x_1536_, 0);
lean_inc(v_size_1541_);
v_k_1542_ = lean_ctor_get(v_x_1536_, 1);
lean_inc(v_k_1542_);
v_v_1543_ = lean_ctor_get(v_x_1536_, 2);
lean_inc(v_v_1543_);
v_l_1544_ = lean_ctor_get(v_x_1536_, 3);
lean_inc(v_l_1544_);
lean_dec_ref(v_x_1536_);
v_size_1545_ = lean_ctor_get(v_r_1540_, 0);
lean_inc(v_size_1545_);
v_k_1546_ = lean_ctor_get(v_r_1540_, 1);
lean_inc(v_k_1546_);
v_v_1547_ = lean_ctor_get(v_r_1540_, 2);
lean_inc(v_v_1547_);
v_l_1548_ = lean_ctor_get(v_r_1540_, 3);
lean_inc(v_l_1548_);
v_r_1549_ = lean_ctor_get(v_r_1540_, 4);
lean_inc(v_r_1549_);
lean_dec_ref(v_r_1540_);
v___x_1550_ = lean_apply_9(v_h__3_1539_, v_size_1541_, v_k_1542_, v_v_1543_, v_l_1544_, v_size_1545_, v_k_1546_, v_v_1547_, v_l_1548_, v_r_1549_);
return v___x_1550_;
}
else
{
lean_object* v_size_1551_; lean_object* v_k_1552_; lean_object* v_v_1553_; lean_object* v_l_1554_; lean_object* v___x_1555_; 
lean_dec(v_h__3_1539_);
v_size_1551_ = lean_ctor_get(v_x_1536_, 0);
lean_inc(v_size_1551_);
v_k_1552_ = lean_ctor_get(v_x_1536_, 1);
lean_inc(v_k_1552_);
v_v_1553_ = lean_ctor_get(v_x_1536_, 2);
lean_inc(v_v_1553_);
v_l_1554_ = lean_ctor_get(v_x_1536_, 3);
lean_inc(v_l_1554_);
lean_dec_ref(v_x_1536_);
v___x_1555_ = lean_apply_4(v_h__2_1538_, v_size_1551_, v_k_1552_, v_v_1553_, v_l_1554_);
return v___x_1555_;
}
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec(v_h__3_1539_);
lean_dec(v_h__2_1538_);
v___x_1556_ = lean_box(0);
v___x_1557_ = lean_apply_1(v_h__1_1537_, v___x_1556_);
return v___x_1557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1558_, lean_object* v_x_1559_, lean_object* v_h__1_1560_, lean_object* v_h__2_1561_, lean_object* v_h__3_1562_){
_start:
{
if (lean_obj_tag(v_x_1558_) == 0)
{
lean_object* v_r_1563_; 
lean_dec(v_h__1_1560_);
v_r_1563_ = lean_ctor_get(v_x_1558_, 4);
if (lean_obj_tag(v_r_1563_) == 0)
{
lean_object* v_size_1564_; lean_object* v_k_1565_; lean_object* v_v_1566_; lean_object* v_l_1567_; lean_object* v_size_1568_; lean_object* v_k_1569_; lean_object* v_v_1570_; lean_object* v_l_1571_; lean_object* v_r_1572_; lean_object* v___x_1573_; 
lean_inc_ref(v_r_1563_);
lean_dec(v_h__2_1561_);
v_size_1564_ = lean_ctor_get(v_x_1558_, 0);
lean_inc(v_size_1564_);
v_k_1565_ = lean_ctor_get(v_x_1558_, 1);
lean_inc(v_k_1565_);
v_v_1566_ = lean_ctor_get(v_x_1558_, 2);
lean_inc(v_v_1566_);
v_l_1567_ = lean_ctor_get(v_x_1558_, 3);
lean_inc(v_l_1567_);
lean_dec_ref(v_x_1558_);
v_size_1568_ = lean_ctor_get(v_r_1563_, 0);
lean_inc(v_size_1568_);
v_k_1569_ = lean_ctor_get(v_r_1563_, 1);
lean_inc(v_k_1569_);
v_v_1570_ = lean_ctor_get(v_r_1563_, 2);
lean_inc(v_v_1570_);
v_l_1571_ = lean_ctor_get(v_r_1563_, 3);
lean_inc(v_l_1571_);
v_r_1572_ = lean_ctor_get(v_r_1563_, 4);
lean_inc(v_r_1572_);
lean_dec_ref(v_r_1563_);
v___x_1573_ = lean_apply_10(v_h__3_1562_, v_size_1564_, v_k_1565_, v_v_1566_, v_l_1567_, v_size_1568_, v_k_1569_, v_v_1570_, v_l_1571_, v_r_1572_, v_x_1559_);
return v___x_1573_;
}
else
{
lean_object* v_size_1574_; lean_object* v_k_1575_; lean_object* v_v_1576_; lean_object* v_l_1577_; lean_object* v___x_1578_; 
lean_dec(v_h__3_1562_);
v_size_1574_ = lean_ctor_get(v_x_1558_, 0);
lean_inc(v_size_1574_);
v_k_1575_ = lean_ctor_get(v_x_1558_, 1);
lean_inc(v_k_1575_);
v_v_1576_ = lean_ctor_get(v_x_1558_, 2);
lean_inc(v_v_1576_);
v_l_1577_ = lean_ctor_get(v_x_1558_, 3);
lean_inc(v_l_1577_);
lean_dec_ref(v_x_1558_);
v___x_1578_ = lean_apply_5(v_h__2_1561_, v_size_1574_, v_k_1575_, v_v_1576_, v_l_1577_, v_x_1559_);
return v___x_1578_;
}
}
else
{
lean_object* v___x_1579_; 
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
v___x_1579_ = lean_apply_1(v_h__1_1560_, v_x_1559_);
return v___x_1579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1580_, lean_object* v_00_u03b2_1581_, lean_object* v_motive_1582_, lean_object* v_x_1583_, lean_object* v_x_1584_, lean_object* v_h__1_1585_, lean_object* v_h__2_1586_, lean_object* v_h__3_1587_){
_start:
{
if (lean_obj_tag(v_x_1583_) == 0)
{
lean_object* v_r_1588_; 
lean_dec(v_h__1_1585_);
v_r_1588_ = lean_ctor_get(v_x_1583_, 4);
if (lean_obj_tag(v_r_1588_) == 0)
{
lean_object* v_size_1589_; lean_object* v_k_1590_; lean_object* v_v_1591_; lean_object* v_l_1592_; lean_object* v_size_1593_; lean_object* v_k_1594_; lean_object* v_v_1595_; lean_object* v_l_1596_; lean_object* v_r_1597_; lean_object* v___x_1598_; 
lean_inc_ref(v_r_1588_);
lean_dec(v_h__2_1586_);
v_size_1589_ = lean_ctor_get(v_x_1583_, 0);
lean_inc(v_size_1589_);
v_k_1590_ = lean_ctor_get(v_x_1583_, 1);
lean_inc(v_k_1590_);
v_v_1591_ = lean_ctor_get(v_x_1583_, 2);
lean_inc(v_v_1591_);
v_l_1592_ = lean_ctor_get(v_x_1583_, 3);
lean_inc(v_l_1592_);
lean_dec_ref(v_x_1583_);
v_size_1593_ = lean_ctor_get(v_r_1588_, 0);
lean_inc(v_size_1593_);
v_k_1594_ = lean_ctor_get(v_r_1588_, 1);
lean_inc(v_k_1594_);
v_v_1595_ = lean_ctor_get(v_r_1588_, 2);
lean_inc(v_v_1595_);
v_l_1596_ = lean_ctor_get(v_r_1588_, 3);
lean_inc(v_l_1596_);
v_r_1597_ = lean_ctor_get(v_r_1588_, 4);
lean_inc(v_r_1597_);
lean_dec_ref(v_r_1588_);
v___x_1598_ = lean_apply_10(v_h__3_1587_, v_size_1589_, v_k_1590_, v_v_1591_, v_l_1592_, v_size_1593_, v_k_1594_, v_v_1595_, v_l_1596_, v_r_1597_, v_x_1584_);
return v___x_1598_;
}
else
{
lean_object* v_size_1599_; lean_object* v_k_1600_; lean_object* v_v_1601_; lean_object* v_l_1602_; lean_object* v___x_1603_; 
lean_dec(v_h__3_1587_);
v_size_1599_ = lean_ctor_get(v_x_1583_, 0);
lean_inc(v_size_1599_);
v_k_1600_ = lean_ctor_get(v_x_1583_, 1);
lean_inc(v_k_1600_);
v_v_1601_ = lean_ctor_get(v_x_1583_, 2);
lean_inc(v_v_1601_);
v_l_1602_ = lean_ctor_get(v_x_1583_, 3);
lean_inc(v_l_1602_);
lean_dec_ref(v_x_1583_);
v___x_1603_ = lean_apply_5(v_h__2_1586_, v_size_1599_, v_k_1600_, v_v_1601_, v_l_1602_, v_x_1584_);
return v___x_1603_;
}
}
else
{
lean_object* v___x_1604_; 
lean_dec(v_h__3_1587_);
lean_dec(v_h__2_1586_);
v___x_1604_ = lean_apply_1(v_h__1_1585_, v_x_1584_);
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* v_x_1605_, lean_object* v_h__1_1606_, lean_object* v_h__2_1607_){
_start:
{
lean_object* v_r_1608_; 
v_r_1608_ = lean_ctor_get(v_x_1605_, 4);
if (lean_obj_tag(v_r_1608_) == 0)
{
lean_object* v_size_1609_; lean_object* v_k_1610_; lean_object* v_v_1611_; lean_object* v_l_1612_; lean_object* v_size_1613_; lean_object* v_k_1614_; lean_object* v_v_1615_; lean_object* v_l_1616_; lean_object* v_r_1617_; lean_object* v___x_1618_; 
lean_inc_ref(v_r_1608_);
lean_dec(v_h__1_1606_);
v_size_1609_ = lean_ctor_get(v_x_1605_, 0);
lean_inc(v_size_1609_);
v_k_1610_ = lean_ctor_get(v_x_1605_, 1);
lean_inc(v_k_1610_);
v_v_1611_ = lean_ctor_get(v_x_1605_, 2);
lean_inc(v_v_1611_);
v_l_1612_ = lean_ctor_get(v_x_1605_, 3);
lean_inc(v_l_1612_);
lean_dec(v_x_1605_);
v_size_1613_ = lean_ctor_get(v_r_1608_, 0);
lean_inc(v_size_1613_);
v_k_1614_ = lean_ctor_get(v_r_1608_, 1);
lean_inc(v_k_1614_);
v_v_1615_ = lean_ctor_get(v_r_1608_, 2);
lean_inc(v_v_1615_);
v_l_1616_ = lean_ctor_get(v_r_1608_, 3);
lean_inc(v_l_1616_);
v_r_1617_ = lean_ctor_get(v_r_1608_, 4);
lean_inc(v_r_1617_);
lean_dec_ref(v_r_1608_);
v___x_1618_ = lean_apply_10(v_h__2_1607_, v_size_1609_, v_k_1610_, v_v_1611_, v_l_1612_, v_size_1613_, v_k_1614_, v_v_1615_, v_l_1616_, v_r_1617_, lean_box(0));
return v___x_1618_;
}
else
{
lean_object* v_size_1619_; lean_object* v_k_1620_; lean_object* v_v_1621_; lean_object* v_l_1622_; lean_object* v___x_1623_; 
lean_dec(v_h__2_1607_);
v_size_1619_ = lean_ctor_get(v_x_1605_, 0);
lean_inc(v_size_1619_);
v_k_1620_ = lean_ctor_get(v_x_1605_, 1);
lean_inc(v_k_1620_);
v_v_1621_ = lean_ctor_get(v_x_1605_, 2);
lean_inc(v_v_1621_);
v_l_1622_ = lean_ctor_get(v_x_1605_, 3);
lean_inc(v_l_1622_);
lean_dec(v_x_1605_);
v___x_1623_ = lean_apply_5(v_h__1_1606_, v_size_1619_, v_k_1620_, v_v_1621_, v_l_1622_, lean_box(0));
return v___x_1623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1624_, lean_object* v_00_u03b2_1625_, lean_object* v_motive_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_, lean_object* v_h__1_1629_, lean_object* v_h__2_1630_){
_start:
{
lean_object* v_r_1631_; 
v_r_1631_ = lean_ctor_get(v_x_1627_, 4);
if (lean_obj_tag(v_r_1631_) == 0)
{
lean_object* v_size_1632_; lean_object* v_k_1633_; lean_object* v_v_1634_; lean_object* v_l_1635_; lean_object* v_size_1636_; lean_object* v_k_1637_; lean_object* v_v_1638_; lean_object* v_l_1639_; lean_object* v_r_1640_; lean_object* v___x_1641_; 
lean_inc_ref(v_r_1631_);
lean_dec(v_h__1_1629_);
v_size_1632_ = lean_ctor_get(v_x_1627_, 0);
lean_inc(v_size_1632_);
v_k_1633_ = lean_ctor_get(v_x_1627_, 1);
lean_inc(v_k_1633_);
v_v_1634_ = lean_ctor_get(v_x_1627_, 2);
lean_inc(v_v_1634_);
v_l_1635_ = lean_ctor_get(v_x_1627_, 3);
lean_inc(v_l_1635_);
lean_dec(v_x_1627_);
v_size_1636_ = lean_ctor_get(v_r_1631_, 0);
lean_inc(v_size_1636_);
v_k_1637_ = lean_ctor_get(v_r_1631_, 1);
lean_inc(v_k_1637_);
v_v_1638_ = lean_ctor_get(v_r_1631_, 2);
lean_inc(v_v_1638_);
v_l_1639_ = lean_ctor_get(v_r_1631_, 3);
lean_inc(v_l_1639_);
v_r_1640_ = lean_ctor_get(v_r_1631_, 4);
lean_inc(v_r_1640_);
lean_dec_ref(v_r_1631_);
v___x_1641_ = lean_apply_10(v_h__2_1630_, v_size_1632_, v_k_1633_, v_v_1634_, v_l_1635_, v_size_1636_, v_k_1637_, v_v_1638_, v_l_1639_, v_r_1640_, lean_box(0));
return v___x_1641_;
}
else
{
lean_object* v_size_1642_; lean_object* v_k_1643_; lean_object* v_v_1644_; lean_object* v_l_1645_; lean_object* v___x_1646_; 
lean_dec(v_h__2_1630_);
v_size_1642_ = lean_ctor_get(v_x_1627_, 0);
lean_inc(v_size_1642_);
v_k_1643_ = lean_ctor_get(v_x_1627_, 1);
lean_inc(v_k_1643_);
v_v_1644_ = lean_ctor_get(v_x_1627_, 2);
lean_inc(v_v_1644_);
v_l_1645_ = lean_ctor_get(v_x_1627_, 3);
lean_inc(v_l_1645_);
lean_dec(v_x_1627_);
v___x_1646_ = lean_apply_5(v_h__1_1629_, v_size_1642_, v_k_1643_, v_v_1644_, v_l_1645_, lean_box(0));
return v___x_1646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object* v_l_1647_, lean_object* v_h__1_1648_, lean_object* v_h__2_1649_){
_start:
{
if (lean_obj_tag(v_l_1647_) == 0)
{
lean_object* v_size_1650_; lean_object* v_k_1651_; lean_object* v_v_1652_; lean_object* v_l_1653_; lean_object* v_r_1654_; lean_object* v___x_1655_; 
lean_dec(v_h__1_1648_);
v_size_1650_ = lean_ctor_get(v_l_1647_, 0);
lean_inc(v_size_1650_);
v_k_1651_ = lean_ctor_get(v_l_1647_, 1);
lean_inc(v_k_1651_);
v_v_1652_ = lean_ctor_get(v_l_1647_, 2);
lean_inc(v_v_1652_);
v_l_1653_ = lean_ctor_get(v_l_1647_, 3);
lean_inc(v_l_1653_);
v_r_1654_ = lean_ctor_get(v_l_1647_, 4);
lean_inc(v_r_1654_);
lean_dec_ref(v_l_1647_);
v___x_1655_ = lean_apply_7(v_h__2_1649_, v_size_1650_, v_k_1651_, v_v_1652_, v_l_1653_, v_r_1654_, lean_box(0), lean_box(0));
return v___x_1655_;
}
else
{
lean_object* v___x_1656_; 
lean_dec(v_h__2_1649_);
v___x_1656_ = lean_apply_2(v_h__1_1648_, lean_box(0), lean_box(0));
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object* v_00_u03b1_1657_, lean_object* v_00_u03b2_1658_, lean_object* v_r_1659_, lean_object* v_motive_1660_, lean_object* v_l_1661_, lean_object* v_hl_1662_, lean_object* v_hlr_1663_, lean_object* v_h__1_1664_, lean_object* v_h__2_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(v_l_1661_, v_h__1_1664_, v_h__2_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object* v_00_u03b1_1667_, lean_object* v_00_u03b2_1668_, lean_object* v_r_1669_, lean_object* v_motive_1670_, lean_object* v_l_1671_, lean_object* v_hl_1672_, lean_object* v_hlr_1673_, lean_object* v_h__1_1674_, lean_object* v_h__2_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(v_00_u03b1_1667_, v_00_u03b2_1668_, v_r_1669_, v_motive_1670_, v_l_1671_, v_hl_1672_, v_hlr_1673_, v_h__1_1674_, v_h__2_1675_);
lean_dec(v_r_1669_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(lean_object* v_x_1677_, lean_object* v_h__1_1678_){
_start:
{
lean_object* v_k_1679_; lean_object* v_v_1680_; lean_object* v_tree_1681_; lean_object* v___x_1682_; 
v_k_1679_ = lean_ctor_get(v_x_1677_, 0);
lean_inc(v_k_1679_);
v_v_1680_ = lean_ctor_get(v_x_1677_, 1);
lean_inc(v_v_1680_);
v_tree_1681_ = lean_ctor_get(v_x_1677_, 2);
lean_inc(v_tree_1681_);
lean_dec_ref(v_x_1677_);
v___x_1682_ = lean_apply_5(v_h__1_1678_, v_k_1679_, v_v_1680_, v_tree_1681_, lean_box(0), lean_box(0));
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object* v_00_u03b1_1683_, lean_object* v_00_u03b2_1684_, lean_object* v_l_x27_1685_, lean_object* v_r_x27_1686_, lean_object* v_motive_1687_, lean_object* v_x_1688_, lean_object* v_h__1_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(v_x_1688_, v_h__1_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object* v_00_u03b1_1691_, lean_object* v_00_u03b2_1692_, lean_object* v_l_x27_1693_, lean_object* v_r_x27_1694_, lean_object* v_motive_1695_, lean_object* v_x_1696_, lean_object* v_h__1_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(v_00_u03b1_1691_, v_00_u03b2_1692_, v_l_x27_1693_, v_r_x27_1694_, v_motive_1695_, v_x_1696_, v_h__1_1697_);
lean_dec(v_r_x27_1694_);
lean_dec(v_l_x27_1693_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object* v_l_1699_, lean_object* v_h__1_1700_, lean_object* v_h__2_1701_){
_start:
{
if (lean_obj_tag(v_l_1699_) == 0)
{
lean_object* v_size_1702_; lean_object* v_k_1703_; lean_object* v_v_1704_; lean_object* v_l_1705_; lean_object* v_r_1706_; lean_object* v___x_1707_; 
lean_dec(v_h__1_1700_);
v_size_1702_ = lean_ctor_get(v_l_1699_, 0);
lean_inc(v_size_1702_);
v_k_1703_ = lean_ctor_get(v_l_1699_, 1);
lean_inc(v_k_1703_);
v_v_1704_ = lean_ctor_get(v_l_1699_, 2);
lean_inc(v_v_1704_);
v_l_1705_ = lean_ctor_get(v_l_1699_, 3);
lean_inc(v_l_1705_);
v_r_1706_ = lean_ctor_get(v_l_1699_, 4);
lean_inc(v_r_1706_);
lean_dec_ref(v_l_1699_);
v___x_1707_ = lean_apply_5(v_h__2_1701_, v_size_1702_, v_k_1703_, v_v_1704_, v_l_1705_, v_r_1706_);
return v___x_1707_;
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_dec(v_h__2_1701_);
v___x_1708_ = lean_box(0);
v___x_1709_ = lean_apply_1(v_h__1_1700_, v___x_1708_);
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object* v_00_u03b1_1710_, lean_object* v_00_u03b2_1711_, lean_object* v_motive_1712_, lean_object* v_l_1713_, lean_object* v_h__1_1714_, lean_object* v_h__2_1715_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(v_l_1713_, v_h__1_1714_, v_h__2_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(lean_object* v_r_1717_, lean_object* v_h__1_1718_, lean_object* v_h__2_1719_){
_start:
{
if (lean_obj_tag(v_r_1717_) == 0)
{
lean_object* v_size_1720_; lean_object* v_k_1721_; lean_object* v_v_1722_; lean_object* v_l_1723_; lean_object* v_r_1724_; lean_object* v___x_1725_; 
lean_dec(v_h__1_1718_);
v_size_1720_ = lean_ctor_get(v_r_1717_, 0);
lean_inc(v_size_1720_);
v_k_1721_ = lean_ctor_get(v_r_1717_, 1);
lean_inc(v_k_1721_);
v_v_1722_ = lean_ctor_get(v_r_1717_, 2);
lean_inc(v_v_1722_);
v_l_1723_ = lean_ctor_get(v_r_1717_, 3);
lean_inc(v_l_1723_);
v_r_1724_ = lean_ctor_get(v_r_1717_, 4);
lean_inc(v_r_1724_);
lean_dec_ref(v_r_1717_);
v___x_1725_ = lean_apply_7(v_h__2_1719_, v_size_1720_, v_k_1721_, v_v_1722_, v_l_1723_, v_r_1724_, lean_box(0), lean_box(0));
return v___x_1725_;
}
else
{
lean_object* v___x_1726_; 
lean_dec(v_h__2_1719_);
v___x_1726_ = lean_apply_2(v_h__1_1718_, lean_box(0), lean_box(0));
return v___x_1726_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object* v_00_u03b1_1727_, lean_object* v_00_u03b2_1728_, lean_object* v_l_1729_, lean_object* v_motive_1730_, lean_object* v_r_1731_, lean_object* v_hr_1732_, lean_object* v_hlr_1733_, lean_object* v_h__1_1734_, lean_object* v_h__2_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(v_r_1731_, v_h__1_1734_, v_h__2_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object* v_00_u03b1_1737_, lean_object* v_00_u03b2_1738_, lean_object* v_l_1739_, lean_object* v_motive_1740_, lean_object* v_r_1741_, lean_object* v_hr_1742_, lean_object* v_hlr_1743_, lean_object* v_h__1_1744_, lean_object* v_h__2_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(v_00_u03b1_1737_, v_00_u03b2_1738_, v_l_1739_, v_motive_1740_, v_r_1741_, v_hr_1742_, v_hlr_1743_, v_h__1_1744_, v_h__2_1745_);
lean_dec(v_l_1739_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(lean_object* v_r_1747_, lean_object* v_h__1_1748_, lean_object* v_h__2_1749_){
_start:
{
if (lean_obj_tag(v_r_1747_) == 0)
{
lean_object* v_size_1750_; lean_object* v_k_1751_; lean_object* v_v_1752_; lean_object* v_l_1753_; lean_object* v_r_1754_; lean_object* v___x_1755_; 
lean_dec(v_h__1_1748_);
v_size_1750_ = lean_ctor_get(v_r_1747_, 0);
lean_inc(v_size_1750_);
v_k_1751_ = lean_ctor_get(v_r_1747_, 1);
lean_inc(v_k_1751_);
v_v_1752_ = lean_ctor_get(v_r_1747_, 2);
lean_inc(v_v_1752_);
v_l_1753_ = lean_ctor_get(v_r_1747_, 3);
lean_inc(v_l_1753_);
v_r_1754_ = lean_ctor_get(v_r_1747_, 4);
lean_inc(v_r_1754_);
lean_dec_ref(v_r_1747_);
v___x_1755_ = lean_apply_7(v_h__2_1749_, v_size_1750_, v_k_1751_, v_v_1752_, v_l_1753_, v_r_1754_, lean_box(0), lean_box(0));
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; 
lean_dec(v_h__2_1749_);
v___x_1756_ = lean_apply_2(v_h__1_1748_, lean_box(0), lean_box(0));
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object* v_00_u03b1_1757_, lean_object* v_00_u03b2_1758_, lean_object* v_sz_1759_, lean_object* v_k_1760_, lean_object* v_v_1761_, lean_object* v_l_x27_1762_, lean_object* v_r_x27_1763_, lean_object* v_motive_1764_, lean_object* v_r_1765_, lean_object* v_hr_1766_, lean_object* v_hlr_1767_, lean_object* v_h__1_1768_, lean_object* v_h__2_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(v_r_1765_, v_h__1_1768_, v_h__2_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object* v_00_u03b1_1771_, lean_object* v_00_u03b2_1772_, lean_object* v_sz_1773_, lean_object* v_k_1774_, lean_object* v_v_1775_, lean_object* v_l_x27_1776_, lean_object* v_r_x27_1777_, lean_object* v_motive_1778_, lean_object* v_r_1779_, lean_object* v_hr_1780_, lean_object* v_hlr_1781_, lean_object* v_h__1_1782_, lean_object* v_h__2_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(v_00_u03b1_1771_, v_00_u03b2_1772_, v_sz_1773_, v_k_1774_, v_v_1775_, v_l_x27_1776_, v_r_x27_1777_, v_motive_1778_, v_r_1779_, v_hr_1780_, v_hlr_1781_, v_h__1_1782_, v_h__2_1783_);
lean_dec(v_r_x27_1777_);
lean_dec(v_l_x27_1776_);
lean_dec(v_v_1775_);
lean_dec(v_k_1774_);
lean_dec(v_sz_1773_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object* v_t_1785_, lean_object* v_h__1_1786_, lean_object* v_h__2_1787_){
_start:
{
if (lean_obj_tag(v_t_1785_) == 0)
{
lean_object* v_size_1788_; lean_object* v_k_1789_; lean_object* v_v_1790_; lean_object* v_l_1791_; lean_object* v_r_1792_; lean_object* v___x_1793_; 
lean_dec(v_h__1_1786_);
v_size_1788_ = lean_ctor_get(v_t_1785_, 0);
lean_inc(v_size_1788_);
v_k_1789_ = lean_ctor_get(v_t_1785_, 1);
lean_inc(v_k_1789_);
v_v_1790_ = lean_ctor_get(v_t_1785_, 2);
lean_inc(v_v_1790_);
v_l_1791_ = lean_ctor_get(v_t_1785_, 3);
lean_inc(v_l_1791_);
v_r_1792_ = lean_ctor_get(v_t_1785_, 4);
lean_inc(v_r_1792_);
lean_dec_ref(v_t_1785_);
v___x_1793_ = lean_apply_6(v_h__2_1787_, v_size_1788_, v_k_1789_, v_v_1790_, v_l_1791_, v_r_1792_, lean_box(0));
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; 
lean_dec(v_h__2_1787_);
v___x_1794_ = lean_apply_1(v_h__1_1786_, lean_box(0));
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object* v_00_u03b1_1795_, lean_object* v_00_u03b2_1796_, lean_object* v_motive_1797_, lean_object* v_t_1798_, lean_object* v_hr_1799_, lean_object* v_h__1_1800_, lean_object* v_h__2_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(v_t_1798_, v_h__1_1800_, v_h__2_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t v_x_1803_, lean_object* v_h__1_1804_, lean_object* v_h__2_1805_, lean_object* v_h__3_1806_){
_start:
{
switch(v_x_1803_)
{
case 0:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec(v_h__3_1806_);
lean_dec(v_h__2_1805_);
v___x_1807_ = lean_box(0);
v___x_1808_ = lean_apply_1(v_h__1_1804_, v___x_1807_);
return v___x_1808_;
}
case 1:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec(v_h__2_1805_);
lean_dec(v_h__1_1804_);
v___x_1809_ = lean_box(0);
v___x_1810_ = lean_apply_1(v_h__3_1806_, v___x_1809_);
return v___x_1810_;
}
default: 
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
lean_dec(v_h__3_1806_);
lean_dec(v_h__1_1804_);
v___x_1811_ = lean_box(0);
v___x_1812_ = lean_apply_1(v_h__2_1805_, v___x_1811_);
return v___x_1812_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object* v_x_1813_, lean_object* v_h__1_1814_, lean_object* v_h__2_1815_, lean_object* v_h__3_1816_){
_start:
{
uint8_t v_x_30__boxed_1817_; lean_object* v_res_1818_; 
v_x_30__boxed_1817_ = lean_unbox(v_x_1813_);
v_res_1818_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_30__boxed_1817_, v_h__1_1814_, v_h__2_1815_, v_h__3_1816_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object* v_motive_1819_, uint8_t v_x_1820_, lean_object* v_h__1_1821_, lean_object* v_h__2_1822_, lean_object* v_h__3_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_1820_, v_h__1_1821_, v_h__2_1822_, v_h__3_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object* v_motive_1825_, lean_object* v_x_1826_, lean_object* v_h__1_1827_, lean_object* v_h__2_1828_, lean_object* v_h__3_1829_){
_start:
{
uint8_t v_x_45__boxed_1830_; lean_object* v_res_1831_; 
v_x_45__boxed_1830_ = lean_unbox(v_x_1826_);
v_res_1831_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_1825_, v_x_45__boxed_1830_, v_h__1_1827_, v_h__2_1828_, v_h__3_1829_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___redArg(lean_object* v_x_1832_, lean_object* v_h__1_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_apply_4(v_h__1_1833_, v_x_1832_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(lean_object* v_00_u03b1_1835_, lean_object* v_00_u03b2_1836_, lean_object* v_l_x27_1837_, lean_object* v_motive_1838_, lean_object* v_x_1839_, lean_object* v_h__1_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_apply_4(v_h__1_1840_, v_x_1839_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___boxed(lean_object* v_00_u03b1_1842_, lean_object* v_00_u03b2_1843_, lean_object* v_l_x27_1844_, lean_object* v_motive_1845_, lean_object* v_x_1846_, lean_object* v_h__1_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(v_00_u03b1_1842_, v_00_u03b2_1843_, v_l_x27_1844_, v_motive_1845_, v_x_1846_, v_h__1_1847_);
lean_dec(v_l_x27_1844_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(lean_object* v_l_1849_, lean_object* v_h__1_1850_, lean_object* v_h__2_1851_){
_start:
{
if (lean_obj_tag(v_l_1849_) == 0)
{
lean_object* v_size_1852_; lean_object* v_k_1853_; lean_object* v_v_1854_; lean_object* v_l_1855_; lean_object* v_r_1856_; lean_object* v___x_1857_; 
lean_dec(v_h__1_1850_);
v_size_1852_ = lean_ctor_get(v_l_1849_, 0);
lean_inc(v_size_1852_);
v_k_1853_ = lean_ctor_get(v_l_1849_, 1);
lean_inc(v_k_1853_);
v_v_1854_ = lean_ctor_get(v_l_1849_, 2);
lean_inc(v_v_1854_);
v_l_1855_ = lean_ctor_get(v_l_1849_, 3);
lean_inc(v_l_1855_);
v_r_1856_ = lean_ctor_get(v_l_1849_, 4);
lean_inc(v_r_1856_);
lean_dec_ref(v_l_1849_);
v___x_1857_ = lean_apply_6(v_h__2_1851_, v_size_1852_, v_k_1853_, v_v_1854_, v_l_1855_, v_r_1856_, lean_box(0));
return v___x_1857_;
}
else
{
lean_object* v___x_1858_; 
lean_dec(v_h__2_1851_);
v___x_1858_ = lean_apply_1(v_h__1_1850_, lean_box(0));
return v___x_1858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(lean_object* v_00_u03b1_1859_, lean_object* v_00_u03b2_1860_, lean_object* v_motive_1861_, lean_object* v_l_1862_, lean_object* v_hl_1863_, lean_object* v_h__1_1864_, lean_object* v_h__2_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(v_l_1862_, v_h__1_1864_, v_h__2_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object* v_x_1867_, lean_object* v_h__1_1868_, lean_object* v_h__2_1869_){
_start:
{
if (lean_obj_tag(v_x_1867_) == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
lean_dec(v_h__2_1869_);
v___x_1870_ = lean_box(0);
v___x_1871_ = lean_apply_1(v_h__1_1868_, v___x_1870_);
return v___x_1871_;
}
else
{
lean_object* v_val_1872_; lean_object* v_fst_1873_; lean_object* v_snd_1874_; lean_object* v___x_1875_; 
lean_dec(v_h__1_1868_);
v_val_1872_ = lean_ctor_get(v_x_1867_, 0);
lean_inc(v_val_1872_);
lean_dec_ref(v_x_1867_);
v_fst_1873_ = lean_ctor_get(v_val_1872_, 0);
lean_inc(v_fst_1873_);
v_snd_1874_ = lean_ctor_get(v_val_1872_, 1);
lean_inc(v_snd_1874_);
lean_dec(v_val_1872_);
v___x_1875_ = lean_apply_2(v_h__2_1869_, v_fst_1873_, v_snd_1874_);
return v___x_1875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* v_00_u03b1_1876_, lean_object* v_00_u03b2_1877_, lean_object* v_motive_1878_, lean_object* v_x_1879_, lean_object* v_h__1_1880_, lean_object* v_h__2_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(v_x_1879_, v_h__1_1880_, v_h__2_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(lean_object* v_x_1883_, lean_object* v_h__1_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_apply_4(v_h__1_1884_, v_x_1883_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(lean_object* v_00_u03b1_1886_, lean_object* v_00_u03b2_1887_, lean_object* v_l_1888_, lean_object* v_motive_1889_, lean_object* v_x_1890_, lean_object* v_h__1_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = lean_apply_4(v_h__1_1891_, v_x_1890_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(lean_object* v_00_u03b1_1893_, lean_object* v_00_u03b2_1894_, lean_object* v_l_1895_, lean_object* v_motive_1896_, lean_object* v_x_1897_, lean_object* v_h__1_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_1893_, v_00_u03b2_1894_, v_l_1895_, v_motive_1896_, v_x_1897_, v_h__1_1898_);
lean_dec(v_l_1895_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___redArg(lean_object* v_x_1900_, lean_object* v_h__1_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = lean_apply_4(v_h__1_1901_, v_x_1900_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(lean_object* v_00_u03b1_1903_, lean_object* v_00_u03b2_1904_, lean_object* v_l_1905_, lean_object* v_motive_1906_, lean_object* v_x_1907_, lean_object* v_h__1_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_apply_4(v_h__1_1908_, v_x_1907_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_1910_, lean_object* v_00_u03b2_1911_, lean_object* v_l_1912_, lean_object* v_motive_1913_, lean_object* v_x_1914_, lean_object* v_h__1_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(v_00_u03b1_1910_, v_00_u03b2_1911_, v_l_1912_, v_motive_1913_, v_x_1914_, v_h__1_1915_);
lean_dec(v_l_1912_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___redArg(lean_object* v_x_1917_, lean_object* v_h__1_1918_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_apply_3(v_h__1_1918_, v_x_1917_, lean_box(0), lean_box(0));
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(lean_object* v_00_u03b1_1920_, lean_object* v_00_u03b2_1921_, lean_object* v_l_x27_1922_, lean_object* v_motive_1923_, lean_object* v_x_1924_, lean_object* v_h__1_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_apply_3(v_h__1_1925_, v_x_1924_, lean_box(0), lean_box(0));
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___boxed(lean_object* v_00_u03b1_1927_, lean_object* v_00_u03b2_1928_, lean_object* v_l_x27_1929_, lean_object* v_motive_1930_, lean_object* v_x_1931_, lean_object* v_h__1_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(v_00_u03b1_1927_, v_00_u03b2_1928_, v_l_x27_1929_, v_motive_1930_, v_x_1931_, v_h__1_1932_);
lean_dec(v_l_x27_1929_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___redArg(lean_object* v_x_1934_, lean_object* v_h__1_1935_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_apply_3(v_h__1_1935_, v_x_1934_, lean_box(0), lean_box(0));
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(lean_object* v_00_u03b1_1937_, lean_object* v_00_u03b2_1938_, lean_object* v_r_x27_1939_, lean_object* v_motive_1940_, lean_object* v_x_1941_, lean_object* v_h__1_1942_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_apply_3(v_h__1_1942_, v_x_1941_, lean_box(0), lean_box(0));
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___boxed(lean_object* v_00_u03b1_1944_, lean_object* v_00_u03b2_1945_, lean_object* v_r_x27_1946_, lean_object* v_motive_1947_, lean_object* v_x_1948_, lean_object* v_h__1_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(v_00_u03b1_1944_, v_00_u03b2_1945_, v_r_x27_1946_, v_motive_1947_, v_x_1948_, v_h__1_1949_);
lean_dec(v_r_x27_1946_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(lean_object* v_r_1951_, lean_object* v_h__1_1952_, lean_object* v_h__2_1953_){
_start:
{
if (lean_obj_tag(v_r_1951_) == 0)
{
lean_object* v_size_1954_; lean_object* v_k_1955_; lean_object* v_v_1956_; lean_object* v_l_1957_; lean_object* v_r_1958_; lean_object* v___x_1959_; 
lean_dec(v_h__1_1952_);
v_size_1954_ = lean_ctor_get(v_r_1951_, 0);
lean_inc(v_size_1954_);
v_k_1955_ = lean_ctor_get(v_r_1951_, 1);
lean_inc(v_k_1955_);
v_v_1956_ = lean_ctor_get(v_r_1951_, 2);
lean_inc(v_v_1956_);
v_l_1957_ = lean_ctor_get(v_r_1951_, 3);
lean_inc(v_l_1957_);
v_r_1958_ = lean_ctor_get(v_r_1951_, 4);
lean_inc(v_r_1958_);
lean_dec_ref(v_r_1951_);
v___x_1959_ = lean_apply_5(v_h__2_1953_, v_size_1954_, v_k_1955_, v_v_1956_, v_l_1957_, v_r_1958_);
return v___x_1959_;
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec(v_h__2_1953_);
v___x_1960_ = lean_box(0);
v___x_1961_ = lean_apply_1(v_h__1_1952_, v___x_1960_);
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object* v_00_u03b1_1962_, lean_object* v_00_u03b2_1963_, lean_object* v_motive_1964_, lean_object* v_r_1965_, lean_object* v_h__1_1966_, lean_object* v_h__2_1967_){
_start:
{
if (lean_obj_tag(v_r_1965_) == 0)
{
lean_object* v_size_1968_; lean_object* v_k_1969_; lean_object* v_v_1970_; lean_object* v_l_1971_; lean_object* v_r_1972_; lean_object* v___x_1973_; 
lean_dec(v_h__1_1966_);
v_size_1968_ = lean_ctor_get(v_r_1965_, 0);
lean_inc(v_size_1968_);
v_k_1969_ = lean_ctor_get(v_r_1965_, 1);
lean_inc(v_k_1969_);
v_v_1970_ = lean_ctor_get(v_r_1965_, 2);
lean_inc(v_v_1970_);
v_l_1971_ = lean_ctor_get(v_r_1965_, 3);
lean_inc(v_l_1971_);
v_r_1972_ = lean_ctor_get(v_r_1965_, 4);
lean_inc(v_r_1972_);
lean_dec_ref(v_r_1965_);
v___x_1973_ = lean_apply_5(v_h__2_1967_, v_size_1968_, v_k_1969_, v_v_1970_, v_l_1971_, v_r_1972_);
return v___x_1973_;
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_dec(v_h__2_1967_);
v___x_1974_ = lean_box(0);
v___x_1975_ = lean_apply_1(v_h__1_1966_, v___x_1974_);
return v___x_1975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(lean_object* v_x_1976_, lean_object* v_h__1_1977_, lean_object* v_h__2_1978_){
_start:
{
if (lean_obj_tag(v_x_1976_) == 0)
{
lean_object* v_size_1979_; lean_object* v_k_1980_; lean_object* v_v_1981_; lean_object* v_l_1982_; lean_object* v_r_1983_; lean_object* v___x_1984_; 
lean_dec(v_h__2_1978_);
v_size_1979_ = lean_ctor_get(v_x_1976_, 0);
lean_inc(v_size_1979_);
v_k_1980_ = lean_ctor_get(v_x_1976_, 1);
lean_inc(v_k_1980_);
v_v_1981_ = lean_ctor_get(v_x_1976_, 2);
lean_inc(v_v_1981_);
v_l_1982_ = lean_ctor_get(v_x_1976_, 3);
lean_inc(v_l_1982_);
v_r_1983_ = lean_ctor_get(v_x_1976_, 4);
lean_inc(v_r_1983_);
lean_dec_ref(v_x_1976_);
v___x_1984_ = lean_apply_5(v_h__1_1977_, v_size_1979_, v_k_1980_, v_v_1981_, v_l_1982_, v_r_1983_);
return v___x_1984_;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_dec(v_h__1_1977_);
v___x_1985_ = lean_box(0);
v___x_1986_ = lean_apply_1(v_h__2_1978_, v___x_1985_);
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(lean_object* v_00_u03b1_1987_, lean_object* v_00_u03b2_1988_, lean_object* v_motive_1989_, lean_object* v_x_1990_, lean_object* v_h__1_1991_, lean_object* v_h__2_1992_){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(v_x_1990_, v_h__1_1991_, v_h__2_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(lean_object* v_r_1994_, lean_object* v_h__1_1995_, lean_object* v_h__2_1996_){
_start:
{
if (lean_obj_tag(v_r_1994_) == 0)
{
lean_object* v_size_1997_; lean_object* v_k_1998_; lean_object* v_v_1999_; lean_object* v_l_2000_; lean_object* v_r_2001_; lean_object* v___x_2002_; 
lean_dec(v_h__1_1995_);
v_size_1997_ = lean_ctor_get(v_r_1994_, 0);
lean_inc(v_size_1997_);
v_k_1998_ = lean_ctor_get(v_r_1994_, 1);
lean_inc(v_k_1998_);
v_v_1999_ = lean_ctor_get(v_r_1994_, 2);
lean_inc(v_v_1999_);
v_l_2000_ = lean_ctor_get(v_r_1994_, 3);
lean_inc(v_l_2000_);
v_r_2001_ = lean_ctor_get(v_r_1994_, 4);
lean_inc(v_r_2001_);
lean_dec_ref(v_r_1994_);
v___x_2002_ = lean_apply_7(v_h__2_1996_, v_size_1997_, v_k_1998_, v_v_1999_, v_l_2000_, v_r_2001_, lean_box(0), lean_box(0));
return v___x_2002_;
}
else
{
lean_object* v___x_2003_; 
lean_dec(v_h__2_1996_);
v___x_2003_ = lean_apply_2(v_h__1_1995_, lean_box(0), lean_box(0));
return v___x_2003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(lean_object* v_00_u03b1_2004_, lean_object* v_00_u03b2_2005_, lean_object* v_motive_2006_, lean_object* v_r_2007_, lean_object* v_hr_2008_, lean_object* v_h__1_2009_, lean_object* v_h__2_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(v_r_2007_, v_h__1_2009_, v_h__2_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg(lean_object* v_t_2012_, lean_object* v_h__1_2013_, lean_object* v_h__2_2014_){
_start:
{
if (lean_obj_tag(v_t_2012_) == 0)
{
lean_object* v_size_2015_; lean_object* v_k_2016_; lean_object* v_v_2017_; lean_object* v_l_2018_; lean_object* v_r_2019_; lean_object* v___x_2020_; 
lean_dec(v_h__1_2013_);
v_size_2015_ = lean_ctor_get(v_t_2012_, 0);
lean_inc(v_size_2015_);
v_k_2016_ = lean_ctor_get(v_t_2012_, 1);
lean_inc(v_k_2016_);
v_v_2017_ = lean_ctor_get(v_t_2012_, 2);
lean_inc(v_v_2017_);
v_l_2018_ = lean_ctor_get(v_t_2012_, 3);
lean_inc(v_l_2018_);
v_r_2019_ = lean_ctor_get(v_t_2012_, 4);
lean_inc(v_r_2019_);
lean_dec_ref(v_t_2012_);
v___x_2020_ = lean_apply_5(v_h__2_2014_, v_size_2015_, v_k_2016_, v_v_2017_, v_l_2018_, v_r_2019_);
return v___x_2020_;
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec(v_h__2_2014_);
v___x_2021_ = lean_box(0);
v___x_2022_ = lean_apply_1(v_h__1_2013_, v___x_2021_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_2023_, lean_object* v_00_u03b4_2024_, lean_object* v_motive_2025_, lean_object* v_t_2026_, lean_object* v_h__1_2027_, lean_object* v_h__2_2028_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg(v_t_2026_, v_h__1_2027_, v_h__2_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object* v_x_2030_, lean_object* v_h__1_2031_, lean_object* v_h__2_2032_){
_start:
{
if (lean_obj_tag(v_x_2030_) == 0)
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_dec(v_h__2_2032_);
v___x_2033_ = lean_box(0);
v___x_2034_ = lean_apply_1(v_h__1_2031_, v___x_2033_);
return v___x_2034_;
}
else
{
lean_object* v_val_2035_; lean_object* v___x_2036_; 
lean_dec(v_h__1_2031_);
v_val_2035_ = lean_ctor_get(v_x_2030_, 0);
lean_inc(v_val_2035_);
lean_dec_ref(v_x_2030_);
v___x_2036_ = lean_apply_1(v_h__2_2032_, v_val_2035_);
return v___x_2036_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_2037_, lean_object* v_00_u03b2_2038_, lean_object* v_motive_2039_, lean_object* v_x_2040_, lean_object* v_h__1_2041_, lean_object* v_h__2_2042_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(v_x_2040_, v_h__1_2041_, v_h__2_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___redArg(lean_object* v_t_2044_, lean_object* v_h__1_2045_){
_start:
{
lean_object* v_size_2046_; lean_object* v_k_2047_; lean_object* v_v_2048_; lean_object* v_l_2049_; lean_object* v_r_2050_; lean_object* v___x_2051_; 
v_size_2046_ = lean_ctor_get(v_t_2044_, 0);
lean_inc(v_size_2046_);
v_k_2047_ = lean_ctor_get(v_t_2044_, 1);
lean_inc(v_k_2047_);
v_v_2048_ = lean_ctor_get(v_t_2044_, 2);
lean_inc(v_v_2048_);
v_l_2049_ = lean_ctor_get(v_t_2044_, 3);
lean_inc(v_l_2049_);
v_r_2050_ = lean_ctor_get(v_t_2044_, 4);
lean_inc(v_r_2050_);
lean_dec(v_t_2044_);
v___x_2051_ = lean_apply_6(v_h__1_2045_, v_size_2046_, v_k_2047_, v_v_2048_, v_l_2049_, v_r_2050_, lean_box(0));
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(lean_object* v_00_u03b1_2052_, lean_object* v_00_u03b4_2053_, lean_object* v_inst_2054_, lean_object* v_k_2055_, lean_object* v_motive_2056_, lean_object* v_t_2057_, lean_object* v_hlk_2058_, lean_object* v_h__1_2059_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___redArg(v_t_2057_, v_h__1_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___boxed(lean_object* v_00_u03b1_2061_, lean_object* v_00_u03b4_2062_, lean_object* v_inst_2063_, lean_object* v_k_2064_, lean_object* v_motive_2065_, lean_object* v_t_2066_, lean_object* v_hlk_2067_, lean_object* v_h__1_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(v_00_u03b1_2061_, v_00_u03b4_2062_, v_inst_2063_, v_k_2064_, v_motive_2065_, v_t_2066_, v_hlk_2067_, v_h__1_2068_);
lean_dec(v_k_2064_);
lean_dec_ref(v_inst_2063_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(lean_object* v_x_2070_, lean_object* v_x_2071_, lean_object* v_h__1_2072_){
_start:
{
lean_object* v_size_2073_; lean_object* v_k_2074_; lean_object* v_v_2075_; lean_object* v_l_2076_; lean_object* v_r_2077_; lean_object* v___x_2078_; 
v_size_2073_ = lean_ctor_get(v_x_2070_, 0);
lean_inc(v_size_2073_);
v_k_2074_ = lean_ctor_get(v_x_2070_, 1);
lean_inc(v_k_2074_);
v_v_2075_ = lean_ctor_get(v_x_2070_, 2);
lean_inc(v_v_2075_);
v_l_2076_ = lean_ctor_get(v_x_2070_, 3);
lean_inc(v_l_2076_);
v_r_2077_ = lean_ctor_get(v_x_2070_, 4);
lean_inc(v_r_2077_);
lean_dec(v_x_2070_);
v___x_2078_ = lean_apply_8(v_h__1_2072_, v_size_2073_, v_k_2074_, v_v_2075_, v_l_2076_, v_r_2077_, lean_box(0), v_x_2071_, lean_box(0));
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter(lean_object* v_00_u03b1_2079_, lean_object* v_00_u03b2_2080_, lean_object* v_motive_2081_, lean_object* v_x_2082_, lean_object* v_x_2083_, lean_object* v_x_2084_, lean_object* v_x_2085_, lean_object* v_h__1_2086_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(v_x_2082_, v_x_2084_, v_h__1_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(uint8_t v_x_2088_, lean_object* v_h__1_2089_, lean_object* v_h__2_2090_, lean_object* v_h__3_2091_){
_start:
{
switch(v_x_2088_)
{
case 0:
{
lean_object* v___x_2092_; 
lean_dec(v_h__3_2091_);
lean_dec(v_h__2_2090_);
v___x_2092_ = lean_apply_1(v_h__1_2089_, lean_box(0));
return v___x_2092_;
}
case 1:
{
lean_object* v___x_2093_; 
lean_dec(v_h__3_2091_);
lean_dec(v_h__1_2089_);
v___x_2093_ = lean_apply_1(v_h__2_2090_, lean_box(0));
return v___x_2093_;
}
default: 
{
lean_object* v___x_2094_; 
lean_dec(v_h__2_2090_);
lean_dec(v_h__1_2089_);
v___x_2094_ = lean_apply_1(v_h__3_2091_, lean_box(0));
return v___x_2094_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg___boxed(lean_object* v_x_2095_, lean_object* v_h__1_2096_, lean_object* v_h__2_2097_, lean_object* v_h__3_2098_){
_start:
{
uint8_t v_x_30__boxed_2099_; lean_object* v_res_2100_; 
v_x_30__boxed_2099_ = lean_unbox(v_x_2095_);
v_res_2100_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(v_x_30__boxed_2099_, v_h__1_2096_, v_h__2_2097_, v_h__3_2098_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(lean_object* v_motive_2101_, uint8_t v_x_2102_, lean_object* v_h__1_2103_, lean_object* v_h__2_2104_, lean_object* v_h__3_2105_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(v_x_2102_, v_h__1_2103_, v_h__2_2104_, v_h__3_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___boxed(lean_object* v_motive_2107_, lean_object* v_x_2108_, lean_object* v_h__1_2109_, lean_object* v_h__2_2110_, lean_object* v_h__3_2111_){
_start:
{
uint8_t v_x_39__boxed_2112_; lean_object* v_res_2113_; 
v_x_39__boxed_2112_ = lean_unbox(v_x_2108_);
v_res_2113_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(v_motive_2107_, v_x_39__boxed_2112_, v_h__1_2109_, v_h__2_2110_, v_h__3_2111_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object* v_x_2114_, lean_object* v_x_2115_, lean_object* v_h__1_2116_, lean_object* v_h__2_2117_){
_start:
{
if (lean_obj_tag(v_x_2114_) == 0)
{
lean_object* v_size_2118_; lean_object* v_k_2119_; lean_object* v_v_2120_; lean_object* v_l_2121_; lean_object* v_r_2122_; lean_object* v___x_2123_; 
lean_dec(v_h__1_2116_);
v_size_2118_ = lean_ctor_get(v_x_2114_, 0);
lean_inc(v_size_2118_);
v_k_2119_ = lean_ctor_get(v_x_2114_, 1);
lean_inc(v_k_2119_);
v_v_2120_ = lean_ctor_get(v_x_2114_, 2);
lean_inc(v_v_2120_);
v_l_2121_ = lean_ctor_get(v_x_2114_, 3);
lean_inc(v_l_2121_);
v_r_2122_ = lean_ctor_get(v_x_2114_, 4);
lean_inc(v_r_2122_);
lean_dec_ref(v_x_2114_);
v___x_2123_ = lean_apply_6(v_h__2_2117_, v_size_2118_, v_k_2119_, v_v_2120_, v_l_2121_, v_r_2122_, v_x_2115_);
return v___x_2123_;
}
else
{
lean_object* v___x_2124_; 
lean_dec(v_h__2_2117_);
v___x_2124_ = lean_apply_1(v_h__1_2116_, v_x_2115_);
return v___x_2124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object* v_00_u03b1_2125_, lean_object* v_00_u03b2_2126_, lean_object* v_motive_2127_, lean_object* v_x_2128_, lean_object* v_x_2129_, lean_object* v_h__1_2130_, lean_object* v_h__2_2131_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(v_x_2128_, v_x_2129_, v_h__1_2130_, v_h__2_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t v_x_2133_, lean_object* v_h__1_2134_, lean_object* v_h__2_2135_, lean_object* v_h__3_2136_){
_start:
{
switch(v_x_2133_)
{
case 0:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec(v_h__3_2136_);
lean_dec(v_h__2_2135_);
v___x_2137_ = lean_box(0);
v___x_2138_ = lean_apply_1(v_h__1_2134_, v___x_2137_);
return v___x_2138_;
}
case 1:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
lean_dec(v_h__3_2136_);
lean_dec(v_h__1_2134_);
v___x_2139_ = lean_box(0);
v___x_2140_ = lean_apply_1(v_h__2_2135_, v___x_2139_);
return v___x_2140_;
}
default: 
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_dec(v_h__2_2135_);
lean_dec(v_h__1_2134_);
v___x_2141_ = lean_box(0);
v___x_2142_ = lean_apply_1(v_h__3_2136_, v___x_2141_);
return v___x_2142_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_2143_, lean_object* v_h__1_2144_, lean_object* v_h__2_2145_, lean_object* v_h__3_2146_){
_start:
{
uint8_t v_x_30__boxed_2147_; lean_object* v_res_2148_; 
v_x_30__boxed_2147_ = lean_unbox(v_x_2143_);
v_res_2148_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_30__boxed_2147_, v_h__1_2144_, v_h__2_2145_, v_h__3_2146_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object* v_motive_2149_, uint8_t v_x_2150_, lean_object* v_h__1_2151_, lean_object* v_h__2_2152_, lean_object* v_h__3_2153_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_2150_, v_h__1_2151_, v_h__2_2152_, v_h__3_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object* v_motive_2155_, lean_object* v_x_2156_, lean_object* v_h__1_2157_, lean_object* v_h__2_2158_, lean_object* v_h__3_2159_){
_start:
{
uint8_t v_x_45__boxed_2160_; lean_object* v_res_2161_; 
v_x_45__boxed_2160_ = lean_unbox(v_x_2156_);
v_res_2161_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(v_motive_2155_, v_x_45__boxed_2160_, v_h__1_2157_, v_h__2_2158_, v_h__3_2159_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter___redArg(lean_object* v_x_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_, lean_object* v_h__1_2165_, lean_object* v_h__2_2166_){
_start:
{
if (lean_obj_tag(v_x_2162_) == 0)
{
lean_object* v_size_2167_; lean_object* v_k_2168_; lean_object* v_v_2169_; lean_object* v_l_2170_; lean_object* v_r_2171_; lean_object* v___x_2172_; 
lean_dec(v_h__1_2165_);
v_size_2167_ = lean_ctor_get(v_x_2162_, 0);
lean_inc(v_size_2167_);
v_k_2168_ = lean_ctor_get(v_x_2162_, 1);
lean_inc(v_k_2168_);
v_v_2169_ = lean_ctor_get(v_x_2162_, 2);
lean_inc(v_v_2169_);
v_l_2170_ = lean_ctor_get(v_x_2162_, 3);
lean_inc(v_l_2170_);
v_r_2171_ = lean_ctor_get(v_x_2162_, 4);
lean_inc(v_r_2171_);
lean_dec_ref(v_x_2162_);
v___x_2172_ = lean_apply_7(v_h__2_2166_, v_size_2167_, v_k_2168_, v_v_2169_, v_l_2170_, v_r_2171_, v_x_2163_, v_x_2164_);
return v___x_2172_;
}
else
{
lean_object* v___x_2173_; 
lean_dec(v_h__2_2166_);
v___x_2173_ = lean_apply_2(v_h__1_2165_, v_x_2163_, v_x_2164_);
return v___x_2173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2174_, lean_object* v_00_u03b2_2175_, lean_object* v_motive_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_, lean_object* v_x_2179_, lean_object* v_h__1_2180_, lean_object* v_h__2_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter___redArg(v_x_2177_, v_x_2178_, v_x_2179_, v_h__1_2180_, v_h__2_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter___redArg(lean_object* v_x_2183_, lean_object* v_x_2184_, lean_object* v_x_2185_, lean_object* v_h__1_2186_, lean_object* v_h__2_2187_){
_start:
{
if (lean_obj_tag(v_x_2183_) == 0)
{
lean_object* v_size_2188_; lean_object* v_k_2189_; lean_object* v_v_2190_; lean_object* v_l_2191_; lean_object* v_r_2192_; lean_object* v___x_2193_; 
lean_dec(v_h__1_2186_);
v_size_2188_ = lean_ctor_get(v_x_2183_, 0);
lean_inc(v_size_2188_);
v_k_2189_ = lean_ctor_get(v_x_2183_, 1);
lean_inc(v_k_2189_);
v_v_2190_ = lean_ctor_get(v_x_2183_, 2);
lean_inc(v_v_2190_);
v_l_2191_ = lean_ctor_get(v_x_2183_, 3);
lean_inc(v_l_2191_);
v_r_2192_ = lean_ctor_get(v_x_2183_, 4);
lean_inc(v_r_2192_);
lean_dec_ref(v_x_2183_);
v___x_2193_ = lean_apply_7(v_h__2_2187_, v_size_2188_, v_k_2189_, v_v_2190_, v_l_2191_, v_r_2192_, v_x_2184_, v_x_2185_);
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; 
lean_dec(v_h__2_2187_);
v___x_2194_ = lean_apply_2(v_h__1_2186_, v_x_2184_, v_x_2185_);
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2195_, lean_object* v_00_u03b2_2196_, lean_object* v_motive_2197_, lean_object* v_x_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_, lean_object* v_h__1_2201_, lean_object* v_h__2_2202_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter___redArg(v_x_2198_, v_x_2199_, v_x_2200_, v_h__1_2201_, v_h__2_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(lean_object* v_x_2204_, lean_object* v_c_2205_, lean_object* v_x_2206_, lean_object* v_r_2207_){
_start:
{
if (lean_obj_tag(v_c_2205_) == 0)
{
lean_object* v___x_2208_; 
v___x_2208_ = l_List_head_x3f___redArg(v_r_2207_);
return v___x_2208_;
}
else
{
lean_object* v_val_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
v_val_2209_ = lean_ctor_get(v_c_2205_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_c_2205_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v_c_2205_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_val_2209_);
lean_dec(v_c_2205_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_val_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed(lean_object* v_x_2217_, lean_object* v_c_2218_, lean_object* v_x_2219_, lean_object* v_r_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(v_x_2217_, v_c_2218_, v_x_2219_, v_r_2220_);
lean_dec(v_r_2220_);
lean_dec(v_x_2217_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(lean_object* v_inst_2223_, lean_object* v_k_2224_, lean_object* v_t_2225_){
_start:
{
lean_object* v___f_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___f_2226_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0));
v___x_2227_ = lean_apply_1(v_inst_2223_, v_k_2224_);
v___x_2228_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___x_2227_, v_t_2225_, v___f_2226_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098(lean_object* v_00_u03b1_2229_, lean_object* v_00_u03b2_2230_, lean_object* v_inst_2231_, lean_object* v_k_2232_, lean_object* v_t_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(v_inst_2231_, v_k_2232_, v_t_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(lean_object* v_x_2235_, lean_object* v_x_2236_){
_start:
{
switch(lean_obj_tag(v_x_2236_))
{
case 0:
{
lean_object* v_a_2237_; lean_object* v_a_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_a_2237_ = lean_ctor_get(v_x_2236_, 0);
lean_inc(v_a_2237_);
v_a_2238_ = lean_ctor_get(v_x_2236_, 1);
lean_inc(v_a_2238_);
lean_dec_ref(v_x_2236_);
v___x_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2239_, 0, v_a_2237_);
lean_ctor_set(v___x_2239_, 1, v_a_2238_);
v___x_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
case 1:
{
lean_object* v_a_2241_; 
v_a_2241_ = lean_ctor_get(v_x_2236_, 1);
lean_inc(v_a_2241_);
if (lean_obj_tag(v_a_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2243_; 
v_a_2242_ = lean_ctor_get(v_x_2236_, 2);
lean_inc(v_a_2242_);
lean_dec_ref(v_x_2236_);
v___x_2243_ = l_List_head_x3f___redArg(v_a_2242_);
lean_dec(v_a_2242_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_inc(v_x_2235_);
return v_x_2235_;
}
else
{
return v___x_2243_;
}
}
else
{
lean_object* v_val_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec_ref(v_x_2236_);
v_val_2244_ = lean_ctor_get(v_a_2241_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v_a_2241_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v_a_2241_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_val_2244_);
lean_dec(v_a_2241_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_val_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
default: 
{
lean_dec_ref(v_x_2236_);
lean_inc(v_x_2235_);
return v_x_2235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* v_x_2252_, lean_object* v_x_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(v_x_2252_, v_x_2253_);
lean_dec(v_x_2252_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(lean_object* v_inst_2256_, lean_object* v_k_2257_, lean_object* v_t_2258_){
_start:
{
lean_object* v___f_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___f_2259_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0));
v___x_2260_ = lean_apply_1(v_inst_2256_, v_k_2257_);
v___x_2261_ = lean_box(0);
v___x_2262_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___x_2260_, v___x_2261_, v___f_2259_, v_t_2258_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27(lean_object* v_00_u03b1_2263_, lean_object* v_00_u03b2_2264_, lean_object* v_inst_2265_, lean_object* v_k_2266_, lean_object* v_t_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(v_inst_2265_, v_k_2266_, v_t_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_x_2269_, lean_object* v_x_2270_, lean_object* v_h__1_2271_, lean_object* v_h__2_2272_, lean_object* v_h__3_2273_){
_start:
{
switch(lean_obj_tag(v_x_2270_))
{
case 0:
{
lean_object* v_a_2274_; lean_object* v_a_2275_; lean_object* v_a_2276_; lean_object* v___x_2277_; 
lean_dec(v_h__3_2273_);
lean_dec(v_h__2_2272_);
v_a_2274_ = lean_ctor_get(v_x_2270_, 0);
lean_inc(v_a_2274_);
v_a_2275_ = lean_ctor_get(v_x_2270_, 1);
lean_inc(v_a_2275_);
v_a_2276_ = lean_ctor_get(v_x_2270_, 2);
lean_inc(v_a_2276_);
lean_dec_ref(v_x_2270_);
v___x_2277_ = lean_apply_5(v_h__1_2271_, v_x_2269_, v_a_2274_, lean_box(0), v_a_2275_, v_a_2276_);
return v___x_2277_;
}
case 1:
{
lean_object* v_a_2278_; lean_object* v_a_2279_; lean_object* v_a_2280_; lean_object* v___x_2281_; 
lean_dec(v_h__3_2273_);
lean_dec(v_h__1_2271_);
v_a_2278_ = lean_ctor_get(v_x_2270_, 0);
lean_inc(v_a_2278_);
v_a_2279_ = lean_ctor_get(v_x_2270_, 1);
lean_inc(v_a_2279_);
v_a_2280_ = lean_ctor_get(v_x_2270_, 2);
lean_inc(v_a_2280_);
lean_dec_ref(v_x_2270_);
v___x_2281_ = lean_apply_4(v_h__2_2272_, v_x_2269_, v_a_2278_, v_a_2279_, v_a_2280_);
return v___x_2281_;
}
default: 
{
lean_object* v_a_2282_; lean_object* v_a_2283_; lean_object* v_a_2284_; lean_object* v___x_2285_; 
lean_dec(v_h__2_2272_);
lean_dec(v_h__1_2271_);
v_a_2282_ = lean_ctor_get(v_x_2270_, 0);
lean_inc(v_a_2282_);
v_a_2283_ = lean_ctor_get(v_x_2270_, 1);
lean_inc(v_a_2283_);
v_a_2284_ = lean_ctor_get(v_x_2270_, 2);
lean_inc(v_a_2284_);
lean_dec_ref(v_x_2270_);
v___x_2285_ = lean_apply_5(v_h__3_2273_, v_x_2269_, v_a_2282_, v_a_2283_, lean_box(0), v_a_2284_);
return v___x_2285_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_2286_, lean_object* v_00_u03b2_2287_, lean_object* v_inst_2288_, lean_object* v_k_2289_, lean_object* v_motive_2290_, lean_object* v_x_2291_, lean_object* v_x_2292_, lean_object* v_h__1_2293_, lean_object* v_h__2_2294_, lean_object* v_h__3_2295_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___redArg(v_x_2291_, v_x_2292_, v_h__1_2293_, v_h__2_2294_, v_h__3_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_2297_, lean_object* v_00_u03b2_2298_, lean_object* v_inst_2299_, lean_object* v_k_2300_, lean_object* v_motive_2301_, lean_object* v_x_2302_, lean_object* v_x_2303_, lean_object* v_h__1_2304_, lean_object* v_h__2_2305_, lean_object* v_h__3_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(v_00_u03b1_2297_, v_00_u03b2_2298_, v_inst_2299_, v_k_2300_, v_motive_2301_, v_x_2302_, v_x_2303_, v_h__1_2304_, v_h__2_2305_, v_h__3_2306_);
lean_dec(v_k_2300_);
lean_dec_ref(v_inst_2299_);
return v_res_2307_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(lean_object* v_inst_2308_, lean_object* v_k_2309_, lean_object* v_k_x27_2310_){
_start:
{
lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2311_ = lean_apply_2(v_inst_2308_, v_k_2309_, v_k_x27_2310_);
v___x_2312_ = lean_unbox(v___x_2311_);
if (v___x_2312_ == 1)
{
uint8_t v___x_2313_; 
v___x_2313_ = 2;
return v___x_2313_;
}
else
{
uint8_t v___x_2314_; 
v___x_2314_ = lean_unbox(v___x_2311_);
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed(lean_object* v_inst_2315_, lean_object* v_k_2316_, lean_object* v_k_x27_2317_){
_start:
{
uint8_t v_res_2318_; lean_object* v_r_2319_; 
v_res_2318_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(v_inst_2315_, v_k_2316_, v_k_x27_2317_);
v_r_2319_ = lean_box(v_res_2318_);
return v_r_2319_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(lean_object* v_inst_2320_, lean_object* v_k_2321_, lean_object* v_t_2322_){
_start:
{
lean_object* v___f_2323_; lean_object* v___f_2324_; lean_object* v___x_2325_; 
v___f_2323_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2323_, 0, v_inst_2320_);
lean_closure_set(v___f_2323_, 1, v_k_2321_);
v___f_2324_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0));
v___x_2325_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_2323_, v_t_2322_, v___f_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098(lean_object* v_00_u03b1_2326_, lean_object* v_00_u03b2_2327_, lean_object* v_inst_2328_, lean_object* v_k_2329_, lean_object* v_t_2330_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(v_inst_2328_, v_k_2329_, v_t_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(lean_object* v_x_2332_, lean_object* v_x_2333_){
_start:
{
switch(lean_obj_tag(v_x_2333_))
{
case 0:
{
lean_object* v_a_2334_; lean_object* v_a_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v_a_2334_ = lean_ctor_get(v_x_2333_, 0);
v_a_2335_ = lean_ctor_get(v_x_2333_, 1);
lean_inc(v_a_2335_);
lean_inc(v_a_2334_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v_a_2334_);
lean_ctor_set(v___x_2336_, 1, v_a_2335_);
v___x_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
return v___x_2337_;
}
case 1:
{
lean_object* v_a_2338_; lean_object* v___x_2339_; 
v_a_2338_ = lean_ctor_get(v_x_2333_, 2);
v___x_2339_ = l_List_head_x3f___redArg(v_a_2338_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_inc(v_x_2332_);
return v_x_2332_;
}
else
{
return v___x_2339_;
}
}
default: 
{
lean_inc(v_x_2332_);
return v_x_2332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* v_x_2340_, lean_object* v_x_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(v_x_2340_, v_x_2341_);
lean_dec_ref(v_x_2341_);
lean_dec(v_x_2340_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(lean_object* v_inst_2344_, lean_object* v_k_2345_, lean_object* v_t_2346_){
_start:
{
lean_object* v___f_2347_; lean_object* v___f_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___f_2347_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2347_, 0, v_inst_2344_);
lean_closure_set(v___f_2347_, 1, v_k_2345_);
v___f_2348_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0));
v___x_2349_ = lean_box(0);
v___x_2350_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___f_2347_, v___x_2349_, v___f_2348_, v_t_2346_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27(lean_object* v_00_u03b1_2351_, lean_object* v_00_u03b2_2352_, lean_object* v_inst_2353_, lean_object* v_k_2354_, lean_object* v_t_2355_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(v_inst_2353_, v_k_2354_, v_t_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(uint8_t v_x_2357_, lean_object* v_h__1_2358_, lean_object* v_h__2_2359_){
_start:
{
if (v_x_2357_ == 0)
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
lean_dec(v_h__2_2359_);
v___x_2360_ = lean_box(0);
v___x_2361_ = lean_apply_1(v_h__1_2358_, v___x_2360_);
return v___x_2361_;
}
else
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
lean_dec(v_h__1_2358_);
v___x_2362_ = lean_box(v_x_2357_);
v___x_2363_ = lean_apply_2(v_h__2_2359_, v___x_2362_, lean_box(0));
return v___x_2363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg___boxed(lean_object* v_x_2364_, lean_object* v_h__1_2365_, lean_object* v_h__2_2366_){
_start:
{
uint8_t v_x_17__boxed_2367_; lean_object* v_res_2368_; 
v_x_17__boxed_2367_ = lean_unbox(v_x_2364_);
v_res_2368_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(v_x_17__boxed_2367_, v_h__1_2365_, v_h__2_2366_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(lean_object* v_motive_2369_, uint8_t v_x_2370_, lean_object* v_h__1_2371_, lean_object* v_h__2_2372_){
_start:
{
if (v_x_2370_ == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec(v_h__2_2372_);
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_apply_1(v_h__1_2371_, v___x_2373_);
return v___x_2374_;
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
lean_dec(v_h__1_2371_);
v___x_2375_ = lean_box(v_x_2370_);
v___x_2376_ = lean_apply_2(v_h__2_2372_, v___x_2375_, lean_box(0));
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___boxed(lean_object* v_motive_2377_, lean_object* v_x_2378_, lean_object* v_h__1_2379_, lean_object* v_h__2_2380_){
_start:
{
uint8_t v_x_28__boxed_2381_; lean_object* v_res_2382_; 
v_x_28__boxed_2381_ = lean_unbox(v_x_2378_);
v_res_2382_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(v_motive_2377_, v_x_28__boxed_2381_, v_h__1_2379_, v_h__2_2380_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_x_2383_, lean_object* v_x_2384_, lean_object* v_h__1_2385_, lean_object* v_h__2_2386_, lean_object* v_h__3_2387_){
_start:
{
switch(lean_obj_tag(v_x_2384_))
{
case 0:
{
lean_object* v_a_2388_; lean_object* v_a_2389_; lean_object* v_a_2390_; lean_object* v___x_2391_; 
lean_dec(v_h__3_2387_);
lean_dec(v_h__2_2386_);
v_a_2388_ = lean_ctor_get(v_x_2384_, 0);
lean_inc(v_a_2388_);
v_a_2389_ = lean_ctor_get(v_x_2384_, 1);
lean_inc(v_a_2389_);
v_a_2390_ = lean_ctor_get(v_x_2384_, 2);
lean_inc(v_a_2390_);
lean_dec_ref(v_x_2384_);
v___x_2391_ = lean_apply_5(v_h__1_2385_, v_x_2383_, v_a_2388_, lean_box(0), v_a_2389_, v_a_2390_);
return v___x_2391_;
}
case 1:
{
lean_object* v_a_2392_; lean_object* v_a_2393_; lean_object* v_a_2394_; lean_object* v___x_2395_; 
lean_dec(v_h__3_2387_);
lean_dec(v_h__1_2385_);
v_a_2392_ = lean_ctor_get(v_x_2384_, 0);
lean_inc(v_a_2392_);
v_a_2393_ = lean_ctor_get(v_x_2384_, 1);
lean_inc(v_a_2393_);
v_a_2394_ = lean_ctor_get(v_x_2384_, 2);
lean_inc(v_a_2394_);
lean_dec_ref(v_x_2384_);
v___x_2395_ = lean_apply_4(v_h__2_2386_, v_x_2383_, v_a_2392_, v_a_2393_, v_a_2394_);
return v___x_2395_;
}
default: 
{
lean_object* v_a_2396_; lean_object* v_a_2397_; lean_object* v_a_2398_; lean_object* v___x_2399_; 
lean_dec(v_h__2_2386_);
lean_dec(v_h__1_2385_);
v_a_2396_ = lean_ctor_get(v_x_2384_, 0);
lean_inc(v_a_2396_);
v_a_2397_ = lean_ctor_get(v_x_2384_, 1);
lean_inc(v_a_2397_);
v_a_2398_ = lean_ctor_get(v_x_2384_, 2);
lean_inc(v_a_2398_);
lean_dec_ref(v_x_2384_);
v___x_2399_ = lean_apply_5(v_h__3_2387_, v_x_2383_, v_a_2396_, v_a_2397_, lean_box(0), v_a_2398_);
return v___x_2399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_2400_, lean_object* v_00_u03b2_2401_, lean_object* v_inst_2402_, lean_object* v_k_2403_, lean_object* v_motive_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_, lean_object* v_h__1_2407_, lean_object* v_h__2_2408_, lean_object* v_h__3_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___redArg(v_x_2405_, v_x_2406_, v_h__1_2407_, v_h__2_2408_, v_h__3_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_2411_, lean_object* v_00_u03b2_2412_, lean_object* v_inst_2413_, lean_object* v_k_2414_, lean_object* v_motive_2415_, lean_object* v_x_2416_, lean_object* v_x_2417_, lean_object* v_h__1_2418_, lean_object* v_h__2_2419_, lean_object* v_h__3_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(v_00_u03b1_2411_, v_00_u03b2_2412_, v_inst_2413_, v_k_2414_, v_motive_2415_, v_x_2416_, v_x_2417_, v_h__1_2418_, v_h__2_2419_, v_h__3_2420_);
lean_dec(v_k_2414_);
lean_dec_ref(v_inst_2413_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(uint8_t v_x_2422_, lean_object* v_h__1_2423_, lean_object* v_h__2_2424_){
_start:
{
if (v_x_2422_ == 2)
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_dec(v_h__2_2424_);
v___x_2425_ = lean_box(0);
v___x_2426_ = lean_apply_1(v_h__1_2423_, v___x_2425_);
return v___x_2426_;
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_dec(v_h__1_2423_);
v___x_2427_ = lean_box(v_x_2422_);
v___x_2428_ = lean_apply_2(v_h__2_2424_, v___x_2427_, lean_box(0));
return v___x_2428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg___boxed(lean_object* v_x_2429_, lean_object* v_h__1_2430_, lean_object* v_h__2_2431_){
_start:
{
uint8_t v_x_17__boxed_2432_; lean_object* v_res_2433_; 
v_x_17__boxed_2432_ = lean_unbox(v_x_2429_);
v_res_2433_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(v_x_17__boxed_2432_, v_h__1_2430_, v_h__2_2431_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(lean_object* v_motive_2434_, uint8_t v_x_2435_, lean_object* v_h__1_2436_, lean_object* v_h__2_2437_){
_start:
{
if (v_x_2435_ == 2)
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
lean_dec(v_h__2_2437_);
v___x_2438_ = lean_box(0);
v___x_2439_ = lean_apply_1(v_h__1_2436_, v___x_2438_);
return v___x_2439_;
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
lean_dec(v_h__1_2436_);
v___x_2440_ = lean_box(v_x_2435_);
v___x_2441_ = lean_apply_2(v_h__2_2437_, v___x_2440_, lean_box(0));
return v___x_2441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___boxed(lean_object* v_motive_2442_, lean_object* v_x_2443_, lean_object* v_h__1_2444_, lean_object* v_h__2_2445_){
_start:
{
uint8_t v_x_28__boxed_2446_; lean_object* v_res_2447_; 
v_x_28__boxed_2446_ = lean_unbox(v_x_2443_);
v_res_2447_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(v_motive_2442_, v_x_28__boxed_2446_, v_h__1_2444_, v_h__2_2445_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(uint8_t v_x_2448_, lean_object* v_h__1_2449_, lean_object* v_h__2_2450_, lean_object* v_h__3_2451_){
_start:
{
switch(v_x_2448_)
{
case 0:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
lean_dec(v_h__3_2451_);
lean_dec(v_h__2_2450_);
v___x_2452_ = lean_box(0);
v___x_2453_ = lean_apply_1(v_h__1_2449_, v___x_2452_);
return v___x_2453_;
}
case 1:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
lean_dec(v_h__3_2451_);
lean_dec(v_h__1_2449_);
v___x_2454_ = lean_box(0);
v___x_2455_ = lean_apply_1(v_h__2_2450_, v___x_2454_);
return v___x_2455_;
}
default: 
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
lean_dec(v_h__2_2450_);
lean_dec(v_h__1_2449_);
v___x_2456_ = lean_box(0);
v___x_2457_ = lean_apply_1(v_h__3_2451_, v___x_2456_);
return v___x_2457_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object* v_x_2458_, lean_object* v_h__1_2459_, lean_object* v_h__2_2460_, lean_object* v_h__3_2461_){
_start:
{
uint8_t v_x_30__boxed_2462_; lean_object* v_res_2463_; 
v_x_30__boxed_2462_ = lean_unbox(v_x_2458_);
v_res_2463_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(v_x_30__boxed_2462_, v_h__1_2459_, v_h__2_2460_, v_h__3_2461_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(lean_object* v_motive_2464_, uint8_t v_x_2465_, lean_object* v_h__1_2466_, lean_object* v_h__2_2467_, lean_object* v_h__3_2468_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(v_x_2465_, v_h__1_2466_, v_h__2_2467_, v_h__3_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___boxed(lean_object* v_motive_2470_, lean_object* v_x_2471_, lean_object* v_h__1_2472_, lean_object* v_h__2_2473_, lean_object* v_h__3_2474_){
_start:
{
uint8_t v_x_45__boxed_2475_; lean_object* v_res_2476_; 
v_x_45__boxed_2475_ = lean_unbox(v_x_2471_);
v_res_2476_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(v_motive_2470_, v_x_45__boxed_2475_, v_h__1_2472_, v_h__2_2473_, v_h__3_2474_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___redArg(lean_object* v_x_2477_, lean_object* v_h__1_2478_, lean_object* v_h__2_2479_){
_start:
{
if (lean_obj_tag(v_x_2477_) == 0)
{
lean_object* v_size_2480_; lean_object* v_k_2481_; lean_object* v_v_2482_; lean_object* v_l_2483_; lean_object* v_r_2484_; lean_object* v___x_2485_; 
lean_dec(v_h__1_2478_);
v_size_2480_ = lean_ctor_get(v_x_2477_, 0);
lean_inc(v_size_2480_);
v_k_2481_ = lean_ctor_get(v_x_2477_, 1);
lean_inc(v_k_2481_);
v_v_2482_ = lean_ctor_get(v_x_2477_, 2);
lean_inc(v_v_2482_);
v_l_2483_ = lean_ctor_get(v_x_2477_, 3);
lean_inc(v_l_2483_);
v_r_2484_ = lean_ctor_get(v_x_2477_, 4);
lean_inc(v_r_2484_);
lean_dec_ref(v_x_2477_);
v___x_2485_ = lean_apply_7(v_h__2_2479_, v_size_2480_, v_k_2481_, v_v_2482_, v_l_2483_, v_r_2484_, lean_box(0), lean_box(0));
return v___x_2485_;
}
else
{
lean_object* v___x_2486_; 
lean_dec(v_h__2_2479_);
v___x_2486_ = lean_apply_2(v_h__1_2478_, lean_box(0), lean_box(0));
return v___x_2486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(lean_object* v_00_u03b1_2487_, lean_object* v_00_u03b2_2488_, lean_object* v_inst_2489_, lean_object* v_k_2490_, lean_object* v_motive_2491_, lean_object* v_x_2492_, lean_object* v_x_2493_, lean_object* v_x_2494_, lean_object* v_h__1_2495_, lean_object* v_h__2_2496_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___redArg(v_x_2492_, v_h__1_2495_, v_h__2_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___boxed(lean_object* v_00_u03b1_2498_, lean_object* v_00_u03b2_2499_, lean_object* v_inst_2500_, lean_object* v_k_2501_, lean_object* v_motive_2502_, lean_object* v_x_2503_, lean_object* v_x_2504_, lean_object* v_x_2505_, lean_object* v_h__1_2506_, lean_object* v_h__2_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(v_00_u03b1_2498_, v_00_u03b2_2499_, v_inst_2500_, v_k_2501_, v_motive_2502_, v_x_2503_, v_x_2504_, v_x_2505_, v_h__1_2506_, v_h__2_2507_);
lean_dec(v_k_2501_);
lean_dec_ref(v_inst_2500_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___redArg(lean_object* v_x_2509_, lean_object* v_h__1_2510_, lean_object* v_h__2_2511_){
_start:
{
if (lean_obj_tag(v_x_2509_) == 0)
{
lean_object* v_size_2512_; lean_object* v_k_2513_; lean_object* v_v_2514_; lean_object* v_l_2515_; lean_object* v_r_2516_; lean_object* v___x_2517_; 
lean_dec(v_h__1_2510_);
v_size_2512_ = lean_ctor_get(v_x_2509_, 0);
lean_inc(v_size_2512_);
v_k_2513_ = lean_ctor_get(v_x_2509_, 1);
lean_inc(v_k_2513_);
v_v_2514_ = lean_ctor_get(v_x_2509_, 2);
lean_inc(v_v_2514_);
v_l_2515_ = lean_ctor_get(v_x_2509_, 3);
lean_inc(v_l_2515_);
v_r_2516_ = lean_ctor_get(v_x_2509_, 4);
lean_inc(v_r_2516_);
lean_dec_ref(v_x_2509_);
v___x_2517_ = lean_apply_7(v_h__2_2511_, v_size_2512_, v_k_2513_, v_v_2514_, v_l_2515_, v_r_2516_, lean_box(0), lean_box(0));
return v___x_2517_;
}
else
{
lean_object* v___x_2518_; 
lean_dec(v_h__2_2511_);
v___x_2518_ = lean_apply_2(v_h__1_2510_, lean_box(0), lean_box(0));
return v___x_2518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(lean_object* v_00_u03b1_2519_, lean_object* v_00_u03b2_2520_, lean_object* v_inst_2521_, lean_object* v_k_2522_, lean_object* v_motive_2523_, lean_object* v_x_2524_, lean_object* v_x_2525_, lean_object* v_x_2526_, lean_object* v_h__1_2527_, lean_object* v_h__2_2528_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___redArg(v_x_2524_, v_h__1_2527_, v_h__2_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___boxed(lean_object* v_00_u03b1_2530_, lean_object* v_00_u03b2_2531_, lean_object* v_inst_2532_, lean_object* v_k_2533_, lean_object* v_motive_2534_, lean_object* v_x_2535_, lean_object* v_x_2536_, lean_object* v_x_2537_, lean_object* v_h__1_2538_, lean_object* v_h__2_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(v_00_u03b1_2530_, v_00_u03b2_2531_, v_inst_2532_, v_k_2533_, v_motive_2534_, v_x_2535_, v_x_2536_, v_x_2537_, v_h__1_2538_, v_h__2_2539_);
lean_dec(v_k_2533_);
lean_dec_ref(v_inst_2532_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___redArg(lean_object* v_x_2541_, lean_object* v_h__1_2542_, lean_object* v_h__2_2543_){
_start:
{
if (lean_obj_tag(v_x_2541_) == 0)
{
lean_object* v_size_2544_; lean_object* v_k_2545_; lean_object* v_v_2546_; lean_object* v_l_2547_; lean_object* v_r_2548_; lean_object* v___x_2549_; 
lean_dec(v_h__1_2542_);
v_size_2544_ = lean_ctor_get(v_x_2541_, 0);
lean_inc(v_size_2544_);
v_k_2545_ = lean_ctor_get(v_x_2541_, 1);
lean_inc(v_k_2545_);
v_v_2546_ = lean_ctor_get(v_x_2541_, 2);
lean_inc(v_v_2546_);
v_l_2547_ = lean_ctor_get(v_x_2541_, 3);
lean_inc(v_l_2547_);
v_r_2548_ = lean_ctor_get(v_x_2541_, 4);
lean_inc(v_r_2548_);
lean_dec_ref(v_x_2541_);
v___x_2549_ = lean_apply_7(v_h__2_2543_, v_size_2544_, v_k_2545_, v_v_2546_, v_l_2547_, v_r_2548_, lean_box(0), lean_box(0));
return v___x_2549_;
}
else
{
lean_object* v___x_2550_; 
lean_dec(v_h__2_2543_);
v___x_2550_ = lean_apply_2(v_h__1_2542_, lean_box(0), lean_box(0));
return v___x_2550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(lean_object* v_00_u03b1_2551_, lean_object* v_00_u03b2_2552_, lean_object* v_inst_2553_, lean_object* v_k_2554_, lean_object* v_motive_2555_, lean_object* v_x_2556_, lean_object* v_x_2557_, lean_object* v_x_2558_, lean_object* v_h__1_2559_, lean_object* v_h__2_2560_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___redArg(v_x_2556_, v_h__1_2559_, v_h__2_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___boxed(lean_object* v_00_u03b1_2562_, lean_object* v_00_u03b2_2563_, lean_object* v_inst_2564_, lean_object* v_k_2565_, lean_object* v_motive_2566_, lean_object* v_x_2567_, lean_object* v_x_2568_, lean_object* v_x_2569_, lean_object* v_h__1_2570_, lean_object* v_h__2_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(v_00_u03b1_2562_, v_00_u03b2_2563_, v_inst_2564_, v_k_2565_, v_motive_2566_, v_x_2567_, v_x_2568_, v_x_2569_, v_h__1_2570_, v_h__2_2571_);
lean_dec(v_k_2565_);
lean_dec_ref(v_inst_2564_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(uint8_t v_x_2573_, lean_object* v_h__1_2574_, lean_object* v_h__2_2575_, lean_object* v_h__3_2576_){
_start:
{
switch(v_x_2573_)
{
case 0:
{
lean_object* v___x_2577_; 
lean_dec(v_h__2_2575_);
lean_dec(v_h__1_2574_);
v___x_2577_ = lean_apply_1(v_h__3_2576_, lean_box(0));
return v___x_2577_;
}
case 1:
{
lean_object* v___x_2578_; 
lean_dec(v_h__3_2576_);
lean_dec(v_h__1_2574_);
v___x_2578_ = lean_apply_1(v_h__2_2575_, lean_box(0));
return v___x_2578_;
}
default: 
{
lean_object* v___x_2579_; 
lean_dec(v_h__3_2576_);
lean_dec(v_h__2_2575_);
v___x_2579_ = lean_apply_1(v_h__1_2574_, lean_box(0));
return v___x_2579_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg___boxed(lean_object* v_x_2580_, lean_object* v_h__1_2581_, lean_object* v_h__2_2582_, lean_object* v_h__3_2583_){
_start:
{
uint8_t v_x_30__boxed_2584_; lean_object* v_res_2585_; 
v_x_30__boxed_2584_ = lean_unbox(v_x_2580_);
v_res_2585_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(v_x_30__boxed_2584_, v_h__1_2581_, v_h__2_2582_, v_h__3_2583_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(lean_object* v_motive_2586_, uint8_t v_x_2587_, lean_object* v_h__1_2588_, lean_object* v_h__2_2589_, lean_object* v_h__3_2590_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(v_x_2587_, v_h__1_2588_, v_h__2_2589_, v_h__3_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___boxed(lean_object* v_motive_2592_, lean_object* v_x_2593_, lean_object* v_h__1_2594_, lean_object* v_h__2_2595_, lean_object* v_h__3_2596_){
_start:
{
uint8_t v_x_39__boxed_2597_; lean_object* v_res_2598_; 
v_x_39__boxed_2597_ = lean_unbox(v_x_2593_);
v_res_2598_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(v_motive_2592_, v_x_39__boxed_2597_, v_h__1_2594_, v_h__2_2595_, v_h__3_2596_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___redArg(lean_object* v_x_2599_, lean_object* v_h__1_2600_, lean_object* v_h__2_2601_){
_start:
{
if (lean_obj_tag(v_x_2599_) == 0)
{
lean_object* v_size_2602_; lean_object* v_k_2603_; lean_object* v_v_2604_; lean_object* v_l_2605_; lean_object* v_r_2606_; lean_object* v___x_2607_; 
lean_dec(v_h__1_2600_);
v_size_2602_ = lean_ctor_get(v_x_2599_, 0);
lean_inc(v_size_2602_);
v_k_2603_ = lean_ctor_get(v_x_2599_, 1);
lean_inc(v_k_2603_);
v_v_2604_ = lean_ctor_get(v_x_2599_, 2);
lean_inc(v_v_2604_);
v_l_2605_ = lean_ctor_get(v_x_2599_, 3);
lean_inc(v_l_2605_);
v_r_2606_ = lean_ctor_get(v_x_2599_, 4);
lean_inc(v_r_2606_);
lean_dec_ref(v_x_2599_);
v___x_2607_ = lean_apply_7(v_h__2_2601_, v_size_2602_, v_k_2603_, v_v_2604_, v_l_2605_, v_r_2606_, lean_box(0), lean_box(0));
return v___x_2607_;
}
else
{
lean_object* v___x_2608_; 
lean_dec(v_h__2_2601_);
v___x_2608_ = lean_apply_2(v_h__1_2600_, lean_box(0), lean_box(0));
return v___x_2608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(lean_object* v_00_u03b1_2609_, lean_object* v_00_u03b2_2610_, lean_object* v_inst_2611_, lean_object* v_k_2612_, lean_object* v_motive_2613_, lean_object* v_x_2614_, lean_object* v_x_2615_, lean_object* v_x_2616_, lean_object* v_h__1_2617_, lean_object* v_h__2_2618_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___redArg(v_x_2614_, v_h__1_2617_, v_h__2_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___boxed(lean_object* v_00_u03b1_2620_, lean_object* v_00_u03b2_2621_, lean_object* v_inst_2622_, lean_object* v_k_2623_, lean_object* v_motive_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_, lean_object* v_x_2627_, lean_object* v_h__1_2628_, lean_object* v_h__2_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(v_00_u03b1_2620_, v_00_u03b2_2621_, v_inst_2622_, v_k_2623_, v_motive_2624_, v_x_2625_, v_x_2626_, v_x_2627_, v_h__1_2628_, v_h__2_2629_);
lean_dec(v_k_2623_);
lean_dec_ref(v_inst_2622_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(lean_object* v_x_2631_, lean_object* v_x_2632_, lean_object* v_h__1_2633_, lean_object* v_h__2_2634_){
_start:
{
if (lean_obj_tag(v_x_2631_) == 0)
{
lean_object* v_size_2635_; lean_object* v_k_2636_; lean_object* v_v_2637_; lean_object* v_l_2638_; lean_object* v_r_2639_; lean_object* v___x_2640_; 
lean_dec(v_h__1_2633_);
v_size_2635_ = lean_ctor_get(v_x_2631_, 0);
lean_inc(v_size_2635_);
v_k_2636_ = lean_ctor_get(v_x_2631_, 1);
lean_inc(v_k_2636_);
v_v_2637_ = lean_ctor_get(v_x_2631_, 2);
lean_inc(v_v_2637_);
v_l_2638_ = lean_ctor_get(v_x_2631_, 3);
lean_inc(v_l_2638_);
v_r_2639_ = lean_ctor_get(v_x_2631_, 4);
lean_inc(v_r_2639_);
lean_dec_ref(v_x_2631_);
v___x_2640_ = lean_apply_6(v_h__2_2634_, v_size_2635_, v_k_2636_, v_v_2637_, v_l_2638_, v_r_2639_, v_x_2632_);
return v___x_2640_;
}
else
{
lean_object* v___x_2641_; 
lean_dec(v_h__2_2634_);
v___x_2641_ = lean_apply_1(v_h__1_2633_, v_x_2632_);
return v___x_2641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter(lean_object* v_00_u03b1_2642_, lean_object* v_00_u03b2_2643_, lean_object* v_motive_2644_, lean_object* v_x_2645_, lean_object* v_x_2646_, lean_object* v_h__1_2647_, lean_object* v_h__2_2648_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(v_x_2645_, v_x_2646_, v_h__1_2647_, v_h__2_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(lean_object* v_x_2650_, lean_object* v_x_2651_, lean_object* v_h__1_2652_){
_start:
{
lean_object* v_size_2653_; lean_object* v_k_2654_; lean_object* v_v_2655_; lean_object* v_l_2656_; lean_object* v_r_2657_; lean_object* v___x_2658_; 
v_size_2653_ = lean_ctor_get(v_x_2650_, 0);
lean_inc(v_size_2653_);
v_k_2654_ = lean_ctor_get(v_x_2650_, 1);
lean_inc(v_k_2654_);
v_v_2655_ = lean_ctor_get(v_x_2650_, 2);
lean_inc(v_v_2655_);
v_l_2656_ = lean_ctor_get(v_x_2650_, 3);
lean_inc(v_l_2656_);
v_r_2657_ = lean_ctor_get(v_x_2650_, 4);
lean_inc(v_r_2657_);
lean_dec(v_x_2650_);
v___x_2658_ = lean_apply_8(v_h__1_2652_, v_size_2653_, v_k_2654_, v_v_2655_, v_l_2656_, v_r_2657_, lean_box(0), v_x_2651_, lean_box(0));
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter(lean_object* v_00_u03b1_2659_, lean_object* v_00_u03b2_2660_, lean_object* v_motive_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_, lean_object* v_x_2664_, lean_object* v_x_2665_, lean_object* v_h__1_2666_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(v_x_2662_, v_x_2664_, v_h__1_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter___redArg(lean_object* v_x_2668_, lean_object* v_x_2669_, lean_object* v_x_2670_, lean_object* v_h__1_2671_, lean_object* v_h__2_2672_){
_start:
{
if (lean_obj_tag(v_x_2668_) == 0)
{
lean_object* v_size_2673_; lean_object* v_k_2674_; lean_object* v_v_2675_; lean_object* v_l_2676_; lean_object* v_r_2677_; lean_object* v___x_2678_; 
lean_dec(v_h__1_2671_);
v_size_2673_ = lean_ctor_get(v_x_2668_, 0);
lean_inc(v_size_2673_);
v_k_2674_ = lean_ctor_get(v_x_2668_, 1);
lean_inc(v_k_2674_);
v_v_2675_ = lean_ctor_get(v_x_2668_, 2);
lean_inc(v_v_2675_);
v_l_2676_ = lean_ctor_get(v_x_2668_, 3);
lean_inc(v_l_2676_);
v_r_2677_ = lean_ctor_get(v_x_2668_, 4);
lean_inc(v_r_2677_);
lean_dec_ref(v_x_2668_);
v___x_2678_ = lean_apply_7(v_h__2_2672_, v_size_2673_, v_k_2674_, v_v_2675_, v_l_2676_, v_r_2677_, v_x_2669_, v_x_2670_);
return v___x_2678_;
}
else
{
lean_object* v___x_2679_; 
lean_dec(v_h__2_2672_);
v___x_2679_ = lean_apply_2(v_h__1_2671_, v_x_2669_, v_x_2670_);
return v___x_2679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter(lean_object* v_00_u03b1_2680_, lean_object* v_00_u03b2_2681_, lean_object* v_motive_2682_, lean_object* v_x_2683_, lean_object* v_x_2684_, lean_object* v_x_2685_, lean_object* v_h__1_2686_, lean_object* v_h__2_2687_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter___redArg(v_x_2683_, v_x_2684_, v_x_2685_, v_h__1_2686_, v_h__2_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___redArg(lean_object* v_x_2689_, lean_object* v_h__1_2690_, lean_object* v_h__2_2691_){
_start:
{
if (lean_obj_tag(v_x_2689_) == 0)
{
lean_object* v_size_2692_; lean_object* v_k_2693_; lean_object* v_v_2694_; lean_object* v_l_2695_; lean_object* v_r_2696_; lean_object* v___x_2697_; 
lean_dec(v_h__1_2690_);
v_size_2692_ = lean_ctor_get(v_x_2689_, 0);
lean_inc(v_size_2692_);
v_k_2693_ = lean_ctor_get(v_x_2689_, 1);
lean_inc(v_k_2693_);
v_v_2694_ = lean_ctor_get(v_x_2689_, 2);
lean_inc(v_v_2694_);
v_l_2695_ = lean_ctor_get(v_x_2689_, 3);
lean_inc(v_l_2695_);
v_r_2696_ = lean_ctor_get(v_x_2689_, 4);
lean_inc(v_r_2696_);
lean_dec_ref(v_x_2689_);
v___x_2697_ = lean_apply_7(v_h__2_2691_, v_size_2692_, v_k_2693_, v_v_2694_, v_l_2695_, v_r_2696_, lean_box(0), lean_box(0));
return v___x_2697_;
}
else
{
lean_object* v___x_2698_; 
lean_dec(v_h__2_2691_);
v___x_2698_ = lean_apply_2(v_h__1_2690_, lean_box(0), lean_box(0));
return v___x_2698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(lean_object* v_00_u03b1_2699_, lean_object* v_00_u03b2_2700_, lean_object* v_inst_2701_, lean_object* v_k_2702_, lean_object* v_motive_2703_, lean_object* v_x_2704_, lean_object* v_x_2705_, lean_object* v_x_2706_, lean_object* v_h__1_2707_, lean_object* v_h__2_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___redArg(v_x_2704_, v_h__1_2707_, v_h__2_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___boxed(lean_object* v_00_u03b1_2710_, lean_object* v_00_u03b2_2711_, lean_object* v_inst_2712_, lean_object* v_k_2713_, lean_object* v_motive_2714_, lean_object* v_x_2715_, lean_object* v_x_2716_, lean_object* v_x_2717_, lean_object* v_h__1_2718_, lean_object* v_h__2_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(v_00_u03b1_2710_, v_00_u03b2_2711_, v_inst_2712_, v_k_2713_, v_motive_2714_, v_x_2715_, v_x_2716_, v_x_2717_, v_h__1_2718_, v_h__2_2719_);
lean_dec(v_k_2713_);
lean_dec_ref(v_inst_2712_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___redArg(lean_object* v_x_2721_, lean_object* v_h__1_2722_, lean_object* v_h__2_2723_){
_start:
{
if (lean_obj_tag(v_x_2721_) == 0)
{
lean_object* v_size_2724_; lean_object* v_k_2725_; lean_object* v_v_2726_; lean_object* v_l_2727_; lean_object* v_r_2728_; lean_object* v___x_2729_; 
lean_dec(v_h__1_2722_);
v_size_2724_ = lean_ctor_get(v_x_2721_, 0);
lean_inc(v_size_2724_);
v_k_2725_ = lean_ctor_get(v_x_2721_, 1);
lean_inc(v_k_2725_);
v_v_2726_ = lean_ctor_get(v_x_2721_, 2);
lean_inc(v_v_2726_);
v_l_2727_ = lean_ctor_get(v_x_2721_, 3);
lean_inc(v_l_2727_);
v_r_2728_ = lean_ctor_get(v_x_2721_, 4);
lean_inc(v_r_2728_);
lean_dec_ref(v_x_2721_);
v___x_2729_ = lean_apply_7(v_h__2_2723_, v_size_2724_, v_k_2725_, v_v_2726_, v_l_2727_, v_r_2728_, lean_box(0), lean_box(0));
return v___x_2729_;
}
else
{
lean_object* v___x_2730_; 
lean_dec(v_h__2_2723_);
v___x_2730_ = lean_apply_2(v_h__1_2722_, lean_box(0), lean_box(0));
return v___x_2730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(lean_object* v_00_u03b1_2731_, lean_object* v_00_u03b2_2732_, lean_object* v_inst_2733_, lean_object* v_k_2734_, lean_object* v_motive_2735_, lean_object* v_x_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_, lean_object* v_h__1_2739_, lean_object* v_h__2_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___redArg(v_x_2736_, v_h__1_2739_, v_h__2_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___boxed(lean_object* v_00_u03b1_2742_, lean_object* v_00_u03b2_2743_, lean_object* v_inst_2744_, lean_object* v_k_2745_, lean_object* v_motive_2746_, lean_object* v_x_2747_, lean_object* v_x_2748_, lean_object* v_x_2749_, lean_object* v_h__1_2750_, lean_object* v_h__2_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(v_00_u03b1_2742_, v_00_u03b2_2743_, v_inst_2744_, v_k_2745_, v_motive_2746_, v_x_2747_, v_x_2748_, v_x_2749_, v_h__1_2750_, v_h__2_2751_);
lean_dec(v_k_2745_);
lean_dec_ref(v_inst_2744_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___redArg(lean_object* v_x_2753_, lean_object* v_h__1_2754_, lean_object* v_h__2_2755_){
_start:
{
if (lean_obj_tag(v_x_2753_) == 0)
{
lean_object* v_size_2756_; lean_object* v_k_2757_; lean_object* v_v_2758_; lean_object* v_l_2759_; lean_object* v_r_2760_; lean_object* v___x_2761_; 
lean_dec(v_h__1_2754_);
v_size_2756_ = lean_ctor_get(v_x_2753_, 0);
lean_inc(v_size_2756_);
v_k_2757_ = lean_ctor_get(v_x_2753_, 1);
lean_inc(v_k_2757_);
v_v_2758_ = lean_ctor_get(v_x_2753_, 2);
lean_inc(v_v_2758_);
v_l_2759_ = lean_ctor_get(v_x_2753_, 3);
lean_inc(v_l_2759_);
v_r_2760_ = lean_ctor_get(v_x_2753_, 4);
lean_inc(v_r_2760_);
lean_dec_ref(v_x_2753_);
v___x_2761_ = lean_apply_7(v_h__2_2755_, v_size_2756_, v_k_2757_, v_v_2758_, v_l_2759_, v_r_2760_, lean_box(0), lean_box(0));
return v___x_2761_;
}
else
{
lean_object* v___x_2762_; 
lean_dec(v_h__2_2755_);
v___x_2762_ = lean_apply_2(v_h__1_2754_, lean_box(0), lean_box(0));
return v___x_2762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(lean_object* v_00_u03b1_2763_, lean_object* v_00_u03b2_2764_, lean_object* v_inst_2765_, lean_object* v_k_2766_, lean_object* v_motive_2767_, lean_object* v_x_2768_, lean_object* v_x_2769_, lean_object* v_x_2770_, lean_object* v_h__1_2771_, lean_object* v_h__2_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___redArg(v_x_2768_, v_h__1_2771_, v_h__2_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___boxed(lean_object* v_00_u03b1_2774_, lean_object* v_00_u03b2_2775_, lean_object* v_inst_2776_, lean_object* v_k_2777_, lean_object* v_motive_2778_, lean_object* v_x_2779_, lean_object* v_x_2780_, lean_object* v_x_2781_, lean_object* v_h__1_2782_, lean_object* v_h__2_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(v_00_u03b1_2774_, v_00_u03b2_2775_, v_inst_2776_, v_k_2777_, v_motive_2778_, v_x_2779_, v_x_2780_, v_x_2781_, v_h__1_2782_, v_h__2_2783_);
lean_dec(v_k_2777_);
lean_dec_ref(v_inst_2776_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___redArg(lean_object* v_x_2785_, lean_object* v_h__1_2786_, lean_object* v_h__2_2787_){
_start:
{
if (lean_obj_tag(v_x_2785_) == 0)
{
lean_object* v_size_2788_; lean_object* v_k_2789_; lean_object* v_v_2790_; lean_object* v_l_2791_; lean_object* v_r_2792_; lean_object* v___x_2793_; 
lean_dec(v_h__1_2786_);
v_size_2788_ = lean_ctor_get(v_x_2785_, 0);
lean_inc(v_size_2788_);
v_k_2789_ = lean_ctor_get(v_x_2785_, 1);
lean_inc(v_k_2789_);
v_v_2790_ = lean_ctor_get(v_x_2785_, 2);
lean_inc(v_v_2790_);
v_l_2791_ = lean_ctor_get(v_x_2785_, 3);
lean_inc(v_l_2791_);
v_r_2792_ = lean_ctor_get(v_x_2785_, 4);
lean_inc(v_r_2792_);
lean_dec_ref(v_x_2785_);
v___x_2793_ = lean_apply_7(v_h__2_2787_, v_size_2788_, v_k_2789_, v_v_2790_, v_l_2791_, v_r_2792_, lean_box(0), lean_box(0));
return v___x_2793_;
}
else
{
lean_object* v___x_2794_; 
lean_dec(v_h__2_2787_);
v___x_2794_ = lean_apply_2(v_h__1_2786_, lean_box(0), lean_box(0));
return v___x_2794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(lean_object* v_00_u03b1_2795_, lean_object* v_00_u03b2_2796_, lean_object* v_inst_2797_, lean_object* v_k_2798_, lean_object* v_motive_2799_, lean_object* v_x_2800_, lean_object* v_x_2801_, lean_object* v_x_2802_, lean_object* v_h__1_2803_, lean_object* v_h__2_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___redArg(v_x_2800_, v_h__1_2803_, v_h__2_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___boxed(lean_object* v_00_u03b1_2806_, lean_object* v_00_u03b2_2807_, lean_object* v_inst_2808_, lean_object* v_k_2809_, lean_object* v_motive_2810_, lean_object* v_x_2811_, lean_object* v_x_2812_, lean_object* v_x_2813_, lean_object* v_h__1_2814_, lean_object* v_h__2_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(v_00_u03b1_2806_, v_00_u03b2_2807_, v_inst_2808_, v_k_2809_, v_motive_2810_, v_x_2811_, v_x_2812_, v_x_2813_, v_h__1_2814_, v_h__2_2815_);
lean_dec(v_k_2809_);
lean_dec_ref(v_inst_2808_);
return v_res_2816_;
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
