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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(uint8_t v_x_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_, lean_object* v_h__3_32_){
_start:
{
switch(v_x_29_)
{
case 0:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec(v_h__3_32_);
lean_dec(v_h__2_31_);
v___x_33_ = lean_box(0);
v___x_34_ = lean_apply_1(v_h__1_30_, v___x_33_);
return v___x_34_;
}
case 1:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
lean_dec(v_h__2_31_);
lean_dec(v_h__1_30_);
v___x_35_ = lean_box(0);
v___x_36_ = lean_apply_1(v_h__3_32_, v___x_35_);
return v___x_36_;
}
default: 
{
lean_object* v___x_37_; lean_object* v___x_38_; 
lean_dec(v_h__3_32_);
lean_dec(v_h__1_30_);
v___x_37_ = lean_box(0);
v___x_38_ = lean_apply_1(v_h__2_31_, v___x_37_);
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(lean_object* v_x_39_, lean_object* v_h__1_40_, lean_object* v_h__2_41_, lean_object* v_h__3_42_){
_start:
{
uint8_t v_x_33__boxed_43_; lean_object* v_res_44_; 
v_x_33__boxed_43_ = lean_unbox(v_x_39_);
v_res_44_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_33__boxed_43_, v_h__1_40_, v_h__2_41_, v_h__3_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object* v_motive_45_, uint8_t v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_, lean_object* v_h__3_49_){
_start:
{
switch(v_x_46_)
{
case 0:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec(v_h__3_49_);
lean_dec(v_h__2_48_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_apply_1(v_h__1_47_, v___x_50_);
return v___x_51_;
}
case 1:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec(v_h__2_48_);
lean_dec(v_h__1_47_);
v___x_52_ = lean_box(0);
v___x_53_ = lean_apply_1(v_h__3_49_, v___x_52_);
return v___x_53_;
}
default: 
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec(v_h__3_49_);
lean_dec(v_h__1_47_);
v___x_54_ = lean_box(0);
v___x_55_ = lean_apply_1(v_h__2_48_, v___x_54_);
return v___x_55_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(lean_object* v_motive_56_, lean_object* v_x_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_, lean_object* v_h__3_60_){
_start:
{
uint8_t v_x_48__boxed_61_; lean_object* v_res_62_; 
v_x_48__boxed_61_ = lean_unbox(v_x_57_);
v_res_62_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_56_, v_x_48__boxed_61_, v_h__1_58_, v_h__2_59_, v_h__3_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(uint8_t v_x_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_, lean_object* v_h__3_66_){
_start:
{
switch(v_x_63_)
{
case 0:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_h__3_66_);
lean_dec(v_h__2_65_);
v___x_67_ = lean_box(0);
v___x_68_ = lean_apply_1(v_h__1_64_, v___x_67_);
return v___x_68_;
}
case 1:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_h__2_65_);
lean_dec(v_h__1_64_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_apply_1(v_h__3_66_, v___x_69_);
return v___x_70_;
}
default: 
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_h__3_66_);
lean_dec(v_h__1_64_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_apply_1(v_h__2_65_, v___x_71_);
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(lean_object* v_x_73_, lean_object* v_h__1_74_, lean_object* v_h__2_75_, lean_object* v_h__3_76_){
_start:
{
uint8_t v_x_33__boxed_77_; lean_object* v_res_78_; 
v_x_33__boxed_77_ = lean_unbox(v_x_73_);
v_res_78_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_33__boxed_77_, v_h__1_74_, v_h__2_75_, v_h__3_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object* v_motive_79_, uint8_t v_x_80_, lean_object* v_h__1_81_, lean_object* v_h__2_82_, lean_object* v_h__3_83_){
_start:
{
switch(v_x_80_)
{
case 0:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_h__3_83_);
lean_dec(v_h__2_82_);
v___x_84_ = lean_box(0);
v___x_85_ = lean_apply_1(v_h__1_81_, v___x_84_);
return v___x_85_;
}
case 1:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v_h__2_82_);
lean_dec(v_h__1_81_);
v___x_86_ = lean_box(0);
v___x_87_ = lean_apply_1(v_h__3_83_, v___x_86_);
return v___x_87_;
}
default: 
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec(v_h__3_83_);
lean_dec(v_h__1_81_);
v___x_88_ = lean_box(0);
v___x_89_ = lean_apply_1(v_h__2_82_, v___x_88_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(lean_object* v_motive_90_, lean_object* v_x_91_, lean_object* v_h__1_92_, lean_object* v_h__2_93_, lean_object* v_h__3_94_){
_start:
{
uint8_t v_x_48__boxed_95_; lean_object* v_res_96_; 
v_x_48__boxed_95_ = lean_unbox(v_x_91_);
v_res_96_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_90_, v_x_48__boxed_95_, v_h__1_92_, v_h__2_93_, v_h__3_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(lean_object* v_k_97_, lean_object* v_f_98_, lean_object* v_ll_99_, lean_object* v_m_100_, lean_object* v_rr_101_){
_start:
{
if (lean_obj_tag(v_m_100_) == 0)
{
lean_object* v_k_102_; lean_object* v_v_103_; lean_object* v_l_104_; lean_object* v_r_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_k_102_ = lean_ctor_get(v_m_100_, 1);
lean_inc_n(v_k_102_, 2);
v_v_103_ = lean_ctor_get(v_m_100_, 2);
lean_inc(v_v_103_);
v_l_104_ = lean_ctor_get(v_m_100_, 3);
lean_inc(v_l_104_);
v_r_105_ = lean_ctor_get(v_m_100_, 4);
lean_inc(v_r_105_);
lean_dec_ref_known(v_m_100_, 5);
lean_inc_ref(v_k_97_);
v___x_106_ = lean_apply_1(v_k_97_, v_k_102_);
v___x_107_ = lean_unbox(v___x_106_);
switch(v___x_107_)
{
case 0:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v_k_102_);
lean_ctor_set(v___x_108_, 1, v_v_103_);
v___x_109_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_105_);
lean_dec(v_r_105_);
v___x_110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = l_List_appendTR___redArg(v___x_110_, v_rr_101_);
v_m_100_ = v_l_104_;
v_rr_101_ = v___x_111_;
goto _start;
}
case 1:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec_ref(v_k_97_);
v___x_113_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_104_);
lean_dec(v_l_104_);
v___x_114_ = l_List_appendTR___redArg(v_ll_99_, v___x_113_);
v___x_115_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_102_, v_v_103_);
v___x_116_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_105_);
lean_dec(v_r_105_);
v___x_117_ = l_List_appendTR___redArg(v___x_116_, v_rr_101_);
v___x_118_ = lean_apply_4(v_f_98_, v___x_114_, v___x_115_, lean_box(0), v___x_117_);
return v___x_118_;
}
default: 
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_119_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_104_);
lean_dec(v_l_104_);
v___x_120_ = l_List_appendTR___redArg(v_ll_99_, v___x_119_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_k_102_);
lean_ctor_set(v___x_121_, 1, v_v_103_);
v___x_122_ = lean_box(0);
v___x_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = l_List_appendTR___redArg(v___x_120_, v___x_123_);
v_ll_99_ = v___x_124_;
v_m_100_ = v_r_105_;
goto _start;
}
}
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec_ref(v_k_97_);
v___x_126_ = lean_box(0);
v___x_127_ = lean_apply_4(v_f_98_, v_ll_99_, v___x_126_, lean_box(0), v_rr_101_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go(lean_object* v_00_u03b1_128_, lean_object* v_00_u03b2_129_, lean_object* v_00_u03b4_130_, lean_object* v_inst_131_, lean_object* v_k_132_, lean_object* v_l_133_, lean_object* v_f_134_, lean_object* v_ll_135_, lean_object* v_m_136_, lean_object* v_hm_137_, lean_object* v_rr_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(v_k_132_, v_f_134_, v_ll_135_, v_m_136_, v_rr_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___boxed(lean_object* v_00_u03b1_140_, lean_object* v_00_u03b2_141_, lean_object* v_00_u03b4_142_, lean_object* v_inst_143_, lean_object* v_k_144_, lean_object* v_l_145_, lean_object* v_f_146_, lean_object* v_ll_147_, lean_object* v_m_148_, lean_object* v_hm_149_, lean_object* v_rr_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go(v_00_u03b1_140_, v_00_u03b2_141_, v_00_u03b4_142_, v_inst_143_, v_k_144_, v_l_145_, v_f_146_, v_ll_147_, v_m_148_, v_hm_149_, v_rr_150_);
lean_dec(v_l_145_);
lean_dec_ref(v_inst_143_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(lean_object* v_k_152_, lean_object* v_l_153_, lean_object* v_f_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_box(0);
v___x_156_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(v_k_152_, v_f_154_, v___x_155_, v_l_153_, v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition(lean_object* v_00_u03b1_157_, lean_object* v_00_u03b2_158_, lean_object* v_00_u03b4_159_, lean_object* v_inst_160_, lean_object* v_k_161_, lean_object* v_l_162_, lean_object* v_f_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v_k_161_, v_l_162_, v_f_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___boxed(lean_object* v_00_u03b1_165_, lean_object* v_00_u03b2_166_, lean_object* v_00_u03b4_167_, lean_object* v_inst_168_, lean_object* v_k_169_, lean_object* v_l_170_, lean_object* v_f_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_DTreeMap_Internal_Impl_applyPartition(v_00_u03b1_165_, v_00_u03b2_166_, v_00_u03b4_167_, v_inst_168_, v_k_169_, v_l_170_, v_f_171_);
lean_dec_ref(v_inst_168_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0(lean_object* v_f_173_, lean_object* v_c_174_, lean_object* v_h_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_apply_2(v_f_173_, v_c_174_, lean_box(0));
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___redArg(lean_object* v_inst_177_, lean_object* v_k_178_, lean_object* v_l_179_, lean_object* v_f_180_){
_start:
{
if (lean_obj_tag(v_l_179_) == 0)
{
lean_object* v_k_181_; lean_object* v_v_182_; lean_object* v_l_183_; lean_object* v_r_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_k_181_ = lean_ctor_get(v_l_179_, 1);
lean_inc_n(v_k_181_, 2);
v_v_182_ = lean_ctor_get(v_l_179_, 2);
lean_inc(v_v_182_);
v_l_183_ = lean_ctor_get(v_l_179_, 3);
lean_inc(v_l_183_);
v_r_184_ = lean_ctor_get(v_l_179_, 4);
lean_inc(v_r_184_);
lean_dec_ref_known(v_l_179_, 5);
lean_inc_ref(v_inst_177_);
lean_inc(v_k_178_);
v___x_185_ = lean_apply_2(v_inst_177_, v_k_178_, v_k_181_);
v___x_186_ = lean_unbox(v___x_185_);
switch(v___x_186_)
{
case 0:
{
lean_object* v___f_187_; 
lean_dec(v_r_184_);
lean_dec(v_v_182_);
lean_dec(v_k_181_);
v___f_187_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0), 3, 1);
lean_closure_set(v___f_187_, 0, v_f_180_);
v_l_179_ = v_l_183_;
v_f_180_ = v___f_187_;
goto _start;
}
case 1:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec(v_r_184_);
lean_dec(v_l_183_);
lean_dec(v_k_178_);
lean_dec_ref(v_inst_177_);
v___x_189_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_181_, v_v_182_);
v___x_190_ = lean_apply_2(v_f_180_, v___x_189_, lean_box(0));
return v___x_190_;
}
default: 
{
lean_object* v___f_191_; 
lean_dec(v_l_183_);
lean_dec(v_v_182_);
lean_dec(v_k_181_);
v___f_191_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0), 3, 1);
lean_closure_set(v___f_191_, 0, v_f_180_);
v_l_179_ = v_r_184_;
v_f_180_ = v___f_191_;
goto _start;
}
}
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_k_178_);
lean_dec_ref(v_inst_177_);
v___x_193_ = lean_box(0);
v___x_194_ = lean_apply_2(v_f_180_, v___x_193_, lean_box(0));
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_00_u03b4_197_, lean_object* v_inst_198_, lean_object* v_k_199_, lean_object* v_l_200_, lean_object* v_f_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_198_, v_k_199_, v_l_200_, v_f_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(uint8_t v_x_203_, lean_object* v_h__1_204_, lean_object* v_h__2_205_, lean_object* v_h__3_206_){
_start:
{
switch(v_x_203_)
{
case 0:
{
lean_object* v___x_207_; 
lean_dec(v_h__3_206_);
lean_dec(v_h__2_205_);
v___x_207_ = lean_apply_1(v_h__1_204_, lean_box(0));
return v___x_207_;
}
case 1:
{
lean_object* v___x_208_; 
lean_dec(v_h__3_206_);
lean_dec(v_h__1_204_);
v___x_208_ = lean_apply_1(v_h__2_205_, lean_box(0));
return v___x_208_;
}
default: 
{
lean_object* v___x_209_; 
lean_dec(v_h__2_205_);
lean_dec(v_h__1_204_);
v___x_209_ = lean_apply_1(v_h__3_206_, lean_box(0));
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(lean_object* v_x_210_, lean_object* v_h__1_211_, lean_object* v_h__2_212_, lean_object* v_h__3_213_){
_start:
{
uint8_t v_x_33__boxed_214_; lean_object* v_res_215_; 
v_x_33__boxed_214_ = lean_unbox(v_x_210_);
v_res_215_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_33__boxed_214_, v_h__1_211_, v_h__2_212_, v_h__3_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object* v_motive_216_, uint8_t v_x_217_, lean_object* v_h__1_218_, lean_object* v_h__2_219_, lean_object* v_h__3_220_){
_start:
{
switch(v_x_217_)
{
case 0:
{
lean_object* v___x_221_; 
lean_dec(v_h__3_220_);
lean_dec(v_h__2_219_);
v___x_221_ = lean_apply_1(v_h__1_218_, lean_box(0));
return v___x_221_;
}
case 1:
{
lean_object* v___x_222_; 
lean_dec(v_h__3_220_);
lean_dec(v_h__1_218_);
v___x_222_ = lean_apply_1(v_h__2_219_, lean_box(0));
return v___x_222_;
}
default: 
{
lean_object* v___x_223_; 
lean_dec(v_h__2_219_);
lean_dec(v_h__1_218_);
v___x_223_ = lean_apply_1(v_h__3_220_, lean_box(0));
return v___x_223_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(lean_object* v_motive_224_, lean_object* v_x_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_, lean_object* v_h__3_228_){
_start:
{
uint8_t v_x_42__boxed_229_; lean_object* v_res_230_; 
v_x_42__boxed_229_ = lean_unbox(v_x_225_);
v_res_230_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(v_motive_224_, v_x_42__boxed_229_, v_h__1_226_, v_h__2_227_, v_h__3_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___redArg(lean_object* v_x_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_obj_tag_nat(v_x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___redArg___boxed(lean_object* v_x_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___redArg(v_x_233_);
lean_dec_ref(v_x_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl(lean_object* v_00_u03b1_235_, lean_object* v_00_u03b2_236_, lean_object* v_inst_237_, lean_object* v_k_238_, lean_object* v_x_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_tag_nat(v_x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___boxed(lean_object* v_00_u03b1_241_, lean_object* v_00_u03b2_242_, lean_object* v_inst_243_, lean_object* v_k_244_, lean_object* v_x_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl(v_00_u03b1_241_, v_00_u03b2_242_, v_inst_243_, v_k_244_, v_x_245_);
lean_dec_ref(v_x_245_);
lean_dec_ref(v_k_244_);
lean_dec_ref(v_inst_243_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(lean_object* v_t_247_, lean_object* v_k_248_){
_start:
{
switch(lean_obj_tag(v_t_247_))
{
case 0:
{
lean_object* v_a_249_; lean_object* v_a_250_; lean_object* v_a_251_; lean_object* v___x_252_; 
v_a_249_ = lean_ctor_get(v_t_247_, 0);
lean_inc(v_a_249_);
v_a_250_ = lean_ctor_get(v_t_247_, 1);
lean_inc(v_a_250_);
v_a_251_ = lean_ctor_get(v_t_247_, 2);
lean_inc(v_a_251_);
lean_dec_ref_known(v_t_247_, 3);
v___x_252_ = lean_apply_4(v_k_248_, v_a_249_, lean_box(0), v_a_250_, v_a_251_);
return v___x_252_;
}
case 1:
{
lean_object* v_a_253_; lean_object* v_a_254_; lean_object* v_a_255_; lean_object* v___x_256_; 
v_a_253_ = lean_ctor_get(v_t_247_, 0);
lean_inc(v_a_253_);
v_a_254_ = lean_ctor_get(v_t_247_, 1);
lean_inc(v_a_254_);
v_a_255_ = lean_ctor_get(v_t_247_, 2);
lean_inc(v_a_255_);
lean_dec_ref_known(v_t_247_, 3);
v___x_256_ = lean_apply_3(v_k_248_, v_a_253_, v_a_254_, v_a_255_);
return v___x_256_;
}
default: 
{
lean_object* v_a_257_; lean_object* v_a_258_; lean_object* v_a_259_; lean_object* v___x_260_; 
v_a_257_ = lean_ctor_get(v_t_247_, 0);
lean_inc(v_a_257_);
v_a_258_ = lean_ctor_get(v_t_247_, 1);
lean_inc(v_a_258_);
v_a_259_ = lean_ctor_get(v_t_247_, 2);
lean_inc(v_a_259_);
lean_dec_ref_known(v_t_247_, 3);
v___x_260_ = lean_apply_4(v_k_248_, v_a_257_, v_a_258_, lean_box(0), v_a_259_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_inst_263_, lean_object* v_k_264_, lean_object* v_motive_265_, lean_object* v_ctorIdx_266_, lean_object* v_t_267_, lean_object* v_h_268_, lean_object* v_k_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_267_, v_k_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___boxed(lean_object* v_00_u03b1_271_, lean_object* v_00_u03b2_272_, lean_object* v_inst_273_, lean_object* v_k_274_, lean_object* v_motive_275_, lean_object* v_ctorIdx_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_k_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim(v_00_u03b1_271_, v_00_u03b2_272_, v_inst_273_, v_k_274_, v_motive_275_, v_ctorIdx_276_, v_t_277_, v_h_278_, v_k_279_);
lean_dec(v_ctorIdx_276_);
lean_dec_ref(v_k_274_);
lean_dec_ref(v_inst_273_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___redArg(lean_object* v_t_281_, lean_object* v_lt_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_281_, v_lt_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim(lean_object* v_00_u03b1_284_, lean_object* v_00_u03b2_285_, lean_object* v_inst_286_, lean_object* v_k_287_, lean_object* v_motive_288_, lean_object* v_t_289_, lean_object* v_h_290_, lean_object* v_lt_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_289_, v_lt_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___boxed(lean_object* v_00_u03b1_293_, lean_object* v_00_u03b2_294_, lean_object* v_inst_295_, lean_object* v_k_296_, lean_object* v_motive_297_, lean_object* v_t_298_, lean_object* v_h_299_, lean_object* v_lt_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim(v_00_u03b1_293_, v_00_u03b2_294_, v_inst_295_, v_k_296_, v_motive_297_, v_t_298_, v_h_299_, v_lt_300_);
lean_dec_ref(v_k_296_);
lean_dec_ref(v_inst_295_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___redArg(lean_object* v_t_302_, lean_object* v_eq_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_302_, v_eq_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim(lean_object* v_00_u03b1_305_, lean_object* v_00_u03b2_306_, lean_object* v_inst_307_, lean_object* v_k_308_, lean_object* v_motive_309_, lean_object* v_t_310_, lean_object* v_h_311_, lean_object* v_eq_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_310_, v_eq_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___boxed(lean_object* v_00_u03b1_314_, lean_object* v_00_u03b2_315_, lean_object* v_inst_316_, lean_object* v_k_317_, lean_object* v_motive_318_, lean_object* v_t_319_, lean_object* v_h_320_, lean_object* v_eq_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim(v_00_u03b1_314_, v_00_u03b2_315_, v_inst_316_, v_k_317_, v_motive_318_, v_t_319_, v_h_320_, v_eq_321_);
lean_dec_ref(v_k_317_);
lean_dec_ref(v_inst_316_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___redArg(lean_object* v_t_323_, lean_object* v_gt_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_323_, v_gt_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim(lean_object* v_00_u03b1_326_, lean_object* v_00_u03b2_327_, lean_object* v_inst_328_, lean_object* v_k_329_, lean_object* v_motive_330_, lean_object* v_t_331_, lean_object* v_h_332_, lean_object* v_gt_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_331_, v_gt_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___boxed(lean_object* v_00_u03b1_335_, lean_object* v_00_u03b2_336_, lean_object* v_inst_337_, lean_object* v_k_338_, lean_object* v_motive_339_, lean_object* v_t_340_, lean_object* v_h_341_, lean_object* v_gt_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim(v_00_u03b1_335_, v_00_u03b2_336_, v_inst_337_, v_k_338_, v_motive_339_, v_t_340_, v_h_341_, v_gt_342_);
lean_dec_ref(v_k_338_);
lean_dec_ref(v_inst_337_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___redArg(lean_object* v_k_347_, lean_object* v_init_348_, lean_object* v_inner_349_, lean_object* v_l_350_){
_start:
{
if (lean_obj_tag(v_l_350_) == 0)
{
lean_object* v_k_351_; lean_object* v_v_352_; lean_object* v_l_353_; lean_object* v_r_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v_k_351_ = lean_ctor_get(v_l_350_, 1);
lean_inc_n(v_k_351_, 2);
v_v_352_ = lean_ctor_get(v_l_350_, 2);
lean_inc(v_v_352_);
v_l_353_ = lean_ctor_get(v_l_350_, 3);
lean_inc(v_l_353_);
v_r_354_ = lean_ctor_get(v_l_350_, 4);
lean_inc(v_r_354_);
lean_dec_ref_known(v_l_350_, 5);
lean_inc_ref(v_k_347_);
v___x_355_ = lean_apply_1(v_k_347_, v_k_351_);
v___x_356_ = lean_unbox(v___x_355_);
switch(v___x_356_)
{
case 0:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_354_);
lean_dec(v_r_354_);
v___x_358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_358_, 0, v_k_351_);
lean_ctor_set(v___x_358_, 1, v_v_352_);
lean_ctor_set(v___x_358_, 2, v___x_357_);
lean_inc(v_inner_349_);
v___x_359_ = lean_apply_2(v_inner_349_, v_init_348_, v___x_358_);
v_init_348_ = v___x_359_;
v_l_350_ = v_l_353_;
goto _start;
}
case 1:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec_ref(v_k_347_);
v___x_361_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_353_);
lean_dec(v_l_353_);
v___x_362_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_351_, v_v_352_);
v___x_363_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_354_);
lean_dec(v_r_354_);
v___x_364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_364_, 0, v___x_361_);
lean_ctor_set(v___x_364_, 1, v___x_362_);
lean_ctor_set(v___x_364_, 2, v___x_363_);
v___x_365_ = lean_apply_2(v_inner_349_, v_init_348_, v___x_364_);
return v___x_365_;
}
default: 
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_353_);
lean_dec(v_l_353_);
v___x_367_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v_k_351_);
lean_ctor_set(v___x_367_, 2, v_v_352_);
lean_inc(v_inner_349_);
v___x_368_ = lean_apply_2(v_inner_349_, v_init_348_, v___x_367_);
v_init_348_ = v___x_368_;
v_l_350_ = v_r_354_;
goto _start;
}
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec_ref(v_k_347_);
v___x_370_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0));
v___x_371_ = lean_apply_2(v_inner_349_, v_init_348_, v___x_370_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore(lean_object* v_00_u03b1_372_, lean_object* v_00_u03b2_373_, lean_object* v_00_u03b3_374_, lean_object* v_inst_375_, lean_object* v_k_376_, lean_object* v_init_377_, lean_object* v_inner_378_, lean_object* v_l_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v_k_376_, v_init_377_, v_inner_378_, v_l_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___boxed(lean_object* v_00_u03b1_381_, lean_object* v_00_u03b2_382_, lean_object* v_00_u03b3_383_, lean_object* v_inst_384_, lean_object* v_k_385_, lean_object* v_init_386_, lean_object* v_inner_387_, lean_object* v_l_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_DTreeMap_Internal_Impl_explore(v_00_u03b1_381_, v_00_u03b2_382_, v_00_u03b3_383_, v_inst_384_, v_k_385_, v_init_386_, v_inner_387_, v_l_388_);
lean_dec_ref(v_inst_384_);
return v_res_389_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(lean_object* v_c_390_, lean_object* v_x_391_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0___boxed(lean_object* v_c_393_, lean_object* v_x_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(v_c_393_, v_x_394_);
lean_dec(v_c_393_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(lean_object* v_inst_398_, lean_object* v_l_399_, lean_object* v_k_400_){
_start:
{
lean_object* v___f_401_; lean_object* v___x_402_; 
v___f_401_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0));
v___x_402_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_398_, v_k_400_, v_l_399_, v___f_401_);
return v___x_402_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098(lean_object* v_00_u03b1_403_, lean_object* v_00_u03b2_404_, lean_object* v_inst_405_, lean_object* v_l_406_, lean_object* v_k_407_){
_start:
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(v_inst_405_, v_l_406_, v_k_407_);
v___x_409_ = lean_unbox(v___x_408_);
lean_dec(v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___boxed(lean_object* v_00_u03b1_410_, lean_object* v_00_u03b2_411_, lean_object* v_inst_412_, lean_object* v_l_413_, lean_object* v_k_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Std_DTreeMap_Internal_Impl_contains_u2098(v_00_u03b1_410_, v_00_u03b2_411_, v_inst_412_, v_l_413_, v_k_414_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0(lean_object* v_c_417_, lean_object* v_x_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(v_c_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(lean_object* v_inst_421_, lean_object* v_l_422_, lean_object* v_k_423_){
_start:
{
lean_object* v___f_424_; lean_object* v___x_425_; 
v___f_424_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0));
v___x_425_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_421_, v_k_423_, v_l_422_, v___f_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098(lean_object* v_00_u03b1_426_, lean_object* v_00_u03b2_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_l_431_, lean_object* v_k_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_428_, v_l_431_, v_k_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(lean_object* v_inst_434_, lean_object* v_l_435_, lean_object* v_k_436_){
_start:
{
lean_object* v___x_437_; lean_object* v_val_438_; 
v___x_437_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_434_, v_l_435_, v_k_436_);
v_val_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_val_438_);
lean_dec(v___x_437_);
return v_val_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098(lean_object* v_00_u03b1_439_, lean_object* v_00_u03b2_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_l_444_, lean_object* v_k_445_, lean_object* v_h_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(v_inst_441_, v_l_444_, v_k_445_);
return v___x_447_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_451_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2));
v___x_452_ = lean_unsigned_to_nat(14u);
v___x_453_ = lean_unsigned_to_nat(22u);
v___x_454_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1));
v___x_455_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0));
v___x_456_ = l_mkPanicMessageWithDecl(v___x_455_, v___x_454_, v___x_453_, v___x_452_, v___x_451_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(lean_object* v_inst_457_, lean_object* v_l_458_, lean_object* v_k_459_, lean_object* v_inst_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_457_, v_l_458_, v_k_459_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_463_ = l_panic___redArg(v_inst_460_, v___x_462_);
return v___x_463_;
}
else
{
lean_object* v_val_464_; 
v_val_464_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_val_464_);
lean_dec_ref_known(v___x_461_, 1);
return v_val_464_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___boxed(lean_object* v_inst_465_, lean_object* v_l_466_, lean_object* v_k_467_, lean_object* v_inst_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(v_inst_465_, v_l_466_, v_k_467_, v_inst_468_);
lean_dec(v_inst_468_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098(lean_object* v_00_u03b1_470_, lean_object* v_00_u03b2_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_l_475_, lean_object* v_k_476_, lean_object* v_inst_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(v_inst_472_, v_l_475_, v_k_476_, v_inst_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___boxed(lean_object* v_00_u03b1_479_, lean_object* v_00_u03b2_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_l_484_, lean_object* v_k_485_, lean_object* v_inst_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098(v_00_u03b1_479_, v_00_u03b2_480_, v_inst_481_, v_inst_482_, v_inst_483_, v_l_484_, v_k_485_, v_inst_486_);
lean_dec(v_inst_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(lean_object* v_inst_488_, lean_object* v_k_489_, lean_object* v_l_490_, lean_object* v_fallback_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_488_, v_l_490_, v_k_489_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_inc(v_fallback_491_);
return v_fallback_491_;
}
else
{
lean_object* v_val_493_; 
v_val_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_val_493_);
lean_dec_ref_known(v___x_492_, 1);
return v_val_493_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg___boxed(lean_object* v_inst_494_, lean_object* v_k_495_, lean_object* v_l_496_, lean_object* v_fallback_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(v_inst_494_, v_k_495_, v_l_496_, v_fallback_497_);
lean_dec(v_fallback_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098(lean_object* v_00_u03b1_499_, lean_object* v_00_u03b2_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_k_504_, lean_object* v_l_505_, lean_object* v_fallback_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(v_inst_501_, v_k_504_, v_l_505_, v_fallback_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___boxed(lean_object* v_00_u03b1_508_, lean_object* v_00_u03b2_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_k_513_, lean_object* v_l_514_, lean_object* v_fallback_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_DTreeMap_Internal_Impl_getD_u2098(v_00_u03b1_508_, v_00_u03b2_509_, v_inst_510_, v_inst_511_, v_inst_512_, v_k_513_, v_l_514_, v_fallback_515_);
lean_dec(v_fallback_515_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___lam__0(lean_object* v_c_517_, lean_object* v_x_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(v_c_517_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(lean_object* v_inst_521_, lean_object* v_l_522_, lean_object* v_k_523_){
_start:
{
lean_object* v___f_524_; lean_object* v___x_525_; 
v___f_524_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0));
v___x_525_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_521_, v_k_523_, v_l_522_, v___f_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098(lean_object* v_00_u03b1_526_, lean_object* v_00_u03b2_527_, lean_object* v_inst_528_, lean_object* v_l_529_, lean_object* v_k_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_528_, v_l_529_, v_k_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(lean_object* v_inst_532_, lean_object* v_l_533_, lean_object* v_k_534_){
_start:
{
lean_object* v___x_535_; lean_object* v_val_536_; 
v___x_535_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_532_, v_l_533_, v_k_534_);
v_val_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_val_536_);
lean_dec(v___x_535_);
return v_val_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098(lean_object* v_00_u03b1_537_, lean_object* v_00_u03b2_538_, lean_object* v_inst_539_, lean_object* v_l_540_, lean_object* v_k_541_, lean_object* v_h_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(v_inst_539_, v_l_540_, v_k_541_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_l_546_, lean_object* v_k_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_544_, v_l_546_, v_k_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_550_ = l_panic___redArg(v_inst_545_, v___x_549_);
return v___x_550_;
}
else
{
lean_object* v_val_551_; 
v_val_551_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_val_551_);
lean_dec_ref_known(v___x_548_, 1);
return v_val_551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg___boxed(lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_l_554_, lean_object* v_k_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(v_inst_552_, v_inst_553_, v_l_554_, v_k_555_);
lean_dec_ref(v_inst_553_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(lean_object* v_00_u03b1_557_, lean_object* v_00_u03b2_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_l_561_, lean_object* v_k_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(v_inst_559_, v_inst_560_, v_l_561_, v_k_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___boxed(lean_object* v_00_u03b1_564_, lean_object* v_00_u03b2_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_l_568_, lean_object* v_k_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(v_00_u03b1_564_, v_00_u03b2_565_, v_inst_566_, v_inst_567_, v_l_568_, v_k_569_);
lean_dec_ref(v_inst_567_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(lean_object* v_inst_571_, lean_object* v_k_572_, lean_object* v_l_573_, lean_object* v_fallback_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_571_, v_l_573_, v_k_572_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_inc_ref(v_fallback_574_);
return v_fallback_574_;
}
else
{
lean_object* v_val_576_; 
v_val_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_val_576_);
lean_dec_ref_known(v___x_575_, 1);
return v_val_576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg___boxed(lean_object* v_inst_577_, lean_object* v_k_578_, lean_object* v_l_579_, lean_object* v_fallback_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(v_inst_577_, v_k_578_, v_l_579_, v_fallback_580_);
lean_dec_ref(v_fallback_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(lean_object* v_00_u03b1_582_, lean_object* v_00_u03b2_583_, lean_object* v_inst_584_, lean_object* v_k_585_, lean_object* v_l_586_, lean_object* v_fallback_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(v_inst_584_, v_k_585_, v_l_586_, v_fallback_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___boxed(lean_object* v_00_u03b1_589_, lean_object* v_00_u03b2_590_, lean_object* v_inst_591_, lean_object* v_k_592_, lean_object* v_l_593_, lean_object* v_fallback_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(v_00_u03b1_589_, v_00_u03b2_590_, v_inst_591_, v_k_592_, v_l_593_, v_fallback_594_);
lean_dec_ref(v_fallback_594_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0(lean_object* v_c_596_, lean_object* v_x_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(v_c_596_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(lean_object* v_inst_600_, lean_object* v_l_601_, lean_object* v_k_602_){
_start:
{
lean_object* v___f_603_; lean_object* v___x_604_; 
v___f_603_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0));
v___x_604_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_600_, v_k_602_, v_l_601_, v___f_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098(lean_object* v_00_u03b1_605_, lean_object* v_00_u03b2_606_, lean_object* v_inst_607_, lean_object* v_l_608_, lean_object* v_k_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_607_, v_l_608_, v_k_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(lean_object* v_inst_611_, lean_object* v_l_612_, lean_object* v_k_613_){
_start:
{
lean_object* v___x_614_; lean_object* v_val_615_; 
v___x_614_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_611_, v_l_612_, v_k_613_);
v_val_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_val_615_);
lean_dec(v___x_614_);
return v_val_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098(lean_object* v_00_u03b1_616_, lean_object* v_00_u03b2_617_, lean_object* v_inst_618_, lean_object* v_l_619_, lean_object* v_k_620_, lean_object* v_h_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(v_inst_618_, v_l_619_, v_k_620_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(lean_object* v_inst_623_, lean_object* v_l_624_, lean_object* v_k_625_, lean_object* v_inst_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_623_, v_l_624_, v_k_625_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_629_ = l_panic___redArg(v_inst_626_, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v_val_630_; 
v_val_630_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v___x_627_, 1);
return v_val_630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg___boxed(lean_object* v_inst_631_, lean_object* v_l_632_, lean_object* v_k_633_, lean_object* v_inst_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(v_inst_631_, v_l_632_, v_k_633_, v_inst_634_);
lean_dec(v_inst_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(lean_object* v_00_u03b1_636_, lean_object* v_00_u03b2_637_, lean_object* v_inst_638_, lean_object* v_l_639_, lean_object* v_k_640_, lean_object* v_inst_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(v_inst_638_, v_l_639_, v_k_640_, v_inst_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___boxed(lean_object* v_00_u03b1_643_, lean_object* v_00_u03b2_644_, lean_object* v_inst_645_, lean_object* v_l_646_, lean_object* v_k_647_, lean_object* v_inst_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(v_00_u03b1_643_, v_00_u03b2_644_, v_inst_645_, v_l_646_, v_k_647_, v_inst_648_);
lean_dec(v_inst_648_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(lean_object* v_inst_650_, lean_object* v_k_651_, lean_object* v_l_652_, lean_object* v_fallback_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_650_, v_l_652_, v_k_651_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_inc(v_fallback_653_);
return v_fallback_653_;
}
else
{
lean_object* v_val_655_; 
v_val_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_val_655_);
lean_dec_ref_known(v___x_654_, 1);
return v_val_655_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg___boxed(lean_object* v_inst_656_, lean_object* v_k_657_, lean_object* v_l_658_, lean_object* v_fallback_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(v_inst_656_, v_k_657_, v_l_658_, v_fallback_659_);
lean_dec(v_fallback_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(lean_object* v_00_u03b1_661_, lean_object* v_00_u03b2_662_, lean_object* v_inst_663_, lean_object* v_k_664_, lean_object* v_l_665_, lean_object* v_fallback_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(v_inst_663_, v_k_664_, v_l_665_, v_fallback_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___boxed(lean_object* v_00_u03b1_668_, lean_object* v_00_u03b2_669_, lean_object* v_inst_670_, lean_object* v_k_671_, lean_object* v_l_672_, lean_object* v_fallback_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(v_00_u03b1_668_, v_00_u03b2_669_, v_inst_670_, v_k_671_, v_l_672_, v_fallback_673_);
lean_dec(v_fallback_673_);
return v_res_674_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(lean_object* v_x_675_){
_start:
{
uint8_t v___x_676_; 
v___x_676_ = 0;
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* v_x_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(v_x_677_);
lean_dec(v_x_677_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(lean_object* v_sofar_680_, lean_object* v_step_681_){
_start:
{
if (lean_obj_tag(v_step_681_) == 0)
{
lean_object* v_a_682_; lean_object* v_a_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_a_682_ = lean_ctor_get(v_step_681_, 0);
v_a_683_ = lean_ctor_get(v_step_681_, 1);
lean_inc(v_a_683_);
lean_inc(v_a_682_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_a_682_);
lean_ctor_set(v___x_684_, 1, v_a_683_);
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
return v___x_685_;
}
else
{
lean_object* v_a_686_; lean_object* v___x_687_; 
v_a_686_ = lean_ctor_get(v_step_681_, 2);
v___x_687_ = l_List_head_x3f___redArg(v_a_686_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_inc(v_sofar_680_);
return v_sofar_680_;
}
else
{
return v___x_687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* v_sofar_688_, lean_object* v_step_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(v_sofar_688_, v_step_689_);
lean_dec_ref(v_step_689_);
lean_dec(v_sofar_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(lean_object* v_l_693_){
_start:
{
lean_object* v___f_694_; lean_object* v___f_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___f_694_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0));
v___f_695_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1));
v___x_696_ = lean_box(0);
v___x_697_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___f_694_, v___x_696_, v___f_695_, v_l_693_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_inst_700_, lean_object* v_l_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(v_l_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___boxed(lean_object* v_00_u03b1_703_, lean_object* v_00_u03b2_704_, lean_object* v_inst_705_, lean_object* v_l_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(v_00_u03b1_703_, v_00_u03b2_704_, v_inst_705_, v_l_706_);
lean_dec_ref(v_inst_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v_r_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_List_head_x3f___redArg(v_r_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed(lean_object* v_x_713_, lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_r_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(v_x_713_, v_x_714_, v_x_715_, v_r_716_);
lean_dec(v_r_716_);
lean_dec(v_x_714_);
lean_dec(v_x_713_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(lean_object* v_l_719_){
_start:
{
lean_object* v___f_720_; lean_object* v___f_721_; lean_object* v___x_722_; 
v___f_720_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0));
v___f_721_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0));
v___x_722_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_720_, v_l_719_, v___f_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(lean_object* v_00_u03b1_723_, lean_object* v_00_u03b2_724_, lean_object* v_inst_725_, lean_object* v_l_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(v_l_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___boxed(lean_object* v_00_u03b1_728_, lean_object* v_00_u03b2_729_, lean_object* v_inst_730_, lean_object* v_l_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(v_00_u03b1_728_, v_00_u03b2_729_, v_inst_730_, v_l_731_);
lean_dec_ref(v_inst_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse___redArg(lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_733_) == 0)
{
lean_object* v_size_734_; lean_object* v_k_735_; lean_object* v_v_736_; lean_object* v_l_737_; lean_object* v_r_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_747_; 
v_size_734_ = lean_ctor_get(v_x_733_, 0);
v_k_735_ = lean_ctor_get(v_x_733_, 1);
v_v_736_ = lean_ctor_get(v_x_733_, 2);
v_l_737_ = lean_ctor_get(v_x_733_, 3);
v_r_738_ = lean_ctor_get(v_x_733_, 4);
v_isSharedCheck_747_ = !lean_is_exclusive(v_x_733_);
if (v_isSharedCheck_747_ == 0)
{
v___x_740_ = v_x_733_;
v_isShared_741_ = v_isSharedCheck_747_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_r_738_);
lean_inc(v_l_737_);
lean_inc(v_v_736_);
lean_inc(v_k_735_);
lean_inc(v_size_734_);
lean_dec(v_x_733_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_747_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_742_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_r_738_);
v___x_743_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_l_737_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 4, v___x_743_);
lean_ctor_set(v___x_740_, 3, v___x_742_);
v___x_745_ = v___x_740_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_size_734_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_k_735_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_v_736_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
return v_x_733_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse(lean_object* v_00_u03b1_748_, lean_object* v_00_u03b2_749_, lean_object* v_x_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0(lean_object* v_c_752_, lean_object* v_x_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(v_c_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(lean_object* v_inst_756_, lean_object* v_l_757_, lean_object* v_k_758_){
_start:
{
lean_object* v___f_759_; lean_object* v___x_760_; 
v___f_759_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0));
v___x_760_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_756_, v_k_758_, v_l_757_, v___f_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098(lean_object* v_00_u03b1_761_, lean_object* v_00_u03b2_762_, lean_object* v_inst_763_, lean_object* v_l_764_, lean_object* v_k_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_763_, v_l_764_, v_k_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(lean_object* v_inst_767_, lean_object* v_l_768_, lean_object* v_k_769_){
_start:
{
lean_object* v___x_770_; lean_object* v_val_771_; 
v___x_770_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_767_, v_l_768_, v_k_769_);
v_val_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_val_771_);
lean_dec(v___x_770_);
return v_val_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098(lean_object* v_00_u03b1_772_, lean_object* v_00_u03b2_773_, lean_object* v_inst_774_, lean_object* v_l_775_, lean_object* v_k_776_, lean_object* v_h_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(v_inst_774_, v_l_775_, v_k_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(lean_object* v_inst_779_, lean_object* v_l_780_, lean_object* v_k_781_, lean_object* v_inst_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_779_, v_l_780_, v_k_781_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_785_ = l_panic___redArg(v_inst_782_, v___x_784_);
return v___x_785_;
}
else
{
lean_object* v_val_786_; 
v_val_786_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_val_786_);
lean_dec_ref_known(v___x_783_, 1);
return v_val_786_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg___boxed(lean_object* v_inst_787_, lean_object* v_l_788_, lean_object* v_k_789_, lean_object* v_inst_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(v_inst_787_, v_l_788_, v_k_789_, v_inst_790_);
lean_dec(v_inst_790_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_inst_794_, lean_object* v_l_795_, lean_object* v_k_796_, lean_object* v_inst_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(v_inst_794_, v_l_795_, v_k_796_, v_inst_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___boxed(lean_object* v_00_u03b1_799_, lean_object* v_00_u03b2_800_, lean_object* v_inst_801_, lean_object* v_l_802_, lean_object* v_k_803_, lean_object* v_inst_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(v_00_u03b1_799_, v_00_u03b2_800_, v_inst_801_, v_l_802_, v_k_803_, v_inst_804_);
lean_dec(v_inst_804_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(lean_object* v_inst_806_, lean_object* v_l_807_, lean_object* v_k_808_, lean_object* v_fallback_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_806_, v_l_807_, v_k_808_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_inc(v_fallback_809_);
return v_fallback_809_;
}
else
{
lean_object* v_val_811_; 
v_val_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_val_811_);
lean_dec_ref_known(v___x_810_, 1);
return v_val_811_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg___boxed(lean_object* v_inst_812_, lean_object* v_l_813_, lean_object* v_k_814_, lean_object* v_fallback_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(v_inst_812_, v_l_813_, v_k_814_, v_fallback_815_);
lean_dec(v_fallback_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(lean_object* v_00_u03b1_817_, lean_object* v_00_u03b2_818_, lean_object* v_inst_819_, lean_object* v_l_820_, lean_object* v_k_821_, lean_object* v_fallback_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(v_inst_819_, v_l_820_, v_k_821_, v_fallback_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___boxed(lean_object* v_00_u03b1_824_, lean_object* v_00_u03b2_825_, lean_object* v_inst_826_, lean_object* v_l_827_, lean_object* v_k_828_, lean_object* v_fallback_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(v_00_u03b1_824_, v_00_u03b2_825_, v_inst_826_, v_l_827_, v_k_828_, v_fallback_829_);
lean_dec(v_fallback_829_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(uint8_t v_x_831_, lean_object* v_h__1_832_, lean_object* v_h__2_833_, lean_object* v_h__3_834_){
_start:
{
switch(v_x_831_)
{
case 0:
{
lean_object* v___x_835_; 
lean_dec(v_h__3_834_);
lean_dec(v_h__2_833_);
v___x_835_ = lean_apply_1(v_h__1_832_, lean_box(0));
return v___x_835_;
}
case 1:
{
lean_object* v___x_836_; 
lean_dec(v_h__2_833_);
lean_dec(v_h__1_832_);
v___x_836_ = lean_apply_1(v_h__3_834_, lean_box(0));
return v___x_836_;
}
default: 
{
lean_object* v___x_837_; 
lean_dec(v_h__3_834_);
lean_dec(v_h__1_832_);
v___x_837_ = lean_apply_1(v_h__2_833_, lean_box(0));
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_838_, lean_object* v_h__1_839_, lean_object* v_h__2_840_, lean_object* v_h__3_841_){
_start:
{
uint8_t v_x_33__boxed_842_; lean_object* v_res_843_; 
v_x_33__boxed_842_ = lean_unbox(v_x_838_);
v_res_843_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(v_x_33__boxed_842_, v_h__1_839_, v_h__2_840_, v_h__3_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(lean_object* v_motive_844_, uint8_t v_x_845_, lean_object* v_h__1_846_, lean_object* v_h__2_847_, lean_object* v_h__3_848_){
_start:
{
switch(v_x_845_)
{
case 0:
{
lean_object* v___x_849_; 
lean_dec(v_h__3_848_);
lean_dec(v_h__2_847_);
v___x_849_ = lean_apply_1(v_h__1_846_, lean_box(0));
return v___x_849_;
}
case 1:
{
lean_object* v___x_850_; 
lean_dec(v_h__2_847_);
lean_dec(v_h__1_846_);
v___x_850_ = lean_apply_1(v_h__3_848_, lean_box(0));
return v___x_850_;
}
default: 
{
lean_object* v___x_851_; 
lean_dec(v_h__3_848_);
lean_dec(v_h__1_846_);
v___x_851_ = lean_apply_1(v_h__2_847_, lean_box(0));
return v___x_851_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___boxed(lean_object* v_motive_852_, lean_object* v_x_853_, lean_object* v_h__1_854_, lean_object* v_h__2_855_, lean_object* v_h__3_856_){
_start:
{
uint8_t v_x_42__boxed_857_; lean_object* v_res_858_; 
v_x_42__boxed_857_ = lean_unbox(v_x_853_);
v_res_858_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(v_motive_852_, v_x_42__boxed_857_, v_h__1_854_, v_h__2_855_, v_h__3_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object* v_x_859_, lean_object* v_h__1_860_, lean_object* v_h__2_861_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_object* v___x_862_; 
lean_dec(v_h__2_861_);
v___x_862_ = lean_apply_1(v_h__1_860_, lean_box(0));
return v___x_862_;
}
else
{
lean_object* v_val_863_; lean_object* v___x_864_; 
lean_dec(v_h__1_860_);
v_val_863_ = lean_ctor_get(v_x_859_, 0);
lean_inc(v_val_863_);
lean_dec_ref_known(v_x_859_, 1);
v___x_864_ = lean_apply_2(v_h__2_861_, v_val_863_, lean_box(0));
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object* v_00_u03b1_865_, lean_object* v_00_u03b2_866_, lean_object* v_motive_867_, lean_object* v_x_868_, lean_object* v_h__1_869_, lean_object* v_h__2_870_){
_start:
{
if (lean_obj_tag(v_x_868_) == 0)
{
lean_object* v___x_871_; 
lean_dec(v_h__2_870_);
v___x_871_ = lean_apply_1(v_h__1_869_, lean_box(0));
return v___x_871_;
}
else
{
lean_object* v_val_872_; lean_object* v___x_873_; 
lean_dec(v_h__1_869_);
v_val_872_ = lean_ctor_get(v_x_868_, 0);
lean_inc(v_val_872_);
lean_dec_ref_known(v_x_868_, 1);
v___x_873_ = lean_apply_2(v_h__2_870_, v_val_872_, lean_box(0));
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_874_, lean_object* v_h__1_875_, lean_object* v_h__2_876_){
_start:
{
if (lean_obj_tag(v_x_874_) == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec(v_h__2_876_);
v___x_877_ = lean_box(0);
v___x_878_ = lean_apply_1(v_h__1_875_, v___x_877_);
return v___x_878_;
}
else
{
lean_object* v_val_879_; lean_object* v___x_880_; 
lean_dec(v_h__1_875_);
v_val_879_ = lean_ctor_get(v_x_874_, 0);
lean_inc(v_val_879_);
lean_dec_ref_known(v_x_874_, 1);
v___x_880_ = lean_apply_1(v_h__2_876_, v_val_879_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_motive_883_, lean_object* v_x_884_, lean_object* v_h__1_885_, lean_object* v_h__2_886_){
_start:
{
if (lean_obj_tag(v_x_884_) == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec(v_h__2_886_);
v___x_887_ = lean_box(0);
v___x_888_ = lean_apply_1(v_h__1_885_, v___x_887_);
return v___x_888_;
}
else
{
lean_object* v_val_889_; lean_object* v___x_890_; 
lean_dec(v_h__1_885_);
v_val_889_ = lean_ctor_get(v_x_884_, 0);
lean_inc(v_val_889_);
lean_dec_ref_known(v_x_884_, 1);
v___x_890_ = lean_apply_1(v_h__2_886_, v_val_889_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_891_, lean_object* v_h__1_892_, lean_object* v_h__2_893_, lean_object* v_h__3_894_){
_start:
{
if (lean_obj_tag(v_x_891_) == 0)
{
lean_object* v_l_895_; 
lean_dec(v_h__1_892_);
v_l_895_ = lean_ctor_get(v_x_891_, 3);
if (lean_obj_tag(v_l_895_) == 0)
{
lean_object* v_size_896_; lean_object* v_k_897_; lean_object* v_v_898_; lean_object* v_r_899_; lean_object* v_size_900_; lean_object* v_k_901_; lean_object* v_v_902_; lean_object* v_l_903_; lean_object* v_r_904_; lean_object* v___x_905_; 
lean_inc_ref(v_l_895_);
lean_dec(v_h__2_893_);
v_size_896_ = lean_ctor_get(v_x_891_, 0);
lean_inc(v_size_896_);
v_k_897_ = lean_ctor_get(v_x_891_, 1);
lean_inc(v_k_897_);
v_v_898_ = lean_ctor_get(v_x_891_, 2);
lean_inc(v_v_898_);
v_r_899_ = lean_ctor_get(v_x_891_, 4);
lean_inc(v_r_899_);
lean_dec_ref_known(v_x_891_, 5);
v_size_900_ = lean_ctor_get(v_l_895_, 0);
lean_inc(v_size_900_);
v_k_901_ = lean_ctor_get(v_l_895_, 1);
lean_inc(v_k_901_);
v_v_902_ = lean_ctor_get(v_l_895_, 2);
lean_inc(v_v_902_);
v_l_903_ = lean_ctor_get(v_l_895_, 3);
lean_inc(v_l_903_);
v_r_904_ = lean_ctor_get(v_l_895_, 4);
lean_inc(v_r_904_);
lean_dec_ref_known(v_l_895_, 5);
v___x_905_ = lean_apply_9(v_h__3_894_, v_size_896_, v_k_897_, v_v_898_, v_size_900_, v_k_901_, v_v_902_, v_l_903_, v_r_904_, v_r_899_);
return v___x_905_;
}
else
{
lean_object* v_size_906_; lean_object* v_k_907_; lean_object* v_v_908_; lean_object* v_r_909_; lean_object* v___x_910_; 
lean_dec(v_h__3_894_);
v_size_906_ = lean_ctor_get(v_x_891_, 0);
lean_inc(v_size_906_);
v_k_907_ = lean_ctor_get(v_x_891_, 1);
lean_inc(v_k_907_);
v_v_908_ = lean_ctor_get(v_x_891_, 2);
lean_inc(v_v_908_);
v_r_909_ = lean_ctor_get(v_x_891_, 4);
lean_inc(v_r_909_);
lean_dec_ref_known(v_x_891_, 5);
v___x_910_ = lean_apply_4(v_h__2_893_, v_size_906_, v_k_907_, v_v_908_, v_r_909_);
return v___x_910_;
}
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec(v_h__3_894_);
lean_dec(v_h__2_893_);
v___x_911_ = lean_box(0);
v___x_912_ = lean_apply_1(v_h__1_892_, v___x_911_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_913_, lean_object* v_00_u03b2_914_, lean_object* v_motive_915_, lean_object* v_x_916_, lean_object* v_h__1_917_, lean_object* v_h__2_918_, lean_object* v_h__3_919_){
_start:
{
if (lean_obj_tag(v_x_916_) == 0)
{
lean_object* v_l_920_; 
lean_dec(v_h__1_917_);
v_l_920_ = lean_ctor_get(v_x_916_, 3);
if (lean_obj_tag(v_l_920_) == 0)
{
lean_object* v_size_921_; lean_object* v_k_922_; lean_object* v_v_923_; lean_object* v_r_924_; lean_object* v_size_925_; lean_object* v_k_926_; lean_object* v_v_927_; lean_object* v_l_928_; lean_object* v_r_929_; lean_object* v___x_930_; 
lean_inc_ref(v_l_920_);
lean_dec(v_h__2_918_);
v_size_921_ = lean_ctor_get(v_x_916_, 0);
lean_inc(v_size_921_);
v_k_922_ = lean_ctor_get(v_x_916_, 1);
lean_inc(v_k_922_);
v_v_923_ = lean_ctor_get(v_x_916_, 2);
lean_inc(v_v_923_);
v_r_924_ = lean_ctor_get(v_x_916_, 4);
lean_inc(v_r_924_);
lean_dec_ref_known(v_x_916_, 5);
v_size_925_ = lean_ctor_get(v_l_920_, 0);
lean_inc(v_size_925_);
v_k_926_ = lean_ctor_get(v_l_920_, 1);
lean_inc(v_k_926_);
v_v_927_ = lean_ctor_get(v_l_920_, 2);
lean_inc(v_v_927_);
v_l_928_ = lean_ctor_get(v_l_920_, 3);
lean_inc(v_l_928_);
v_r_929_ = lean_ctor_get(v_l_920_, 4);
lean_inc(v_r_929_);
lean_dec_ref_known(v_l_920_, 5);
v___x_930_ = lean_apply_9(v_h__3_919_, v_size_921_, v_k_922_, v_v_923_, v_size_925_, v_k_926_, v_v_927_, v_l_928_, v_r_929_, v_r_924_);
return v___x_930_;
}
else
{
lean_object* v_size_931_; lean_object* v_k_932_; lean_object* v_v_933_; lean_object* v_r_934_; lean_object* v___x_935_; 
lean_dec(v_h__3_919_);
v_size_931_ = lean_ctor_get(v_x_916_, 0);
lean_inc(v_size_931_);
v_k_932_ = lean_ctor_get(v_x_916_, 1);
lean_inc(v_k_932_);
v_v_933_ = lean_ctor_get(v_x_916_, 2);
lean_inc(v_v_933_);
v_r_934_ = lean_ctor_get(v_x_916_, 4);
lean_inc(v_r_934_);
lean_dec_ref_known(v_x_916_, 5);
v___x_935_ = lean_apply_4(v_h__2_918_, v_size_931_, v_k_932_, v_v_933_, v_r_934_);
return v___x_935_;
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec(v_h__3_919_);
lean_dec(v_h__2_918_);
v___x_936_ = lean_box(0);
v___x_937_ = lean_apply_1(v_h__1_917_, v___x_936_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_step_938_, lean_object* v_h__1_939_, lean_object* v_h__2_940_){
_start:
{
if (lean_obj_tag(v_step_938_) == 0)
{
lean_object* v_a_941_; lean_object* v_a_942_; lean_object* v_a_943_; lean_object* v___x_944_; 
lean_dec(v_h__2_940_);
v_a_941_ = lean_ctor_get(v_step_938_, 0);
lean_inc(v_a_941_);
v_a_942_ = lean_ctor_get(v_step_938_, 1);
lean_inc(v_a_942_);
v_a_943_ = lean_ctor_get(v_step_938_, 2);
lean_inc(v_a_943_);
lean_dec_ref_known(v_step_938_, 3);
v___x_944_ = lean_apply_4(v_h__1_939_, v_a_941_, lean_box(0), v_a_942_, v_a_943_);
return v___x_944_;
}
else
{
lean_object* v_a_945_; lean_object* v_a_946_; lean_object* v_a_947_; lean_object* v___x_948_; 
lean_dec(v_h__1_939_);
v_a_945_ = lean_ctor_get(v_step_938_, 0);
lean_inc(v_a_945_);
v_a_946_ = lean_ctor_get(v_step_938_, 1);
lean_inc(v_a_946_);
v_a_947_ = lean_ctor_get(v_step_938_, 2);
lean_inc(v_a_947_);
lean_dec_ref_known(v_step_938_, 3);
v___x_948_ = lean_apply_3(v_h__2_940_, v_a_945_, v_a_946_, v_a_947_);
return v___x_948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_949_, lean_object* v_00_u03b2_950_, lean_object* v_inst_951_, lean_object* v_motive_952_, lean_object* v_step_953_, lean_object* v_h__1_954_, lean_object* v_h__2_955_){
_start:
{
if (lean_obj_tag(v_step_953_) == 0)
{
lean_object* v_a_956_; lean_object* v_a_957_; lean_object* v_a_958_; lean_object* v___x_959_; 
lean_dec(v_h__2_955_);
v_a_956_ = lean_ctor_get(v_step_953_, 0);
lean_inc(v_a_956_);
v_a_957_ = lean_ctor_get(v_step_953_, 1);
lean_inc(v_a_957_);
v_a_958_ = lean_ctor_get(v_step_953_, 2);
lean_inc(v_a_958_);
lean_dec_ref_known(v_step_953_, 3);
v___x_959_ = lean_apply_4(v_h__1_954_, v_a_956_, lean_box(0), v_a_957_, v_a_958_);
return v___x_959_;
}
else
{
lean_object* v_a_960_; lean_object* v_a_961_; lean_object* v_a_962_; lean_object* v___x_963_; 
lean_dec(v_h__1_954_);
v_a_960_ = lean_ctor_get(v_step_953_, 0);
lean_inc(v_a_960_);
v_a_961_ = lean_ctor_get(v_step_953_, 1);
lean_inc(v_a_961_);
v_a_962_ = lean_ctor_get(v_step_953_, 2);
lean_inc(v_a_962_);
lean_dec_ref_known(v_step_953_, 3);
v___x_963_ = lean_apply_3(v_h__2_955_, v_a_960_, v_a_961_, v_a_962_);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_964_, lean_object* v_00_u03b2_965_, lean_object* v_inst_966_, lean_object* v_motive_967_, lean_object* v_step_968_, lean_object* v_h__1_969_, lean_object* v_h__2_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(v_00_u03b1_964_, v_00_u03b2_965_, v_inst_966_, v_motive_967_, v_step_968_, v_h__1_969_, v_h__2_970_);
lean_dec_ref(v_inst_966_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object* v_x_972_, lean_object* v_h__1_973_, lean_object* v_h__2_974_){
_start:
{
lean_object* v_l_975_; 
v_l_975_ = lean_ctor_get(v_x_972_, 3);
if (lean_obj_tag(v_l_975_) == 0)
{
lean_object* v_size_976_; lean_object* v_k_977_; lean_object* v_v_978_; lean_object* v_r_979_; lean_object* v_size_980_; lean_object* v_k_981_; lean_object* v_v_982_; lean_object* v_l_983_; lean_object* v_r_984_; lean_object* v___x_985_; 
lean_inc_ref(v_l_975_);
lean_dec(v_h__1_973_);
v_size_976_ = lean_ctor_get(v_x_972_, 0);
lean_inc(v_size_976_);
v_k_977_ = lean_ctor_get(v_x_972_, 1);
lean_inc(v_k_977_);
v_v_978_ = lean_ctor_get(v_x_972_, 2);
lean_inc(v_v_978_);
v_r_979_ = lean_ctor_get(v_x_972_, 4);
lean_inc(v_r_979_);
lean_dec(v_x_972_);
v_size_980_ = lean_ctor_get(v_l_975_, 0);
lean_inc(v_size_980_);
v_k_981_ = lean_ctor_get(v_l_975_, 1);
lean_inc(v_k_981_);
v_v_982_ = lean_ctor_get(v_l_975_, 2);
lean_inc(v_v_982_);
v_l_983_ = lean_ctor_get(v_l_975_, 3);
lean_inc(v_l_983_);
v_r_984_ = lean_ctor_get(v_l_975_, 4);
lean_inc(v_r_984_);
lean_dec_ref_known(v_l_975_, 5);
v___x_985_ = lean_apply_10(v_h__2_974_, v_size_976_, v_k_977_, v_v_978_, v_size_980_, v_k_981_, v_v_982_, v_l_983_, v_r_984_, v_r_979_, lean_box(0));
return v___x_985_;
}
else
{
lean_object* v_size_986_; lean_object* v_k_987_; lean_object* v_v_988_; lean_object* v_r_989_; lean_object* v___x_990_; 
lean_dec(v_h__2_974_);
v_size_986_ = lean_ctor_get(v_x_972_, 0);
lean_inc(v_size_986_);
v_k_987_ = lean_ctor_get(v_x_972_, 1);
lean_inc(v_k_987_);
v_v_988_ = lean_ctor_get(v_x_972_, 2);
lean_inc(v_v_988_);
v_r_989_ = lean_ctor_get(v_x_972_, 4);
lean_inc(v_r_989_);
lean_dec(v_x_972_);
v___x_990_ = lean_apply_5(v_h__1_973_, v_size_986_, v_k_987_, v_v_988_, v_r_989_, lean_box(0));
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* v_00_u03b1_991_, lean_object* v_00_u03b2_992_, lean_object* v_motive_993_, lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_h__1_996_, lean_object* v_h__2_997_){
_start:
{
lean_object* v_l_998_; 
v_l_998_ = lean_ctor_get(v_x_994_, 3);
if (lean_obj_tag(v_l_998_) == 0)
{
lean_object* v_size_999_; lean_object* v_k_1000_; lean_object* v_v_1001_; lean_object* v_r_1002_; lean_object* v_size_1003_; lean_object* v_k_1004_; lean_object* v_v_1005_; lean_object* v_l_1006_; lean_object* v_r_1007_; lean_object* v___x_1008_; 
lean_inc_ref(v_l_998_);
lean_dec(v_h__1_996_);
v_size_999_ = lean_ctor_get(v_x_994_, 0);
lean_inc(v_size_999_);
v_k_1000_ = lean_ctor_get(v_x_994_, 1);
lean_inc(v_k_1000_);
v_v_1001_ = lean_ctor_get(v_x_994_, 2);
lean_inc(v_v_1001_);
v_r_1002_ = lean_ctor_get(v_x_994_, 4);
lean_inc(v_r_1002_);
lean_dec(v_x_994_);
v_size_1003_ = lean_ctor_get(v_l_998_, 0);
lean_inc(v_size_1003_);
v_k_1004_ = lean_ctor_get(v_l_998_, 1);
lean_inc(v_k_1004_);
v_v_1005_ = lean_ctor_get(v_l_998_, 2);
lean_inc(v_v_1005_);
v_l_1006_ = lean_ctor_get(v_l_998_, 3);
lean_inc(v_l_1006_);
v_r_1007_ = lean_ctor_get(v_l_998_, 4);
lean_inc(v_r_1007_);
lean_dec_ref_known(v_l_998_, 5);
v___x_1008_ = lean_apply_10(v_h__2_997_, v_size_999_, v_k_1000_, v_v_1001_, v_size_1003_, v_k_1004_, v_v_1005_, v_l_1006_, v_r_1007_, v_r_1002_, lean_box(0));
return v___x_1008_;
}
else
{
lean_object* v_size_1009_; lean_object* v_k_1010_; lean_object* v_v_1011_; lean_object* v_r_1012_; lean_object* v___x_1013_; 
lean_dec(v_h__2_997_);
v_size_1009_ = lean_ctor_get(v_x_994_, 0);
lean_inc(v_size_1009_);
v_k_1010_ = lean_ctor_get(v_x_994_, 1);
lean_inc(v_k_1010_);
v_v_1011_ = lean_ctor_get(v_x_994_, 2);
lean_inc(v_v_1011_);
v_r_1012_ = lean_ctor_get(v_x_994_, 4);
lean_inc(v_r_1012_);
lean_dec(v_x_994_);
v___x_1013_ = lean_apply_5(v_h__1_996_, v_size_1009_, v_k_1010_, v_v_1011_, v_r_1012_, lean_box(0));
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1014_, lean_object* v_h__1_1015_, lean_object* v_h__2_1016_, lean_object* v_h__3_1017_){
_start:
{
if (lean_obj_tag(v_x_1014_) == 0)
{
lean_object* v_r_1018_; 
lean_dec(v_h__1_1015_);
v_r_1018_ = lean_ctor_get(v_x_1014_, 4);
if (lean_obj_tag(v_r_1018_) == 0)
{
lean_object* v_size_1019_; lean_object* v_k_1020_; lean_object* v_v_1021_; lean_object* v_l_1022_; lean_object* v_size_1023_; lean_object* v_k_1024_; lean_object* v_v_1025_; lean_object* v_l_1026_; lean_object* v_r_1027_; lean_object* v___x_1028_; 
lean_inc_ref(v_r_1018_);
lean_dec(v_h__2_1016_);
v_size_1019_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_size_1019_);
v_k_1020_ = lean_ctor_get(v_x_1014_, 1);
lean_inc(v_k_1020_);
v_v_1021_ = lean_ctor_get(v_x_1014_, 2);
lean_inc(v_v_1021_);
v_l_1022_ = lean_ctor_get(v_x_1014_, 3);
lean_inc(v_l_1022_);
lean_dec_ref_known(v_x_1014_, 5);
v_size_1023_ = lean_ctor_get(v_r_1018_, 0);
lean_inc(v_size_1023_);
v_k_1024_ = lean_ctor_get(v_r_1018_, 1);
lean_inc(v_k_1024_);
v_v_1025_ = lean_ctor_get(v_r_1018_, 2);
lean_inc(v_v_1025_);
v_l_1026_ = lean_ctor_get(v_r_1018_, 3);
lean_inc(v_l_1026_);
v_r_1027_ = lean_ctor_get(v_r_1018_, 4);
lean_inc(v_r_1027_);
lean_dec_ref_known(v_r_1018_, 5);
v___x_1028_ = lean_apply_9(v_h__3_1017_, v_size_1019_, v_k_1020_, v_v_1021_, v_l_1022_, v_size_1023_, v_k_1024_, v_v_1025_, v_l_1026_, v_r_1027_);
return v___x_1028_;
}
else
{
lean_object* v_size_1029_; lean_object* v_k_1030_; lean_object* v_v_1031_; lean_object* v_l_1032_; lean_object* v___x_1033_; 
lean_dec(v_h__3_1017_);
v_size_1029_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_size_1029_);
v_k_1030_ = lean_ctor_get(v_x_1014_, 1);
lean_inc(v_k_1030_);
v_v_1031_ = lean_ctor_get(v_x_1014_, 2);
lean_inc(v_v_1031_);
v_l_1032_ = lean_ctor_get(v_x_1014_, 3);
lean_inc(v_l_1032_);
lean_dec_ref_known(v_x_1014_, 5);
v___x_1033_ = lean_apply_4(v_h__2_1016_, v_size_1029_, v_k_1030_, v_v_1031_, v_l_1032_);
return v___x_1033_;
}
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec(v_h__3_1017_);
lean_dec(v_h__2_1016_);
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_apply_1(v_h__1_1015_, v___x_1034_);
return v___x_1035_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1036_, lean_object* v_00_u03b2_1037_, lean_object* v_motive_1038_, lean_object* v_x_1039_, lean_object* v_h__1_1040_, lean_object* v_h__2_1041_, lean_object* v_h__3_1042_){
_start:
{
if (lean_obj_tag(v_x_1039_) == 0)
{
lean_object* v_r_1043_; 
lean_dec(v_h__1_1040_);
v_r_1043_ = lean_ctor_get(v_x_1039_, 4);
if (lean_obj_tag(v_r_1043_) == 0)
{
lean_object* v_size_1044_; lean_object* v_k_1045_; lean_object* v_v_1046_; lean_object* v_l_1047_; lean_object* v_size_1048_; lean_object* v_k_1049_; lean_object* v_v_1050_; lean_object* v_l_1051_; lean_object* v_r_1052_; lean_object* v___x_1053_; 
lean_inc_ref(v_r_1043_);
lean_dec(v_h__2_1041_);
v_size_1044_ = lean_ctor_get(v_x_1039_, 0);
lean_inc(v_size_1044_);
v_k_1045_ = lean_ctor_get(v_x_1039_, 1);
lean_inc(v_k_1045_);
v_v_1046_ = lean_ctor_get(v_x_1039_, 2);
lean_inc(v_v_1046_);
v_l_1047_ = lean_ctor_get(v_x_1039_, 3);
lean_inc(v_l_1047_);
lean_dec_ref_known(v_x_1039_, 5);
v_size_1048_ = lean_ctor_get(v_r_1043_, 0);
lean_inc(v_size_1048_);
v_k_1049_ = lean_ctor_get(v_r_1043_, 1);
lean_inc(v_k_1049_);
v_v_1050_ = lean_ctor_get(v_r_1043_, 2);
lean_inc(v_v_1050_);
v_l_1051_ = lean_ctor_get(v_r_1043_, 3);
lean_inc(v_l_1051_);
v_r_1052_ = lean_ctor_get(v_r_1043_, 4);
lean_inc(v_r_1052_);
lean_dec_ref_known(v_r_1043_, 5);
v___x_1053_ = lean_apply_9(v_h__3_1042_, v_size_1044_, v_k_1045_, v_v_1046_, v_l_1047_, v_size_1048_, v_k_1049_, v_v_1050_, v_l_1051_, v_r_1052_);
return v___x_1053_;
}
else
{
lean_object* v_size_1054_; lean_object* v_k_1055_; lean_object* v_v_1056_; lean_object* v_l_1057_; lean_object* v___x_1058_; 
lean_dec(v_h__3_1042_);
v_size_1054_ = lean_ctor_get(v_x_1039_, 0);
lean_inc(v_size_1054_);
v_k_1055_ = lean_ctor_get(v_x_1039_, 1);
lean_inc(v_k_1055_);
v_v_1056_ = lean_ctor_get(v_x_1039_, 2);
lean_inc(v_v_1056_);
v_l_1057_ = lean_ctor_get(v_x_1039_, 3);
lean_inc(v_l_1057_);
lean_dec_ref_known(v_x_1039_, 5);
v___x_1058_ = lean_apply_4(v_h__2_1041_, v_size_1054_, v_k_1055_, v_v_1056_, v_l_1057_);
return v___x_1058_;
}
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_dec(v_h__3_1042_);
lean_dec(v_h__2_1041_);
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_apply_1(v_h__1_1040_, v___x_1059_);
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object* v_x_1061_, lean_object* v_h__1_1062_, lean_object* v_h__2_1063_){
_start:
{
lean_object* v_r_1064_; 
v_r_1064_ = lean_ctor_get(v_x_1061_, 4);
if (lean_obj_tag(v_r_1064_) == 0)
{
lean_object* v_size_1065_; lean_object* v_k_1066_; lean_object* v_v_1067_; lean_object* v_l_1068_; lean_object* v_size_1069_; lean_object* v_k_1070_; lean_object* v_v_1071_; lean_object* v_l_1072_; lean_object* v_r_1073_; lean_object* v___x_1074_; 
lean_inc_ref(v_r_1064_);
lean_dec(v_h__1_1062_);
v_size_1065_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_size_1065_);
v_k_1066_ = lean_ctor_get(v_x_1061_, 1);
lean_inc(v_k_1066_);
v_v_1067_ = lean_ctor_get(v_x_1061_, 2);
lean_inc(v_v_1067_);
v_l_1068_ = lean_ctor_get(v_x_1061_, 3);
lean_inc(v_l_1068_);
lean_dec(v_x_1061_);
v_size_1069_ = lean_ctor_get(v_r_1064_, 0);
lean_inc(v_size_1069_);
v_k_1070_ = lean_ctor_get(v_r_1064_, 1);
lean_inc(v_k_1070_);
v_v_1071_ = lean_ctor_get(v_r_1064_, 2);
lean_inc(v_v_1071_);
v_l_1072_ = lean_ctor_get(v_r_1064_, 3);
lean_inc(v_l_1072_);
v_r_1073_ = lean_ctor_get(v_r_1064_, 4);
lean_inc(v_r_1073_);
lean_dec_ref_known(v_r_1064_, 5);
v___x_1074_ = lean_apply_10(v_h__2_1063_, v_size_1065_, v_k_1066_, v_v_1067_, v_l_1068_, v_size_1069_, v_k_1070_, v_v_1071_, v_l_1072_, v_r_1073_, lean_box(0));
return v___x_1074_;
}
else
{
lean_object* v_size_1075_; lean_object* v_k_1076_; lean_object* v_v_1077_; lean_object* v_l_1078_; lean_object* v___x_1079_; 
lean_dec(v_h__2_1063_);
v_size_1075_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_size_1075_);
v_k_1076_ = lean_ctor_get(v_x_1061_, 1);
lean_inc(v_k_1076_);
v_v_1077_ = lean_ctor_get(v_x_1061_, 2);
lean_inc(v_v_1077_);
v_l_1078_ = lean_ctor_get(v_x_1061_, 3);
lean_inc(v_l_1078_);
lean_dec(v_x_1061_);
v___x_1079_ = lean_apply_5(v_h__1_1062_, v_size_1075_, v_k_1076_, v_v_1077_, v_l_1078_, lean_box(0));
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1080_, lean_object* v_00_u03b2_1081_, lean_object* v_motive_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_h__1_1085_, lean_object* v_h__2_1086_){
_start:
{
lean_object* v_r_1087_; 
v_r_1087_ = lean_ctor_get(v_x_1083_, 4);
if (lean_obj_tag(v_r_1087_) == 0)
{
lean_object* v_size_1088_; lean_object* v_k_1089_; lean_object* v_v_1090_; lean_object* v_l_1091_; lean_object* v_size_1092_; lean_object* v_k_1093_; lean_object* v_v_1094_; lean_object* v_l_1095_; lean_object* v_r_1096_; lean_object* v___x_1097_; 
lean_inc_ref(v_r_1087_);
lean_dec(v_h__1_1085_);
v_size_1088_ = lean_ctor_get(v_x_1083_, 0);
lean_inc(v_size_1088_);
v_k_1089_ = lean_ctor_get(v_x_1083_, 1);
lean_inc(v_k_1089_);
v_v_1090_ = lean_ctor_get(v_x_1083_, 2);
lean_inc(v_v_1090_);
v_l_1091_ = lean_ctor_get(v_x_1083_, 3);
lean_inc(v_l_1091_);
lean_dec(v_x_1083_);
v_size_1092_ = lean_ctor_get(v_r_1087_, 0);
lean_inc(v_size_1092_);
v_k_1093_ = lean_ctor_get(v_r_1087_, 1);
lean_inc(v_k_1093_);
v_v_1094_ = lean_ctor_get(v_r_1087_, 2);
lean_inc(v_v_1094_);
v_l_1095_ = lean_ctor_get(v_r_1087_, 3);
lean_inc(v_l_1095_);
v_r_1096_ = lean_ctor_get(v_r_1087_, 4);
lean_inc(v_r_1096_);
lean_dec_ref_known(v_r_1087_, 5);
v___x_1097_ = lean_apply_10(v_h__2_1086_, v_size_1088_, v_k_1089_, v_v_1090_, v_l_1091_, v_size_1092_, v_k_1093_, v_v_1094_, v_l_1095_, v_r_1096_, lean_box(0));
return v___x_1097_;
}
else
{
lean_object* v_size_1098_; lean_object* v_k_1099_; lean_object* v_v_1100_; lean_object* v_l_1101_; lean_object* v___x_1102_; 
lean_dec(v_h__2_1086_);
v_size_1098_ = lean_ctor_get(v_x_1083_, 0);
lean_inc(v_size_1098_);
v_k_1099_ = lean_ctor_get(v_x_1083_, 1);
lean_inc(v_k_1099_);
v_v_1100_ = lean_ctor_get(v_x_1083_, 2);
lean_inc(v_v_1100_);
v_l_1101_ = lean_ctor_get(v_x_1083_, 3);
lean_inc(v_l_1101_);
lean_dec(v_x_1083_);
v___x_1102_ = lean_apply_5(v_h__1_1085_, v_size_1098_, v_k_1099_, v_v_1100_, v_l_1101_, lean_box(0));
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object* v_x_1103_, lean_object* v_x_1104_, lean_object* v_h__1_1105_, lean_object* v_h__2_1106_, lean_object* v_h__3_1107_){
_start:
{
if (lean_obj_tag(v_x_1103_) == 0)
{
lean_object* v_l_1108_; 
lean_dec(v_h__1_1105_);
v_l_1108_ = lean_ctor_get(v_x_1103_, 3);
if (lean_obj_tag(v_l_1108_) == 0)
{
lean_object* v_size_1109_; lean_object* v_k_1110_; lean_object* v_v_1111_; lean_object* v_r_1112_; lean_object* v_size_1113_; lean_object* v_k_1114_; lean_object* v_v_1115_; lean_object* v_l_1116_; lean_object* v_r_1117_; lean_object* v___x_1118_; 
lean_inc_ref(v_l_1108_);
lean_dec(v_h__2_1106_);
v_size_1109_ = lean_ctor_get(v_x_1103_, 0);
lean_inc(v_size_1109_);
v_k_1110_ = lean_ctor_get(v_x_1103_, 1);
lean_inc(v_k_1110_);
v_v_1111_ = lean_ctor_get(v_x_1103_, 2);
lean_inc(v_v_1111_);
v_r_1112_ = lean_ctor_get(v_x_1103_, 4);
lean_inc(v_r_1112_);
lean_dec_ref_known(v_x_1103_, 5);
v_size_1113_ = lean_ctor_get(v_l_1108_, 0);
lean_inc(v_size_1113_);
v_k_1114_ = lean_ctor_get(v_l_1108_, 1);
lean_inc(v_k_1114_);
v_v_1115_ = lean_ctor_get(v_l_1108_, 2);
lean_inc(v_v_1115_);
v_l_1116_ = lean_ctor_get(v_l_1108_, 3);
lean_inc(v_l_1116_);
v_r_1117_ = lean_ctor_get(v_l_1108_, 4);
lean_inc(v_r_1117_);
lean_dec_ref_known(v_l_1108_, 5);
v___x_1118_ = lean_apply_10(v_h__3_1107_, v_size_1109_, v_k_1110_, v_v_1111_, v_size_1113_, v_k_1114_, v_v_1115_, v_l_1116_, v_r_1117_, v_r_1112_, v_x_1104_);
return v___x_1118_;
}
else
{
lean_object* v_size_1119_; lean_object* v_k_1120_; lean_object* v_v_1121_; lean_object* v_r_1122_; lean_object* v___x_1123_; 
lean_dec(v_h__3_1107_);
v_size_1119_ = lean_ctor_get(v_x_1103_, 0);
lean_inc(v_size_1119_);
v_k_1120_ = lean_ctor_get(v_x_1103_, 1);
lean_inc(v_k_1120_);
v_v_1121_ = lean_ctor_get(v_x_1103_, 2);
lean_inc(v_v_1121_);
v_r_1122_ = lean_ctor_get(v_x_1103_, 4);
lean_inc(v_r_1122_);
lean_dec_ref_known(v_x_1103_, 5);
v___x_1123_ = lean_apply_5(v_h__2_1106_, v_size_1119_, v_k_1120_, v_v_1121_, v_r_1122_, v_x_1104_);
return v___x_1123_;
}
}
else
{
lean_object* v___x_1124_; 
lean_dec(v_h__3_1107_);
lean_dec(v_h__2_1106_);
v___x_1124_ = lean_apply_1(v_h__1_1105_, v_x_1104_);
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_motive_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_, lean_object* v_h__1_1130_, lean_object* v_h__2_1131_, lean_object* v_h__3_1132_){
_start:
{
if (lean_obj_tag(v_x_1128_) == 0)
{
lean_object* v_l_1133_; 
lean_dec(v_h__1_1130_);
v_l_1133_ = lean_ctor_get(v_x_1128_, 3);
if (lean_obj_tag(v_l_1133_) == 0)
{
lean_object* v_size_1134_; lean_object* v_k_1135_; lean_object* v_v_1136_; lean_object* v_r_1137_; lean_object* v_size_1138_; lean_object* v_k_1139_; lean_object* v_v_1140_; lean_object* v_l_1141_; lean_object* v_r_1142_; lean_object* v___x_1143_; 
lean_inc_ref(v_l_1133_);
lean_dec(v_h__2_1131_);
v_size_1134_ = lean_ctor_get(v_x_1128_, 0);
lean_inc(v_size_1134_);
v_k_1135_ = lean_ctor_get(v_x_1128_, 1);
lean_inc(v_k_1135_);
v_v_1136_ = lean_ctor_get(v_x_1128_, 2);
lean_inc(v_v_1136_);
v_r_1137_ = lean_ctor_get(v_x_1128_, 4);
lean_inc(v_r_1137_);
lean_dec_ref_known(v_x_1128_, 5);
v_size_1138_ = lean_ctor_get(v_l_1133_, 0);
lean_inc(v_size_1138_);
v_k_1139_ = lean_ctor_get(v_l_1133_, 1);
lean_inc(v_k_1139_);
v_v_1140_ = lean_ctor_get(v_l_1133_, 2);
lean_inc(v_v_1140_);
v_l_1141_ = lean_ctor_get(v_l_1133_, 3);
lean_inc(v_l_1141_);
v_r_1142_ = lean_ctor_get(v_l_1133_, 4);
lean_inc(v_r_1142_);
lean_dec_ref_known(v_l_1133_, 5);
v___x_1143_ = lean_apply_10(v_h__3_1132_, v_size_1134_, v_k_1135_, v_v_1136_, v_size_1138_, v_k_1139_, v_v_1140_, v_l_1141_, v_r_1142_, v_r_1137_, v_x_1129_);
return v___x_1143_;
}
else
{
lean_object* v_size_1144_; lean_object* v_k_1145_; lean_object* v_v_1146_; lean_object* v_r_1147_; lean_object* v___x_1148_; 
lean_dec(v_h__3_1132_);
v_size_1144_ = lean_ctor_get(v_x_1128_, 0);
lean_inc(v_size_1144_);
v_k_1145_ = lean_ctor_get(v_x_1128_, 1);
lean_inc(v_k_1145_);
v_v_1146_ = lean_ctor_get(v_x_1128_, 2);
lean_inc(v_v_1146_);
v_r_1147_ = lean_ctor_get(v_x_1128_, 4);
lean_inc(v_r_1147_);
lean_dec_ref_known(v_x_1128_, 5);
v___x_1148_ = lean_apply_5(v_h__2_1131_, v_size_1144_, v_k_1145_, v_v_1146_, v_r_1147_, v_x_1129_);
return v___x_1148_;
}
}
else
{
lean_object* v___x_1149_; 
lean_dec(v_h__3_1132_);
lean_dec(v_h__2_1131_);
v___x_1149_ = lean_apply_1(v_h__1_1130_, v_x_1129_);
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1150_, lean_object* v_h__1_1151_, lean_object* v_h__2_1152_, lean_object* v_h__3_1153_){
_start:
{
if (lean_obj_tag(v_x_1150_) == 0)
{
lean_object* v_l_1154_; 
lean_dec(v_h__1_1151_);
v_l_1154_ = lean_ctor_get(v_x_1150_, 3);
if (lean_obj_tag(v_l_1154_) == 0)
{
lean_object* v_size_1155_; lean_object* v_k_1156_; lean_object* v_v_1157_; lean_object* v_r_1158_; lean_object* v_size_1159_; lean_object* v_k_1160_; lean_object* v_v_1161_; lean_object* v_l_1162_; lean_object* v_r_1163_; lean_object* v___x_1164_; 
lean_inc_ref(v_l_1154_);
lean_dec(v_h__2_1152_);
v_size_1155_ = lean_ctor_get(v_x_1150_, 0);
lean_inc(v_size_1155_);
v_k_1156_ = lean_ctor_get(v_x_1150_, 1);
lean_inc(v_k_1156_);
v_v_1157_ = lean_ctor_get(v_x_1150_, 2);
lean_inc(v_v_1157_);
v_r_1158_ = lean_ctor_get(v_x_1150_, 4);
lean_inc(v_r_1158_);
lean_dec_ref_known(v_x_1150_, 5);
v_size_1159_ = lean_ctor_get(v_l_1154_, 0);
lean_inc(v_size_1159_);
v_k_1160_ = lean_ctor_get(v_l_1154_, 1);
lean_inc(v_k_1160_);
v_v_1161_ = lean_ctor_get(v_l_1154_, 2);
lean_inc(v_v_1161_);
v_l_1162_ = lean_ctor_get(v_l_1154_, 3);
lean_inc(v_l_1162_);
v_r_1163_ = lean_ctor_get(v_l_1154_, 4);
lean_inc(v_r_1163_);
lean_dec_ref_known(v_l_1154_, 5);
v___x_1164_ = lean_apply_9(v_h__3_1153_, v_size_1155_, v_k_1156_, v_v_1157_, v_size_1159_, v_k_1160_, v_v_1161_, v_l_1162_, v_r_1163_, v_r_1158_);
return v___x_1164_;
}
else
{
lean_object* v_size_1165_; lean_object* v_k_1166_; lean_object* v_v_1167_; lean_object* v_r_1168_; lean_object* v___x_1169_; 
lean_dec(v_h__3_1153_);
v_size_1165_ = lean_ctor_get(v_x_1150_, 0);
lean_inc(v_size_1165_);
v_k_1166_ = lean_ctor_get(v_x_1150_, 1);
lean_inc(v_k_1166_);
v_v_1167_ = lean_ctor_get(v_x_1150_, 2);
lean_inc(v_v_1167_);
v_r_1168_ = lean_ctor_get(v_x_1150_, 4);
lean_inc(v_r_1168_);
lean_dec_ref_known(v_x_1150_, 5);
v___x_1169_ = lean_apply_4(v_h__2_1152_, v_size_1165_, v_k_1166_, v_v_1167_, v_r_1168_);
return v___x_1169_;
}
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_dec(v_h__3_1153_);
lean_dec(v_h__2_1152_);
v___x_1170_ = lean_box(0);
v___x_1171_ = lean_apply_1(v_h__1_1151_, v___x_1170_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_motive_1174_, lean_object* v_x_1175_, lean_object* v_h__1_1176_, lean_object* v_h__2_1177_, lean_object* v_h__3_1178_){
_start:
{
if (lean_obj_tag(v_x_1175_) == 0)
{
lean_object* v_l_1179_; 
lean_dec(v_h__1_1176_);
v_l_1179_ = lean_ctor_get(v_x_1175_, 3);
if (lean_obj_tag(v_l_1179_) == 0)
{
lean_object* v_size_1180_; lean_object* v_k_1181_; lean_object* v_v_1182_; lean_object* v_r_1183_; lean_object* v_size_1184_; lean_object* v_k_1185_; lean_object* v_v_1186_; lean_object* v_l_1187_; lean_object* v_r_1188_; lean_object* v___x_1189_; 
lean_inc_ref(v_l_1179_);
lean_dec(v_h__2_1177_);
v_size_1180_ = lean_ctor_get(v_x_1175_, 0);
lean_inc(v_size_1180_);
v_k_1181_ = lean_ctor_get(v_x_1175_, 1);
lean_inc(v_k_1181_);
v_v_1182_ = lean_ctor_get(v_x_1175_, 2);
lean_inc(v_v_1182_);
v_r_1183_ = lean_ctor_get(v_x_1175_, 4);
lean_inc(v_r_1183_);
lean_dec_ref_known(v_x_1175_, 5);
v_size_1184_ = lean_ctor_get(v_l_1179_, 0);
lean_inc(v_size_1184_);
v_k_1185_ = lean_ctor_get(v_l_1179_, 1);
lean_inc(v_k_1185_);
v_v_1186_ = lean_ctor_get(v_l_1179_, 2);
lean_inc(v_v_1186_);
v_l_1187_ = lean_ctor_get(v_l_1179_, 3);
lean_inc(v_l_1187_);
v_r_1188_ = lean_ctor_get(v_l_1179_, 4);
lean_inc(v_r_1188_);
lean_dec_ref_known(v_l_1179_, 5);
v___x_1189_ = lean_apply_9(v_h__3_1178_, v_size_1180_, v_k_1181_, v_v_1182_, v_size_1184_, v_k_1185_, v_v_1186_, v_l_1187_, v_r_1188_, v_r_1183_);
return v___x_1189_;
}
else
{
lean_object* v_size_1190_; lean_object* v_k_1191_; lean_object* v_v_1192_; lean_object* v_r_1193_; lean_object* v___x_1194_; 
lean_dec(v_h__3_1178_);
v_size_1190_ = lean_ctor_get(v_x_1175_, 0);
lean_inc(v_size_1190_);
v_k_1191_ = lean_ctor_get(v_x_1175_, 1);
lean_inc(v_k_1191_);
v_v_1192_ = lean_ctor_get(v_x_1175_, 2);
lean_inc(v_v_1192_);
v_r_1193_ = lean_ctor_get(v_x_1175_, 4);
lean_inc(v_r_1193_);
lean_dec_ref_known(v_x_1175_, 5);
v___x_1194_ = lean_apply_4(v_h__2_1177_, v_size_1190_, v_k_1191_, v_v_1192_, v_r_1193_);
return v___x_1194_;
}
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec(v_h__3_1178_);
lean_dec(v_h__2_1177_);
v___x_1195_ = lean_box(0);
v___x_1196_ = lean_apply_1(v_h__1_1176_, v___x_1195_);
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* v_x_1197_, lean_object* v_h__1_1198_, lean_object* v_h__2_1199_){
_start:
{
lean_object* v_l_1200_; 
v_l_1200_ = lean_ctor_get(v_x_1197_, 3);
if (lean_obj_tag(v_l_1200_) == 0)
{
lean_object* v_size_1201_; lean_object* v_k_1202_; lean_object* v_v_1203_; lean_object* v_r_1204_; lean_object* v_size_1205_; lean_object* v_k_1206_; lean_object* v_v_1207_; lean_object* v_l_1208_; lean_object* v_r_1209_; lean_object* v___x_1210_; 
lean_inc_ref(v_l_1200_);
lean_dec(v_h__1_1198_);
v_size_1201_ = lean_ctor_get(v_x_1197_, 0);
lean_inc(v_size_1201_);
v_k_1202_ = lean_ctor_get(v_x_1197_, 1);
lean_inc(v_k_1202_);
v_v_1203_ = lean_ctor_get(v_x_1197_, 2);
lean_inc(v_v_1203_);
v_r_1204_ = lean_ctor_get(v_x_1197_, 4);
lean_inc(v_r_1204_);
lean_dec(v_x_1197_);
v_size_1205_ = lean_ctor_get(v_l_1200_, 0);
lean_inc(v_size_1205_);
v_k_1206_ = lean_ctor_get(v_l_1200_, 1);
lean_inc(v_k_1206_);
v_v_1207_ = lean_ctor_get(v_l_1200_, 2);
lean_inc(v_v_1207_);
v_l_1208_ = lean_ctor_get(v_l_1200_, 3);
lean_inc(v_l_1208_);
v_r_1209_ = lean_ctor_get(v_l_1200_, 4);
lean_inc(v_r_1209_);
lean_dec_ref_known(v_l_1200_, 5);
v___x_1210_ = lean_apply_10(v_h__2_1199_, v_size_1201_, v_k_1202_, v_v_1203_, v_size_1205_, v_k_1206_, v_v_1207_, v_l_1208_, v_r_1209_, v_r_1204_, lean_box(0));
return v___x_1210_;
}
else
{
lean_object* v_size_1211_; lean_object* v_k_1212_; lean_object* v_v_1213_; lean_object* v_r_1214_; lean_object* v___x_1215_; 
lean_dec(v_h__2_1199_);
v_size_1211_ = lean_ctor_get(v_x_1197_, 0);
lean_inc(v_size_1211_);
v_k_1212_ = lean_ctor_get(v_x_1197_, 1);
lean_inc(v_k_1212_);
v_v_1213_ = lean_ctor_get(v_x_1197_, 2);
lean_inc(v_v_1213_);
v_r_1214_ = lean_ctor_get(v_x_1197_, 4);
lean_inc(v_r_1214_);
lean_dec(v_x_1197_);
v___x_1215_ = lean_apply_5(v_h__1_1198_, v_size_1211_, v_k_1212_, v_v_1213_, v_r_1214_, lean_box(0));
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* v_00_u03b1_1216_, lean_object* v_00_u03b2_1217_, lean_object* v_motive_1218_, lean_object* v_x_1219_, lean_object* v_x_1220_, lean_object* v_h__1_1221_, lean_object* v_h__2_1222_){
_start:
{
lean_object* v_l_1223_; 
v_l_1223_ = lean_ctor_get(v_x_1219_, 3);
if (lean_obj_tag(v_l_1223_) == 0)
{
lean_object* v_size_1224_; lean_object* v_k_1225_; lean_object* v_v_1226_; lean_object* v_r_1227_; lean_object* v_size_1228_; lean_object* v_k_1229_; lean_object* v_v_1230_; lean_object* v_l_1231_; lean_object* v_r_1232_; lean_object* v___x_1233_; 
lean_inc_ref(v_l_1223_);
lean_dec(v_h__1_1221_);
v_size_1224_ = lean_ctor_get(v_x_1219_, 0);
lean_inc(v_size_1224_);
v_k_1225_ = lean_ctor_get(v_x_1219_, 1);
lean_inc(v_k_1225_);
v_v_1226_ = lean_ctor_get(v_x_1219_, 2);
lean_inc(v_v_1226_);
v_r_1227_ = lean_ctor_get(v_x_1219_, 4);
lean_inc(v_r_1227_);
lean_dec(v_x_1219_);
v_size_1228_ = lean_ctor_get(v_l_1223_, 0);
lean_inc(v_size_1228_);
v_k_1229_ = lean_ctor_get(v_l_1223_, 1);
lean_inc(v_k_1229_);
v_v_1230_ = lean_ctor_get(v_l_1223_, 2);
lean_inc(v_v_1230_);
v_l_1231_ = lean_ctor_get(v_l_1223_, 3);
lean_inc(v_l_1231_);
v_r_1232_ = lean_ctor_get(v_l_1223_, 4);
lean_inc(v_r_1232_);
lean_dec_ref_known(v_l_1223_, 5);
v___x_1233_ = lean_apply_10(v_h__2_1222_, v_size_1224_, v_k_1225_, v_v_1226_, v_size_1228_, v_k_1229_, v_v_1230_, v_l_1231_, v_r_1232_, v_r_1227_, lean_box(0));
return v___x_1233_;
}
else
{
lean_object* v_size_1234_; lean_object* v_k_1235_; lean_object* v_v_1236_; lean_object* v_r_1237_; lean_object* v___x_1238_; 
lean_dec(v_h__2_1222_);
v_size_1234_ = lean_ctor_get(v_x_1219_, 0);
lean_inc(v_size_1234_);
v_k_1235_ = lean_ctor_get(v_x_1219_, 1);
lean_inc(v_k_1235_);
v_v_1236_ = lean_ctor_get(v_x_1219_, 2);
lean_inc(v_v_1236_);
v_r_1237_ = lean_ctor_get(v_x_1219_, 4);
lean_inc(v_r_1237_);
lean_dec(v_x_1219_);
v___x_1238_ = lean_apply_5(v_h__1_1221_, v_size_1234_, v_k_1235_, v_v_1236_, v_r_1237_, lean_box(0));
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1239_, lean_object* v_h__1_1240_, lean_object* v_h__2_1241_, lean_object* v_h__3_1242_){
_start:
{
if (lean_obj_tag(v_x_1239_) == 0)
{
lean_object* v_r_1243_; 
lean_dec(v_h__1_1240_);
v_r_1243_ = lean_ctor_get(v_x_1239_, 4);
if (lean_obj_tag(v_r_1243_) == 0)
{
lean_object* v_size_1244_; lean_object* v_k_1245_; lean_object* v_v_1246_; lean_object* v_l_1247_; lean_object* v_size_1248_; lean_object* v_k_1249_; lean_object* v_v_1250_; lean_object* v_l_1251_; lean_object* v_r_1252_; lean_object* v___x_1253_; 
lean_inc_ref(v_r_1243_);
lean_dec(v_h__2_1241_);
v_size_1244_ = lean_ctor_get(v_x_1239_, 0);
lean_inc(v_size_1244_);
v_k_1245_ = lean_ctor_get(v_x_1239_, 1);
lean_inc(v_k_1245_);
v_v_1246_ = lean_ctor_get(v_x_1239_, 2);
lean_inc(v_v_1246_);
v_l_1247_ = lean_ctor_get(v_x_1239_, 3);
lean_inc(v_l_1247_);
lean_dec_ref_known(v_x_1239_, 5);
v_size_1248_ = lean_ctor_get(v_r_1243_, 0);
lean_inc(v_size_1248_);
v_k_1249_ = lean_ctor_get(v_r_1243_, 1);
lean_inc(v_k_1249_);
v_v_1250_ = lean_ctor_get(v_r_1243_, 2);
lean_inc(v_v_1250_);
v_l_1251_ = lean_ctor_get(v_r_1243_, 3);
lean_inc(v_l_1251_);
v_r_1252_ = lean_ctor_get(v_r_1243_, 4);
lean_inc(v_r_1252_);
lean_dec_ref_known(v_r_1243_, 5);
v___x_1253_ = lean_apply_9(v_h__3_1242_, v_size_1244_, v_k_1245_, v_v_1246_, v_l_1247_, v_size_1248_, v_k_1249_, v_v_1250_, v_l_1251_, v_r_1252_);
return v___x_1253_;
}
else
{
lean_object* v_size_1254_; lean_object* v_k_1255_; lean_object* v_v_1256_; lean_object* v_l_1257_; lean_object* v___x_1258_; 
lean_dec(v_h__3_1242_);
v_size_1254_ = lean_ctor_get(v_x_1239_, 0);
lean_inc(v_size_1254_);
v_k_1255_ = lean_ctor_get(v_x_1239_, 1);
lean_inc(v_k_1255_);
v_v_1256_ = lean_ctor_get(v_x_1239_, 2);
lean_inc(v_v_1256_);
v_l_1257_ = lean_ctor_get(v_x_1239_, 3);
lean_inc(v_l_1257_);
lean_dec_ref_known(v_x_1239_, 5);
v___x_1258_ = lean_apply_4(v_h__2_1241_, v_size_1254_, v_k_1255_, v_v_1256_, v_l_1257_);
return v___x_1258_;
}
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec(v_h__3_1242_);
lean_dec(v_h__2_1241_);
v___x_1259_ = lean_box(0);
v___x_1260_ = lean_apply_1(v_h__1_1240_, v___x_1259_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1261_, lean_object* v_00_u03b2_1262_, lean_object* v_motive_1263_, lean_object* v_x_1264_, lean_object* v_h__1_1265_, lean_object* v_h__2_1266_, lean_object* v_h__3_1267_){
_start:
{
if (lean_obj_tag(v_x_1264_) == 0)
{
lean_object* v_r_1268_; 
lean_dec(v_h__1_1265_);
v_r_1268_ = lean_ctor_get(v_x_1264_, 4);
if (lean_obj_tag(v_r_1268_) == 0)
{
lean_object* v_size_1269_; lean_object* v_k_1270_; lean_object* v_v_1271_; lean_object* v_l_1272_; lean_object* v_size_1273_; lean_object* v_k_1274_; lean_object* v_v_1275_; lean_object* v_l_1276_; lean_object* v_r_1277_; lean_object* v___x_1278_; 
lean_inc_ref(v_r_1268_);
lean_dec(v_h__2_1266_);
v_size_1269_ = lean_ctor_get(v_x_1264_, 0);
lean_inc(v_size_1269_);
v_k_1270_ = lean_ctor_get(v_x_1264_, 1);
lean_inc(v_k_1270_);
v_v_1271_ = lean_ctor_get(v_x_1264_, 2);
lean_inc(v_v_1271_);
v_l_1272_ = lean_ctor_get(v_x_1264_, 3);
lean_inc(v_l_1272_);
lean_dec_ref_known(v_x_1264_, 5);
v_size_1273_ = lean_ctor_get(v_r_1268_, 0);
lean_inc(v_size_1273_);
v_k_1274_ = lean_ctor_get(v_r_1268_, 1);
lean_inc(v_k_1274_);
v_v_1275_ = lean_ctor_get(v_r_1268_, 2);
lean_inc(v_v_1275_);
v_l_1276_ = lean_ctor_get(v_r_1268_, 3);
lean_inc(v_l_1276_);
v_r_1277_ = lean_ctor_get(v_r_1268_, 4);
lean_inc(v_r_1277_);
lean_dec_ref_known(v_r_1268_, 5);
v___x_1278_ = lean_apply_9(v_h__3_1267_, v_size_1269_, v_k_1270_, v_v_1271_, v_l_1272_, v_size_1273_, v_k_1274_, v_v_1275_, v_l_1276_, v_r_1277_);
return v___x_1278_;
}
else
{
lean_object* v_size_1279_; lean_object* v_k_1280_; lean_object* v_v_1281_; lean_object* v_l_1282_; lean_object* v___x_1283_; 
lean_dec(v_h__3_1267_);
v_size_1279_ = lean_ctor_get(v_x_1264_, 0);
lean_inc(v_size_1279_);
v_k_1280_ = lean_ctor_get(v_x_1264_, 1);
lean_inc(v_k_1280_);
v_v_1281_ = lean_ctor_get(v_x_1264_, 2);
lean_inc(v_v_1281_);
v_l_1282_ = lean_ctor_get(v_x_1264_, 3);
lean_inc(v_l_1282_);
lean_dec_ref_known(v_x_1264_, 5);
v___x_1283_ = lean_apply_4(v_h__2_1266_, v_size_1279_, v_k_1280_, v_v_1281_, v_l_1282_);
return v___x_1283_;
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec(v_h__3_1267_);
lean_dec(v_h__2_1266_);
v___x_1284_ = lean_box(0);
v___x_1285_ = lean_apply_1(v_h__1_1265_, v___x_1284_);
return v___x_1285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* v_x_1286_, lean_object* v_h__1_1287_, lean_object* v_h__2_1288_){
_start:
{
lean_object* v_r_1289_; 
v_r_1289_ = lean_ctor_get(v_x_1286_, 4);
if (lean_obj_tag(v_r_1289_) == 0)
{
lean_object* v_size_1290_; lean_object* v_k_1291_; lean_object* v_v_1292_; lean_object* v_l_1293_; lean_object* v_size_1294_; lean_object* v_k_1295_; lean_object* v_v_1296_; lean_object* v_l_1297_; lean_object* v_r_1298_; lean_object* v___x_1299_; 
lean_inc_ref(v_r_1289_);
lean_dec(v_h__1_1287_);
v_size_1290_ = lean_ctor_get(v_x_1286_, 0);
lean_inc(v_size_1290_);
v_k_1291_ = lean_ctor_get(v_x_1286_, 1);
lean_inc(v_k_1291_);
v_v_1292_ = lean_ctor_get(v_x_1286_, 2);
lean_inc(v_v_1292_);
v_l_1293_ = lean_ctor_get(v_x_1286_, 3);
lean_inc(v_l_1293_);
lean_dec(v_x_1286_);
v_size_1294_ = lean_ctor_get(v_r_1289_, 0);
lean_inc(v_size_1294_);
v_k_1295_ = lean_ctor_get(v_r_1289_, 1);
lean_inc(v_k_1295_);
v_v_1296_ = lean_ctor_get(v_r_1289_, 2);
lean_inc(v_v_1296_);
v_l_1297_ = lean_ctor_get(v_r_1289_, 3);
lean_inc(v_l_1297_);
v_r_1298_ = lean_ctor_get(v_r_1289_, 4);
lean_inc(v_r_1298_);
lean_dec_ref_known(v_r_1289_, 5);
v___x_1299_ = lean_apply_10(v_h__2_1288_, v_size_1290_, v_k_1291_, v_v_1292_, v_l_1293_, v_size_1294_, v_k_1295_, v_v_1296_, v_l_1297_, v_r_1298_, lean_box(0));
return v___x_1299_;
}
else
{
lean_object* v_size_1300_; lean_object* v_k_1301_; lean_object* v_v_1302_; lean_object* v_l_1303_; lean_object* v___x_1304_; 
lean_dec(v_h__2_1288_);
v_size_1300_ = lean_ctor_get(v_x_1286_, 0);
lean_inc(v_size_1300_);
v_k_1301_ = lean_ctor_get(v_x_1286_, 1);
lean_inc(v_k_1301_);
v_v_1302_ = lean_ctor_get(v_x_1286_, 2);
lean_inc(v_v_1302_);
v_l_1303_ = lean_ctor_get(v_x_1286_, 3);
lean_inc(v_l_1303_);
lean_dec(v_x_1286_);
v___x_1304_ = lean_apply_5(v_h__1_1287_, v_size_1300_, v_k_1301_, v_v_1302_, v_l_1303_, lean_box(0));
return v___x_1304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1305_, lean_object* v_00_u03b2_1306_, lean_object* v_motive_1307_, lean_object* v_x_1308_, lean_object* v_x_1309_, lean_object* v_h__1_1310_, lean_object* v_h__2_1311_){
_start:
{
lean_object* v_r_1312_; 
v_r_1312_ = lean_ctor_get(v_x_1308_, 4);
if (lean_obj_tag(v_r_1312_) == 0)
{
lean_object* v_size_1313_; lean_object* v_k_1314_; lean_object* v_v_1315_; lean_object* v_l_1316_; lean_object* v_size_1317_; lean_object* v_k_1318_; lean_object* v_v_1319_; lean_object* v_l_1320_; lean_object* v_r_1321_; lean_object* v___x_1322_; 
lean_inc_ref(v_r_1312_);
lean_dec(v_h__1_1310_);
v_size_1313_ = lean_ctor_get(v_x_1308_, 0);
lean_inc(v_size_1313_);
v_k_1314_ = lean_ctor_get(v_x_1308_, 1);
lean_inc(v_k_1314_);
v_v_1315_ = lean_ctor_get(v_x_1308_, 2);
lean_inc(v_v_1315_);
v_l_1316_ = lean_ctor_get(v_x_1308_, 3);
lean_inc(v_l_1316_);
lean_dec(v_x_1308_);
v_size_1317_ = lean_ctor_get(v_r_1312_, 0);
lean_inc(v_size_1317_);
v_k_1318_ = lean_ctor_get(v_r_1312_, 1);
lean_inc(v_k_1318_);
v_v_1319_ = lean_ctor_get(v_r_1312_, 2);
lean_inc(v_v_1319_);
v_l_1320_ = lean_ctor_get(v_r_1312_, 3);
lean_inc(v_l_1320_);
v_r_1321_ = lean_ctor_get(v_r_1312_, 4);
lean_inc(v_r_1321_);
lean_dec_ref_known(v_r_1312_, 5);
v___x_1322_ = lean_apply_10(v_h__2_1311_, v_size_1313_, v_k_1314_, v_v_1315_, v_l_1316_, v_size_1317_, v_k_1318_, v_v_1319_, v_l_1320_, v_r_1321_, lean_box(0));
return v___x_1322_;
}
else
{
lean_object* v_size_1323_; lean_object* v_k_1324_; lean_object* v_v_1325_; lean_object* v_l_1326_; lean_object* v___x_1327_; 
lean_dec(v_h__2_1311_);
v_size_1323_ = lean_ctor_get(v_x_1308_, 0);
lean_inc(v_size_1323_);
v_k_1324_ = lean_ctor_get(v_x_1308_, 1);
lean_inc(v_k_1324_);
v_v_1325_ = lean_ctor_get(v_x_1308_, 2);
lean_inc(v_v_1325_);
v_l_1326_ = lean_ctor_get(v_x_1308_, 3);
lean_inc(v_l_1326_);
lean_dec(v_x_1308_);
v___x_1327_ = lean_apply_5(v_h__1_1310_, v_size_1323_, v_k_1324_, v_v_1325_, v_l_1326_, lean_box(0));
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object* v_l_1328_, lean_object* v_h__1_1329_, lean_object* v_h__2_1330_){
_start:
{
if (lean_obj_tag(v_l_1328_) == 0)
{
lean_object* v_size_1331_; lean_object* v_k_1332_; lean_object* v_v_1333_; lean_object* v_l_1334_; lean_object* v_r_1335_; lean_object* v___x_1336_; 
lean_dec(v_h__1_1329_);
v_size_1331_ = lean_ctor_get(v_l_1328_, 0);
lean_inc(v_size_1331_);
v_k_1332_ = lean_ctor_get(v_l_1328_, 1);
lean_inc(v_k_1332_);
v_v_1333_ = lean_ctor_get(v_l_1328_, 2);
lean_inc(v_v_1333_);
v_l_1334_ = lean_ctor_get(v_l_1328_, 3);
lean_inc(v_l_1334_);
v_r_1335_ = lean_ctor_get(v_l_1328_, 4);
lean_inc(v_r_1335_);
lean_dec_ref_known(v_l_1328_, 5);
v___x_1336_ = lean_apply_7(v_h__2_1330_, v_size_1331_, v_k_1332_, v_v_1333_, v_l_1334_, v_r_1335_, lean_box(0), lean_box(0));
return v___x_1336_;
}
else
{
lean_object* v___x_1337_; 
lean_dec(v_h__2_1330_);
v___x_1337_ = lean_apply_2(v_h__1_1329_, lean_box(0), lean_box(0));
return v___x_1337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object* v_00_u03b1_1338_, lean_object* v_00_u03b2_1339_, lean_object* v_r_1340_, lean_object* v_motive_1341_, lean_object* v_l_1342_, lean_object* v_hl_1343_, lean_object* v_hlr_1344_, lean_object* v_h__1_1345_, lean_object* v_h__2_1346_){
_start:
{
if (lean_obj_tag(v_l_1342_) == 0)
{
lean_object* v_size_1347_; lean_object* v_k_1348_; lean_object* v_v_1349_; lean_object* v_l_1350_; lean_object* v_r_1351_; lean_object* v___x_1352_; 
lean_dec(v_h__1_1345_);
v_size_1347_ = lean_ctor_get(v_l_1342_, 0);
lean_inc(v_size_1347_);
v_k_1348_ = lean_ctor_get(v_l_1342_, 1);
lean_inc(v_k_1348_);
v_v_1349_ = lean_ctor_get(v_l_1342_, 2);
lean_inc(v_v_1349_);
v_l_1350_ = lean_ctor_get(v_l_1342_, 3);
lean_inc(v_l_1350_);
v_r_1351_ = lean_ctor_get(v_l_1342_, 4);
lean_inc(v_r_1351_);
lean_dec_ref_known(v_l_1342_, 5);
v___x_1352_ = lean_apply_7(v_h__2_1346_, v_size_1347_, v_k_1348_, v_v_1349_, v_l_1350_, v_r_1351_, lean_box(0), lean_box(0));
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; 
lean_dec(v_h__2_1346_);
v___x_1353_ = lean_apply_2(v_h__1_1345_, lean_box(0), lean_box(0));
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object* v_00_u03b1_1354_, lean_object* v_00_u03b2_1355_, lean_object* v_r_1356_, lean_object* v_motive_1357_, lean_object* v_l_1358_, lean_object* v_hl_1359_, lean_object* v_hlr_1360_, lean_object* v_h__1_1361_, lean_object* v_h__2_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(v_00_u03b1_1354_, v_00_u03b2_1355_, v_r_1356_, v_motive_1357_, v_l_1358_, v_hl_1359_, v_hlr_1360_, v_h__1_1361_, v_h__2_1362_);
lean_dec(v_r_1356_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(lean_object* v_x_1364_, lean_object* v_h__1_1365_){
_start:
{
lean_object* v_k_1366_; lean_object* v_v_1367_; lean_object* v_tree_1368_; lean_object* v___x_1369_; 
v_k_1366_ = lean_ctor_get(v_x_1364_, 0);
lean_inc(v_k_1366_);
v_v_1367_ = lean_ctor_get(v_x_1364_, 1);
lean_inc(v_v_1367_);
v_tree_1368_ = lean_ctor_get(v_x_1364_, 2);
lean_inc(v_tree_1368_);
lean_dec_ref(v_x_1364_);
v___x_1369_ = lean_apply_5(v_h__1_1365_, v_k_1366_, v_v_1367_, v_tree_1368_, lean_box(0), lean_box(0));
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object* v_00_u03b1_1370_, lean_object* v_00_u03b2_1371_, lean_object* v_l_x27_1372_, lean_object* v_r_x27_1373_, lean_object* v_motive_1374_, lean_object* v_x_1375_, lean_object* v_h__1_1376_){
_start:
{
lean_object* v_k_1377_; lean_object* v_v_1378_; lean_object* v_tree_1379_; lean_object* v___x_1380_; 
v_k_1377_ = lean_ctor_get(v_x_1375_, 0);
lean_inc(v_k_1377_);
v_v_1378_ = lean_ctor_get(v_x_1375_, 1);
lean_inc(v_v_1378_);
v_tree_1379_ = lean_ctor_get(v_x_1375_, 2);
lean_inc(v_tree_1379_);
lean_dec_ref(v_x_1375_);
v___x_1380_ = lean_apply_5(v_h__1_1376_, v_k_1377_, v_v_1378_, v_tree_1379_, lean_box(0), lean_box(0));
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object* v_00_u03b1_1381_, lean_object* v_00_u03b2_1382_, lean_object* v_l_x27_1383_, lean_object* v_r_x27_1384_, lean_object* v_motive_1385_, lean_object* v_x_1386_, lean_object* v_h__1_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(v_00_u03b1_1381_, v_00_u03b2_1382_, v_l_x27_1383_, v_r_x27_1384_, v_motive_1385_, v_x_1386_, v_h__1_1387_);
lean_dec(v_r_x27_1384_);
lean_dec(v_l_x27_1383_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(lean_object* v_r_1389_, lean_object* v_h__1_1390_, lean_object* v_h__2_1391_){
_start:
{
if (lean_obj_tag(v_r_1389_) == 0)
{
lean_object* v_size_1392_; lean_object* v_k_1393_; lean_object* v_v_1394_; lean_object* v_l_1395_; lean_object* v_r_1396_; lean_object* v___x_1397_; 
lean_dec(v_h__1_1390_);
v_size_1392_ = lean_ctor_get(v_r_1389_, 0);
lean_inc(v_size_1392_);
v_k_1393_ = lean_ctor_get(v_r_1389_, 1);
lean_inc(v_k_1393_);
v_v_1394_ = lean_ctor_get(v_r_1389_, 2);
lean_inc(v_v_1394_);
v_l_1395_ = lean_ctor_get(v_r_1389_, 3);
lean_inc(v_l_1395_);
v_r_1396_ = lean_ctor_get(v_r_1389_, 4);
lean_inc(v_r_1396_);
lean_dec_ref_known(v_r_1389_, 5);
v___x_1397_ = lean_apply_7(v_h__2_1391_, v_size_1392_, v_k_1393_, v_v_1394_, v_l_1395_, v_r_1396_, lean_box(0), lean_box(0));
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; 
lean_dec(v_h__2_1391_);
v___x_1398_ = lean_apply_2(v_h__1_1390_, lean_box(0), lean_box(0));
return v___x_1398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object* v_00_u03b1_1399_, lean_object* v_00_u03b2_1400_, lean_object* v_l_1401_, lean_object* v_motive_1402_, lean_object* v_r_1403_, lean_object* v_hr_1404_, lean_object* v_hlr_1405_, lean_object* v_h__1_1406_, lean_object* v_h__2_1407_){
_start:
{
if (lean_obj_tag(v_r_1403_) == 0)
{
lean_object* v_size_1408_; lean_object* v_k_1409_; lean_object* v_v_1410_; lean_object* v_l_1411_; lean_object* v_r_1412_; lean_object* v___x_1413_; 
lean_dec(v_h__1_1406_);
v_size_1408_ = lean_ctor_get(v_r_1403_, 0);
lean_inc(v_size_1408_);
v_k_1409_ = lean_ctor_get(v_r_1403_, 1);
lean_inc(v_k_1409_);
v_v_1410_ = lean_ctor_get(v_r_1403_, 2);
lean_inc(v_v_1410_);
v_l_1411_ = lean_ctor_get(v_r_1403_, 3);
lean_inc(v_l_1411_);
v_r_1412_ = lean_ctor_get(v_r_1403_, 4);
lean_inc(v_r_1412_);
lean_dec_ref_known(v_r_1403_, 5);
v___x_1413_ = lean_apply_7(v_h__2_1407_, v_size_1408_, v_k_1409_, v_v_1410_, v_l_1411_, v_r_1412_, lean_box(0), lean_box(0));
return v___x_1413_;
}
else
{
lean_object* v___x_1414_; 
lean_dec(v_h__2_1407_);
v___x_1414_ = lean_apply_2(v_h__1_1406_, lean_box(0), lean_box(0));
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_l_1417_, lean_object* v_motive_1418_, lean_object* v_r_1419_, lean_object* v_hr_1420_, lean_object* v_hlr_1421_, lean_object* v_h__1_1422_, lean_object* v_h__2_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(v_00_u03b1_1415_, v_00_u03b2_1416_, v_l_1417_, v_motive_1418_, v_r_1419_, v_hr_1420_, v_hlr_1421_, v_h__1_1422_, v_h__2_1423_);
lean_dec(v_l_1417_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(lean_object* v_r_1425_, lean_object* v_h__1_1426_, lean_object* v_h__2_1427_){
_start:
{
if (lean_obj_tag(v_r_1425_) == 0)
{
lean_object* v_size_1428_; lean_object* v_k_1429_; lean_object* v_v_1430_; lean_object* v_l_1431_; lean_object* v_r_1432_; lean_object* v___x_1433_; 
lean_dec(v_h__1_1426_);
v_size_1428_ = lean_ctor_get(v_r_1425_, 0);
lean_inc(v_size_1428_);
v_k_1429_ = lean_ctor_get(v_r_1425_, 1);
lean_inc(v_k_1429_);
v_v_1430_ = lean_ctor_get(v_r_1425_, 2);
lean_inc(v_v_1430_);
v_l_1431_ = lean_ctor_get(v_r_1425_, 3);
lean_inc(v_l_1431_);
v_r_1432_ = lean_ctor_get(v_r_1425_, 4);
lean_inc(v_r_1432_);
lean_dec_ref_known(v_r_1425_, 5);
v___x_1433_ = lean_apply_7(v_h__2_1427_, v_size_1428_, v_k_1429_, v_v_1430_, v_l_1431_, v_r_1432_, lean_box(0), lean_box(0));
return v___x_1433_;
}
else
{
lean_object* v___x_1434_; 
lean_dec(v_h__2_1427_);
v___x_1434_ = lean_apply_2(v_h__1_1426_, lean_box(0), lean_box(0));
return v___x_1434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object* v_00_u03b1_1435_, lean_object* v_00_u03b2_1436_, lean_object* v_sz_1437_, lean_object* v_k_1438_, lean_object* v_v_1439_, lean_object* v_l_x27_1440_, lean_object* v_r_x27_1441_, lean_object* v_motive_1442_, lean_object* v_r_1443_, lean_object* v_hr_1444_, lean_object* v_hlr_1445_, lean_object* v_h__1_1446_, lean_object* v_h__2_1447_){
_start:
{
if (lean_obj_tag(v_r_1443_) == 0)
{
lean_object* v_size_1448_; lean_object* v_k_1449_; lean_object* v_v_1450_; lean_object* v_l_1451_; lean_object* v_r_1452_; lean_object* v___x_1453_; 
lean_dec(v_h__1_1446_);
v_size_1448_ = lean_ctor_get(v_r_1443_, 0);
lean_inc(v_size_1448_);
v_k_1449_ = lean_ctor_get(v_r_1443_, 1);
lean_inc(v_k_1449_);
v_v_1450_ = lean_ctor_get(v_r_1443_, 2);
lean_inc(v_v_1450_);
v_l_1451_ = lean_ctor_get(v_r_1443_, 3);
lean_inc(v_l_1451_);
v_r_1452_ = lean_ctor_get(v_r_1443_, 4);
lean_inc(v_r_1452_);
lean_dec_ref_known(v_r_1443_, 5);
v___x_1453_ = lean_apply_7(v_h__2_1447_, v_size_1448_, v_k_1449_, v_v_1450_, v_l_1451_, v_r_1452_, lean_box(0), lean_box(0));
return v___x_1453_;
}
else
{
lean_object* v___x_1454_; 
lean_dec(v_h__2_1447_);
v___x_1454_ = lean_apply_2(v_h__1_1446_, lean_box(0), lean_box(0));
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object* v_00_u03b1_1455_, lean_object* v_00_u03b2_1456_, lean_object* v_sz_1457_, lean_object* v_k_1458_, lean_object* v_v_1459_, lean_object* v_l_x27_1460_, lean_object* v_r_x27_1461_, lean_object* v_motive_1462_, lean_object* v_r_1463_, lean_object* v_hr_1464_, lean_object* v_hlr_1465_, lean_object* v_h__1_1466_, lean_object* v_h__2_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(v_00_u03b1_1455_, v_00_u03b2_1456_, v_sz_1457_, v_k_1458_, v_v_1459_, v_l_x27_1460_, v_r_x27_1461_, v_motive_1462_, v_r_1463_, v_hr_1464_, v_hlr_1465_, v_h__1_1466_, v_h__2_1467_);
lean_dec(v_r_x27_1461_);
lean_dec(v_l_x27_1460_);
lean_dec(v_v_1459_);
lean_dec(v_k_1458_);
lean_dec(v_sz_1457_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object* v_t_1469_, lean_object* v_h__1_1470_, lean_object* v_h__2_1471_){
_start:
{
if (lean_obj_tag(v_t_1469_) == 0)
{
lean_object* v_size_1472_; lean_object* v_k_1473_; lean_object* v_v_1474_; lean_object* v_l_1475_; lean_object* v_r_1476_; lean_object* v___x_1477_; 
lean_dec(v_h__1_1470_);
v_size_1472_ = lean_ctor_get(v_t_1469_, 0);
lean_inc(v_size_1472_);
v_k_1473_ = lean_ctor_get(v_t_1469_, 1);
lean_inc(v_k_1473_);
v_v_1474_ = lean_ctor_get(v_t_1469_, 2);
lean_inc(v_v_1474_);
v_l_1475_ = lean_ctor_get(v_t_1469_, 3);
lean_inc(v_l_1475_);
v_r_1476_ = lean_ctor_get(v_t_1469_, 4);
lean_inc(v_r_1476_);
lean_dec_ref_known(v_t_1469_, 5);
v___x_1477_ = lean_apply_6(v_h__2_1471_, v_size_1472_, v_k_1473_, v_v_1474_, v_l_1475_, v_r_1476_, lean_box(0));
return v___x_1477_;
}
else
{
lean_object* v___x_1478_; 
lean_dec(v_h__2_1471_);
v___x_1478_ = lean_apply_1(v_h__1_1470_, lean_box(0));
return v___x_1478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object* v_00_u03b1_1479_, lean_object* v_00_u03b2_1480_, lean_object* v_motive_1481_, lean_object* v_t_1482_, lean_object* v_hr_1483_, lean_object* v_h__1_1484_, lean_object* v_h__2_1485_){
_start:
{
if (lean_obj_tag(v_t_1482_) == 0)
{
lean_object* v_size_1486_; lean_object* v_k_1487_; lean_object* v_v_1488_; lean_object* v_l_1489_; lean_object* v_r_1490_; lean_object* v___x_1491_; 
lean_dec(v_h__1_1484_);
v_size_1486_ = lean_ctor_get(v_t_1482_, 0);
lean_inc(v_size_1486_);
v_k_1487_ = lean_ctor_get(v_t_1482_, 1);
lean_inc(v_k_1487_);
v_v_1488_ = lean_ctor_get(v_t_1482_, 2);
lean_inc(v_v_1488_);
v_l_1489_ = lean_ctor_get(v_t_1482_, 3);
lean_inc(v_l_1489_);
v_r_1490_ = lean_ctor_get(v_t_1482_, 4);
lean_inc(v_r_1490_);
lean_dec_ref_known(v_t_1482_, 5);
v___x_1491_ = lean_apply_6(v_h__2_1485_, v_size_1486_, v_k_1487_, v_v_1488_, v_l_1489_, v_r_1490_, lean_box(0));
return v___x_1491_;
}
else
{
lean_object* v___x_1492_; 
lean_dec(v_h__2_1485_);
v___x_1492_ = lean_apply_1(v_h__1_1484_, lean_box(0));
return v___x_1492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t v_x_1493_, lean_object* v_h__1_1494_, lean_object* v_h__2_1495_, lean_object* v_h__3_1496_){
_start:
{
switch(v_x_1493_)
{
case 0:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_dec(v_h__3_1496_);
lean_dec(v_h__2_1495_);
v___x_1497_ = lean_box(0);
v___x_1498_ = lean_apply_1(v_h__1_1494_, v___x_1497_);
return v___x_1498_;
}
case 1:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_dec(v_h__2_1495_);
lean_dec(v_h__1_1494_);
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_apply_1(v_h__3_1496_, v___x_1499_);
return v___x_1500_;
}
default: 
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec(v_h__3_1496_);
lean_dec(v_h__1_1494_);
v___x_1501_ = lean_box(0);
v___x_1502_ = lean_apply_1(v_h__2_1495_, v___x_1501_);
return v___x_1502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object* v_x_1503_, lean_object* v_h__1_1504_, lean_object* v_h__2_1505_, lean_object* v_h__3_1506_){
_start:
{
uint8_t v_x_33__boxed_1507_; lean_object* v_res_1508_; 
v_x_33__boxed_1507_ = lean_unbox(v_x_1503_);
v_res_1508_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_33__boxed_1507_, v_h__1_1504_, v_h__2_1505_, v_h__3_1506_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object* v_motive_1509_, uint8_t v_x_1510_, lean_object* v_h__1_1511_, lean_object* v_h__2_1512_, lean_object* v_h__3_1513_){
_start:
{
switch(v_x_1510_)
{
case 0:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec(v_h__3_1513_);
lean_dec(v_h__2_1512_);
v___x_1514_ = lean_box(0);
v___x_1515_ = lean_apply_1(v_h__1_1511_, v___x_1514_);
return v___x_1515_;
}
case 1:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec(v_h__2_1512_);
lean_dec(v_h__1_1511_);
v___x_1516_ = lean_box(0);
v___x_1517_ = lean_apply_1(v_h__3_1513_, v___x_1516_);
return v___x_1517_;
}
default: 
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec(v_h__3_1513_);
lean_dec(v_h__1_1511_);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_apply_1(v_h__2_1512_, v___x_1518_);
return v___x_1519_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object* v_motive_1520_, lean_object* v_x_1521_, lean_object* v_h__1_1522_, lean_object* v_h__2_1523_, lean_object* v_h__3_1524_){
_start:
{
uint8_t v_x_48__boxed_1525_; lean_object* v_res_1526_; 
v_x_48__boxed_1525_ = lean_unbox(v_x_1521_);
v_res_1526_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_1520_, v_x_48__boxed_1525_, v_h__1_1522_, v_h__2_1523_, v_h__3_1524_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___redArg(lean_object* v_x_1527_, lean_object* v_h__1_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_apply_4(v_h__1_1528_, v_x_1527_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(lean_object* v_00_u03b1_1530_, lean_object* v_00_u03b2_1531_, lean_object* v_l_x27_1532_, lean_object* v_motive_1533_, lean_object* v_x_1534_, lean_object* v_h__1_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_apply_4(v_h__1_1535_, v_x_1534_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___boxed(lean_object* v_00_u03b1_1537_, lean_object* v_00_u03b2_1538_, lean_object* v_l_x27_1539_, lean_object* v_motive_1540_, lean_object* v_x_1541_, lean_object* v_h__1_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(v_00_u03b1_1537_, v_00_u03b2_1538_, v_l_x27_1539_, v_motive_1540_, v_x_1541_, v_h__1_1542_);
lean_dec(v_l_x27_1539_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object* v_x_1544_, lean_object* v_h__1_1545_, lean_object* v_h__2_1546_){
_start:
{
if (lean_obj_tag(v_x_1544_) == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_dec(v_h__2_1546_);
v___x_1547_ = lean_box(0);
v___x_1548_ = lean_apply_1(v_h__1_1545_, v___x_1547_);
return v___x_1548_;
}
else
{
lean_object* v_val_1549_; lean_object* v_fst_1550_; lean_object* v_snd_1551_; lean_object* v___x_1552_; 
lean_dec(v_h__1_1545_);
v_val_1549_ = lean_ctor_get(v_x_1544_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v_x_1544_, 1);
v_fst_1550_ = lean_ctor_get(v_val_1549_, 0);
lean_inc(v_fst_1550_);
v_snd_1551_ = lean_ctor_get(v_val_1549_, 1);
lean_inc(v_snd_1551_);
lean_dec(v_val_1549_);
v___x_1552_ = lean_apply_2(v_h__2_1546_, v_fst_1550_, v_snd_1551_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* v_00_u03b1_1553_, lean_object* v_00_u03b2_1554_, lean_object* v_motive_1555_, lean_object* v_x_1556_, lean_object* v_h__1_1557_, lean_object* v_h__2_1558_){
_start:
{
if (lean_obj_tag(v_x_1556_) == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_dec(v_h__2_1558_);
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_apply_1(v_h__1_1557_, v___x_1559_);
return v___x_1560_;
}
else
{
lean_object* v_val_1561_; lean_object* v_fst_1562_; lean_object* v_snd_1563_; lean_object* v___x_1564_; 
lean_dec(v_h__1_1557_);
v_val_1561_ = lean_ctor_get(v_x_1556_, 0);
lean_inc(v_val_1561_);
lean_dec_ref_known(v_x_1556_, 1);
v_fst_1562_ = lean_ctor_get(v_val_1561_, 0);
lean_inc(v_fst_1562_);
v_snd_1563_ = lean_ctor_get(v_val_1561_, 1);
lean_inc(v_snd_1563_);
lean_dec(v_val_1561_);
v___x_1564_ = lean_apply_2(v_h__2_1558_, v_fst_1562_, v_snd_1563_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___redArg(lean_object* v_x_1565_, lean_object* v_h__1_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_apply_4(v_h__1_1566_, v_x_1565_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(lean_object* v_00_u03b1_1568_, lean_object* v_00_u03b2_1569_, lean_object* v_l_1570_, lean_object* v_motive_1571_, lean_object* v_x_1572_, lean_object* v_h__1_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_apply_4(v_h__1_1573_, v_x_1572_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_l_1577_, lean_object* v_motive_1578_, lean_object* v_x_1579_, lean_object* v_h__1_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(v_00_u03b1_1575_, v_00_u03b2_1576_, v_l_1577_, v_motive_1578_, v_x_1579_, v_h__1_1580_);
lean_dec(v_l_1577_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object* v_l_1582_, lean_object* v_h__1_1583_, lean_object* v_h__2_1584_){
_start:
{
if (lean_obj_tag(v_l_1582_) == 0)
{
lean_object* v_size_1585_; lean_object* v_k_1586_; lean_object* v_v_1587_; lean_object* v_l_1588_; lean_object* v_r_1589_; lean_object* v___x_1590_; 
lean_dec(v_h__1_1583_);
v_size_1585_ = lean_ctor_get(v_l_1582_, 0);
lean_inc(v_size_1585_);
v_k_1586_ = lean_ctor_get(v_l_1582_, 1);
lean_inc(v_k_1586_);
v_v_1587_ = lean_ctor_get(v_l_1582_, 2);
lean_inc(v_v_1587_);
v_l_1588_ = lean_ctor_get(v_l_1582_, 3);
lean_inc(v_l_1588_);
v_r_1589_ = lean_ctor_get(v_l_1582_, 4);
lean_inc(v_r_1589_);
lean_dec_ref_known(v_l_1582_, 5);
v___x_1590_ = lean_apply_5(v_h__2_1584_, v_size_1585_, v_k_1586_, v_v_1587_, v_l_1588_, v_r_1589_);
return v___x_1590_;
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec(v_h__2_1584_);
v___x_1591_ = lean_box(0);
v___x_1592_ = lean_apply_1(v_h__1_1583_, v___x_1591_);
return v___x_1592_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object* v_00_u03b1_1593_, lean_object* v_00_u03b2_1594_, lean_object* v_motive_1595_, lean_object* v_l_1596_, lean_object* v_h__1_1597_, lean_object* v_h__2_1598_){
_start:
{
if (lean_obj_tag(v_l_1596_) == 0)
{
lean_object* v_size_1599_; lean_object* v_k_1600_; lean_object* v_v_1601_; lean_object* v_l_1602_; lean_object* v_r_1603_; lean_object* v___x_1604_; 
lean_dec(v_h__1_1597_);
v_size_1599_ = lean_ctor_get(v_l_1596_, 0);
lean_inc(v_size_1599_);
v_k_1600_ = lean_ctor_get(v_l_1596_, 1);
lean_inc(v_k_1600_);
v_v_1601_ = lean_ctor_get(v_l_1596_, 2);
lean_inc(v_v_1601_);
v_l_1602_ = lean_ctor_get(v_l_1596_, 3);
lean_inc(v_l_1602_);
v_r_1603_ = lean_ctor_get(v_l_1596_, 4);
lean_inc(v_r_1603_);
lean_dec_ref_known(v_l_1596_, 5);
v___x_1604_ = lean_apply_5(v_h__2_1598_, v_size_1599_, v_k_1600_, v_v_1601_, v_l_1602_, v_r_1603_);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec(v_h__2_1598_);
v___x_1605_ = lean_box(0);
v___x_1606_ = lean_apply_1(v_h__1_1597_, v___x_1605_);
return v___x_1606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(lean_object* v_r_1607_, lean_object* v_h__1_1608_, lean_object* v_h__2_1609_){
_start:
{
if (lean_obj_tag(v_r_1607_) == 0)
{
lean_object* v_size_1610_; lean_object* v_k_1611_; lean_object* v_v_1612_; lean_object* v_l_1613_; lean_object* v_r_1614_; lean_object* v___x_1615_; 
lean_dec(v_h__1_1608_);
v_size_1610_ = lean_ctor_get(v_r_1607_, 0);
lean_inc(v_size_1610_);
v_k_1611_ = lean_ctor_get(v_r_1607_, 1);
lean_inc(v_k_1611_);
v_v_1612_ = lean_ctor_get(v_r_1607_, 2);
lean_inc(v_v_1612_);
v_l_1613_ = lean_ctor_get(v_r_1607_, 3);
lean_inc(v_l_1613_);
v_r_1614_ = lean_ctor_get(v_r_1607_, 4);
lean_inc(v_r_1614_);
lean_dec_ref_known(v_r_1607_, 5);
v___x_1615_ = lean_apply_5(v_h__2_1609_, v_size_1610_, v_k_1611_, v_v_1612_, v_l_1613_, v_r_1614_);
return v___x_1615_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec(v_h__2_1609_);
v___x_1616_ = lean_box(0);
v___x_1617_ = lean_apply_1(v_h__1_1608_, v___x_1616_);
return v___x_1617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object* v_00_u03b1_1618_, lean_object* v_00_u03b2_1619_, lean_object* v_motive_1620_, lean_object* v_r_1621_, lean_object* v_h__1_1622_, lean_object* v_h__2_1623_){
_start:
{
if (lean_obj_tag(v_r_1621_) == 0)
{
lean_object* v_size_1624_; lean_object* v_k_1625_; lean_object* v_v_1626_; lean_object* v_l_1627_; lean_object* v_r_1628_; lean_object* v___x_1629_; 
lean_dec(v_h__1_1622_);
v_size_1624_ = lean_ctor_get(v_r_1621_, 0);
lean_inc(v_size_1624_);
v_k_1625_ = lean_ctor_get(v_r_1621_, 1);
lean_inc(v_k_1625_);
v_v_1626_ = lean_ctor_get(v_r_1621_, 2);
lean_inc(v_v_1626_);
v_l_1627_ = lean_ctor_get(v_r_1621_, 3);
lean_inc(v_l_1627_);
v_r_1628_ = lean_ctor_get(v_r_1621_, 4);
lean_inc(v_r_1628_);
lean_dec_ref_known(v_r_1621_, 5);
v___x_1629_ = lean_apply_5(v_h__2_1623_, v_size_1624_, v_k_1625_, v_v_1626_, v_l_1627_, v_r_1628_);
return v___x_1629_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec(v_h__2_1623_);
v___x_1630_ = lean_box(0);
v___x_1631_ = lean_apply_1(v_h__1_1622_, v___x_1630_);
return v___x_1631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object* v_x_1632_, lean_object* v_h__1_1633_, lean_object* v_h__2_1634_){
_start:
{
if (lean_obj_tag(v_x_1632_) == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec(v_h__2_1634_);
v___x_1635_ = lean_box(0);
v___x_1636_ = lean_apply_1(v_h__1_1633_, v___x_1635_);
return v___x_1636_;
}
else
{
lean_object* v_val_1637_; lean_object* v___x_1638_; 
lean_dec(v_h__1_1633_);
v_val_1637_ = lean_ctor_get(v_x_1632_, 0);
lean_inc(v_val_1637_);
lean_dec_ref_known(v_x_1632_, 1);
v___x_1638_ = lean_apply_1(v_h__2_1634_, v_val_1637_);
return v___x_1638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_1639_, lean_object* v_00_u03b2_1640_, lean_object* v_motive_1641_, lean_object* v_x_1642_, lean_object* v_h__1_1643_, lean_object* v_h__2_1644_){
_start:
{
if (lean_obj_tag(v_x_1642_) == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v_h__2_1644_);
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_apply_1(v_h__1_1643_, v___x_1645_);
return v___x_1646_;
}
else
{
lean_object* v_val_1647_; lean_object* v___x_1648_; 
lean_dec(v_h__1_1643_);
v_val_1647_ = lean_ctor_get(v_x_1642_, 0);
lean_inc(v_val_1647_);
lean_dec_ref_known(v_x_1642_, 1);
v___x_1648_ = lean_apply_1(v_h__2_1644_, v_val_1647_);
return v___x_1648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(lean_object* v_x_1649_, lean_object* v_x_1650_, lean_object* v_h__1_1651_){
_start:
{
lean_object* v_size_1652_; lean_object* v_k_1653_; lean_object* v_v_1654_; lean_object* v_l_1655_; lean_object* v_r_1656_; lean_object* v___x_1657_; 
v_size_1652_ = lean_ctor_get(v_x_1649_, 0);
lean_inc(v_size_1652_);
v_k_1653_ = lean_ctor_get(v_x_1649_, 1);
lean_inc(v_k_1653_);
v_v_1654_ = lean_ctor_get(v_x_1649_, 2);
lean_inc(v_v_1654_);
v_l_1655_ = lean_ctor_get(v_x_1649_, 3);
lean_inc(v_l_1655_);
v_r_1656_ = lean_ctor_get(v_x_1649_, 4);
lean_inc(v_r_1656_);
lean_dec(v_x_1649_);
v___x_1657_ = lean_apply_8(v_h__1_1651_, v_size_1652_, v_k_1653_, v_v_1654_, v_l_1655_, v_r_1656_, lean_box(0), v_x_1650_, lean_box(0));
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter(lean_object* v_00_u03b1_1658_, lean_object* v_00_u03b2_1659_, lean_object* v_motive_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_, lean_object* v_h__1_1665_){
_start:
{
lean_object* v_size_1666_; lean_object* v_k_1667_; lean_object* v_v_1668_; lean_object* v_l_1669_; lean_object* v_r_1670_; lean_object* v___x_1671_; 
v_size_1666_ = lean_ctor_get(v_x_1661_, 0);
lean_inc(v_size_1666_);
v_k_1667_ = lean_ctor_get(v_x_1661_, 1);
lean_inc(v_k_1667_);
v_v_1668_ = lean_ctor_get(v_x_1661_, 2);
lean_inc(v_v_1668_);
v_l_1669_ = lean_ctor_get(v_x_1661_, 3);
lean_inc(v_l_1669_);
v_r_1670_ = lean_ctor_get(v_x_1661_, 4);
lean_inc(v_r_1670_);
lean_dec(v_x_1661_);
v___x_1671_ = lean_apply_8(v_h__1_1665_, v_size_1666_, v_k_1667_, v_v_1668_, v_l_1669_, v_r_1670_, lean_box(0), v_x_1663_, lean_box(0));
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(uint8_t v_x_1672_, lean_object* v_h__1_1673_, lean_object* v_h__2_1674_, lean_object* v_h__3_1675_){
_start:
{
switch(v_x_1672_)
{
case 0:
{
lean_object* v___x_1676_; 
lean_dec(v_h__3_1675_);
lean_dec(v_h__2_1674_);
v___x_1676_ = lean_apply_1(v_h__1_1673_, lean_box(0));
return v___x_1676_;
}
case 1:
{
lean_object* v___x_1677_; 
lean_dec(v_h__3_1675_);
lean_dec(v_h__1_1673_);
v___x_1677_ = lean_apply_1(v_h__2_1674_, lean_box(0));
return v___x_1677_;
}
default: 
{
lean_object* v___x_1678_; 
lean_dec(v_h__2_1674_);
lean_dec(v_h__1_1673_);
v___x_1678_ = lean_apply_1(v_h__3_1675_, lean_box(0));
return v___x_1678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg___boxed(lean_object* v_x_1679_, lean_object* v_h__1_1680_, lean_object* v_h__2_1681_, lean_object* v_h__3_1682_){
_start:
{
uint8_t v_x_33__boxed_1683_; lean_object* v_res_1684_; 
v_x_33__boxed_1683_ = lean_unbox(v_x_1679_);
v_res_1684_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(v_x_33__boxed_1683_, v_h__1_1680_, v_h__2_1681_, v_h__3_1682_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(lean_object* v_motive_1685_, uint8_t v_x_1686_, lean_object* v_h__1_1687_, lean_object* v_h__2_1688_, lean_object* v_h__3_1689_){
_start:
{
switch(v_x_1686_)
{
case 0:
{
lean_object* v___x_1690_; 
lean_dec(v_h__3_1689_);
lean_dec(v_h__2_1688_);
v___x_1690_ = lean_apply_1(v_h__1_1687_, lean_box(0));
return v___x_1690_;
}
case 1:
{
lean_object* v___x_1691_; 
lean_dec(v_h__3_1689_);
lean_dec(v_h__1_1687_);
v___x_1691_ = lean_apply_1(v_h__2_1688_, lean_box(0));
return v___x_1691_;
}
default: 
{
lean_object* v___x_1692_; 
lean_dec(v_h__2_1688_);
lean_dec(v_h__1_1687_);
v___x_1692_ = lean_apply_1(v_h__3_1689_, lean_box(0));
return v___x_1692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___boxed(lean_object* v_motive_1693_, lean_object* v_x_1694_, lean_object* v_h__1_1695_, lean_object* v_h__2_1696_, lean_object* v_h__3_1697_){
_start:
{
uint8_t v_x_42__boxed_1698_; lean_object* v_res_1699_; 
v_x_42__boxed_1698_ = lean_unbox(v_x_1694_);
v_res_1699_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(v_motive_1693_, v_x_42__boxed_1698_, v_h__1_1695_, v_h__2_1696_, v_h__3_1697_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t v_x_1700_, lean_object* v_h__1_1701_, lean_object* v_h__2_1702_, lean_object* v_h__3_1703_){
_start:
{
switch(v_x_1700_)
{
case 0:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec(v_h__3_1703_);
lean_dec(v_h__2_1702_);
v___x_1704_ = lean_box(0);
v___x_1705_ = lean_apply_1(v_h__1_1701_, v___x_1704_);
return v___x_1705_;
}
case 1:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec(v_h__3_1703_);
lean_dec(v_h__1_1701_);
v___x_1706_ = lean_box(0);
v___x_1707_ = lean_apply_1(v_h__2_1702_, v___x_1706_);
return v___x_1707_;
}
default: 
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_dec(v_h__2_1702_);
lean_dec(v_h__1_1701_);
v___x_1708_ = lean_box(0);
v___x_1709_ = lean_apply_1(v_h__3_1703_, v___x_1708_);
return v___x_1709_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_1710_, lean_object* v_h__1_1711_, lean_object* v_h__2_1712_, lean_object* v_h__3_1713_){
_start:
{
uint8_t v_x_33__boxed_1714_; lean_object* v_res_1715_; 
v_x_33__boxed_1714_ = lean_unbox(v_x_1710_);
v_res_1715_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_33__boxed_1714_, v_h__1_1711_, v_h__2_1712_, v_h__3_1713_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object* v_motive_1716_, uint8_t v_x_1717_, lean_object* v_h__1_1718_, lean_object* v_h__2_1719_, lean_object* v_h__3_1720_){
_start:
{
switch(v_x_1717_)
{
case 0:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec(v_h__3_1720_);
lean_dec(v_h__2_1719_);
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_apply_1(v_h__1_1718_, v___x_1721_);
return v___x_1722_;
}
case 1:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec(v_h__3_1720_);
lean_dec(v_h__1_1718_);
v___x_1723_ = lean_box(0);
v___x_1724_ = lean_apply_1(v_h__2_1719_, v___x_1723_);
return v___x_1724_;
}
default: 
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
lean_dec(v_h__2_1719_);
lean_dec(v_h__1_1718_);
v___x_1725_ = lean_box(0);
v___x_1726_ = lean_apply_1(v_h__3_1720_, v___x_1725_);
return v___x_1726_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object* v_motive_1727_, lean_object* v_x_1728_, lean_object* v_h__1_1729_, lean_object* v_h__2_1730_, lean_object* v_h__3_1731_){
_start:
{
uint8_t v_x_48__boxed_1732_; lean_object* v_res_1733_; 
v_x_48__boxed_1732_ = lean_unbox(v_x_1728_);
v_res_1733_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(v_motive_1727_, v_x_48__boxed_1732_, v_h__1_1729_, v_h__2_1730_, v_h__3_1731_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object* v_x_1734_, lean_object* v_x_1735_, lean_object* v_h__1_1736_, lean_object* v_h__2_1737_){
_start:
{
if (lean_obj_tag(v_x_1734_) == 0)
{
lean_object* v_size_1738_; lean_object* v_k_1739_; lean_object* v_v_1740_; lean_object* v_l_1741_; lean_object* v_r_1742_; lean_object* v___x_1743_; 
lean_dec(v_h__1_1736_);
v_size_1738_ = lean_ctor_get(v_x_1734_, 0);
lean_inc(v_size_1738_);
v_k_1739_ = lean_ctor_get(v_x_1734_, 1);
lean_inc(v_k_1739_);
v_v_1740_ = lean_ctor_get(v_x_1734_, 2);
lean_inc(v_v_1740_);
v_l_1741_ = lean_ctor_get(v_x_1734_, 3);
lean_inc(v_l_1741_);
v_r_1742_ = lean_ctor_get(v_x_1734_, 4);
lean_inc(v_r_1742_);
lean_dec_ref_known(v_x_1734_, 5);
v___x_1743_ = lean_apply_6(v_h__2_1737_, v_size_1738_, v_k_1739_, v_v_1740_, v_l_1741_, v_r_1742_, v_x_1735_);
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; 
lean_dec(v_h__2_1737_);
v___x_1744_ = lean_apply_1(v_h__1_1736_, v_x_1735_);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object* v_00_u03b1_1745_, lean_object* v_00_u03b2_1746_, lean_object* v_motive_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_, lean_object* v_h__1_1750_, lean_object* v_h__2_1751_){
_start:
{
if (lean_obj_tag(v_x_1748_) == 0)
{
lean_object* v_size_1752_; lean_object* v_k_1753_; lean_object* v_v_1754_; lean_object* v_l_1755_; lean_object* v_r_1756_; lean_object* v___x_1757_; 
lean_dec(v_h__1_1750_);
v_size_1752_ = lean_ctor_get(v_x_1748_, 0);
lean_inc(v_size_1752_);
v_k_1753_ = lean_ctor_get(v_x_1748_, 1);
lean_inc(v_k_1753_);
v_v_1754_ = lean_ctor_get(v_x_1748_, 2);
lean_inc(v_v_1754_);
v_l_1755_ = lean_ctor_get(v_x_1748_, 3);
lean_inc(v_l_1755_);
v_r_1756_ = lean_ctor_get(v_x_1748_, 4);
lean_inc(v_r_1756_);
lean_dec_ref_known(v_x_1748_, 5);
v___x_1757_ = lean_apply_6(v_h__2_1751_, v_size_1752_, v_k_1753_, v_v_1754_, v_l_1755_, v_r_1756_, v_x_1749_);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; 
lean_dec(v_h__2_1751_);
v___x_1758_ = lean_apply_1(v_h__1_1750_, v_x_1749_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(lean_object* v_x_1759_, lean_object* v_c_1760_, lean_object* v_x_1761_, lean_object* v_r_1762_){
_start:
{
if (lean_obj_tag(v_c_1760_) == 0)
{
lean_object* v___x_1763_; 
v___x_1763_ = l_List_head_x3f___redArg(v_r_1762_);
return v___x_1763_;
}
else
{
lean_object* v_val_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
v_val_1764_ = lean_ctor_get(v_c_1760_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_c_1760_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v_c_1760_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_val_1764_);
lean_dec(v_c_1760_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_val_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed(lean_object* v_x_1772_, lean_object* v_c_1773_, lean_object* v_x_1774_, lean_object* v_r_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(v_x_1772_, v_c_1773_, v_x_1774_, v_r_1775_);
lean_dec(v_r_1775_);
lean_dec(v_x_1772_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(lean_object* v_inst_1778_, lean_object* v_k_1779_, lean_object* v_t_1780_){
_start:
{
lean_object* v___f_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___f_1781_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0));
v___x_1782_ = lean_apply_1(v_inst_1778_, v_k_1779_);
v___x_1783_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___x_1782_, v_t_1780_, v___f_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098(lean_object* v_00_u03b1_1784_, lean_object* v_00_u03b2_1785_, lean_object* v_inst_1786_, lean_object* v_k_1787_, lean_object* v_t_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(v_inst_1786_, v_k_1787_, v_t_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(lean_object* v_x_1790_, lean_object* v_x_1791_){
_start:
{
switch(lean_obj_tag(v_x_1791_))
{
case 0:
{
lean_object* v_a_1792_; lean_object* v_a_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_a_1792_ = lean_ctor_get(v_x_1791_, 0);
lean_inc(v_a_1792_);
v_a_1793_ = lean_ctor_get(v_x_1791_, 1);
lean_inc(v_a_1793_);
lean_dec_ref_known(v_x_1791_, 3);
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v_a_1792_);
lean_ctor_set(v___x_1794_, 1, v_a_1793_);
v___x_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
case 1:
{
lean_object* v_a_1796_; 
v_a_1796_ = lean_ctor_get(v_x_1791_, 1);
lean_inc(v_a_1796_);
if (lean_obj_tag(v_a_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; 
v_a_1797_ = lean_ctor_get(v_x_1791_, 2);
lean_inc(v_a_1797_);
lean_dec_ref_known(v_x_1791_, 3);
v___x_1798_ = l_List_head_x3f___redArg(v_a_1797_);
lean_dec(v_a_1797_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_inc(v_x_1790_);
return v_x_1790_;
}
else
{
return v___x_1798_;
}
}
else
{
lean_object* v_val_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref_known(v_x_1791_, 3);
v_val_1799_ = lean_ctor_get(v_a_1796_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_a_1796_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v_a_1796_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_val_1799_);
lean_dec(v_a_1796_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_val_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
default: 
{
lean_dec_ref_known(v_x_1791_, 3);
lean_inc(v_x_1790_);
return v_x_1790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* v_x_1807_, lean_object* v_x_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(v_x_1807_, v_x_1808_);
lean_dec(v_x_1807_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(lean_object* v_inst_1811_, lean_object* v_k_1812_, lean_object* v_t_1813_){
_start:
{
lean_object* v___f_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___f_1814_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0));
v___x_1815_ = lean_apply_1(v_inst_1811_, v_k_1812_);
v___x_1816_ = lean_box(0);
v___x_1817_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___x_1815_, v___x_1816_, v___f_1814_, v_t_1813_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27(lean_object* v_00_u03b1_1818_, lean_object* v_00_u03b2_1819_, lean_object* v_inst_1820_, lean_object* v_k_1821_, lean_object* v_t_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(v_inst_1820_, v_k_1821_, v_t_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_x_1824_, lean_object* v_x_1825_, lean_object* v_h__1_1826_, lean_object* v_h__2_1827_, lean_object* v_h__3_1828_){
_start:
{
switch(lean_obj_tag(v_x_1825_))
{
case 0:
{
lean_object* v_a_1829_; lean_object* v_a_1830_; lean_object* v_a_1831_; lean_object* v___x_1832_; 
lean_dec(v_h__3_1828_);
lean_dec(v_h__2_1827_);
v_a_1829_ = lean_ctor_get(v_x_1825_, 0);
lean_inc(v_a_1829_);
v_a_1830_ = lean_ctor_get(v_x_1825_, 1);
lean_inc(v_a_1830_);
v_a_1831_ = lean_ctor_get(v_x_1825_, 2);
lean_inc(v_a_1831_);
lean_dec_ref_known(v_x_1825_, 3);
v___x_1832_ = lean_apply_5(v_h__1_1826_, v_x_1824_, v_a_1829_, lean_box(0), v_a_1830_, v_a_1831_);
return v___x_1832_;
}
case 1:
{
lean_object* v_a_1833_; lean_object* v_a_1834_; lean_object* v_a_1835_; lean_object* v___x_1836_; 
lean_dec(v_h__3_1828_);
lean_dec(v_h__1_1826_);
v_a_1833_ = lean_ctor_get(v_x_1825_, 0);
lean_inc(v_a_1833_);
v_a_1834_ = lean_ctor_get(v_x_1825_, 1);
lean_inc(v_a_1834_);
v_a_1835_ = lean_ctor_get(v_x_1825_, 2);
lean_inc(v_a_1835_);
lean_dec_ref_known(v_x_1825_, 3);
v___x_1836_ = lean_apply_4(v_h__2_1827_, v_x_1824_, v_a_1833_, v_a_1834_, v_a_1835_);
return v___x_1836_;
}
default: 
{
lean_object* v_a_1837_; lean_object* v_a_1838_; lean_object* v_a_1839_; lean_object* v___x_1840_; 
lean_dec(v_h__2_1827_);
lean_dec(v_h__1_1826_);
v_a_1837_ = lean_ctor_get(v_x_1825_, 0);
lean_inc(v_a_1837_);
v_a_1838_ = lean_ctor_get(v_x_1825_, 1);
lean_inc(v_a_1838_);
v_a_1839_ = lean_ctor_get(v_x_1825_, 2);
lean_inc(v_a_1839_);
lean_dec_ref_known(v_x_1825_, 3);
v___x_1840_ = lean_apply_5(v_h__3_1828_, v_x_1824_, v_a_1837_, v_a_1838_, lean_box(0), v_a_1839_);
return v___x_1840_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_1841_, lean_object* v_00_u03b2_1842_, lean_object* v_inst_1843_, lean_object* v_k_1844_, lean_object* v_motive_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_, lean_object* v_h__1_1848_, lean_object* v_h__2_1849_, lean_object* v_h__3_1850_){
_start:
{
switch(lean_obj_tag(v_x_1847_))
{
case 0:
{
lean_object* v_a_1851_; lean_object* v_a_1852_; lean_object* v_a_1853_; lean_object* v___x_1854_; 
lean_dec(v_h__3_1850_);
lean_dec(v_h__2_1849_);
v_a_1851_ = lean_ctor_get(v_x_1847_, 0);
lean_inc(v_a_1851_);
v_a_1852_ = lean_ctor_get(v_x_1847_, 1);
lean_inc(v_a_1852_);
v_a_1853_ = lean_ctor_get(v_x_1847_, 2);
lean_inc(v_a_1853_);
lean_dec_ref_known(v_x_1847_, 3);
v___x_1854_ = lean_apply_5(v_h__1_1848_, v_x_1846_, v_a_1851_, lean_box(0), v_a_1852_, v_a_1853_);
return v___x_1854_;
}
case 1:
{
lean_object* v_a_1855_; lean_object* v_a_1856_; lean_object* v_a_1857_; lean_object* v___x_1858_; 
lean_dec(v_h__3_1850_);
lean_dec(v_h__1_1848_);
v_a_1855_ = lean_ctor_get(v_x_1847_, 0);
lean_inc(v_a_1855_);
v_a_1856_ = lean_ctor_get(v_x_1847_, 1);
lean_inc(v_a_1856_);
v_a_1857_ = lean_ctor_get(v_x_1847_, 2);
lean_inc(v_a_1857_);
lean_dec_ref_known(v_x_1847_, 3);
v___x_1858_ = lean_apply_4(v_h__2_1849_, v_x_1846_, v_a_1855_, v_a_1856_, v_a_1857_);
return v___x_1858_;
}
default: 
{
lean_object* v_a_1859_; lean_object* v_a_1860_; lean_object* v_a_1861_; lean_object* v___x_1862_; 
lean_dec(v_h__2_1849_);
lean_dec(v_h__1_1848_);
v_a_1859_ = lean_ctor_get(v_x_1847_, 0);
lean_inc(v_a_1859_);
v_a_1860_ = lean_ctor_get(v_x_1847_, 1);
lean_inc(v_a_1860_);
v_a_1861_ = lean_ctor_get(v_x_1847_, 2);
lean_inc(v_a_1861_);
lean_dec_ref_known(v_x_1847_, 3);
v___x_1862_ = lean_apply_5(v_h__3_1850_, v_x_1846_, v_a_1859_, v_a_1860_, lean_box(0), v_a_1861_);
return v___x_1862_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_1863_, lean_object* v_00_u03b2_1864_, lean_object* v_inst_1865_, lean_object* v_k_1866_, lean_object* v_motive_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_, lean_object* v_h__1_1870_, lean_object* v_h__2_1871_, lean_object* v_h__3_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(v_00_u03b1_1863_, v_00_u03b2_1864_, v_inst_1865_, v_k_1866_, v_motive_1867_, v_x_1868_, v_x_1869_, v_h__1_1870_, v_h__2_1871_, v_h__3_1872_);
lean_dec(v_k_1866_);
lean_dec_ref(v_inst_1865_);
return v_res_1873_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(lean_object* v_inst_1874_, lean_object* v_k_1875_, lean_object* v_k_x27_1876_){
_start:
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = lean_apply_2(v_inst_1874_, v_k_1875_, v_k_x27_1876_);
v___x_1878_ = lean_unbox(v___x_1877_);
if (v___x_1878_ == 1)
{
uint8_t v___x_1879_; 
v___x_1879_ = 2;
return v___x_1879_;
}
else
{
uint8_t v___x_1880_; 
v___x_1880_ = lean_unbox(v___x_1877_);
return v___x_1880_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed(lean_object* v_inst_1881_, lean_object* v_k_1882_, lean_object* v_k_x27_1883_){
_start:
{
uint8_t v_res_1884_; lean_object* v_r_1885_; 
v_res_1884_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(v_inst_1881_, v_k_1882_, v_k_x27_1883_);
v_r_1885_ = lean_box(v_res_1884_);
return v_r_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(lean_object* v_inst_1886_, lean_object* v_k_1887_, lean_object* v_t_1888_){
_start:
{
lean_object* v___f_1889_; lean_object* v___f_1890_; lean_object* v___x_1891_; 
v___f_1889_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1889_, 0, v_inst_1886_);
lean_closure_set(v___f_1889_, 1, v_k_1887_);
v___f_1890_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0));
v___x_1891_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_1889_, v_t_1888_, v___f_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098(lean_object* v_00_u03b1_1892_, lean_object* v_00_u03b2_1893_, lean_object* v_inst_1894_, lean_object* v_k_1895_, lean_object* v_t_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(v_inst_1894_, v_k_1895_, v_t_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
switch(lean_obj_tag(v_x_1899_))
{
case 0:
{
lean_object* v_a_1900_; lean_object* v_a_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v_a_1900_ = lean_ctor_get(v_x_1899_, 0);
v_a_1901_ = lean_ctor_get(v_x_1899_, 1);
lean_inc(v_a_1901_);
lean_inc(v_a_1900_);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v_a_1900_);
lean_ctor_set(v___x_1902_, 1, v_a_1901_);
v___x_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
return v___x_1903_;
}
case 1:
{
lean_object* v_a_1904_; lean_object* v___x_1905_; 
v_a_1904_ = lean_ctor_get(v_x_1899_, 2);
v___x_1905_ = l_List_head_x3f___redArg(v_a_1904_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_inc(v_x_1898_);
return v_x_1898_;
}
else
{
return v___x_1905_;
}
}
default: 
{
lean_inc(v_x_1898_);
return v_x_1898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* v_x_1906_, lean_object* v_x_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(v_x_1906_, v_x_1907_);
lean_dec_ref(v_x_1907_);
lean_dec(v_x_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(lean_object* v_inst_1910_, lean_object* v_k_1911_, lean_object* v_t_1912_){
_start:
{
lean_object* v___f_1913_; lean_object* v___f_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___f_1913_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1913_, 0, v_inst_1910_);
lean_closure_set(v___f_1913_, 1, v_k_1911_);
v___f_1914_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0));
v___x_1915_ = lean_box(0);
v___x_1916_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___f_1913_, v___x_1915_, v___f_1914_, v_t_1912_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27(lean_object* v_00_u03b1_1917_, lean_object* v_00_u03b2_1918_, lean_object* v_inst_1919_, lean_object* v_k_1920_, lean_object* v_t_1921_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(v_inst_1919_, v_k_1920_, v_t_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(uint8_t v_x_1923_, lean_object* v_h__1_1924_, lean_object* v_h__2_1925_){
_start:
{
if (v_x_1923_ == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec(v_h__2_1925_);
v___x_1926_ = lean_box(0);
v___x_1927_ = lean_apply_1(v_h__1_1924_, v___x_1926_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_dec(v_h__1_1924_);
v___x_1928_ = lean_box(v_x_1923_);
v___x_1929_ = lean_apply_2(v_h__2_1925_, v___x_1928_, lean_box(0));
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg___boxed(lean_object* v_x_1930_, lean_object* v_h__1_1931_, lean_object* v_h__2_1932_){
_start:
{
uint8_t v_x_13__boxed_1933_; lean_object* v_res_1934_; 
v_x_13__boxed_1933_ = lean_unbox(v_x_1930_);
v_res_1934_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(v_x_13__boxed_1933_, v_h__1_1931_, v_h__2_1932_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(lean_object* v_motive_1935_, uint8_t v_x_1936_, lean_object* v_h__1_1937_, lean_object* v_h__2_1938_){
_start:
{
if (v_x_1936_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
lean_dec(v_h__2_1938_);
v___x_1939_ = lean_box(0);
v___x_1940_ = lean_apply_1(v_h__1_1937_, v___x_1939_);
return v___x_1940_;
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
lean_dec(v_h__1_1937_);
v___x_1941_ = lean_box(v_x_1936_);
v___x_1942_ = lean_apply_2(v_h__2_1938_, v___x_1941_, lean_box(0));
return v___x_1942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___boxed(lean_object* v_motive_1943_, lean_object* v_x_1944_, lean_object* v_h__1_1945_, lean_object* v_h__2_1946_){
_start:
{
uint8_t v_x_24__boxed_1947_; lean_object* v_res_1948_; 
v_x_24__boxed_1947_ = lean_unbox(v_x_1944_);
v_res_1948_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(v_motive_1943_, v_x_24__boxed_1947_, v_h__1_1945_, v_h__2_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_x_1949_, lean_object* v_x_1950_, lean_object* v_h__1_1951_, lean_object* v_h__2_1952_, lean_object* v_h__3_1953_){
_start:
{
switch(lean_obj_tag(v_x_1950_))
{
case 0:
{
lean_object* v_a_1954_; lean_object* v_a_1955_; lean_object* v_a_1956_; lean_object* v___x_1957_; 
lean_dec(v_h__3_1953_);
lean_dec(v_h__2_1952_);
v_a_1954_ = lean_ctor_get(v_x_1950_, 0);
lean_inc(v_a_1954_);
v_a_1955_ = lean_ctor_get(v_x_1950_, 1);
lean_inc(v_a_1955_);
v_a_1956_ = lean_ctor_get(v_x_1950_, 2);
lean_inc(v_a_1956_);
lean_dec_ref_known(v_x_1950_, 3);
v___x_1957_ = lean_apply_5(v_h__1_1951_, v_x_1949_, v_a_1954_, lean_box(0), v_a_1955_, v_a_1956_);
return v___x_1957_;
}
case 1:
{
lean_object* v_a_1958_; lean_object* v_a_1959_; lean_object* v_a_1960_; lean_object* v___x_1961_; 
lean_dec(v_h__3_1953_);
lean_dec(v_h__1_1951_);
v_a_1958_ = lean_ctor_get(v_x_1950_, 0);
lean_inc(v_a_1958_);
v_a_1959_ = lean_ctor_get(v_x_1950_, 1);
lean_inc(v_a_1959_);
v_a_1960_ = lean_ctor_get(v_x_1950_, 2);
lean_inc(v_a_1960_);
lean_dec_ref_known(v_x_1950_, 3);
v___x_1961_ = lean_apply_4(v_h__2_1952_, v_x_1949_, v_a_1958_, v_a_1959_, v_a_1960_);
return v___x_1961_;
}
default: 
{
lean_object* v_a_1962_; lean_object* v_a_1963_; lean_object* v_a_1964_; lean_object* v___x_1965_; 
lean_dec(v_h__2_1952_);
lean_dec(v_h__1_1951_);
v_a_1962_ = lean_ctor_get(v_x_1950_, 0);
lean_inc(v_a_1962_);
v_a_1963_ = lean_ctor_get(v_x_1950_, 1);
lean_inc(v_a_1963_);
v_a_1964_ = lean_ctor_get(v_x_1950_, 2);
lean_inc(v_a_1964_);
lean_dec_ref_known(v_x_1950_, 3);
v___x_1965_ = lean_apply_5(v_h__3_1953_, v_x_1949_, v_a_1962_, v_a_1963_, lean_box(0), v_a_1964_);
return v___x_1965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_1966_, lean_object* v_00_u03b2_1967_, lean_object* v_inst_1968_, lean_object* v_k_1969_, lean_object* v_motive_1970_, lean_object* v_x_1971_, lean_object* v_x_1972_, lean_object* v_h__1_1973_, lean_object* v_h__2_1974_, lean_object* v_h__3_1975_){
_start:
{
switch(lean_obj_tag(v_x_1972_))
{
case 0:
{
lean_object* v_a_1976_; lean_object* v_a_1977_; lean_object* v_a_1978_; lean_object* v___x_1979_; 
lean_dec(v_h__3_1975_);
lean_dec(v_h__2_1974_);
v_a_1976_ = lean_ctor_get(v_x_1972_, 0);
lean_inc(v_a_1976_);
v_a_1977_ = lean_ctor_get(v_x_1972_, 1);
lean_inc(v_a_1977_);
v_a_1978_ = lean_ctor_get(v_x_1972_, 2);
lean_inc(v_a_1978_);
lean_dec_ref_known(v_x_1972_, 3);
v___x_1979_ = lean_apply_5(v_h__1_1973_, v_x_1971_, v_a_1976_, lean_box(0), v_a_1977_, v_a_1978_);
return v___x_1979_;
}
case 1:
{
lean_object* v_a_1980_; lean_object* v_a_1981_; lean_object* v_a_1982_; lean_object* v___x_1983_; 
lean_dec(v_h__3_1975_);
lean_dec(v_h__1_1973_);
v_a_1980_ = lean_ctor_get(v_x_1972_, 0);
lean_inc(v_a_1980_);
v_a_1981_ = lean_ctor_get(v_x_1972_, 1);
lean_inc(v_a_1981_);
v_a_1982_ = lean_ctor_get(v_x_1972_, 2);
lean_inc(v_a_1982_);
lean_dec_ref_known(v_x_1972_, 3);
v___x_1983_ = lean_apply_4(v_h__2_1974_, v_x_1971_, v_a_1980_, v_a_1981_, v_a_1982_);
return v___x_1983_;
}
default: 
{
lean_object* v_a_1984_; lean_object* v_a_1985_; lean_object* v_a_1986_; lean_object* v___x_1987_; 
lean_dec(v_h__2_1974_);
lean_dec(v_h__1_1973_);
v_a_1984_ = lean_ctor_get(v_x_1972_, 0);
lean_inc(v_a_1984_);
v_a_1985_ = lean_ctor_get(v_x_1972_, 1);
lean_inc(v_a_1985_);
v_a_1986_ = lean_ctor_get(v_x_1972_, 2);
lean_inc(v_a_1986_);
lean_dec_ref_known(v_x_1972_, 3);
v___x_1987_ = lean_apply_5(v_h__3_1975_, v_x_1971_, v_a_1984_, v_a_1985_, lean_box(0), v_a_1986_);
return v___x_1987_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_1988_, lean_object* v_00_u03b2_1989_, lean_object* v_inst_1990_, lean_object* v_k_1991_, lean_object* v_motive_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v_h__1_1995_, lean_object* v_h__2_1996_, lean_object* v_h__3_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(v_00_u03b1_1988_, v_00_u03b2_1989_, v_inst_1990_, v_k_1991_, v_motive_1992_, v_x_1993_, v_x_1994_, v_h__1_1995_, v_h__2_1996_, v_h__3_1997_);
lean_dec(v_k_1991_);
lean_dec_ref(v_inst_1990_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(uint8_t v_x_1999_, lean_object* v_h__1_2000_, lean_object* v_h__2_2001_){
_start:
{
if (v_x_1999_ == 2)
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_dec(v_h__2_2001_);
v___x_2002_ = lean_box(0);
v___x_2003_ = lean_apply_1(v_h__1_2000_, v___x_2002_);
return v___x_2003_;
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
lean_dec(v_h__1_2000_);
v___x_2004_ = lean_box(v_x_1999_);
v___x_2005_ = lean_apply_2(v_h__2_2001_, v___x_2004_, lean_box(0));
return v___x_2005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg___boxed(lean_object* v_x_2006_, lean_object* v_h__1_2007_, lean_object* v_h__2_2008_){
_start:
{
uint8_t v_x_13__boxed_2009_; lean_object* v_res_2010_; 
v_x_13__boxed_2009_ = lean_unbox(v_x_2006_);
v_res_2010_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(v_x_13__boxed_2009_, v_h__1_2007_, v_h__2_2008_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(lean_object* v_motive_2011_, uint8_t v_x_2012_, lean_object* v_h__1_2013_, lean_object* v_h__2_2014_){
_start:
{
if (v_x_2012_ == 2)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_dec(v_h__2_2014_);
v___x_2015_ = lean_box(0);
v___x_2016_ = lean_apply_1(v_h__1_2013_, v___x_2015_);
return v___x_2016_;
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_dec(v_h__1_2013_);
v___x_2017_ = lean_box(v_x_2012_);
v___x_2018_ = lean_apply_2(v_h__2_2014_, v___x_2017_, lean_box(0));
return v___x_2018_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___boxed(lean_object* v_motive_2019_, lean_object* v_x_2020_, lean_object* v_h__1_2021_, lean_object* v_h__2_2022_){
_start:
{
uint8_t v_x_24__boxed_2023_; lean_object* v_res_2024_; 
v_x_24__boxed_2023_ = lean_unbox(v_x_2020_);
v_res_2024_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(v_motive_2019_, v_x_24__boxed_2023_, v_h__1_2021_, v_h__2_2022_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(uint8_t v_x_2025_, lean_object* v_h__1_2026_, lean_object* v_h__2_2027_, lean_object* v_h__3_2028_){
_start:
{
switch(v_x_2025_)
{
case 0:
{
lean_object* v___x_2029_; 
lean_dec(v_h__2_2027_);
lean_dec(v_h__1_2026_);
v___x_2029_ = lean_apply_1(v_h__3_2028_, lean_box(0));
return v___x_2029_;
}
case 1:
{
lean_object* v___x_2030_; 
lean_dec(v_h__3_2028_);
lean_dec(v_h__1_2026_);
v___x_2030_ = lean_apply_1(v_h__2_2027_, lean_box(0));
return v___x_2030_;
}
default: 
{
lean_object* v___x_2031_; 
lean_dec(v_h__3_2028_);
lean_dec(v_h__2_2027_);
v___x_2031_ = lean_apply_1(v_h__1_2026_, lean_box(0));
return v___x_2031_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg___boxed(lean_object* v_x_2032_, lean_object* v_h__1_2033_, lean_object* v_h__2_2034_, lean_object* v_h__3_2035_){
_start:
{
uint8_t v_x_33__boxed_2036_; lean_object* v_res_2037_; 
v_x_33__boxed_2036_ = lean_unbox(v_x_2032_);
v_res_2037_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(v_x_33__boxed_2036_, v_h__1_2033_, v_h__2_2034_, v_h__3_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(lean_object* v_motive_2038_, uint8_t v_x_2039_, lean_object* v_h__1_2040_, lean_object* v_h__2_2041_, lean_object* v_h__3_2042_){
_start:
{
switch(v_x_2039_)
{
case 0:
{
lean_object* v___x_2043_; 
lean_dec(v_h__2_2041_);
lean_dec(v_h__1_2040_);
v___x_2043_ = lean_apply_1(v_h__3_2042_, lean_box(0));
return v___x_2043_;
}
case 1:
{
lean_object* v___x_2044_; 
lean_dec(v_h__3_2042_);
lean_dec(v_h__1_2040_);
v___x_2044_ = lean_apply_1(v_h__2_2041_, lean_box(0));
return v___x_2044_;
}
default: 
{
lean_object* v___x_2045_; 
lean_dec(v_h__3_2042_);
lean_dec(v_h__2_2041_);
v___x_2045_ = lean_apply_1(v_h__1_2040_, lean_box(0));
return v___x_2045_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___boxed(lean_object* v_motive_2046_, lean_object* v_x_2047_, lean_object* v_h__1_2048_, lean_object* v_h__2_2049_, lean_object* v_h__3_2050_){
_start:
{
uint8_t v_x_42__boxed_2051_; lean_object* v_res_2052_; 
v_x_42__boxed_2051_ = lean_unbox(v_x_2047_);
v_res_2052_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(v_motive_2046_, v_x_42__boxed_2051_, v_h__1_2048_, v_h__2_2049_, v_h__3_2050_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(lean_object* v_x_2053_, lean_object* v_x_2054_, lean_object* v_h__1_2055_, lean_object* v_h__2_2056_){
_start:
{
if (lean_obj_tag(v_x_2053_) == 0)
{
lean_object* v_size_2057_; lean_object* v_k_2058_; lean_object* v_v_2059_; lean_object* v_l_2060_; lean_object* v_r_2061_; lean_object* v___x_2062_; 
lean_dec(v_h__1_2055_);
v_size_2057_ = lean_ctor_get(v_x_2053_, 0);
lean_inc(v_size_2057_);
v_k_2058_ = lean_ctor_get(v_x_2053_, 1);
lean_inc(v_k_2058_);
v_v_2059_ = lean_ctor_get(v_x_2053_, 2);
lean_inc(v_v_2059_);
v_l_2060_ = lean_ctor_get(v_x_2053_, 3);
lean_inc(v_l_2060_);
v_r_2061_ = lean_ctor_get(v_x_2053_, 4);
lean_inc(v_r_2061_);
lean_dec_ref_known(v_x_2053_, 5);
v___x_2062_ = lean_apply_6(v_h__2_2056_, v_size_2057_, v_k_2058_, v_v_2059_, v_l_2060_, v_r_2061_, v_x_2054_);
return v___x_2062_;
}
else
{
lean_object* v___x_2063_; 
lean_dec(v_h__2_2056_);
v___x_2063_ = lean_apply_1(v_h__1_2055_, v_x_2054_);
return v___x_2063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter(lean_object* v_00_u03b1_2064_, lean_object* v_00_u03b2_2065_, lean_object* v_motive_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_, lean_object* v_h__1_2069_, lean_object* v_h__2_2070_){
_start:
{
if (lean_obj_tag(v_x_2067_) == 0)
{
lean_object* v_size_2071_; lean_object* v_k_2072_; lean_object* v_v_2073_; lean_object* v_l_2074_; lean_object* v_r_2075_; lean_object* v___x_2076_; 
lean_dec(v_h__1_2069_);
v_size_2071_ = lean_ctor_get(v_x_2067_, 0);
lean_inc(v_size_2071_);
v_k_2072_ = lean_ctor_get(v_x_2067_, 1);
lean_inc(v_k_2072_);
v_v_2073_ = lean_ctor_get(v_x_2067_, 2);
lean_inc(v_v_2073_);
v_l_2074_ = lean_ctor_get(v_x_2067_, 3);
lean_inc(v_l_2074_);
v_r_2075_ = lean_ctor_get(v_x_2067_, 4);
lean_inc(v_r_2075_);
lean_dec_ref_known(v_x_2067_, 5);
v___x_2076_ = lean_apply_6(v_h__2_2070_, v_size_2071_, v_k_2072_, v_v_2073_, v_l_2074_, v_r_2075_, v_x_2068_);
return v___x_2076_;
}
else
{
lean_object* v___x_2077_; 
lean_dec(v_h__2_2070_);
v___x_2077_ = lean_apply_1(v_h__1_2069_, v_x_2068_);
return v___x_2077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(lean_object* v_x_2078_, lean_object* v_x_2079_, lean_object* v_h__1_2080_){
_start:
{
lean_object* v_size_2081_; lean_object* v_k_2082_; lean_object* v_v_2083_; lean_object* v_l_2084_; lean_object* v_r_2085_; lean_object* v___x_2086_; 
v_size_2081_ = lean_ctor_get(v_x_2078_, 0);
lean_inc(v_size_2081_);
v_k_2082_ = lean_ctor_get(v_x_2078_, 1);
lean_inc(v_k_2082_);
v_v_2083_ = lean_ctor_get(v_x_2078_, 2);
lean_inc(v_v_2083_);
v_l_2084_ = lean_ctor_get(v_x_2078_, 3);
lean_inc(v_l_2084_);
v_r_2085_ = lean_ctor_get(v_x_2078_, 4);
lean_inc(v_r_2085_);
lean_dec(v_x_2078_);
v___x_2086_ = lean_apply_8(v_h__1_2080_, v_size_2081_, v_k_2082_, v_v_2083_, v_l_2084_, v_r_2085_, lean_box(0), v_x_2079_, lean_box(0));
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter(lean_object* v_00_u03b1_2087_, lean_object* v_00_u03b2_2088_, lean_object* v_motive_2089_, lean_object* v_x_2090_, lean_object* v_x_2091_, lean_object* v_x_2092_, lean_object* v_x_2093_, lean_object* v_h__1_2094_){
_start:
{
lean_object* v_size_2095_; lean_object* v_k_2096_; lean_object* v_v_2097_; lean_object* v_l_2098_; lean_object* v_r_2099_; lean_object* v___x_2100_; 
v_size_2095_ = lean_ctor_get(v_x_2090_, 0);
lean_inc(v_size_2095_);
v_k_2096_ = lean_ctor_get(v_x_2090_, 1);
lean_inc(v_k_2096_);
v_v_2097_ = lean_ctor_get(v_x_2090_, 2);
lean_inc(v_v_2097_);
v_l_2098_ = lean_ctor_get(v_x_2090_, 3);
lean_inc(v_l_2098_);
v_r_2099_ = lean_ctor_get(v_x_2090_, 4);
lean_inc(v_r_2099_);
lean_dec(v_x_2090_);
v___x_2100_ = lean_apply_8(v_h__1_2094_, v_size_2095_, v_k_2096_, v_v_2097_, v_l_2098_, v_r_2099_, lean_box(0), v_x_2092_, lean_box(0));
return v___x_2100_;
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
