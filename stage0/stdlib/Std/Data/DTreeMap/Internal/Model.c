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
uint8_t l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(lean_object* v_k_1_, lean_object* v_l_2_){
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
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v_l_2_ = stack[1].m_obj;
uint8_t v_res_12_;
v_res_12_ = l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(v_k_1_, v_l_2_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_x27___redArg___boxed(lean_object* v_k_13_, lean_object* v_l_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(v_k_13_, v_l_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains_x27(lean_object* v_00_u03b1_17_, lean_object* v_00_u03b2_18_, lean_object* v_inst_19_, lean_object* v_k_20_, lean_object* v_l_21_){
_start:
{
uint8_t v___x_22_; 
v___x_22_ = l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(v_k_20_, v_l_21_);
return v___x_22_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_19_ = stack[2].m_obj;
lean_object* v_k_20_ = stack[3].m_obj;
lean_object* v_l_21_ = stack[4].m_obj;
uint8_t v_res_23_;
v_res_23_ = l_Std_DTreeMap_Internal_Impl_contains_x27(lean_box(0), lean_box(0), v_inst_19_, v_k_20_, v_l_21_);
stack->m_num = v_res_23_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_x27___boxed(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_inst_26_, lean_object* v_k_27_, lean_object* v_l_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_Std_DTreeMap_Internal_Impl_contains_x27(v_00_u03b1_24_, v_00_u03b2_25_, v_inst_26_, v_k_27_, v_l_28_);
lean_dec_ref(v_inst_26_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(uint8_t v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_, lean_object* v_h__3_34_){
_start:
{
switch(v_x_31_)
{
case 0:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
lean_dec(v_h__3_34_);
lean_dec(v_h__2_33_);
v___x_35_ = lean_box(0);
v___x_36_ = lean_apply_1(v_h__1_32_, v___x_35_);
return v___x_36_;
}
case 1:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
lean_dec(v_h__2_33_);
lean_dec(v_h__1_32_);
v___x_37_ = lean_box(0);
v___x_38_ = lean_apply_1(v_h__3_34_, v___x_37_);
return v___x_38_;
}
default: 
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_h__3_34_);
lean_dec(v_h__1_32_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_apply_1(v_h__2_33_, v___x_39_);
return v___x_40_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_31_ = stack[0].m_num;
lean_object* v_h__1_32_ = stack[1].m_obj;
lean_object* v_h__2_33_ = stack[2].m_obj;
lean_object* v_h__3_34_ = stack[3].m_obj;
lean_object* v_res_41_;
v_res_41_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_31_, v_h__1_32_, v_h__2_33_, v_h__3_34_);
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(lean_object* v_x_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_, lean_object* v_h__3_45_){
_start:
{
uint8_t v_x_33__boxed_46_; lean_object* v_res_47_; 
v_x_33__boxed_46_ = lean_unbox(v_x_42_);
v_res_47_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_33__boxed_46_, v_h__1_43_, v_h__2_44_, v_h__3_45_);
return v_res_47_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_object* v_motive_48_, uint8_t v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_, lean_object* v_h__3_52_){
_start:
{
switch(v_x_49_)
{
case 0:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec(v_h__3_52_);
lean_dec(v_h__2_51_);
v___x_53_ = lean_box(0);
v___x_54_ = lean_apply_1(v_h__1_50_, v___x_53_);
return v___x_54_;
}
case 1:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_51_);
lean_dec(v_h__1_50_);
v___x_55_ = lean_box(0);
v___x_56_ = lean_apply_1(v_h__3_52_, v___x_55_);
return v___x_56_;
}
default: 
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_h__3_52_);
lean_dec(v_h__1_50_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_apply_1(v_h__2_51_, v___x_57_);
return v___x_58_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_49_ = stack[1].m_num;
lean_object* v_h__1_50_ = stack[2].m_obj;
lean_object* v_h__2_51_ = stack[3].m_obj;
lean_object* v_h__3_52_ = stack[4].m_obj;
lean_object* v_res_59_;
v_res_59_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(lean_box(0), v_x_49_, v_h__1_50_, v_h__2_51_, v_h__3_52_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(lean_object* v_motive_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_, lean_object* v_h__3_64_){
_start:
{
uint8_t v_x_56__boxed_65_; lean_object* v_res_66_; 
v_x_56__boxed_65_ = lean_unbox(v_x_61_);
v_res_66_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_60_, v_x_56__boxed_65_, v_h__1_62_, v_h__2_63_, v_h__3_64_);
return v_res_66_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(uint8_t v_x_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_, lean_object* v_h__3_70_){
_start:
{
switch(v_x_67_)
{
case 0:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_h__3_70_);
lean_dec(v_h__2_69_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_apply_1(v_h__1_68_, v___x_71_);
return v___x_72_;
}
case 1:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec(v_h__2_69_);
lean_dec(v_h__1_68_);
v___x_73_ = lean_box(0);
v___x_74_ = lean_apply_1(v_h__3_70_, v___x_73_);
return v___x_74_;
}
default: 
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_h__3_70_);
lean_dec(v_h__1_68_);
v___x_75_ = lean_box(0);
v___x_76_ = lean_apply_1(v_h__2_69_, v___x_75_);
return v___x_76_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_67_ = stack[0].m_num;
lean_object* v_h__1_68_ = stack[1].m_obj;
lean_object* v_h__2_69_ = stack[2].m_obj;
lean_object* v_h__3_70_ = stack[3].m_obj;
lean_object* v_res_77_;
v_res_77_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_67_, v_h__1_68_, v_h__2_69_, v_h__3_70_);
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(lean_object* v_x_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_, lean_object* v_h__3_81_){
_start:
{
uint8_t v_x_33__boxed_82_; lean_object* v_res_83_; 
v_x_33__boxed_82_ = lean_unbox(v_x_78_);
v_res_83_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_33__boxed_82_, v_h__1_79_, v_h__2_80_, v_h__3_81_);
return v_res_83_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object* v_motive_84_, uint8_t v_x_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_, lean_object* v_h__3_88_){
_start:
{
switch(v_x_85_)
{
case 0:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec(v_h__3_88_);
lean_dec(v_h__2_87_);
v___x_89_ = lean_box(0);
v___x_90_ = lean_apply_1(v_h__1_86_, v___x_89_);
return v___x_90_;
}
case 1:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_h__2_87_);
lean_dec(v_h__1_86_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_apply_1(v_h__3_88_, v___x_91_);
return v___x_92_;
}
default: 
{
lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec(v_h__3_88_);
lean_dec(v_h__1_86_);
v___x_93_ = lean_box(0);
v___x_94_ = lean_apply_1(v_h__2_87_, v___x_93_);
return v___x_94_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_85_ = stack[1].m_num;
lean_object* v_h__1_86_ = stack[2].m_obj;
lean_object* v_h__2_87_ = stack[3].m_obj;
lean_object* v_h__3_88_ = stack[4].m_obj;
lean_object* v_res_95_;
v_res_95_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_box(0), v_x_85_, v_h__1_86_, v_h__2_87_, v_h__3_88_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(lean_object* v_motive_96_, lean_object* v_x_97_, lean_object* v_h__1_98_, lean_object* v_h__2_99_, lean_object* v_h__3_100_){
_start:
{
uint8_t v_x_56__boxed_101_; lean_object* v_res_102_; 
v_x_56__boxed_101_ = lean_unbox(v_x_97_);
v_res_102_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_96_, v_x_56__boxed_101_, v_h__1_98_, v_h__2_99_, v_h__3_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(lean_object* v_k_103_, lean_object* v_f_104_, lean_object* v_ll_105_, lean_object* v_m_106_, lean_object* v_rr_107_){
_start:
{
if (lean_obj_tag(v_m_106_) == 0)
{
lean_object* v_k_108_; lean_object* v_v_109_; lean_object* v_l_110_; lean_object* v_r_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_k_108_ = lean_ctor_get(v_m_106_, 1);
lean_inc_n(v_k_108_, 2);
v_v_109_ = lean_ctor_get(v_m_106_, 2);
lean_inc(v_v_109_);
v_l_110_ = lean_ctor_get(v_m_106_, 3);
lean_inc(v_l_110_);
v_r_111_ = lean_ctor_get(v_m_106_, 4);
lean_inc(v_r_111_);
lean_dec_ref_known(v_m_106_, 5);
lean_inc_ref(v_k_103_);
v___x_112_ = lean_apply_1(v_k_103_, v_k_108_);
v___x_113_ = lean_unbox(v___x_112_);
switch(v___x_113_)
{
case 0:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v_k_108_);
lean_ctor_set(v___x_114_, 1, v_v_109_);
v___x_115_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_111_);
lean_dec(v_r_111_);
v___x_116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = l_List_appendTR___redArg(v___x_116_, v_rr_107_);
v_m_106_ = v_l_110_;
v_rr_107_ = v___x_117_;
goto _start;
}
case 1:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec_ref(v_k_103_);
v___x_119_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_110_);
lean_dec(v_l_110_);
v___x_120_ = l_List_appendTR___redArg(v_ll_105_, v___x_119_);
v___x_121_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_108_, v_v_109_);
v___x_122_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_111_);
lean_dec(v_r_111_);
v___x_123_ = l_List_appendTR___redArg(v___x_122_, v_rr_107_);
v___x_124_ = lean_apply_4(v_f_104_, v___x_120_, v___x_121_, lean_box(0), v___x_123_);
return v___x_124_;
}
default: 
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_125_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_110_);
lean_dec(v_l_110_);
v___x_126_ = l_List_appendTR___redArg(v_ll_105_, v___x_125_);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v_k_108_);
lean_ctor_set(v___x_127_, 1, v_v_109_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = l_List_appendTR___redArg(v___x_126_, v___x_129_);
v_ll_105_ = v___x_130_;
v_m_106_ = v_r_111_;
goto _start;
}
}
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec_ref(v_k_103_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_4(v_f_104_, v_ll_105_, v___x_132_, lean_box(0), v_rr_107_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go(lean_object* v_00_u03b1_134_, lean_object* v_00_u03b2_135_, lean_object* v_00_u03b4_136_, lean_object* v_inst_137_, lean_object* v_k_138_, lean_object* v_l_139_, lean_object* v_f_140_, lean_object* v_ll_141_, lean_object* v_m_142_, lean_object* v_hm_143_, lean_object* v_rr_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(v_k_138_, v_f_140_, v_ll_141_, v_m_142_, v_rr_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition_go___boxed(lean_object* v_00_u03b1_146_, lean_object* v_00_u03b2_147_, lean_object* v_00_u03b4_148_, lean_object* v_inst_149_, lean_object* v_k_150_, lean_object* v_l_151_, lean_object* v_f_152_, lean_object* v_ll_153_, lean_object* v_m_154_, lean_object* v_hm_155_, lean_object* v_rr_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go(v_00_u03b1_146_, v_00_u03b2_147_, v_00_u03b4_148_, v_inst_149_, v_k_150_, v_l_151_, v_f_152_, v_ll_153_, v_m_154_, v_hm_155_, v_rr_156_);
lean_dec(v_l_151_);
lean_dec_ref(v_inst_149_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(lean_object* v_k_158_, lean_object* v_l_159_, lean_object* v_f_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_box(0);
v___x_162_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(v_k_158_, v_f_160_, v___x_161_, v_l_159_, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition(lean_object* v_00_u03b1_163_, lean_object* v_00_u03b2_164_, lean_object* v_00_u03b4_165_, lean_object* v_inst_166_, lean_object* v_k_167_, lean_object* v_l_168_, lean_object* v_f_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v_k_167_, v_l_168_, v_f_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyPartition___boxed(lean_object* v_00_u03b1_171_, lean_object* v_00_u03b2_172_, lean_object* v_00_u03b4_173_, lean_object* v_inst_174_, lean_object* v_k_175_, lean_object* v_l_176_, lean_object* v_f_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_DTreeMap_Internal_Impl_applyPartition(v_00_u03b1_171_, v_00_u03b2_172_, v_00_u03b4_173_, v_inst_174_, v_k_175_, v_l_176_, v_f_177_);
lean_dec_ref(v_inst_174_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0(lean_object* v_f_179_, lean_object* v_c_180_, lean_object* v_h_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_apply_2(v_f_179_, v_c_180_, lean_box(0));
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell___redArg(lean_object* v_inst_183_, lean_object* v_k_184_, lean_object* v_l_185_, lean_object* v_f_186_){
_start:
{
if (lean_obj_tag(v_l_185_) == 0)
{
lean_object* v_k_187_; lean_object* v_v_188_; lean_object* v_l_189_; lean_object* v_r_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_k_187_ = lean_ctor_get(v_l_185_, 1);
lean_inc_n(v_k_187_, 2);
v_v_188_ = lean_ctor_get(v_l_185_, 2);
lean_inc(v_v_188_);
v_l_189_ = lean_ctor_get(v_l_185_, 3);
lean_inc(v_l_189_);
v_r_190_ = lean_ctor_get(v_l_185_, 4);
lean_inc(v_r_190_);
lean_dec_ref_known(v_l_185_, 5);
lean_inc_ref(v_inst_183_);
lean_inc(v_k_184_);
v___x_191_ = lean_apply_2(v_inst_183_, v_k_184_, v_k_187_);
v___x_192_ = lean_unbox(v___x_191_);
switch(v___x_192_)
{
case 0:
{
lean_object* v___f_193_; 
lean_dec(v_r_190_);
lean_dec(v_v_188_);
lean_dec(v_k_187_);
v___f_193_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0), 3, 1);
lean_closure_set(v___f_193_, 0, v_f_186_);
v_l_185_ = v_l_189_;
v_f_186_ = v___f_193_;
goto _start;
}
case 1:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v_r_190_);
lean_dec(v_l_189_);
lean_dec(v_k_184_);
lean_dec_ref(v_inst_183_);
v___x_195_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_187_, v_v_188_);
v___x_196_ = lean_apply_2(v_f_186_, v___x_195_, lean_box(0));
return v___x_196_;
}
default: 
{
lean_object* v___f_197_; 
lean_dec(v_l_189_);
lean_dec(v_v_188_);
lean_dec(v_k_187_);
v___f_197_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0), 3, 1);
lean_closure_set(v___f_197_, 0, v_f_186_);
v_l_185_ = v_r_190_;
v_f_186_ = v___f_197_;
goto _start;
}
}
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v_k_184_);
lean_dec_ref(v_inst_183_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_apply_2(v_f_186_, v___x_199_, lean_box(0));
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_applyCell(lean_object* v_00_u03b1_201_, lean_object* v_00_u03b2_202_, lean_object* v_00_u03b4_203_, lean_object* v_inst_204_, lean_object* v_k_205_, lean_object* v_l_206_, lean_object* v_f_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_204_, v_k_205_, v_l_206_, v_f_207_);
return v___x_208_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(uint8_t v_x_209_, lean_object* v_h__1_210_, lean_object* v_h__2_211_, lean_object* v_h__3_212_){
_start:
{
switch(v_x_209_)
{
case 0:
{
lean_object* v___x_213_; 
lean_dec(v_h__3_212_);
lean_dec(v_h__2_211_);
v___x_213_ = lean_apply_1(v_h__1_210_, lean_box(0));
return v___x_213_;
}
case 1:
{
lean_object* v___x_214_; 
lean_dec(v_h__3_212_);
lean_dec(v_h__1_210_);
v___x_214_ = lean_apply_1(v_h__2_211_, lean_box(0));
return v___x_214_;
}
default: 
{
lean_object* v___x_215_; 
lean_dec(v_h__2_211_);
lean_dec(v_h__1_210_);
v___x_215_ = lean_apply_1(v_h__3_212_, lean_box(0));
return v___x_215_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_209_ = stack[0].m_num;
lean_object* v_h__1_210_ = stack[1].m_obj;
lean_object* v_h__2_211_ = stack[2].m_obj;
lean_object* v_h__3_212_ = stack[3].m_obj;
lean_object* v_res_216_;
v_res_216_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_209_, v_h__1_210_, v_h__2_211_, v_h__3_212_);
stack->m_obj
 = v_res_216_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(lean_object* v_x_217_, lean_object* v_h__1_218_, lean_object* v_h__2_219_, lean_object* v_h__3_220_){
_start:
{
uint8_t v_x_33__boxed_221_; lean_object* v_res_222_; 
v_x_33__boxed_221_ = lean_unbox(v_x_217_);
v_res_222_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_33__boxed_221_, v_h__1_218_, v_h__2_219_, v_h__3_220_);
return v_res_222_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_object* v_motive_223_, uint8_t v_x_224_, lean_object* v_h__1_225_, lean_object* v_h__2_226_, lean_object* v_h__3_227_){
_start:
{
switch(v_x_224_)
{
case 0:
{
lean_object* v___x_228_; 
lean_dec(v_h__3_227_);
lean_dec(v_h__2_226_);
v___x_228_ = lean_apply_1(v_h__1_225_, lean_box(0));
return v___x_228_;
}
case 1:
{
lean_object* v___x_229_; 
lean_dec(v_h__3_227_);
lean_dec(v_h__1_225_);
v___x_229_ = lean_apply_1(v_h__2_226_, lean_box(0));
return v___x_229_;
}
default: 
{
lean_object* v___x_230_; 
lean_dec(v_h__2_226_);
lean_dec(v_h__1_225_);
v___x_230_ = lean_apply_1(v_h__3_227_, lean_box(0));
return v___x_230_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_224_ = stack[1].m_num;
lean_object* v_h__1_225_ = stack[2].m_obj;
lean_object* v_h__2_226_ = stack[3].m_obj;
lean_object* v_h__3_227_ = stack[4].m_obj;
lean_object* v_res_231_;
v_res_231_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(lean_box(0), v_x_224_, v_h__1_225_, v_h__2_226_, v_h__3_227_);
stack->m_obj
 = v_res_231_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(lean_object* v_motive_232_, lean_object* v_x_233_, lean_object* v_h__1_234_, lean_object* v_h__2_235_, lean_object* v_h__3_236_){
_start:
{
uint8_t v_x_47__boxed_237_; lean_object* v_res_238_; 
v_x_47__boxed_237_ = lean_unbox(v_x_233_);
v_res_238_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(v_motive_232_, v_x_47__boxed_237_, v_h__1_234_, v_h__2_235_, v_h__3_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___redArg(lean_object* v_x_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_tag_nat(v_x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___redArg___boxed(lean_object* v_x_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___redArg(v_x_241_);
lean_dec_ref(v_x_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl(lean_object* v_00_u03b1_243_, lean_object* v_00_u03b2_244_, lean_object* v_inst_245_, lean_object* v_k_246_, lean_object* v_x_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_obj_tag_nat(v_x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl___boxed(lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_inst_251_, lean_object* v_k_252_, lean_object* v_x_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___impl(v_00_u03b1_249_, v_00_u03b2_250_, v_inst_251_, v_k_252_, v_x_253_);
lean_dec_ref(v_x_253_);
lean_dec_ref(v_k_252_);
lean_dec_ref(v_inst_251_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(lean_object* v_t_255_, lean_object* v_k_256_){
_start:
{
switch(lean_obj_tag(v_t_255_))
{
case 0:
{
lean_object* v_a_257_; lean_object* v_a_258_; lean_object* v_a_259_; lean_object* v___x_260_; 
v_a_257_ = lean_ctor_get(v_t_255_, 0);
lean_inc(v_a_257_);
v_a_258_ = lean_ctor_get(v_t_255_, 1);
lean_inc(v_a_258_);
v_a_259_ = lean_ctor_get(v_t_255_, 2);
lean_inc(v_a_259_);
lean_dec_ref_known(v_t_255_, 3);
v___x_260_ = lean_apply_4(v_k_256_, v_a_257_, lean_box(0), v_a_258_, v_a_259_);
return v___x_260_;
}
case 1:
{
lean_object* v_a_261_; lean_object* v_a_262_; lean_object* v_a_263_; lean_object* v___x_264_; 
v_a_261_ = lean_ctor_get(v_t_255_, 0);
lean_inc(v_a_261_);
v_a_262_ = lean_ctor_get(v_t_255_, 1);
lean_inc(v_a_262_);
v_a_263_ = lean_ctor_get(v_t_255_, 2);
lean_inc(v_a_263_);
lean_dec_ref_known(v_t_255_, 3);
v___x_264_ = lean_apply_3(v_k_256_, v_a_261_, v_a_262_, v_a_263_);
return v___x_264_;
}
default: 
{
lean_object* v_a_265_; lean_object* v_a_266_; lean_object* v_a_267_; lean_object* v___x_268_; 
v_a_265_ = lean_ctor_get(v_t_255_, 0);
lean_inc(v_a_265_);
v_a_266_ = lean_ctor_get(v_t_255_, 1);
lean_inc(v_a_266_);
v_a_267_ = lean_ctor_get(v_t_255_, 2);
lean_inc(v_a_267_);
lean_dec_ref_known(v_t_255_, 3);
v___x_268_ = lean_apply_4(v_k_256_, v_a_265_, v_a_266_, lean_box(0), v_a_267_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_inst_271_, lean_object* v_k_272_, lean_object* v_motive_273_, lean_object* v_ctorIdx_274_, lean_object* v_t_275_, lean_object* v_h_276_, lean_object* v_k_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_275_, v_k_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___boxed(lean_object* v_00_u03b1_279_, lean_object* v_00_u03b2_280_, lean_object* v_inst_281_, lean_object* v_k_282_, lean_object* v_motive_283_, lean_object* v_ctorIdx_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_k_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim(v_00_u03b1_279_, v_00_u03b2_280_, v_inst_281_, v_k_282_, v_motive_283_, v_ctorIdx_284_, v_t_285_, v_h_286_, v_k_287_);
lean_dec(v_ctorIdx_284_);
lean_dec_ref(v_k_282_);
lean_dec_ref(v_inst_281_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___redArg(lean_object* v_t_289_, lean_object* v_lt_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_289_, v_lt_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim(lean_object* v_00_u03b1_292_, lean_object* v_00_u03b2_293_, lean_object* v_inst_294_, lean_object* v_k_295_, lean_object* v_motive_296_, lean_object* v_t_297_, lean_object* v_h_298_, lean_object* v_lt_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_297_, v_lt_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___boxed(lean_object* v_00_u03b1_301_, lean_object* v_00_u03b2_302_, lean_object* v_inst_303_, lean_object* v_k_304_, lean_object* v_motive_305_, lean_object* v_t_306_, lean_object* v_h_307_, lean_object* v_lt_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim(v_00_u03b1_301_, v_00_u03b2_302_, v_inst_303_, v_k_304_, v_motive_305_, v_t_306_, v_h_307_, v_lt_308_);
lean_dec_ref(v_k_304_);
lean_dec_ref(v_inst_303_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___redArg(lean_object* v_t_310_, lean_object* v_eq_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_310_, v_eq_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim(lean_object* v_00_u03b1_313_, lean_object* v_00_u03b2_314_, lean_object* v_inst_315_, lean_object* v_k_316_, lean_object* v_motive_317_, lean_object* v_t_318_, lean_object* v_h_319_, lean_object* v_eq_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_318_, v_eq_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___boxed(lean_object* v_00_u03b1_322_, lean_object* v_00_u03b2_323_, lean_object* v_inst_324_, lean_object* v_k_325_, lean_object* v_motive_326_, lean_object* v_t_327_, lean_object* v_h_328_, lean_object* v_eq_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim(v_00_u03b1_322_, v_00_u03b2_323_, v_inst_324_, v_k_325_, v_motive_326_, v_t_327_, v_h_328_, v_eq_329_);
lean_dec_ref(v_k_325_);
lean_dec_ref(v_inst_324_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___redArg(lean_object* v_t_331_, lean_object* v_gt_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_331_, v_gt_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim(lean_object* v_00_u03b1_334_, lean_object* v_00_u03b2_335_, lean_object* v_inst_336_, lean_object* v_k_337_, lean_object* v_motive_338_, lean_object* v_t_339_, lean_object* v_h_340_, lean_object* v_gt_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_339_, v_gt_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___boxed(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_inst_345_, lean_object* v_k_346_, lean_object* v_motive_347_, lean_object* v_t_348_, lean_object* v_h_349_, lean_object* v_gt_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim(v_00_u03b1_343_, v_00_u03b2_344_, v_inst_345_, v_k_346_, v_motive_347_, v_t_348_, v_h_349_, v_gt_350_);
lean_dec_ref(v_k_346_);
lean_dec_ref(v_inst_345_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___redArg(lean_object* v_k_355_, lean_object* v_init_356_, lean_object* v_inner_357_, lean_object* v_l_358_){
_start:
{
if (lean_obj_tag(v_l_358_) == 0)
{
lean_object* v_k_359_; lean_object* v_v_360_; lean_object* v_l_361_; lean_object* v_r_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_k_359_ = lean_ctor_get(v_l_358_, 1);
lean_inc_n(v_k_359_, 2);
v_v_360_ = lean_ctor_get(v_l_358_, 2);
lean_inc(v_v_360_);
v_l_361_ = lean_ctor_get(v_l_358_, 3);
lean_inc(v_l_361_);
v_r_362_ = lean_ctor_get(v_l_358_, 4);
lean_inc(v_r_362_);
lean_dec_ref_known(v_l_358_, 5);
lean_inc_ref(v_k_355_);
v___x_363_ = lean_apply_1(v_k_355_, v_k_359_);
v___x_364_ = lean_unbox(v___x_363_);
switch(v___x_364_)
{
case 0:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_362_);
lean_dec(v_r_362_);
v___x_366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_366_, 0, v_k_359_);
lean_ctor_set(v___x_366_, 1, v_v_360_);
lean_ctor_set(v___x_366_, 2, v___x_365_);
lean_inc(v_inner_357_);
v___x_367_ = lean_apply_2(v_inner_357_, v_init_356_, v___x_366_);
v_init_356_ = v___x_367_;
v_l_358_ = v_l_361_;
goto _start;
}
case 1:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec_ref(v_k_355_);
v___x_369_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_361_);
lean_dec(v_l_361_);
v___x_370_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_359_, v_v_360_);
v___x_371_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_362_);
lean_dec(v_r_362_);
v___x_372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_372_, 0, v___x_369_);
lean_ctor_set(v___x_372_, 1, v___x_370_);
lean_ctor_set(v___x_372_, 2, v___x_371_);
v___x_373_ = lean_apply_2(v_inner_357_, v_init_356_, v___x_372_);
return v___x_373_;
}
default: 
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_361_);
lean_dec(v_l_361_);
v___x_375_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v_k_359_);
lean_ctor_set(v___x_375_, 2, v_v_360_);
lean_inc(v_inner_357_);
v___x_376_ = lean_apply_2(v_inner_357_, v_init_356_, v___x_375_);
v_init_356_ = v___x_376_;
v_l_358_ = v_r_362_;
goto _start;
}
}
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec_ref(v_k_355_);
v___x_378_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0));
v___x_379_ = lean_apply_2(v_inner_357_, v_init_356_, v___x_378_);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore(lean_object* v_00_u03b1_380_, lean_object* v_00_u03b2_381_, lean_object* v_00_u03b3_382_, lean_object* v_inst_383_, lean_object* v_k_384_, lean_object* v_init_385_, lean_object* v_inner_386_, lean_object* v_l_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v_k_384_, v_init_385_, v_inner_386_, v_l_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_explore___boxed(lean_object* v_00_u03b1_389_, lean_object* v_00_u03b2_390_, lean_object* v_00_u03b3_391_, lean_object* v_inst_392_, lean_object* v_k_393_, lean_object* v_init_394_, lean_object* v_inner_395_, lean_object* v_l_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_DTreeMap_Internal_Impl_explore(v_00_u03b1_389_, v_00_u03b2_390_, v_00_u03b3_391_, v_inst_392_, v_k_393_, v_init_394_, v_inner_395_, v_l_396_);
lean_dec_ref(v_inst_392_);
return v_res_397_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(lean_object* v_c_398_, lean_object* v_x_399_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_398_);
return v___x_400_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_398_ = stack[0].m_obj;
uint8_t v_res_401_;
v_res_401_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(v_c_398_, lean_box(0));
stack->m_num = v_res_401_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0___boxed(lean_object* v_c_402_, lean_object* v_x_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(v_c_402_, v_x_403_);
lean_dec(v_c_402_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(lean_object* v_inst_407_, lean_object* v_l_408_, lean_object* v_k_409_){
_start:
{
lean_object* v___f_410_; lean_object* v___x_411_; 
v___f_410_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0));
v___x_411_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_407_, v_k_409_, v_l_408_, v___f_410_);
return v___x_411_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains_u2098(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_, lean_object* v_inst_414_, lean_object* v_l_415_, lean_object* v_k_416_){
_start:
{
lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_417_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(v_inst_414_, v_l_415_, v_k_416_);
v___x_418_ = lean_unbox(v___x_417_);
lean_dec(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains_u2098_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_414_ = stack[2].m_obj;
lean_object* v_l_415_ = stack[3].m_obj;
lean_object* v_k_416_ = stack[4].m_obj;
uint8_t v_res_419_;
v_res_419_ = l_Std_DTreeMap_Internal_Impl_contains_u2098(lean_box(0), lean_box(0), v_inst_414_, v_l_415_, v_k_416_);
stack->m_num = v_res_419_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains_u2098___boxed(lean_object* v_00_u03b1_420_, lean_object* v_00_u03b2_421_, lean_object* v_inst_422_, lean_object* v_l_423_, lean_object* v_k_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l_Std_DTreeMap_Internal_Impl_contains_u2098(v_00_u03b1_420_, v_00_u03b2_421_, v_inst_422_, v_l_423_, v_k_424_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0(lean_object* v_c_427_, lean_object* v_x_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(v_c_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(lean_object* v_inst_431_, lean_object* v_l_432_, lean_object* v_k_433_){
_start:
{
lean_object* v___f_434_; lean_object* v___x_435_; 
v___f_434_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0));
v___x_435_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_431_, v_k_433_, v_l_432_, v___f_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f_u2098(lean_object* v_00_u03b1_436_, lean_object* v_00_u03b2_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_l_441_, lean_object* v_k_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_438_, v_l_441_, v_k_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(lean_object* v_inst_444_, lean_object* v_l_445_, lean_object* v_k_446_){
_start:
{
lean_object* v___x_447_; lean_object* v_val_448_; 
v___x_447_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_444_, v_l_445_, v_k_446_);
v_val_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_val_448_);
lean_dec(v___x_447_);
return v_val_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_u2098(lean_object* v_00_u03b1_449_, lean_object* v_00_u03b2_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_l_454_, lean_object* v_k_455_, lean_object* v_h_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(v_inst_451_, v_l_454_, v_k_455_);
return v___x_457_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_461_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2));
v___x_462_ = lean_unsigned_to_nat(14u);
v___x_463_ = lean_unsigned_to_nat(22u);
v___x_464_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1));
v___x_465_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0));
v___x_466_ = l_mkPanicMessageWithDecl(v___x_465_, v___x_464_, v___x_463_, v___x_462_, v___x_461_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(lean_object* v_inst_467_, lean_object* v_l_468_, lean_object* v_k_469_, lean_object* v_inst_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_467_, v_l_468_, v_k_469_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_473_ = l_panic___redArg(v_inst_470_, v___x_472_);
return v___x_473_;
}
else
{
lean_object* v_val_474_; 
v_val_474_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_val_474_);
lean_dec_ref_known(v___x_471_, 1);
return v_val_474_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___boxed(lean_object* v_inst_475_, lean_object* v_l_476_, lean_object* v_k_477_, lean_object* v_inst_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(v_inst_475_, v_l_476_, v_k_477_, v_inst_478_);
lean_dec(v_inst_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098(lean_object* v_00_u03b1_480_, lean_object* v_00_u03b2_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_l_485_, lean_object* v_k_486_, lean_object* v_inst_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(v_inst_482_, v_l_485_, v_k_486_, v_inst_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21_u2098___boxed(lean_object* v_00_u03b1_489_, lean_object* v_00_u03b2_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_l_494_, lean_object* v_k_495_, lean_object* v_inst_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098(v_00_u03b1_489_, v_00_u03b2_490_, v_inst_491_, v_inst_492_, v_inst_493_, v_l_494_, v_k_495_, v_inst_496_);
lean_dec(v_inst_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(lean_object* v_inst_498_, lean_object* v_k_499_, lean_object* v_l_500_, lean_object* v_fallback_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_498_, v_l_500_, v_k_499_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_inc(v_fallback_501_);
return v_fallback_501_;
}
else
{
lean_object* v_val_503_; 
v_val_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v___x_502_, 1);
return v_val_503_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg___boxed(lean_object* v_inst_504_, lean_object* v_k_505_, lean_object* v_l_506_, lean_object* v_fallback_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(v_inst_504_, v_k_505_, v_l_506_, v_fallback_507_);
lean_dec(v_fallback_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098(lean_object* v_00_u03b1_509_, lean_object* v_00_u03b2_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_k_514_, lean_object* v_l_515_, lean_object* v_fallback_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(v_inst_511_, v_k_514_, v_l_515_, v_fallback_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD_u2098___boxed(lean_object* v_00_u03b1_518_, lean_object* v_00_u03b2_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_k_523_, lean_object* v_l_524_, lean_object* v_fallback_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_DTreeMap_Internal_Impl_getD_u2098(v_00_u03b1_518_, v_00_u03b2_519_, v_inst_520_, v_inst_521_, v_inst_522_, v_k_523_, v_l_524_, v_fallback_525_);
lean_dec(v_fallback_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___lam__0(lean_object* v_c_527_, lean_object* v_x_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(v_c_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(lean_object* v_inst_531_, lean_object* v_l_532_, lean_object* v_k_533_){
_start:
{
lean_object* v___f_534_; lean_object* v___x_535_; 
v___f_534_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0));
v___x_535_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_531_, v_k_533_, v_l_532_, v___f_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_inst_538_, lean_object* v_l_539_, lean_object* v_k_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_538_, v_l_539_, v_k_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(lean_object* v_inst_542_, lean_object* v_l_543_, lean_object* v_k_544_){
_start:
{
lean_object* v___x_545_; lean_object* v_val_546_; 
v___x_545_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_542_, v_l_543_, v_k_544_);
v_val_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_546_);
lean_dec(v___x_545_);
return v_val_546_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_u2098(lean_object* v_00_u03b1_547_, lean_object* v_00_u03b2_548_, lean_object* v_inst_549_, lean_object* v_l_550_, lean_object* v_k_551_, lean_object* v_h_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(v_inst_549_, v_l_550_, v_k_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(lean_object* v_inst_554_, lean_object* v_inst_555_, lean_object* v_l_556_, lean_object* v_k_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_554_, v_l_556_, v_k_557_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_560_ = l_panic___redArg(v_inst_555_, v___x_559_);
return v___x_560_;
}
else
{
lean_object* v_val_561_; 
v_val_561_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_val_561_);
lean_dec_ref_known(v___x_558_, 1);
return v_val_561_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg___boxed(lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_l_564_, lean_object* v_k_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(v_inst_562_, v_inst_563_, v_l_564_, v_k_565_);
lean_dec_ref(v_inst_563_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(lean_object* v_00_u03b1_567_, lean_object* v_00_u03b2_568_, lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_l_571_, lean_object* v_k_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(v_inst_569_, v_inst_570_, v_l_571_, v_k_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___boxed(lean_object* v_00_u03b1_574_, lean_object* v_00_u03b2_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_l_578_, lean_object* v_k_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(v_00_u03b1_574_, v_00_u03b2_575_, v_inst_576_, v_inst_577_, v_l_578_, v_k_579_);
lean_dec_ref(v_inst_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(lean_object* v_inst_581_, lean_object* v_k_582_, lean_object* v_l_583_, lean_object* v_fallback_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(v_inst_581_, v_l_583_, v_k_582_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_inc_ref(v_fallback_584_);
return v_fallback_584_;
}
else
{
lean_object* v_val_586_; 
v_val_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_val_586_);
lean_dec_ref_known(v___x_585_, 1);
return v_val_586_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg___boxed(lean_object* v_inst_587_, lean_object* v_k_588_, lean_object* v_l_589_, lean_object* v_fallback_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(v_inst_587_, v_k_588_, v_l_589_, v_fallback_590_);
lean_dec_ref(v_fallback_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(lean_object* v_00_u03b1_592_, lean_object* v_00_u03b2_593_, lean_object* v_inst_594_, lean_object* v_k_595_, lean_object* v_l_596_, lean_object* v_fallback_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(v_inst_594_, v_k_595_, v_l_596_, v_fallback_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___boxed(lean_object* v_00_u03b1_599_, lean_object* v_00_u03b2_600_, lean_object* v_inst_601_, lean_object* v_k_602_, lean_object* v_l_603_, lean_object* v_fallback_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(v_00_u03b1_599_, v_00_u03b2_600_, v_inst_601_, v_k_602_, v_l_603_, v_fallback_604_);
lean_dec_ref(v_fallback_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0(lean_object* v_c_606_, lean_object* v_x_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(v_c_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(lean_object* v_inst_610_, lean_object* v_l_611_, lean_object* v_k_612_){
_start:
{
lean_object* v___f_613_; lean_object* v___x_614_; 
v___f_613_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0));
v___x_614_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_610_, v_k_612_, v_l_611_, v___f_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098(lean_object* v_00_u03b1_615_, lean_object* v_00_u03b2_616_, lean_object* v_inst_617_, lean_object* v_l_618_, lean_object* v_k_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_617_, v_l_618_, v_k_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(lean_object* v_inst_621_, lean_object* v_l_622_, lean_object* v_k_623_){
_start:
{
lean_object* v___x_624_; lean_object* v_val_625_; 
v___x_624_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_621_, v_l_622_, v_k_623_);
v_val_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_val_625_);
lean_dec(v___x_624_);
return v_val_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_u2098(lean_object* v_00_u03b1_626_, lean_object* v_00_u03b2_627_, lean_object* v_inst_628_, lean_object* v_l_629_, lean_object* v_k_630_, lean_object* v_h_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(v_inst_628_, v_l_629_, v_k_630_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(lean_object* v_inst_633_, lean_object* v_l_634_, lean_object* v_k_635_, lean_object* v_inst_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_633_, v_l_634_, v_k_635_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_639_ = l_panic___redArg(v_inst_636_, v___x_638_);
return v___x_639_;
}
else
{
lean_object* v_val_640_; 
v_val_640_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v___x_637_, 1);
return v_val_640_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg___boxed(lean_object* v_inst_641_, lean_object* v_l_642_, lean_object* v_k_643_, lean_object* v_inst_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(v_inst_641_, v_l_642_, v_k_643_, v_inst_644_);
lean_dec(v_inst_644_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(lean_object* v_00_u03b1_646_, lean_object* v_00_u03b2_647_, lean_object* v_inst_648_, lean_object* v_l_649_, lean_object* v_k_650_, lean_object* v_inst_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(v_inst_648_, v_l_649_, v_k_650_, v_inst_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___boxed(lean_object* v_00_u03b1_653_, lean_object* v_00_u03b2_654_, lean_object* v_inst_655_, lean_object* v_l_656_, lean_object* v_k_657_, lean_object* v_inst_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(v_00_u03b1_653_, v_00_u03b2_654_, v_inst_655_, v_l_656_, v_k_657_, v_inst_658_);
lean_dec(v_inst_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(lean_object* v_inst_660_, lean_object* v_k_661_, lean_object* v_l_662_, lean_object* v_fallback_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_660_, v_l_662_, v_k_661_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_inc(v_fallback_663_);
return v_fallback_663_;
}
else
{
lean_object* v_val_665_; 
v_val_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_val_665_);
lean_dec_ref_known(v___x_664_, 1);
return v_val_665_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg___boxed(lean_object* v_inst_666_, lean_object* v_k_667_, lean_object* v_l_668_, lean_object* v_fallback_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(v_inst_666_, v_k_667_, v_l_668_, v_fallback_669_);
lean_dec(v_fallback_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(lean_object* v_00_u03b1_671_, lean_object* v_00_u03b2_672_, lean_object* v_inst_673_, lean_object* v_k_674_, lean_object* v_l_675_, lean_object* v_fallback_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(v_inst_673_, v_k_674_, v_l_675_, v_fallback_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___boxed(lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_inst_680_, lean_object* v_k_681_, lean_object* v_l_682_, lean_object* v_fallback_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(v_00_u03b1_678_, v_00_u03b2_679_, v_inst_680_, v_k_681_, v_l_682_, v_fallback_683_);
lean_dec(v_fallback_683_);
return v_res_684_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(lean_object* v_x_685_){
_start:
{
uint8_t v___x_686_; 
v___x_686_ = 0;
return v___x_686_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_685_ = stack[0].m_obj;
uint8_t v_res_687_;
v_res_687_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(v_x_685_);
stack->m_num = v_res_687_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* v_x_688_){
_start:
{
uint8_t v_res_689_; lean_object* v_r_690_; 
v_res_689_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(v_x_688_);
lean_dec(v_x_688_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(lean_object* v_sofar_691_, lean_object* v_step_692_){
_start:
{
if (lean_obj_tag(v_step_692_) == 0)
{
lean_object* v_a_693_; lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_a_693_ = lean_ctor_get(v_step_692_, 0);
v_a_694_ = lean_ctor_get(v_step_692_, 1);
lean_inc(v_a_694_);
lean_inc(v_a_693_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v_a_693_);
lean_ctor_set(v___x_695_, 1, v_a_694_);
v___x_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
else
{
lean_object* v_a_697_; lean_object* v___x_698_; 
v_a_697_ = lean_ctor_get(v_step_692_, 2);
v___x_698_ = l_List_head_x3f___redArg(v_a_697_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_inc(v_sofar_691_);
return v_sofar_691_;
}
else
{
return v___x_698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* v_sofar_699_, lean_object* v_step_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(v_sofar_699_, v_step_700_);
lean_dec_ref(v_step_700_);
lean_dec(v_sofar_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(lean_object* v_l_704_){
_start:
{
lean_object* v___f_705_; lean_object* v___f_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___f_705_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0));
v___f_706_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1));
v___x_707_ = lean_box(0);
v___x_708_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___f_705_, v___x_707_, v___f_706_, v_l_704_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(lean_object* v_00_u03b1_709_, lean_object* v_00_u03b2_710_, lean_object* v_inst_711_, lean_object* v_l_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(v_l_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___boxed(lean_object* v_00_u03b1_714_, lean_object* v_00_u03b2_715_, lean_object* v_inst_716_, lean_object* v_l_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(v_00_u03b1_714_, v_00_u03b2_715_, v_inst_716_, v_l_717_);
lean_dec_ref(v_inst_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v_x_721_, lean_object* v_r_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_List_head_x3f___redArg(v_r_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed(lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v_r_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(v_x_724_, v_x_725_, v_x_726_, v_r_727_);
lean_dec(v_r_727_);
lean_dec(v_x_725_);
lean_dec(v_x_724_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(lean_object* v_l_730_){
_start:
{
lean_object* v___f_731_; lean_object* v___f_732_; lean_object* v___x_733_; 
v___f_731_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0));
v___f_732_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0));
v___x_733_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_731_, v_l_730_, v___f_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(lean_object* v_00_u03b1_734_, lean_object* v_00_u03b2_735_, lean_object* v_inst_736_, lean_object* v_l_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(v_l_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___boxed(lean_object* v_00_u03b1_739_, lean_object* v_00_u03b2_740_, lean_object* v_inst_741_, lean_object* v_l_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(v_00_u03b1_739_, v_00_u03b2_740_, v_inst_741_, v_l_742_);
lean_dec_ref(v_inst_741_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse___redArg(lean_object* v_x_744_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
lean_object* v_size_745_; lean_object* v_k_746_; lean_object* v_v_747_; lean_object* v_l_748_; lean_object* v_r_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_758_; 
v_size_745_ = lean_ctor_get(v_x_744_, 0);
v_k_746_ = lean_ctor_get(v_x_744_, 1);
v_v_747_ = lean_ctor_get(v_x_744_, 2);
v_l_748_ = lean_ctor_get(v_x_744_, 3);
v_r_749_ = lean_ctor_get(v_x_744_, 4);
v_isSharedCheck_758_ = !lean_is_exclusive(v_x_744_);
if (v_isSharedCheck_758_ == 0)
{
v___x_751_ = v_x_744_;
v_isShared_752_ = v_isSharedCheck_758_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_r_749_);
lean_inc(v_l_748_);
lean_inc(v_v_747_);
lean_inc(v_k_746_);
lean_inc(v_size_745_);
lean_dec(v_x_744_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_758_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_753_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_r_749_);
v___x_754_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_l_748_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 4, v___x_754_);
lean_ctor_set(v___x_751_, 3, v___x_753_);
v___x_756_ = v___x_751_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_size_745_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_k_746_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_v_747_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_757_, 4, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
else
{
return v_x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_reverse(lean_object* v_00_u03b1_759_, lean_object* v_00_u03b2_760_, lean_object* v_x_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0(lean_object* v_c_763_, lean_object* v_x_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(v_c_763_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(lean_object* v_inst_767_, lean_object* v_l_768_, lean_object* v_k_769_){
_start:
{
lean_object* v___f_770_; lean_object* v___x_771_; 
v___f_770_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0));
v___x_771_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(v_inst_767_, v_k_769_, v_l_768_, v___f_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098(lean_object* v_00_u03b1_772_, lean_object* v_00_u03b2_773_, lean_object* v_inst_774_, lean_object* v_l_775_, lean_object* v_k_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_774_, v_l_775_, v_k_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(lean_object* v_inst_778_, lean_object* v_l_779_, lean_object* v_k_780_){
_start:
{
lean_object* v___x_781_; lean_object* v_val_782_; 
v___x_781_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_778_, v_l_779_, v_k_780_);
v_val_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_val_782_);
lean_dec(v___x_781_);
return v_val_782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_u2098(lean_object* v_00_u03b1_783_, lean_object* v_00_u03b2_784_, lean_object* v_inst_785_, lean_object* v_l_786_, lean_object* v_k_787_, lean_object* v_h_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(v_inst_785_, v_l_786_, v_k_787_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(lean_object* v_inst_790_, lean_object* v_l_791_, lean_object* v_k_792_, lean_object* v_inst_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_790_, v_l_791_, v_k_792_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3);
v___x_796_ = l_panic___redArg(v_inst_793_, v___x_795_);
return v___x_796_;
}
else
{
lean_object* v_val_797_; 
v_val_797_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v___x_794_, 1);
return v_val_797_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg___boxed(lean_object* v_inst_798_, lean_object* v_l_799_, lean_object* v_k_800_, lean_object* v_inst_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(v_inst_798_, v_l_799_, v_k_800_, v_inst_801_);
lean_dec(v_inst_801_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(lean_object* v_00_u03b1_803_, lean_object* v_00_u03b2_804_, lean_object* v_inst_805_, lean_object* v_l_806_, lean_object* v_k_807_, lean_object* v_inst_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(v_inst_805_, v_l_806_, v_k_807_, v_inst_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___boxed(lean_object* v_00_u03b1_810_, lean_object* v_00_u03b2_811_, lean_object* v_inst_812_, lean_object* v_l_813_, lean_object* v_k_814_, lean_object* v_inst_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(v_00_u03b1_810_, v_00_u03b2_811_, v_inst_812_, v_l_813_, v_k_814_, v_inst_815_);
lean_dec(v_inst_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(lean_object* v_inst_817_, lean_object* v_l_818_, lean_object* v_k_819_, lean_object* v_fallback_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(v_inst_817_, v_l_818_, v_k_819_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_inc(v_fallback_820_);
return v_fallback_820_;
}
else
{
lean_object* v_val_822_; 
v_val_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_val_822_);
lean_dec_ref_known(v___x_821_, 1);
return v_val_822_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg___boxed(lean_object* v_inst_823_, lean_object* v_l_824_, lean_object* v_k_825_, lean_object* v_fallback_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(v_inst_823_, v_l_824_, v_k_825_, v_fallback_826_);
lean_dec(v_fallback_826_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(lean_object* v_00_u03b1_828_, lean_object* v_00_u03b2_829_, lean_object* v_inst_830_, lean_object* v_l_831_, lean_object* v_k_832_, lean_object* v_fallback_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(v_inst_830_, v_l_831_, v_k_832_, v_fallback_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___boxed(lean_object* v_00_u03b1_835_, lean_object* v_00_u03b2_836_, lean_object* v_inst_837_, lean_object* v_l_838_, lean_object* v_k_839_, lean_object* v_fallback_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(v_00_u03b1_835_, v_00_u03b2_836_, v_inst_837_, v_l_838_, v_k_839_, v_fallback_840_);
lean_dec(v_fallback_840_);
return v_res_841_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(uint8_t v_x_842_, lean_object* v_h__1_843_, lean_object* v_h__2_844_, lean_object* v_h__3_845_){
_start:
{
switch(v_x_842_)
{
case 0:
{
lean_object* v___x_846_; 
lean_dec(v_h__3_845_);
lean_dec(v_h__2_844_);
v___x_846_ = lean_apply_1(v_h__1_843_, lean_box(0));
return v___x_846_;
}
case 1:
{
lean_object* v___x_847_; 
lean_dec(v_h__2_844_);
lean_dec(v_h__1_843_);
v___x_847_ = lean_apply_1(v_h__3_845_, lean_box(0));
return v___x_847_;
}
default: 
{
lean_object* v___x_848_; 
lean_dec(v_h__3_845_);
lean_dec(v_h__1_843_);
v___x_848_ = lean_apply_1(v_h__2_844_, lean_box(0));
return v___x_848_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_842_ = stack[0].m_num;
lean_object* v_h__1_843_ = stack[1].m_obj;
lean_object* v_h__2_844_ = stack[2].m_obj;
lean_object* v_h__3_845_ = stack[3].m_obj;
lean_object* v_res_849_;
v_res_849_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(v_x_842_, v_h__1_843_, v_h__2_844_, v_h__3_845_);
stack->m_obj
 = v_res_849_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_850_, lean_object* v_h__1_851_, lean_object* v_h__2_852_, lean_object* v_h__3_853_){
_start:
{
uint8_t v_x_33__boxed_854_; lean_object* v_res_855_; 
v_x_33__boxed_854_ = lean_unbox(v_x_850_);
v_res_855_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(v_x_33__boxed_854_, v_h__1_851_, v_h__2_852_, v_h__3_853_);
return v_res_855_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(lean_object* v_motive_856_, uint8_t v_x_857_, lean_object* v_h__1_858_, lean_object* v_h__2_859_, lean_object* v_h__3_860_){
_start:
{
switch(v_x_857_)
{
case 0:
{
lean_object* v___x_861_; 
lean_dec(v_h__3_860_);
lean_dec(v_h__2_859_);
v___x_861_ = lean_apply_1(v_h__1_858_, lean_box(0));
return v___x_861_;
}
case 1:
{
lean_object* v___x_862_; 
lean_dec(v_h__2_859_);
lean_dec(v_h__1_858_);
v___x_862_ = lean_apply_1(v_h__3_860_, lean_box(0));
return v___x_862_;
}
default: 
{
lean_object* v___x_863_; 
lean_dec(v_h__3_860_);
lean_dec(v_h__1_858_);
v___x_863_ = lean_apply_1(v_h__2_859_, lean_box(0));
return v___x_863_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_857_ = stack[1].m_num;
lean_object* v_h__1_858_ = stack[2].m_obj;
lean_object* v_h__2_859_ = stack[3].m_obj;
lean_object* v_h__3_860_ = stack[4].m_obj;
lean_object* v_res_864_;
v_res_864_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(lean_box(0), v_x_857_, v_h__1_858_, v_h__2_859_, v_h__3_860_);
stack->m_obj
 = v_res_864_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___boxed(lean_object* v_motive_865_, lean_object* v_x_866_, lean_object* v_h__1_867_, lean_object* v_h__2_868_, lean_object* v_h__3_869_){
_start:
{
uint8_t v_x_47__boxed_870_; lean_object* v_res_871_; 
v_x_47__boxed_870_ = lean_unbox(v_x_866_);
v_res_871_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(v_motive_865_, v_x_47__boxed_870_, v_h__1_867_, v_h__2_868_, v_h__3_869_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(lean_object* v_x_872_, lean_object* v_h__1_873_, lean_object* v_h__2_874_){
_start:
{
if (lean_obj_tag(v_x_872_) == 0)
{
lean_object* v___x_875_; 
lean_dec(v_h__2_874_);
v___x_875_ = lean_apply_1(v_h__1_873_, lean_box(0));
return v___x_875_;
}
else
{
lean_object* v_val_876_; lean_object* v___x_877_; 
lean_dec(v_h__1_873_);
v_val_876_ = lean_ctor_get(v_x_872_, 0);
lean_inc(v_val_876_);
lean_dec_ref_known(v_x_872_, 1);
v___x_877_ = lean_apply_2(v_h__2_874_, v_val_876_, lean_box(0));
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(lean_object* v_00_u03b1_878_, lean_object* v_00_u03b2_879_, lean_object* v_motive_880_, lean_object* v_x_881_, lean_object* v_h__1_882_, lean_object* v_h__2_883_){
_start:
{
if (lean_obj_tag(v_x_881_) == 0)
{
lean_object* v___x_884_; 
lean_dec(v_h__2_883_);
v___x_884_ = lean_apply_1(v_h__1_882_, lean_box(0));
return v___x_884_;
}
else
{
lean_object* v_val_885_; lean_object* v___x_886_; 
lean_dec(v_h__1_882_);
v_val_885_ = lean_ctor_get(v_x_881_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v_x_881_, 1);
v___x_886_ = lean_apply_2(v_h__2_883_, v_val_885_, lean_box(0));
return v___x_886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_887_, lean_object* v_h__1_888_, lean_object* v_h__2_889_){
_start:
{
if (lean_obj_tag(v_x_887_) == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec(v_h__2_889_);
v___x_890_ = lean_box(0);
v___x_891_ = lean_apply_1(v_h__1_888_, v___x_890_);
return v___x_891_;
}
else
{
lean_object* v_val_892_; lean_object* v___x_893_; 
lean_dec(v_h__1_888_);
v_val_892_ = lean_ctor_get(v_x_887_, 0);
lean_inc(v_val_892_);
lean_dec_ref_known(v_x_887_, 1);
v___x_893_ = lean_apply_1(v_h__2_889_, v_val_892_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_894_, lean_object* v_00_u03b2_895_, lean_object* v_motive_896_, lean_object* v_x_897_, lean_object* v_h__1_898_, lean_object* v_h__2_899_){
_start:
{
if (lean_obj_tag(v_x_897_) == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec(v_h__2_899_);
v___x_900_ = lean_box(0);
v___x_901_ = lean_apply_1(v_h__1_898_, v___x_900_);
return v___x_901_;
}
else
{
lean_object* v_val_902_; lean_object* v___x_903_; 
lean_dec(v_h__1_898_);
v_val_902_ = lean_ctor_get(v_x_897_, 0);
lean_inc(v_val_902_);
lean_dec_ref_known(v_x_897_, 1);
v___x_903_ = lean_apply_1(v_h__2_899_, v_val_902_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_904_, lean_object* v_h__1_905_, lean_object* v_h__2_906_, lean_object* v_h__3_907_){
_start:
{
if (lean_obj_tag(v_x_904_) == 0)
{
lean_object* v_l_908_; 
lean_dec(v_h__1_905_);
v_l_908_ = lean_ctor_get(v_x_904_, 3);
if (lean_obj_tag(v_l_908_) == 0)
{
lean_object* v_size_909_; lean_object* v_k_910_; lean_object* v_v_911_; lean_object* v_r_912_; lean_object* v_size_913_; lean_object* v_k_914_; lean_object* v_v_915_; lean_object* v_l_916_; lean_object* v_r_917_; lean_object* v___x_918_; 
lean_inc_ref(v_l_908_);
lean_dec(v_h__2_906_);
v_size_909_ = lean_ctor_get(v_x_904_, 0);
lean_inc(v_size_909_);
v_k_910_ = lean_ctor_get(v_x_904_, 1);
lean_inc(v_k_910_);
v_v_911_ = lean_ctor_get(v_x_904_, 2);
lean_inc(v_v_911_);
v_r_912_ = lean_ctor_get(v_x_904_, 4);
lean_inc(v_r_912_);
lean_dec_ref_known(v_x_904_, 5);
v_size_913_ = lean_ctor_get(v_l_908_, 0);
lean_inc(v_size_913_);
v_k_914_ = lean_ctor_get(v_l_908_, 1);
lean_inc(v_k_914_);
v_v_915_ = lean_ctor_get(v_l_908_, 2);
lean_inc(v_v_915_);
v_l_916_ = lean_ctor_get(v_l_908_, 3);
lean_inc(v_l_916_);
v_r_917_ = lean_ctor_get(v_l_908_, 4);
lean_inc(v_r_917_);
lean_dec_ref_known(v_l_908_, 5);
v___x_918_ = lean_apply_9(v_h__3_907_, v_size_909_, v_k_910_, v_v_911_, v_size_913_, v_k_914_, v_v_915_, v_l_916_, v_r_917_, v_r_912_);
return v___x_918_;
}
else
{
lean_object* v_size_919_; lean_object* v_k_920_; lean_object* v_v_921_; lean_object* v_r_922_; lean_object* v___x_923_; 
lean_dec(v_h__3_907_);
v_size_919_ = lean_ctor_get(v_x_904_, 0);
lean_inc(v_size_919_);
v_k_920_ = lean_ctor_get(v_x_904_, 1);
lean_inc(v_k_920_);
v_v_921_ = lean_ctor_get(v_x_904_, 2);
lean_inc(v_v_921_);
v_r_922_ = lean_ctor_get(v_x_904_, 4);
lean_inc(v_r_922_);
lean_dec_ref_known(v_x_904_, 5);
v___x_923_ = lean_apply_4(v_h__2_906_, v_size_919_, v_k_920_, v_v_921_, v_r_922_);
return v___x_923_;
}
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec(v_h__3_907_);
lean_dec(v_h__2_906_);
v___x_924_ = lean_box(0);
v___x_925_ = lean_apply_1(v_h__1_905_, v___x_924_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_926_, lean_object* v_00_u03b2_927_, lean_object* v_motive_928_, lean_object* v_x_929_, lean_object* v_h__1_930_, lean_object* v_h__2_931_, lean_object* v_h__3_932_){
_start:
{
if (lean_obj_tag(v_x_929_) == 0)
{
lean_object* v_l_933_; 
lean_dec(v_h__1_930_);
v_l_933_ = lean_ctor_get(v_x_929_, 3);
if (lean_obj_tag(v_l_933_) == 0)
{
lean_object* v_size_934_; lean_object* v_k_935_; lean_object* v_v_936_; lean_object* v_r_937_; lean_object* v_size_938_; lean_object* v_k_939_; lean_object* v_v_940_; lean_object* v_l_941_; lean_object* v_r_942_; lean_object* v___x_943_; 
lean_inc_ref(v_l_933_);
lean_dec(v_h__2_931_);
v_size_934_ = lean_ctor_get(v_x_929_, 0);
lean_inc(v_size_934_);
v_k_935_ = lean_ctor_get(v_x_929_, 1);
lean_inc(v_k_935_);
v_v_936_ = lean_ctor_get(v_x_929_, 2);
lean_inc(v_v_936_);
v_r_937_ = lean_ctor_get(v_x_929_, 4);
lean_inc(v_r_937_);
lean_dec_ref_known(v_x_929_, 5);
v_size_938_ = lean_ctor_get(v_l_933_, 0);
lean_inc(v_size_938_);
v_k_939_ = lean_ctor_get(v_l_933_, 1);
lean_inc(v_k_939_);
v_v_940_ = lean_ctor_get(v_l_933_, 2);
lean_inc(v_v_940_);
v_l_941_ = lean_ctor_get(v_l_933_, 3);
lean_inc(v_l_941_);
v_r_942_ = lean_ctor_get(v_l_933_, 4);
lean_inc(v_r_942_);
lean_dec_ref_known(v_l_933_, 5);
v___x_943_ = lean_apply_9(v_h__3_932_, v_size_934_, v_k_935_, v_v_936_, v_size_938_, v_k_939_, v_v_940_, v_l_941_, v_r_942_, v_r_937_);
return v___x_943_;
}
else
{
lean_object* v_size_944_; lean_object* v_k_945_; lean_object* v_v_946_; lean_object* v_r_947_; lean_object* v___x_948_; 
lean_dec(v_h__3_932_);
v_size_944_ = lean_ctor_get(v_x_929_, 0);
lean_inc(v_size_944_);
v_k_945_ = lean_ctor_get(v_x_929_, 1);
lean_inc(v_k_945_);
v_v_946_ = lean_ctor_get(v_x_929_, 2);
lean_inc(v_v_946_);
v_r_947_ = lean_ctor_get(v_x_929_, 4);
lean_inc(v_r_947_);
lean_dec_ref_known(v_x_929_, 5);
v___x_948_ = lean_apply_4(v_h__2_931_, v_size_944_, v_k_945_, v_v_946_, v_r_947_);
return v___x_948_;
}
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec(v_h__3_932_);
lean_dec(v_h__2_931_);
v___x_949_ = lean_box(0);
v___x_950_ = lean_apply_1(v_h__1_930_, v___x_949_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_step_951_, lean_object* v_h__1_952_, lean_object* v_h__2_953_){
_start:
{
if (lean_obj_tag(v_step_951_) == 0)
{
lean_object* v_a_954_; lean_object* v_a_955_; lean_object* v_a_956_; lean_object* v___x_957_; 
lean_dec(v_h__2_953_);
v_a_954_ = lean_ctor_get(v_step_951_, 0);
lean_inc(v_a_954_);
v_a_955_ = lean_ctor_get(v_step_951_, 1);
lean_inc(v_a_955_);
v_a_956_ = lean_ctor_get(v_step_951_, 2);
lean_inc(v_a_956_);
lean_dec_ref_known(v_step_951_, 3);
v___x_957_ = lean_apply_4(v_h__1_952_, v_a_954_, lean_box(0), v_a_955_, v_a_956_);
return v___x_957_;
}
else
{
lean_object* v_a_958_; lean_object* v_a_959_; lean_object* v_a_960_; lean_object* v___x_961_; 
lean_dec(v_h__1_952_);
v_a_958_ = lean_ctor_get(v_step_951_, 0);
lean_inc(v_a_958_);
v_a_959_ = lean_ctor_get(v_step_951_, 1);
lean_inc(v_a_959_);
v_a_960_ = lean_ctor_get(v_step_951_, 2);
lean_inc(v_a_960_);
lean_dec_ref_known(v_step_951_, 3);
v___x_961_ = lean_apply_3(v_h__2_953_, v_a_958_, v_a_959_, v_a_960_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_962_, lean_object* v_00_u03b2_963_, lean_object* v_inst_964_, lean_object* v_motive_965_, lean_object* v_step_966_, lean_object* v_h__1_967_, lean_object* v_h__2_968_){
_start:
{
if (lean_obj_tag(v_step_966_) == 0)
{
lean_object* v_a_969_; lean_object* v_a_970_; lean_object* v_a_971_; lean_object* v___x_972_; 
lean_dec(v_h__2_968_);
v_a_969_ = lean_ctor_get(v_step_966_, 0);
lean_inc(v_a_969_);
v_a_970_ = lean_ctor_get(v_step_966_, 1);
lean_inc(v_a_970_);
v_a_971_ = lean_ctor_get(v_step_966_, 2);
lean_inc(v_a_971_);
lean_dec_ref_known(v_step_966_, 3);
v___x_972_ = lean_apply_4(v_h__1_967_, v_a_969_, lean_box(0), v_a_970_, v_a_971_);
return v___x_972_;
}
else
{
lean_object* v_a_973_; lean_object* v_a_974_; lean_object* v_a_975_; lean_object* v___x_976_; 
lean_dec(v_h__1_967_);
v_a_973_ = lean_ctor_get(v_step_966_, 0);
lean_inc(v_a_973_);
v_a_974_ = lean_ctor_get(v_step_966_, 1);
lean_inc(v_a_974_);
v_a_975_ = lean_ctor_get(v_step_966_, 2);
lean_inc(v_a_975_);
lean_dec_ref_known(v_step_966_, 3);
v___x_976_ = lean_apply_3(v_h__2_968_, v_a_973_, v_a_974_, v_a_975_);
return v___x_976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_977_, lean_object* v_00_u03b2_978_, lean_object* v_inst_979_, lean_object* v_motive_980_, lean_object* v_step_981_, lean_object* v_h__1_982_, lean_object* v_h__2_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(v_00_u03b1_977_, v_00_u03b2_978_, v_inst_979_, v_motive_980_, v_step_981_, v_h__1_982_, v_h__2_983_);
lean_dec_ref(v_inst_979_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object* v_x_985_, lean_object* v_h__1_986_, lean_object* v_h__2_987_){
_start:
{
lean_object* v_l_988_; 
v_l_988_ = lean_ctor_get(v_x_985_, 3);
if (lean_obj_tag(v_l_988_) == 0)
{
lean_object* v_size_989_; lean_object* v_k_990_; lean_object* v_v_991_; lean_object* v_r_992_; lean_object* v_size_993_; lean_object* v_k_994_; lean_object* v_v_995_; lean_object* v_l_996_; lean_object* v_r_997_; lean_object* v___x_998_; 
lean_inc_ref(v_l_988_);
lean_dec(v_h__1_986_);
v_size_989_ = lean_ctor_get(v_x_985_, 0);
lean_inc(v_size_989_);
v_k_990_ = lean_ctor_get(v_x_985_, 1);
lean_inc(v_k_990_);
v_v_991_ = lean_ctor_get(v_x_985_, 2);
lean_inc(v_v_991_);
v_r_992_ = lean_ctor_get(v_x_985_, 4);
lean_inc(v_r_992_);
lean_dec(v_x_985_);
v_size_993_ = lean_ctor_get(v_l_988_, 0);
lean_inc(v_size_993_);
v_k_994_ = lean_ctor_get(v_l_988_, 1);
lean_inc(v_k_994_);
v_v_995_ = lean_ctor_get(v_l_988_, 2);
lean_inc(v_v_995_);
v_l_996_ = lean_ctor_get(v_l_988_, 3);
lean_inc(v_l_996_);
v_r_997_ = lean_ctor_get(v_l_988_, 4);
lean_inc(v_r_997_);
lean_dec_ref_known(v_l_988_, 5);
v___x_998_ = lean_apply_10(v_h__2_987_, v_size_989_, v_k_990_, v_v_991_, v_size_993_, v_k_994_, v_v_995_, v_l_996_, v_r_997_, v_r_992_, lean_box(0));
return v___x_998_;
}
else
{
lean_object* v_size_999_; lean_object* v_k_1000_; lean_object* v_v_1001_; lean_object* v_r_1002_; lean_object* v___x_1003_; 
lean_dec(v_h__2_987_);
v_size_999_ = lean_ctor_get(v_x_985_, 0);
lean_inc(v_size_999_);
v_k_1000_ = lean_ctor_get(v_x_985_, 1);
lean_inc(v_k_1000_);
v_v_1001_ = lean_ctor_get(v_x_985_, 2);
lean_inc(v_v_1001_);
v_r_1002_ = lean_ctor_get(v_x_985_, 4);
lean_inc(v_r_1002_);
lean_dec(v_x_985_);
v___x_1003_ = lean_apply_5(v_h__1_986_, v_size_999_, v_k_1000_, v_v_1001_, v_r_1002_, lean_box(0));
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* v_00_u03b1_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_motive_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v_h__1_1009_, lean_object* v_h__2_1010_){
_start:
{
lean_object* v_l_1011_; 
v_l_1011_ = lean_ctor_get(v_x_1007_, 3);
if (lean_obj_tag(v_l_1011_) == 0)
{
lean_object* v_size_1012_; lean_object* v_k_1013_; lean_object* v_v_1014_; lean_object* v_r_1015_; lean_object* v_size_1016_; lean_object* v_k_1017_; lean_object* v_v_1018_; lean_object* v_l_1019_; lean_object* v_r_1020_; lean_object* v___x_1021_; 
lean_inc_ref(v_l_1011_);
lean_dec(v_h__1_1009_);
v_size_1012_ = lean_ctor_get(v_x_1007_, 0);
lean_inc(v_size_1012_);
v_k_1013_ = lean_ctor_get(v_x_1007_, 1);
lean_inc(v_k_1013_);
v_v_1014_ = lean_ctor_get(v_x_1007_, 2);
lean_inc(v_v_1014_);
v_r_1015_ = lean_ctor_get(v_x_1007_, 4);
lean_inc(v_r_1015_);
lean_dec(v_x_1007_);
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
lean_dec_ref_known(v_l_1011_, 5);
v___x_1021_ = lean_apply_10(v_h__2_1010_, v_size_1012_, v_k_1013_, v_v_1014_, v_size_1016_, v_k_1017_, v_v_1018_, v_l_1019_, v_r_1020_, v_r_1015_, lean_box(0));
return v___x_1021_;
}
else
{
lean_object* v_size_1022_; lean_object* v_k_1023_; lean_object* v_v_1024_; lean_object* v_r_1025_; lean_object* v___x_1026_; 
lean_dec(v_h__2_1010_);
v_size_1022_ = lean_ctor_get(v_x_1007_, 0);
lean_inc(v_size_1022_);
v_k_1023_ = lean_ctor_get(v_x_1007_, 1);
lean_inc(v_k_1023_);
v_v_1024_ = lean_ctor_get(v_x_1007_, 2);
lean_inc(v_v_1024_);
v_r_1025_ = lean_ctor_get(v_x_1007_, 4);
lean_inc(v_r_1025_);
lean_dec(v_x_1007_);
v___x_1026_ = lean_apply_5(v_h__1_1009_, v_size_1022_, v_k_1023_, v_v_1024_, v_r_1025_, lean_box(0));
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1027_, lean_object* v_h__1_1028_, lean_object* v_h__2_1029_, lean_object* v_h__3_1030_){
_start:
{
if (lean_obj_tag(v_x_1027_) == 0)
{
lean_object* v_r_1031_; 
lean_dec(v_h__1_1028_);
v_r_1031_ = lean_ctor_get(v_x_1027_, 4);
if (lean_obj_tag(v_r_1031_) == 0)
{
lean_object* v_size_1032_; lean_object* v_k_1033_; lean_object* v_v_1034_; lean_object* v_l_1035_; lean_object* v_size_1036_; lean_object* v_k_1037_; lean_object* v_v_1038_; lean_object* v_l_1039_; lean_object* v_r_1040_; lean_object* v___x_1041_; 
lean_inc_ref(v_r_1031_);
lean_dec(v_h__2_1029_);
v_size_1032_ = lean_ctor_get(v_x_1027_, 0);
lean_inc(v_size_1032_);
v_k_1033_ = lean_ctor_get(v_x_1027_, 1);
lean_inc(v_k_1033_);
v_v_1034_ = lean_ctor_get(v_x_1027_, 2);
lean_inc(v_v_1034_);
v_l_1035_ = lean_ctor_get(v_x_1027_, 3);
lean_inc(v_l_1035_);
lean_dec_ref_known(v_x_1027_, 5);
v_size_1036_ = lean_ctor_get(v_r_1031_, 0);
lean_inc(v_size_1036_);
v_k_1037_ = lean_ctor_get(v_r_1031_, 1);
lean_inc(v_k_1037_);
v_v_1038_ = lean_ctor_get(v_r_1031_, 2);
lean_inc(v_v_1038_);
v_l_1039_ = lean_ctor_get(v_r_1031_, 3);
lean_inc(v_l_1039_);
v_r_1040_ = lean_ctor_get(v_r_1031_, 4);
lean_inc(v_r_1040_);
lean_dec_ref_known(v_r_1031_, 5);
v___x_1041_ = lean_apply_9(v_h__3_1030_, v_size_1032_, v_k_1033_, v_v_1034_, v_l_1035_, v_size_1036_, v_k_1037_, v_v_1038_, v_l_1039_, v_r_1040_);
return v___x_1041_;
}
else
{
lean_object* v_size_1042_; lean_object* v_k_1043_; lean_object* v_v_1044_; lean_object* v_l_1045_; lean_object* v___x_1046_; 
lean_dec(v_h__3_1030_);
v_size_1042_ = lean_ctor_get(v_x_1027_, 0);
lean_inc(v_size_1042_);
v_k_1043_ = lean_ctor_get(v_x_1027_, 1);
lean_inc(v_k_1043_);
v_v_1044_ = lean_ctor_get(v_x_1027_, 2);
lean_inc(v_v_1044_);
v_l_1045_ = lean_ctor_get(v_x_1027_, 3);
lean_inc(v_l_1045_);
lean_dec_ref_known(v_x_1027_, 5);
v___x_1046_ = lean_apply_4(v_h__2_1029_, v_size_1042_, v_k_1043_, v_v_1044_, v_l_1045_);
return v___x_1046_;
}
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec(v_h__3_1030_);
lean_dec(v_h__2_1029_);
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_apply_1(v_h__1_1028_, v___x_1047_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1049_, lean_object* v_00_u03b2_1050_, lean_object* v_motive_1051_, lean_object* v_x_1052_, lean_object* v_h__1_1053_, lean_object* v_h__2_1054_, lean_object* v_h__3_1055_){
_start:
{
if (lean_obj_tag(v_x_1052_) == 0)
{
lean_object* v_r_1056_; 
lean_dec(v_h__1_1053_);
v_r_1056_ = lean_ctor_get(v_x_1052_, 4);
if (lean_obj_tag(v_r_1056_) == 0)
{
lean_object* v_size_1057_; lean_object* v_k_1058_; lean_object* v_v_1059_; lean_object* v_l_1060_; lean_object* v_size_1061_; lean_object* v_k_1062_; lean_object* v_v_1063_; lean_object* v_l_1064_; lean_object* v_r_1065_; lean_object* v___x_1066_; 
lean_inc_ref(v_r_1056_);
lean_dec(v_h__2_1054_);
v_size_1057_ = lean_ctor_get(v_x_1052_, 0);
lean_inc(v_size_1057_);
v_k_1058_ = lean_ctor_get(v_x_1052_, 1);
lean_inc(v_k_1058_);
v_v_1059_ = lean_ctor_get(v_x_1052_, 2);
lean_inc(v_v_1059_);
v_l_1060_ = lean_ctor_get(v_x_1052_, 3);
lean_inc(v_l_1060_);
lean_dec_ref_known(v_x_1052_, 5);
v_size_1061_ = lean_ctor_get(v_r_1056_, 0);
lean_inc(v_size_1061_);
v_k_1062_ = lean_ctor_get(v_r_1056_, 1);
lean_inc(v_k_1062_);
v_v_1063_ = lean_ctor_get(v_r_1056_, 2);
lean_inc(v_v_1063_);
v_l_1064_ = lean_ctor_get(v_r_1056_, 3);
lean_inc(v_l_1064_);
v_r_1065_ = lean_ctor_get(v_r_1056_, 4);
lean_inc(v_r_1065_);
lean_dec_ref_known(v_r_1056_, 5);
v___x_1066_ = lean_apply_9(v_h__3_1055_, v_size_1057_, v_k_1058_, v_v_1059_, v_l_1060_, v_size_1061_, v_k_1062_, v_v_1063_, v_l_1064_, v_r_1065_);
return v___x_1066_;
}
else
{
lean_object* v_size_1067_; lean_object* v_k_1068_; lean_object* v_v_1069_; lean_object* v_l_1070_; lean_object* v___x_1071_; 
lean_dec(v_h__3_1055_);
v_size_1067_ = lean_ctor_get(v_x_1052_, 0);
lean_inc(v_size_1067_);
v_k_1068_ = lean_ctor_get(v_x_1052_, 1);
lean_inc(v_k_1068_);
v_v_1069_ = lean_ctor_get(v_x_1052_, 2);
lean_inc(v_v_1069_);
v_l_1070_ = lean_ctor_get(v_x_1052_, 3);
lean_inc(v_l_1070_);
lean_dec_ref_known(v_x_1052_, 5);
v___x_1071_ = lean_apply_4(v_h__2_1054_, v_size_1067_, v_k_1068_, v_v_1069_, v_l_1070_);
return v___x_1071_;
}
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_dec(v_h__3_1055_);
lean_dec(v_h__2_1054_);
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_apply_1(v_h__1_1053_, v___x_1072_);
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object* v_x_1074_, lean_object* v_h__1_1075_, lean_object* v_h__2_1076_){
_start:
{
lean_object* v_r_1077_; 
v_r_1077_ = lean_ctor_get(v_x_1074_, 4);
if (lean_obj_tag(v_r_1077_) == 0)
{
lean_object* v_size_1078_; lean_object* v_k_1079_; lean_object* v_v_1080_; lean_object* v_l_1081_; lean_object* v_size_1082_; lean_object* v_k_1083_; lean_object* v_v_1084_; lean_object* v_l_1085_; lean_object* v_r_1086_; lean_object* v___x_1087_; 
lean_inc_ref(v_r_1077_);
lean_dec(v_h__1_1075_);
v_size_1078_ = lean_ctor_get(v_x_1074_, 0);
lean_inc(v_size_1078_);
v_k_1079_ = lean_ctor_get(v_x_1074_, 1);
lean_inc(v_k_1079_);
v_v_1080_ = lean_ctor_get(v_x_1074_, 2);
lean_inc(v_v_1080_);
v_l_1081_ = lean_ctor_get(v_x_1074_, 3);
lean_inc(v_l_1081_);
lean_dec(v_x_1074_);
v_size_1082_ = lean_ctor_get(v_r_1077_, 0);
lean_inc(v_size_1082_);
v_k_1083_ = lean_ctor_get(v_r_1077_, 1);
lean_inc(v_k_1083_);
v_v_1084_ = lean_ctor_get(v_r_1077_, 2);
lean_inc(v_v_1084_);
v_l_1085_ = lean_ctor_get(v_r_1077_, 3);
lean_inc(v_l_1085_);
v_r_1086_ = lean_ctor_get(v_r_1077_, 4);
lean_inc(v_r_1086_);
lean_dec_ref_known(v_r_1077_, 5);
v___x_1087_ = lean_apply_10(v_h__2_1076_, v_size_1078_, v_k_1079_, v_v_1080_, v_l_1081_, v_size_1082_, v_k_1083_, v_v_1084_, v_l_1085_, v_r_1086_, lean_box(0));
return v___x_1087_;
}
else
{
lean_object* v_size_1088_; lean_object* v_k_1089_; lean_object* v_v_1090_; lean_object* v_l_1091_; lean_object* v___x_1092_; 
lean_dec(v_h__2_1076_);
v_size_1088_ = lean_ctor_get(v_x_1074_, 0);
lean_inc(v_size_1088_);
v_k_1089_ = lean_ctor_get(v_x_1074_, 1);
lean_inc(v_k_1089_);
v_v_1090_ = lean_ctor_get(v_x_1074_, 2);
lean_inc(v_v_1090_);
v_l_1091_ = lean_ctor_get(v_x_1074_, 3);
lean_inc(v_l_1091_);
lean_dec(v_x_1074_);
v___x_1092_ = lean_apply_5(v_h__1_1075_, v_size_1088_, v_k_1089_, v_v_1090_, v_l_1091_, lean_box(0));
return v___x_1092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1093_, lean_object* v_00_u03b2_1094_, lean_object* v_motive_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_h__1_1098_, lean_object* v_h__2_1099_){
_start:
{
lean_object* v_r_1100_; 
v_r_1100_ = lean_ctor_get(v_x_1096_, 4);
if (lean_obj_tag(v_r_1100_) == 0)
{
lean_object* v_size_1101_; lean_object* v_k_1102_; lean_object* v_v_1103_; lean_object* v_l_1104_; lean_object* v_size_1105_; lean_object* v_k_1106_; lean_object* v_v_1107_; lean_object* v_l_1108_; lean_object* v_r_1109_; lean_object* v___x_1110_; 
lean_inc_ref(v_r_1100_);
lean_dec(v_h__1_1098_);
v_size_1101_ = lean_ctor_get(v_x_1096_, 0);
lean_inc(v_size_1101_);
v_k_1102_ = lean_ctor_get(v_x_1096_, 1);
lean_inc(v_k_1102_);
v_v_1103_ = lean_ctor_get(v_x_1096_, 2);
lean_inc(v_v_1103_);
v_l_1104_ = lean_ctor_get(v_x_1096_, 3);
lean_inc(v_l_1104_);
lean_dec(v_x_1096_);
v_size_1105_ = lean_ctor_get(v_r_1100_, 0);
lean_inc(v_size_1105_);
v_k_1106_ = lean_ctor_get(v_r_1100_, 1);
lean_inc(v_k_1106_);
v_v_1107_ = lean_ctor_get(v_r_1100_, 2);
lean_inc(v_v_1107_);
v_l_1108_ = lean_ctor_get(v_r_1100_, 3);
lean_inc(v_l_1108_);
v_r_1109_ = lean_ctor_get(v_r_1100_, 4);
lean_inc(v_r_1109_);
lean_dec_ref_known(v_r_1100_, 5);
v___x_1110_ = lean_apply_10(v_h__2_1099_, v_size_1101_, v_k_1102_, v_v_1103_, v_l_1104_, v_size_1105_, v_k_1106_, v_v_1107_, v_l_1108_, v_r_1109_, lean_box(0));
return v___x_1110_;
}
else
{
lean_object* v_size_1111_; lean_object* v_k_1112_; lean_object* v_v_1113_; lean_object* v_l_1114_; lean_object* v___x_1115_; 
lean_dec(v_h__2_1099_);
v_size_1111_ = lean_ctor_get(v_x_1096_, 0);
lean_inc(v_size_1111_);
v_k_1112_ = lean_ctor_get(v_x_1096_, 1);
lean_inc(v_k_1112_);
v_v_1113_ = lean_ctor_get(v_x_1096_, 2);
lean_inc(v_v_1113_);
v_l_1114_ = lean_ctor_get(v_x_1096_, 3);
lean_inc(v_l_1114_);
lean_dec(v_x_1096_);
v___x_1115_ = lean_apply_5(v_h__1_1098_, v_size_1111_, v_k_1112_, v_v_1113_, v_l_1114_, lean_box(0));
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_h__1_1118_, lean_object* v_h__2_1119_, lean_object* v_h__3_1120_){
_start:
{
if (lean_obj_tag(v_x_1116_) == 0)
{
lean_object* v_l_1121_; 
lean_dec(v_h__1_1118_);
v_l_1121_ = lean_ctor_get(v_x_1116_, 3);
if (lean_obj_tag(v_l_1121_) == 0)
{
lean_object* v_size_1122_; lean_object* v_k_1123_; lean_object* v_v_1124_; lean_object* v_r_1125_; lean_object* v_size_1126_; lean_object* v_k_1127_; lean_object* v_v_1128_; lean_object* v_l_1129_; lean_object* v_r_1130_; lean_object* v___x_1131_; 
lean_inc_ref(v_l_1121_);
lean_dec(v_h__2_1119_);
v_size_1122_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_size_1122_);
v_k_1123_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_k_1123_);
v_v_1124_ = lean_ctor_get(v_x_1116_, 2);
lean_inc(v_v_1124_);
v_r_1125_ = lean_ctor_get(v_x_1116_, 4);
lean_inc(v_r_1125_);
lean_dec_ref_known(v_x_1116_, 5);
v_size_1126_ = lean_ctor_get(v_l_1121_, 0);
lean_inc(v_size_1126_);
v_k_1127_ = lean_ctor_get(v_l_1121_, 1);
lean_inc(v_k_1127_);
v_v_1128_ = lean_ctor_get(v_l_1121_, 2);
lean_inc(v_v_1128_);
v_l_1129_ = lean_ctor_get(v_l_1121_, 3);
lean_inc(v_l_1129_);
v_r_1130_ = lean_ctor_get(v_l_1121_, 4);
lean_inc(v_r_1130_);
lean_dec_ref_known(v_l_1121_, 5);
v___x_1131_ = lean_apply_10(v_h__3_1120_, v_size_1122_, v_k_1123_, v_v_1124_, v_size_1126_, v_k_1127_, v_v_1128_, v_l_1129_, v_r_1130_, v_r_1125_, v_x_1117_);
return v___x_1131_;
}
else
{
lean_object* v_size_1132_; lean_object* v_k_1133_; lean_object* v_v_1134_; lean_object* v_r_1135_; lean_object* v___x_1136_; 
lean_dec(v_h__3_1120_);
v_size_1132_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_size_1132_);
v_k_1133_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_k_1133_);
v_v_1134_ = lean_ctor_get(v_x_1116_, 2);
lean_inc(v_v_1134_);
v_r_1135_ = lean_ctor_get(v_x_1116_, 4);
lean_inc(v_r_1135_);
lean_dec_ref_known(v_x_1116_, 5);
v___x_1136_ = lean_apply_5(v_h__2_1119_, v_size_1132_, v_k_1133_, v_v_1134_, v_r_1135_, v_x_1117_);
return v___x_1136_;
}
}
else
{
lean_object* v___x_1137_; 
lean_dec(v_h__3_1120_);
lean_dec(v_h__2_1119_);
v___x_1137_ = lean_apply_1(v_h__1_1118_, v_x_1117_);
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* v_00_u03b1_1138_, lean_object* v_00_u03b2_1139_, lean_object* v_motive_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_h__1_1143_, lean_object* v_h__2_1144_, lean_object* v_h__3_1145_){
_start:
{
if (lean_obj_tag(v_x_1141_) == 0)
{
lean_object* v_l_1146_; 
lean_dec(v_h__1_1143_);
v_l_1146_ = lean_ctor_get(v_x_1141_, 3);
if (lean_obj_tag(v_l_1146_) == 0)
{
lean_object* v_size_1147_; lean_object* v_k_1148_; lean_object* v_v_1149_; lean_object* v_r_1150_; lean_object* v_size_1151_; lean_object* v_k_1152_; lean_object* v_v_1153_; lean_object* v_l_1154_; lean_object* v_r_1155_; lean_object* v___x_1156_; 
lean_inc_ref(v_l_1146_);
lean_dec(v_h__2_1144_);
v_size_1147_ = lean_ctor_get(v_x_1141_, 0);
lean_inc(v_size_1147_);
v_k_1148_ = lean_ctor_get(v_x_1141_, 1);
lean_inc(v_k_1148_);
v_v_1149_ = lean_ctor_get(v_x_1141_, 2);
lean_inc(v_v_1149_);
v_r_1150_ = lean_ctor_get(v_x_1141_, 4);
lean_inc(v_r_1150_);
lean_dec_ref_known(v_x_1141_, 5);
v_size_1151_ = lean_ctor_get(v_l_1146_, 0);
lean_inc(v_size_1151_);
v_k_1152_ = lean_ctor_get(v_l_1146_, 1);
lean_inc(v_k_1152_);
v_v_1153_ = lean_ctor_get(v_l_1146_, 2);
lean_inc(v_v_1153_);
v_l_1154_ = lean_ctor_get(v_l_1146_, 3);
lean_inc(v_l_1154_);
v_r_1155_ = lean_ctor_get(v_l_1146_, 4);
lean_inc(v_r_1155_);
lean_dec_ref_known(v_l_1146_, 5);
v___x_1156_ = lean_apply_10(v_h__3_1145_, v_size_1147_, v_k_1148_, v_v_1149_, v_size_1151_, v_k_1152_, v_v_1153_, v_l_1154_, v_r_1155_, v_r_1150_, v_x_1142_);
return v___x_1156_;
}
else
{
lean_object* v_size_1157_; lean_object* v_k_1158_; lean_object* v_v_1159_; lean_object* v_r_1160_; lean_object* v___x_1161_; 
lean_dec(v_h__3_1145_);
v_size_1157_ = lean_ctor_get(v_x_1141_, 0);
lean_inc(v_size_1157_);
v_k_1158_ = lean_ctor_get(v_x_1141_, 1);
lean_inc(v_k_1158_);
v_v_1159_ = lean_ctor_get(v_x_1141_, 2);
lean_inc(v_v_1159_);
v_r_1160_ = lean_ctor_get(v_x_1141_, 4);
lean_inc(v_r_1160_);
lean_dec_ref_known(v_x_1141_, 5);
v___x_1161_ = lean_apply_5(v_h__2_1144_, v_size_1157_, v_k_1158_, v_v_1159_, v_r_1160_, v_x_1142_);
return v___x_1161_;
}
}
else
{
lean_object* v___x_1162_; 
lean_dec(v_h__3_1145_);
lean_dec(v_h__2_1144_);
v___x_1162_ = lean_apply_1(v_h__1_1143_, v_x_1142_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1163_, lean_object* v_h__1_1164_, lean_object* v_h__2_1165_, lean_object* v_h__3_1166_){
_start:
{
if (lean_obj_tag(v_x_1163_) == 0)
{
lean_object* v_l_1167_; 
lean_dec(v_h__1_1164_);
v_l_1167_ = lean_ctor_get(v_x_1163_, 3);
if (lean_obj_tag(v_l_1167_) == 0)
{
lean_object* v_size_1168_; lean_object* v_k_1169_; lean_object* v_v_1170_; lean_object* v_r_1171_; lean_object* v_size_1172_; lean_object* v_k_1173_; lean_object* v_v_1174_; lean_object* v_l_1175_; lean_object* v_r_1176_; lean_object* v___x_1177_; 
lean_inc_ref(v_l_1167_);
lean_dec(v_h__2_1165_);
v_size_1168_ = lean_ctor_get(v_x_1163_, 0);
lean_inc(v_size_1168_);
v_k_1169_ = lean_ctor_get(v_x_1163_, 1);
lean_inc(v_k_1169_);
v_v_1170_ = lean_ctor_get(v_x_1163_, 2);
lean_inc(v_v_1170_);
v_r_1171_ = lean_ctor_get(v_x_1163_, 4);
lean_inc(v_r_1171_);
lean_dec_ref_known(v_x_1163_, 5);
v_size_1172_ = lean_ctor_get(v_l_1167_, 0);
lean_inc(v_size_1172_);
v_k_1173_ = lean_ctor_get(v_l_1167_, 1);
lean_inc(v_k_1173_);
v_v_1174_ = lean_ctor_get(v_l_1167_, 2);
lean_inc(v_v_1174_);
v_l_1175_ = lean_ctor_get(v_l_1167_, 3);
lean_inc(v_l_1175_);
v_r_1176_ = lean_ctor_get(v_l_1167_, 4);
lean_inc(v_r_1176_);
lean_dec_ref_known(v_l_1167_, 5);
v___x_1177_ = lean_apply_9(v_h__3_1166_, v_size_1168_, v_k_1169_, v_v_1170_, v_size_1172_, v_k_1173_, v_v_1174_, v_l_1175_, v_r_1176_, v_r_1171_);
return v___x_1177_;
}
else
{
lean_object* v_size_1178_; lean_object* v_k_1179_; lean_object* v_v_1180_; lean_object* v_r_1181_; lean_object* v___x_1182_; 
lean_dec(v_h__3_1166_);
v_size_1178_ = lean_ctor_get(v_x_1163_, 0);
lean_inc(v_size_1178_);
v_k_1179_ = lean_ctor_get(v_x_1163_, 1);
lean_inc(v_k_1179_);
v_v_1180_ = lean_ctor_get(v_x_1163_, 2);
lean_inc(v_v_1180_);
v_r_1181_ = lean_ctor_get(v_x_1163_, 4);
lean_inc(v_r_1181_);
lean_dec_ref_known(v_x_1163_, 5);
v___x_1182_ = lean_apply_4(v_h__2_1165_, v_size_1178_, v_k_1179_, v_v_1180_, v_r_1181_);
return v___x_1182_;
}
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_dec(v_h__3_1166_);
lean_dec(v_h__2_1165_);
v___x_1183_ = lean_box(0);
v___x_1184_ = lean_apply_1(v_h__1_1164_, v___x_1183_);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1185_, lean_object* v_00_u03b2_1186_, lean_object* v_motive_1187_, lean_object* v_x_1188_, lean_object* v_h__1_1189_, lean_object* v_h__2_1190_, lean_object* v_h__3_1191_){
_start:
{
if (lean_obj_tag(v_x_1188_) == 0)
{
lean_object* v_l_1192_; 
lean_dec(v_h__1_1189_);
v_l_1192_ = lean_ctor_get(v_x_1188_, 3);
if (lean_obj_tag(v_l_1192_) == 0)
{
lean_object* v_size_1193_; lean_object* v_k_1194_; lean_object* v_v_1195_; lean_object* v_r_1196_; lean_object* v_size_1197_; lean_object* v_k_1198_; lean_object* v_v_1199_; lean_object* v_l_1200_; lean_object* v_r_1201_; lean_object* v___x_1202_; 
lean_inc_ref(v_l_1192_);
lean_dec(v_h__2_1190_);
v_size_1193_ = lean_ctor_get(v_x_1188_, 0);
lean_inc(v_size_1193_);
v_k_1194_ = lean_ctor_get(v_x_1188_, 1);
lean_inc(v_k_1194_);
v_v_1195_ = lean_ctor_get(v_x_1188_, 2);
lean_inc(v_v_1195_);
v_r_1196_ = lean_ctor_get(v_x_1188_, 4);
lean_inc(v_r_1196_);
lean_dec_ref_known(v_x_1188_, 5);
v_size_1197_ = lean_ctor_get(v_l_1192_, 0);
lean_inc(v_size_1197_);
v_k_1198_ = lean_ctor_get(v_l_1192_, 1);
lean_inc(v_k_1198_);
v_v_1199_ = lean_ctor_get(v_l_1192_, 2);
lean_inc(v_v_1199_);
v_l_1200_ = lean_ctor_get(v_l_1192_, 3);
lean_inc(v_l_1200_);
v_r_1201_ = lean_ctor_get(v_l_1192_, 4);
lean_inc(v_r_1201_);
lean_dec_ref_known(v_l_1192_, 5);
v___x_1202_ = lean_apply_9(v_h__3_1191_, v_size_1193_, v_k_1194_, v_v_1195_, v_size_1197_, v_k_1198_, v_v_1199_, v_l_1200_, v_r_1201_, v_r_1196_);
return v___x_1202_;
}
else
{
lean_object* v_size_1203_; lean_object* v_k_1204_; lean_object* v_v_1205_; lean_object* v_r_1206_; lean_object* v___x_1207_; 
lean_dec(v_h__3_1191_);
v_size_1203_ = lean_ctor_get(v_x_1188_, 0);
lean_inc(v_size_1203_);
v_k_1204_ = lean_ctor_get(v_x_1188_, 1);
lean_inc(v_k_1204_);
v_v_1205_ = lean_ctor_get(v_x_1188_, 2);
lean_inc(v_v_1205_);
v_r_1206_ = lean_ctor_get(v_x_1188_, 4);
lean_inc(v_r_1206_);
lean_dec_ref_known(v_x_1188_, 5);
v___x_1207_ = lean_apply_4(v_h__2_1190_, v_size_1203_, v_k_1204_, v_v_1205_, v_r_1206_);
return v___x_1207_;
}
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_h__3_1191_);
lean_dec(v_h__2_1190_);
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_apply_1(v_h__1_1189_, v___x_1208_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* v_x_1210_, lean_object* v_h__1_1211_, lean_object* v_h__2_1212_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* v_00_u03b1_1229_, lean_object* v_00_u03b2_1230_, lean_object* v_motive_1231_, lean_object* v_x_1232_, lean_object* v_x_1233_, lean_object* v_h__1_1234_, lean_object* v_h__2_1235_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1252_, lean_object* v_h__1_1253_, lean_object* v_h__2_1254_, lean_object* v_h__3_1255_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_motive_1276_, lean_object* v_x_1277_, lean_object* v_h__1_1278_, lean_object* v_h__2_1279_, lean_object* v_h__3_1280_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* v_x_1299_, lean_object* v_h__1_1300_, lean_object* v_h__2_1301_){
_start:
{
lean_object* v_r_1302_; 
v_r_1302_ = lean_ctor_get(v_x_1299_, 4);
if (lean_obj_tag(v_r_1302_) == 0)
{
lean_object* v_size_1303_; lean_object* v_k_1304_; lean_object* v_v_1305_; lean_object* v_l_1306_; lean_object* v_size_1307_; lean_object* v_k_1308_; lean_object* v_v_1309_; lean_object* v_l_1310_; lean_object* v_r_1311_; lean_object* v___x_1312_; 
lean_inc_ref(v_r_1302_);
lean_dec(v_h__1_1300_);
v_size_1303_ = lean_ctor_get(v_x_1299_, 0);
lean_inc(v_size_1303_);
v_k_1304_ = lean_ctor_get(v_x_1299_, 1);
lean_inc(v_k_1304_);
v_v_1305_ = lean_ctor_get(v_x_1299_, 2);
lean_inc(v_v_1305_);
v_l_1306_ = lean_ctor_get(v_x_1299_, 3);
lean_inc(v_l_1306_);
lean_dec(v_x_1299_);
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
v___x_1312_ = lean_apply_10(v_h__2_1301_, v_size_1303_, v_k_1304_, v_v_1305_, v_l_1306_, v_size_1307_, v_k_1308_, v_v_1309_, v_l_1310_, v_r_1311_, lean_box(0));
return v___x_1312_;
}
else
{
lean_object* v_size_1313_; lean_object* v_k_1314_; lean_object* v_v_1315_; lean_object* v_l_1316_; lean_object* v___x_1317_; 
lean_dec(v_h__2_1301_);
v_size_1313_ = lean_ctor_get(v_x_1299_, 0);
lean_inc(v_size_1313_);
v_k_1314_ = lean_ctor_get(v_x_1299_, 1);
lean_inc(v_k_1314_);
v_v_1315_ = lean_ctor_get(v_x_1299_, 2);
lean_inc(v_v_1315_);
v_l_1316_ = lean_ctor_get(v_x_1299_, 3);
lean_inc(v_l_1316_);
lean_dec(v_x_1299_);
v___x_1317_ = lean_apply_5(v_h__1_1300_, v_size_1313_, v_k_1314_, v_v_1315_, v_l_1316_, lean_box(0));
return v___x_1317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1318_, lean_object* v_00_u03b2_1319_, lean_object* v_motive_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v_h__1_1323_, lean_object* v_h__2_1324_){
_start:
{
lean_object* v_r_1325_; 
v_r_1325_ = lean_ctor_get(v_x_1321_, 4);
if (lean_obj_tag(v_r_1325_) == 0)
{
lean_object* v_size_1326_; lean_object* v_k_1327_; lean_object* v_v_1328_; lean_object* v_l_1329_; lean_object* v_size_1330_; lean_object* v_k_1331_; lean_object* v_v_1332_; lean_object* v_l_1333_; lean_object* v_r_1334_; lean_object* v___x_1335_; 
lean_inc_ref(v_r_1325_);
lean_dec(v_h__1_1323_);
v_size_1326_ = lean_ctor_get(v_x_1321_, 0);
lean_inc(v_size_1326_);
v_k_1327_ = lean_ctor_get(v_x_1321_, 1);
lean_inc(v_k_1327_);
v_v_1328_ = lean_ctor_get(v_x_1321_, 2);
lean_inc(v_v_1328_);
v_l_1329_ = lean_ctor_get(v_x_1321_, 3);
lean_inc(v_l_1329_);
lean_dec(v_x_1321_);
v_size_1330_ = lean_ctor_get(v_r_1325_, 0);
lean_inc(v_size_1330_);
v_k_1331_ = lean_ctor_get(v_r_1325_, 1);
lean_inc(v_k_1331_);
v_v_1332_ = lean_ctor_get(v_r_1325_, 2);
lean_inc(v_v_1332_);
v_l_1333_ = lean_ctor_get(v_r_1325_, 3);
lean_inc(v_l_1333_);
v_r_1334_ = lean_ctor_get(v_r_1325_, 4);
lean_inc(v_r_1334_);
lean_dec_ref_known(v_r_1325_, 5);
v___x_1335_ = lean_apply_10(v_h__2_1324_, v_size_1326_, v_k_1327_, v_v_1328_, v_l_1329_, v_size_1330_, v_k_1331_, v_v_1332_, v_l_1333_, v_r_1334_, lean_box(0));
return v___x_1335_;
}
else
{
lean_object* v_size_1336_; lean_object* v_k_1337_; lean_object* v_v_1338_; lean_object* v_l_1339_; lean_object* v___x_1340_; 
lean_dec(v_h__2_1324_);
v_size_1336_ = lean_ctor_get(v_x_1321_, 0);
lean_inc(v_size_1336_);
v_k_1337_ = lean_ctor_get(v_x_1321_, 1);
lean_inc(v_k_1337_);
v_v_1338_ = lean_ctor_get(v_x_1321_, 2);
lean_inc(v_v_1338_);
v_l_1339_ = lean_ctor_get(v_x_1321_, 3);
lean_inc(v_l_1339_);
lean_dec(v_x_1321_);
v___x_1340_ = lean_apply_5(v_h__1_1323_, v_size_1336_, v_k_1337_, v_v_1338_, v_l_1339_, lean_box(0));
return v___x_1340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(lean_object* v_l_1341_, lean_object* v_h__1_1342_, lean_object* v_h__2_1343_){
_start:
{
if (lean_obj_tag(v_l_1341_) == 0)
{
lean_object* v_size_1344_; lean_object* v_k_1345_; lean_object* v_v_1346_; lean_object* v_l_1347_; lean_object* v_r_1348_; lean_object* v___x_1349_; 
lean_dec(v_h__1_1342_);
v_size_1344_ = lean_ctor_get(v_l_1341_, 0);
lean_inc(v_size_1344_);
v_k_1345_ = lean_ctor_get(v_l_1341_, 1);
lean_inc(v_k_1345_);
v_v_1346_ = lean_ctor_get(v_l_1341_, 2);
lean_inc(v_v_1346_);
v_l_1347_ = lean_ctor_get(v_l_1341_, 3);
lean_inc(v_l_1347_);
v_r_1348_ = lean_ctor_get(v_l_1341_, 4);
lean_inc(v_r_1348_);
lean_dec_ref_known(v_l_1341_, 5);
v___x_1349_ = lean_apply_7(v_h__2_1343_, v_size_1344_, v_k_1345_, v_v_1346_, v_l_1347_, v_r_1348_, lean_box(0), lean_box(0));
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; 
lean_dec(v_h__2_1343_);
v___x_1350_ = lean_apply_2(v_h__1_1342_, lean_box(0), lean_box(0));
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(lean_object* v_00_u03b1_1351_, lean_object* v_00_u03b2_1352_, lean_object* v_r_1353_, lean_object* v_motive_1354_, lean_object* v_l_1355_, lean_object* v_hl_1356_, lean_object* v_hlr_1357_, lean_object* v_h__1_1358_, lean_object* v_h__2_1359_){
_start:
{
if (lean_obj_tag(v_l_1355_) == 0)
{
lean_object* v_size_1360_; lean_object* v_k_1361_; lean_object* v_v_1362_; lean_object* v_l_1363_; lean_object* v_r_1364_; lean_object* v___x_1365_; 
lean_dec(v_h__1_1358_);
v_size_1360_ = lean_ctor_get(v_l_1355_, 0);
lean_inc(v_size_1360_);
v_k_1361_ = lean_ctor_get(v_l_1355_, 1);
lean_inc(v_k_1361_);
v_v_1362_ = lean_ctor_get(v_l_1355_, 2);
lean_inc(v_v_1362_);
v_l_1363_ = lean_ctor_get(v_l_1355_, 3);
lean_inc(v_l_1363_);
v_r_1364_ = lean_ctor_get(v_l_1355_, 4);
lean_inc(v_r_1364_);
lean_dec_ref_known(v_l_1355_, 5);
v___x_1365_ = lean_apply_7(v_h__2_1359_, v_size_1360_, v_k_1361_, v_v_1362_, v_l_1363_, v_r_1364_, lean_box(0), lean_box(0));
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; 
lean_dec(v_h__2_1359_);
v___x_1366_ = lean_apply_2(v_h__1_1358_, lean_box(0), lean_box(0));
return v___x_1366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(lean_object* v_00_u03b1_1367_, lean_object* v_00_u03b2_1368_, lean_object* v_r_1369_, lean_object* v_motive_1370_, lean_object* v_l_1371_, lean_object* v_hl_1372_, lean_object* v_hlr_1373_, lean_object* v_h__1_1374_, lean_object* v_h__2_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(v_00_u03b1_1367_, v_00_u03b2_1368_, v_r_1369_, v_motive_1370_, v_l_1371_, v_hl_1372_, v_hlr_1373_, v_h__1_1374_, v_h__2_1375_);
lean_dec(v_r_1369_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(lean_object* v_x_1377_, lean_object* v_h__1_1378_){
_start:
{
lean_object* v_k_1379_; lean_object* v_v_1380_; lean_object* v_tree_1381_; lean_object* v___x_1382_; 
v_k_1379_ = lean_ctor_get(v_x_1377_, 0);
lean_inc(v_k_1379_);
v_v_1380_ = lean_ctor_get(v_x_1377_, 1);
lean_inc(v_v_1380_);
v_tree_1381_ = lean_ctor_get(v_x_1377_, 2);
lean_inc(v_tree_1381_);
lean_dec_ref(v_x_1377_);
v___x_1382_ = lean_apply_5(v_h__1_1378_, v_k_1379_, v_v_1380_, v_tree_1381_, lean_box(0), lean_box(0));
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(lean_object* v_00_u03b1_1383_, lean_object* v_00_u03b2_1384_, lean_object* v_l_x27_1385_, lean_object* v_r_x27_1386_, lean_object* v_motive_1387_, lean_object* v_x_1388_, lean_object* v_h__1_1389_){
_start:
{
lean_object* v_k_1390_; lean_object* v_v_1391_; lean_object* v_tree_1392_; lean_object* v___x_1393_; 
v_k_1390_ = lean_ctor_get(v_x_1388_, 0);
lean_inc(v_k_1390_);
v_v_1391_ = lean_ctor_get(v_x_1388_, 1);
lean_inc(v_v_1391_);
v_tree_1392_ = lean_ctor_get(v_x_1388_, 2);
lean_inc(v_tree_1392_);
lean_dec_ref(v_x_1388_);
v___x_1393_ = lean_apply_5(v_h__1_1389_, v_k_1390_, v_v_1391_, v_tree_1392_, lean_box(0), lean_box(0));
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(lean_object* v_00_u03b1_1394_, lean_object* v_00_u03b2_1395_, lean_object* v_l_x27_1396_, lean_object* v_r_x27_1397_, lean_object* v_motive_1398_, lean_object* v_x_1399_, lean_object* v_h__1_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(v_00_u03b1_1394_, v_00_u03b2_1395_, v_l_x27_1396_, v_r_x27_1397_, v_motive_1398_, v_x_1399_, v_h__1_1400_);
lean_dec(v_r_x27_1397_);
lean_dec(v_l_x27_1396_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(lean_object* v_r_1402_, lean_object* v_h__1_1403_, lean_object* v_h__2_1404_){
_start:
{
if (lean_obj_tag(v_r_1402_) == 0)
{
lean_object* v_size_1405_; lean_object* v_k_1406_; lean_object* v_v_1407_; lean_object* v_l_1408_; lean_object* v_r_1409_; lean_object* v___x_1410_; 
lean_dec(v_h__1_1403_);
v_size_1405_ = lean_ctor_get(v_r_1402_, 0);
lean_inc(v_size_1405_);
v_k_1406_ = lean_ctor_get(v_r_1402_, 1);
lean_inc(v_k_1406_);
v_v_1407_ = lean_ctor_get(v_r_1402_, 2);
lean_inc(v_v_1407_);
v_l_1408_ = lean_ctor_get(v_r_1402_, 3);
lean_inc(v_l_1408_);
v_r_1409_ = lean_ctor_get(v_r_1402_, 4);
lean_inc(v_r_1409_);
lean_dec_ref_known(v_r_1402_, 5);
v___x_1410_ = lean_apply_7(v_h__2_1404_, v_size_1405_, v_k_1406_, v_v_1407_, v_l_1408_, v_r_1409_, lean_box(0), lean_box(0));
return v___x_1410_;
}
else
{
lean_object* v___x_1411_; 
lean_dec(v_h__2_1404_);
v___x_1411_ = lean_apply_2(v_h__1_1403_, lean_box(0), lean_box(0));
return v___x_1411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(lean_object* v_00_u03b1_1412_, lean_object* v_00_u03b2_1413_, lean_object* v_l_1414_, lean_object* v_motive_1415_, lean_object* v_r_1416_, lean_object* v_hr_1417_, lean_object* v_hlr_1418_, lean_object* v_h__1_1419_, lean_object* v_h__2_1420_){
_start:
{
if (lean_obj_tag(v_r_1416_) == 0)
{
lean_object* v_size_1421_; lean_object* v_k_1422_; lean_object* v_v_1423_; lean_object* v_l_1424_; lean_object* v_r_1425_; lean_object* v___x_1426_; 
lean_dec(v_h__1_1419_);
v_size_1421_ = lean_ctor_get(v_r_1416_, 0);
lean_inc(v_size_1421_);
v_k_1422_ = lean_ctor_get(v_r_1416_, 1);
lean_inc(v_k_1422_);
v_v_1423_ = lean_ctor_get(v_r_1416_, 2);
lean_inc(v_v_1423_);
v_l_1424_ = lean_ctor_get(v_r_1416_, 3);
lean_inc(v_l_1424_);
v_r_1425_ = lean_ctor_get(v_r_1416_, 4);
lean_inc(v_r_1425_);
lean_dec_ref_known(v_r_1416_, 5);
v___x_1426_ = lean_apply_7(v_h__2_1420_, v_size_1421_, v_k_1422_, v_v_1423_, v_l_1424_, v_r_1425_, lean_box(0), lean_box(0));
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; 
lean_dec(v_h__2_1420_);
v___x_1427_ = lean_apply_2(v_h__1_1419_, lean_box(0), lean_box(0));
return v___x_1427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(lean_object* v_00_u03b1_1428_, lean_object* v_00_u03b2_1429_, lean_object* v_l_1430_, lean_object* v_motive_1431_, lean_object* v_r_1432_, lean_object* v_hr_1433_, lean_object* v_hlr_1434_, lean_object* v_h__1_1435_, lean_object* v_h__2_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(v_00_u03b1_1428_, v_00_u03b2_1429_, v_l_1430_, v_motive_1431_, v_r_1432_, v_hr_1433_, v_hlr_1434_, v_h__1_1435_, v_h__2_1436_);
lean_dec(v_l_1430_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(lean_object* v_r_1438_, lean_object* v_h__1_1439_, lean_object* v_h__2_1440_){
_start:
{
if (lean_obj_tag(v_r_1438_) == 0)
{
lean_object* v_size_1441_; lean_object* v_k_1442_; lean_object* v_v_1443_; lean_object* v_l_1444_; lean_object* v_r_1445_; lean_object* v___x_1446_; 
lean_dec(v_h__1_1439_);
v_size_1441_ = lean_ctor_get(v_r_1438_, 0);
lean_inc(v_size_1441_);
v_k_1442_ = lean_ctor_get(v_r_1438_, 1);
lean_inc(v_k_1442_);
v_v_1443_ = lean_ctor_get(v_r_1438_, 2);
lean_inc(v_v_1443_);
v_l_1444_ = lean_ctor_get(v_r_1438_, 3);
lean_inc(v_l_1444_);
v_r_1445_ = lean_ctor_get(v_r_1438_, 4);
lean_inc(v_r_1445_);
lean_dec_ref_known(v_r_1438_, 5);
v___x_1446_ = lean_apply_7(v_h__2_1440_, v_size_1441_, v_k_1442_, v_v_1443_, v_l_1444_, v_r_1445_, lean_box(0), lean_box(0));
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; 
lean_dec(v_h__2_1440_);
v___x_1447_ = lean_apply_2(v_h__1_1439_, lean_box(0), lean_box(0));
return v___x_1447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(lean_object* v_00_u03b1_1448_, lean_object* v_00_u03b2_1449_, lean_object* v_sz_1450_, lean_object* v_k_1451_, lean_object* v_v_1452_, lean_object* v_l_x27_1453_, lean_object* v_r_x27_1454_, lean_object* v_motive_1455_, lean_object* v_r_1456_, lean_object* v_hr_1457_, lean_object* v_hlr_1458_, lean_object* v_h__1_1459_, lean_object* v_h__2_1460_){
_start:
{
if (lean_obj_tag(v_r_1456_) == 0)
{
lean_object* v_size_1461_; lean_object* v_k_1462_; lean_object* v_v_1463_; lean_object* v_l_1464_; lean_object* v_r_1465_; lean_object* v___x_1466_; 
lean_dec(v_h__1_1459_);
v_size_1461_ = lean_ctor_get(v_r_1456_, 0);
lean_inc(v_size_1461_);
v_k_1462_ = lean_ctor_get(v_r_1456_, 1);
lean_inc(v_k_1462_);
v_v_1463_ = lean_ctor_get(v_r_1456_, 2);
lean_inc(v_v_1463_);
v_l_1464_ = lean_ctor_get(v_r_1456_, 3);
lean_inc(v_l_1464_);
v_r_1465_ = lean_ctor_get(v_r_1456_, 4);
lean_inc(v_r_1465_);
lean_dec_ref_known(v_r_1456_, 5);
v___x_1466_ = lean_apply_7(v_h__2_1460_, v_size_1461_, v_k_1462_, v_v_1463_, v_l_1464_, v_r_1465_, lean_box(0), lean_box(0));
return v___x_1466_;
}
else
{
lean_object* v___x_1467_; 
lean_dec(v_h__2_1460_);
v___x_1467_ = lean_apply_2(v_h__1_1459_, lean_box(0), lean_box(0));
return v___x_1467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(lean_object* v_00_u03b1_1468_, lean_object* v_00_u03b2_1469_, lean_object* v_sz_1470_, lean_object* v_k_1471_, lean_object* v_v_1472_, lean_object* v_l_x27_1473_, lean_object* v_r_x27_1474_, lean_object* v_motive_1475_, lean_object* v_r_1476_, lean_object* v_hr_1477_, lean_object* v_hlr_1478_, lean_object* v_h__1_1479_, lean_object* v_h__2_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(v_00_u03b1_1468_, v_00_u03b2_1469_, v_sz_1470_, v_k_1471_, v_v_1472_, v_l_x27_1473_, v_r_x27_1474_, v_motive_1475_, v_r_1476_, v_hr_1477_, v_hlr_1478_, v_h__1_1479_, v_h__2_1480_);
lean_dec(v_r_x27_1474_);
lean_dec(v_l_x27_1473_);
lean_dec(v_v_1472_);
lean_dec(v_k_1471_);
lean_dec(v_sz_1470_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(lean_object* v_t_1482_, lean_object* v_h__1_1483_, lean_object* v_h__2_1484_){
_start:
{
if (lean_obj_tag(v_t_1482_) == 0)
{
lean_object* v_size_1485_; lean_object* v_k_1486_; lean_object* v_v_1487_; lean_object* v_l_1488_; lean_object* v_r_1489_; lean_object* v___x_1490_; 
lean_dec(v_h__1_1483_);
v_size_1485_ = lean_ctor_get(v_t_1482_, 0);
lean_inc(v_size_1485_);
v_k_1486_ = lean_ctor_get(v_t_1482_, 1);
lean_inc(v_k_1486_);
v_v_1487_ = lean_ctor_get(v_t_1482_, 2);
lean_inc(v_v_1487_);
v_l_1488_ = lean_ctor_get(v_t_1482_, 3);
lean_inc(v_l_1488_);
v_r_1489_ = lean_ctor_get(v_t_1482_, 4);
lean_inc(v_r_1489_);
lean_dec_ref_known(v_t_1482_, 5);
v___x_1490_ = lean_apply_6(v_h__2_1484_, v_size_1485_, v_k_1486_, v_v_1487_, v_l_1488_, v_r_1489_, lean_box(0));
return v___x_1490_;
}
else
{
lean_object* v___x_1491_; 
lean_dec(v_h__2_1484_);
v___x_1491_ = lean_apply_1(v_h__1_1483_, lean_box(0));
return v___x_1491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(lean_object* v_00_u03b1_1492_, lean_object* v_00_u03b2_1493_, lean_object* v_motive_1494_, lean_object* v_t_1495_, lean_object* v_hr_1496_, lean_object* v_h__1_1497_, lean_object* v_h__2_1498_){
_start:
{
if (lean_obj_tag(v_t_1495_) == 0)
{
lean_object* v_size_1499_; lean_object* v_k_1500_; lean_object* v_v_1501_; lean_object* v_l_1502_; lean_object* v_r_1503_; lean_object* v___x_1504_; 
lean_dec(v_h__1_1497_);
v_size_1499_ = lean_ctor_get(v_t_1495_, 0);
lean_inc(v_size_1499_);
v_k_1500_ = lean_ctor_get(v_t_1495_, 1);
lean_inc(v_k_1500_);
v_v_1501_ = lean_ctor_get(v_t_1495_, 2);
lean_inc(v_v_1501_);
v_l_1502_ = lean_ctor_get(v_t_1495_, 3);
lean_inc(v_l_1502_);
v_r_1503_ = lean_ctor_get(v_t_1495_, 4);
lean_inc(v_r_1503_);
lean_dec_ref_known(v_t_1495_, 5);
v___x_1504_ = lean_apply_6(v_h__2_1498_, v_size_1499_, v_k_1500_, v_v_1501_, v_l_1502_, v_r_1503_, lean_box(0));
return v___x_1504_;
}
else
{
lean_object* v___x_1505_; 
lean_dec(v_h__2_1498_);
v___x_1505_ = lean_apply_1(v_h__1_1497_, lean_box(0));
return v___x_1505_;
}
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(uint8_t v_x_1506_, lean_object* v_h__1_1507_, lean_object* v_h__2_1508_, lean_object* v_h__3_1509_){
_start:
{
switch(v_x_1506_)
{
case 0:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec(v_h__3_1509_);
lean_dec(v_h__2_1508_);
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_apply_1(v_h__1_1507_, v___x_1510_);
return v___x_1511_;
}
case 1:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_dec(v_h__2_1508_);
lean_dec(v_h__1_1507_);
v___x_1512_ = lean_box(0);
v___x_1513_ = lean_apply_1(v_h__3_1509_, v___x_1512_);
return v___x_1513_;
}
default: 
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec(v_h__3_1509_);
lean_dec(v_h__1_1507_);
v___x_1514_ = lean_box(0);
v___x_1515_ = lean_apply_1(v_h__2_1508_, v___x_1514_);
return v___x_1515_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1506_ = stack[0].m_num;
lean_object* v_h__1_1507_ = stack[1].m_obj;
lean_object* v_h__2_1508_ = stack[2].m_obj;
lean_object* v_h__3_1509_ = stack[3].m_obj;
lean_object* v_res_1516_;
v_res_1516_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_1506_, v_h__1_1507_, v_h__2_1508_, v_h__3_1509_);
stack->m_obj
 = v_res_1516_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(lean_object* v_x_1517_, lean_object* v_h__1_1518_, lean_object* v_h__2_1519_, lean_object* v_h__3_1520_){
_start:
{
uint8_t v_x_33__boxed_1521_; lean_object* v_res_1522_; 
v_x_33__boxed_1521_ = lean_unbox(v_x_1517_);
v_res_1522_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_33__boxed_1521_, v_h__1_1518_, v_h__2_1519_, v_h__3_1520_);
return v_res_1522_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_object* v_motive_1523_, uint8_t v_x_1524_, lean_object* v_h__1_1525_, lean_object* v_h__2_1526_, lean_object* v_h__3_1527_){
_start:
{
switch(v_x_1524_)
{
case 0:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec(v_h__3_1527_);
lean_dec(v_h__2_1526_);
v___x_1528_ = lean_box(0);
v___x_1529_ = lean_apply_1(v_h__1_1525_, v___x_1528_);
return v___x_1529_;
}
case 1:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec(v_h__2_1526_);
lean_dec(v_h__1_1525_);
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_apply_1(v_h__3_1527_, v___x_1530_);
return v___x_1531_;
}
default: 
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec(v_h__3_1527_);
lean_dec(v_h__1_1525_);
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_apply_1(v_h__2_1526_, v___x_1532_);
return v___x_1533_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1524_ = stack[1].m_num;
lean_object* v_h__1_1525_ = stack[2].m_obj;
lean_object* v_h__2_1526_ = stack[3].m_obj;
lean_object* v_h__3_1527_ = stack[4].m_obj;
lean_object* v_res_1534_;
v_res_1534_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(lean_box(0), v_x_1524_, v_h__1_1525_, v_h__2_1526_, v_h__3_1527_);
stack->m_obj
 = v_res_1534_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(lean_object* v_motive_1535_, lean_object* v_x_1536_, lean_object* v_h__1_1537_, lean_object* v_h__2_1538_, lean_object* v_h__3_1539_){
_start:
{
uint8_t v_x_56__boxed_1540_; lean_object* v_res_1541_; 
v_x_56__boxed_1540_ = lean_unbox(v_x_1536_);
v_res_1541_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_1535_, v_x_56__boxed_1540_, v_h__1_1537_, v_h__2_1538_, v_h__3_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___redArg(lean_object* v_x_1542_, lean_object* v_h__1_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_apply_4(v_h__1_1543_, v_x_1542_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(lean_object* v_00_u03b1_1545_, lean_object* v_00_u03b2_1546_, lean_object* v_l_x27_1547_, lean_object* v_motive_1548_, lean_object* v_x_1549_, lean_object* v_h__1_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_apply_4(v_h__1_1550_, v_x_1549_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___boxed(lean_object* v_00_u03b1_1552_, lean_object* v_00_u03b2_1553_, lean_object* v_l_x27_1554_, lean_object* v_motive_1555_, lean_object* v_x_1556_, lean_object* v_h__1_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(v_00_u03b1_1552_, v_00_u03b2_1553_, v_l_x27_1554_, v_motive_1555_, v_x_1556_, v_h__1_1557_);
lean_dec(v_l_x27_1554_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(lean_object* v_x_1559_, lean_object* v_h__1_1560_, lean_object* v_h__2_1561_){
_start:
{
if (lean_obj_tag(v_x_1559_) == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec(v_h__2_1561_);
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_apply_1(v_h__1_1560_, v___x_1562_);
return v___x_1563_;
}
else
{
lean_object* v_val_1564_; lean_object* v_fst_1565_; lean_object* v_snd_1566_; lean_object* v___x_1567_; 
lean_dec(v_h__1_1560_);
v_val_1564_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_val_1564_);
lean_dec_ref_known(v_x_1559_, 1);
v_fst_1565_ = lean_ctor_get(v_val_1564_, 0);
lean_inc(v_fst_1565_);
v_snd_1566_ = lean_ctor_get(v_val_1564_, 1);
lean_inc(v_snd_1566_);
lean_dec(v_val_1564_);
v___x_1567_ = lean_apply_2(v_h__2_1561_, v_fst_1565_, v_snd_1566_);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(lean_object* v_00_u03b1_1568_, lean_object* v_00_u03b2_1569_, lean_object* v_motive_1570_, lean_object* v_x_1571_, lean_object* v_h__1_1572_, lean_object* v_h__2_1573_){
_start:
{
if (lean_obj_tag(v_x_1571_) == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_dec(v_h__2_1573_);
v___x_1574_ = lean_box(0);
v___x_1575_ = lean_apply_1(v_h__1_1572_, v___x_1574_);
return v___x_1575_;
}
else
{
lean_object* v_val_1576_; lean_object* v_fst_1577_; lean_object* v_snd_1578_; lean_object* v___x_1579_; 
lean_dec(v_h__1_1572_);
v_val_1576_ = lean_ctor_get(v_x_1571_, 0);
lean_inc(v_val_1576_);
lean_dec_ref_known(v_x_1571_, 1);
v_fst_1577_ = lean_ctor_get(v_val_1576_, 0);
lean_inc(v_fst_1577_);
v_snd_1578_ = lean_ctor_get(v_val_1576_, 1);
lean_inc(v_snd_1578_);
lean_dec(v_val_1576_);
v___x_1579_ = lean_apply_2(v_h__2_1573_, v_fst_1577_, v_snd_1578_);
return v___x_1579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___redArg(lean_object* v_x_1580_, lean_object* v_h__1_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_apply_4(v_h__1_1581_, v_x_1580_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(lean_object* v_00_u03b1_1583_, lean_object* v_00_u03b2_1584_, lean_object* v_l_1585_, lean_object* v_motive_1586_, lean_object* v_x_1587_, lean_object* v_h__1_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_apply_4(v_h__1_1588_, v_x_1587_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_1590_, lean_object* v_00_u03b2_1591_, lean_object* v_l_1592_, lean_object* v_motive_1593_, lean_object* v_x_1594_, lean_object* v_h__1_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(v_00_u03b1_1590_, v_00_u03b2_1591_, v_l_1592_, v_motive_1593_, v_x_1594_, v_h__1_1595_);
lean_dec(v_l_1592_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(lean_object* v_l_1597_, lean_object* v_h__1_1598_, lean_object* v_h__2_1599_){
_start:
{
if (lean_obj_tag(v_l_1597_) == 0)
{
lean_object* v_size_1600_; lean_object* v_k_1601_; lean_object* v_v_1602_; lean_object* v_l_1603_; lean_object* v_r_1604_; lean_object* v___x_1605_; 
lean_dec(v_h__1_1598_);
v_size_1600_ = lean_ctor_get(v_l_1597_, 0);
lean_inc(v_size_1600_);
v_k_1601_ = lean_ctor_get(v_l_1597_, 1);
lean_inc(v_k_1601_);
v_v_1602_ = lean_ctor_get(v_l_1597_, 2);
lean_inc(v_v_1602_);
v_l_1603_ = lean_ctor_get(v_l_1597_, 3);
lean_inc(v_l_1603_);
v_r_1604_ = lean_ctor_get(v_l_1597_, 4);
lean_inc(v_r_1604_);
lean_dec_ref_known(v_l_1597_, 5);
v___x_1605_ = lean_apply_5(v_h__2_1599_, v_size_1600_, v_k_1601_, v_v_1602_, v_l_1603_, v_r_1604_);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec(v_h__2_1599_);
v___x_1606_ = lean_box(0);
v___x_1607_ = lean_apply_1(v_h__1_1598_, v___x_1606_);
return v___x_1607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(lean_object* v_00_u03b1_1608_, lean_object* v_00_u03b2_1609_, lean_object* v_motive_1610_, lean_object* v_l_1611_, lean_object* v_h__1_1612_, lean_object* v_h__2_1613_){
_start:
{
if (lean_obj_tag(v_l_1611_) == 0)
{
lean_object* v_size_1614_; lean_object* v_k_1615_; lean_object* v_v_1616_; lean_object* v_l_1617_; lean_object* v_r_1618_; lean_object* v___x_1619_; 
lean_dec(v_h__1_1612_);
v_size_1614_ = lean_ctor_get(v_l_1611_, 0);
lean_inc(v_size_1614_);
v_k_1615_ = lean_ctor_get(v_l_1611_, 1);
lean_inc(v_k_1615_);
v_v_1616_ = lean_ctor_get(v_l_1611_, 2);
lean_inc(v_v_1616_);
v_l_1617_ = lean_ctor_get(v_l_1611_, 3);
lean_inc(v_l_1617_);
v_r_1618_ = lean_ctor_get(v_l_1611_, 4);
lean_inc(v_r_1618_);
lean_dec_ref_known(v_l_1611_, 5);
v___x_1619_ = lean_apply_5(v_h__2_1613_, v_size_1614_, v_k_1615_, v_v_1616_, v_l_1617_, v_r_1618_);
return v___x_1619_;
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_dec(v_h__2_1613_);
v___x_1620_ = lean_box(0);
v___x_1621_ = lean_apply_1(v_h__1_1612_, v___x_1620_);
return v___x_1621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(lean_object* v_r_1622_, lean_object* v_h__1_1623_, lean_object* v_h__2_1624_){
_start:
{
if (lean_obj_tag(v_r_1622_) == 0)
{
lean_object* v_size_1625_; lean_object* v_k_1626_; lean_object* v_v_1627_; lean_object* v_l_1628_; lean_object* v_r_1629_; lean_object* v___x_1630_; 
lean_dec(v_h__1_1623_);
v_size_1625_ = lean_ctor_get(v_r_1622_, 0);
lean_inc(v_size_1625_);
v_k_1626_ = lean_ctor_get(v_r_1622_, 1);
lean_inc(v_k_1626_);
v_v_1627_ = lean_ctor_get(v_r_1622_, 2);
lean_inc(v_v_1627_);
v_l_1628_ = lean_ctor_get(v_r_1622_, 3);
lean_inc(v_l_1628_);
v_r_1629_ = lean_ctor_get(v_r_1622_, 4);
lean_inc(v_r_1629_);
lean_dec_ref_known(v_r_1622_, 5);
v___x_1630_ = lean_apply_5(v_h__2_1624_, v_size_1625_, v_k_1626_, v_v_1627_, v_l_1628_, v_r_1629_);
return v___x_1630_;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_dec(v_h__2_1624_);
v___x_1631_ = lean_box(0);
v___x_1632_ = lean_apply_1(v_h__1_1623_, v___x_1631_);
return v___x_1632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(lean_object* v_00_u03b1_1633_, lean_object* v_00_u03b2_1634_, lean_object* v_motive_1635_, lean_object* v_r_1636_, lean_object* v_h__1_1637_, lean_object* v_h__2_1638_){
_start:
{
if (lean_obj_tag(v_r_1636_) == 0)
{
lean_object* v_size_1639_; lean_object* v_k_1640_; lean_object* v_v_1641_; lean_object* v_l_1642_; lean_object* v_r_1643_; lean_object* v___x_1644_; 
lean_dec(v_h__1_1637_);
v_size_1639_ = lean_ctor_get(v_r_1636_, 0);
lean_inc(v_size_1639_);
v_k_1640_ = lean_ctor_get(v_r_1636_, 1);
lean_inc(v_k_1640_);
v_v_1641_ = lean_ctor_get(v_r_1636_, 2);
lean_inc(v_v_1641_);
v_l_1642_ = lean_ctor_get(v_r_1636_, 3);
lean_inc(v_l_1642_);
v_r_1643_ = lean_ctor_get(v_r_1636_, 4);
lean_inc(v_r_1643_);
lean_dec_ref_known(v_r_1636_, 5);
v___x_1644_ = lean_apply_5(v_h__2_1638_, v_size_1639_, v_k_1640_, v_v_1641_, v_l_1642_, v_r_1643_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v_h__2_1638_);
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_apply_1(v_h__1_1637_, v___x_1645_);
return v___x_1646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(lean_object* v_x_1647_, lean_object* v_h__1_1648_, lean_object* v_h__2_1649_){
_start:
{
if (lean_obj_tag(v_x_1647_) == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec(v_h__2_1649_);
v___x_1650_ = lean_box(0);
v___x_1651_ = lean_apply_1(v_h__1_1648_, v___x_1650_);
return v___x_1651_;
}
else
{
lean_object* v_val_1652_; lean_object* v___x_1653_; 
lean_dec(v_h__1_1648_);
v_val_1652_ = lean_ctor_get(v_x_1647_, 0);
lean_inc(v_val_1652_);
lean_dec_ref_known(v_x_1647_, 1);
v___x_1653_ = lean_apply_1(v_h__2_1649_, v_val_1652_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(lean_object* v_00_u03b1_1654_, lean_object* v_00_u03b2_1655_, lean_object* v_motive_1656_, lean_object* v_x_1657_, lean_object* v_h__1_1658_, lean_object* v_h__2_1659_){
_start:
{
if (lean_obj_tag(v_x_1657_) == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
lean_dec(v_h__2_1659_);
v___x_1660_ = lean_box(0);
v___x_1661_ = lean_apply_1(v_h__1_1658_, v___x_1660_);
return v___x_1661_;
}
else
{
lean_object* v_val_1662_; lean_object* v___x_1663_; 
lean_dec(v_h__1_1658_);
v_val_1662_ = lean_ctor_get(v_x_1657_, 0);
lean_inc(v_val_1662_);
lean_dec_ref_known(v_x_1657_, 1);
v___x_1663_ = lean_apply_1(v_h__2_1659_, v_val_1662_);
return v___x_1663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(lean_object* v_x_1664_, lean_object* v_x_1665_, lean_object* v_h__1_1666_){
_start:
{
lean_object* v_size_1667_; lean_object* v_k_1668_; lean_object* v_v_1669_; lean_object* v_l_1670_; lean_object* v_r_1671_; lean_object* v___x_1672_; 
v_size_1667_ = lean_ctor_get(v_x_1664_, 0);
lean_inc(v_size_1667_);
v_k_1668_ = lean_ctor_get(v_x_1664_, 1);
lean_inc(v_k_1668_);
v_v_1669_ = lean_ctor_get(v_x_1664_, 2);
lean_inc(v_v_1669_);
v_l_1670_ = lean_ctor_get(v_x_1664_, 3);
lean_inc(v_l_1670_);
v_r_1671_ = lean_ctor_get(v_x_1664_, 4);
lean_inc(v_r_1671_);
lean_dec(v_x_1664_);
v___x_1672_ = lean_apply_8(v_h__1_1666_, v_size_1667_, v_k_1668_, v_v_1669_, v_l_1670_, v_r_1671_, lean_box(0), v_x_1665_, lean_box(0));
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter(lean_object* v_00_u03b1_1673_, lean_object* v_00_u03b2_1674_, lean_object* v_motive_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_, lean_object* v_h__1_1680_){
_start:
{
lean_object* v_size_1681_; lean_object* v_k_1682_; lean_object* v_v_1683_; lean_object* v_l_1684_; lean_object* v_r_1685_; lean_object* v___x_1686_; 
v_size_1681_ = lean_ctor_get(v_x_1676_, 0);
lean_inc(v_size_1681_);
v_k_1682_ = lean_ctor_get(v_x_1676_, 1);
lean_inc(v_k_1682_);
v_v_1683_ = lean_ctor_get(v_x_1676_, 2);
lean_inc(v_v_1683_);
v_l_1684_ = lean_ctor_get(v_x_1676_, 3);
lean_inc(v_l_1684_);
v_r_1685_ = lean_ctor_get(v_x_1676_, 4);
lean_inc(v_r_1685_);
lean_dec(v_x_1676_);
v___x_1686_ = lean_apply_8(v_h__1_1680_, v_size_1681_, v_k_1682_, v_v_1683_, v_l_1684_, v_r_1685_, lean_box(0), v_x_1678_, lean_box(0));
return v___x_1686_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(uint8_t v_x_1687_, lean_object* v_h__1_1688_, lean_object* v_h__2_1689_, lean_object* v_h__3_1690_){
_start:
{
switch(v_x_1687_)
{
case 0:
{
lean_object* v___x_1691_; 
lean_dec(v_h__3_1690_);
lean_dec(v_h__2_1689_);
v___x_1691_ = lean_apply_1(v_h__1_1688_, lean_box(0));
return v___x_1691_;
}
case 1:
{
lean_object* v___x_1692_; 
lean_dec(v_h__3_1690_);
lean_dec(v_h__1_1688_);
v___x_1692_ = lean_apply_1(v_h__2_1689_, lean_box(0));
return v___x_1692_;
}
default: 
{
lean_object* v___x_1693_; 
lean_dec(v_h__2_1689_);
lean_dec(v_h__1_1688_);
v___x_1693_ = lean_apply_1(v_h__3_1690_, lean_box(0));
return v___x_1693_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1687_ = stack[0].m_num;
lean_object* v_h__1_1688_ = stack[1].m_obj;
lean_object* v_h__2_1689_ = stack[2].m_obj;
lean_object* v_h__3_1690_ = stack[3].m_obj;
lean_object* v_res_1694_;
v_res_1694_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(v_x_1687_, v_h__1_1688_, v_h__2_1689_, v_h__3_1690_);
stack->m_obj
 = v_res_1694_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg___boxed(lean_object* v_x_1695_, lean_object* v_h__1_1696_, lean_object* v_h__2_1697_, lean_object* v_h__3_1698_){
_start:
{
uint8_t v_x_33__boxed_1699_; lean_object* v_res_1700_; 
v_x_33__boxed_1699_ = lean_unbox(v_x_1695_);
v_res_1700_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(v_x_33__boxed_1699_, v_h__1_1696_, v_h__2_1697_, v_h__3_1698_);
return v_res_1700_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(lean_object* v_motive_1701_, uint8_t v_x_1702_, lean_object* v_h__1_1703_, lean_object* v_h__2_1704_, lean_object* v_h__3_1705_){
_start:
{
switch(v_x_1702_)
{
case 0:
{
lean_object* v___x_1706_; 
lean_dec(v_h__3_1705_);
lean_dec(v_h__2_1704_);
v___x_1706_ = lean_apply_1(v_h__1_1703_, lean_box(0));
return v___x_1706_;
}
case 1:
{
lean_object* v___x_1707_; 
lean_dec(v_h__3_1705_);
lean_dec(v_h__1_1703_);
v___x_1707_ = lean_apply_1(v_h__2_1704_, lean_box(0));
return v___x_1707_;
}
default: 
{
lean_object* v___x_1708_; 
lean_dec(v_h__2_1704_);
lean_dec(v_h__1_1703_);
v___x_1708_ = lean_apply_1(v_h__3_1705_, lean_box(0));
return v___x_1708_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1702_ = stack[1].m_num;
lean_object* v_h__1_1703_ = stack[2].m_obj;
lean_object* v_h__2_1704_ = stack[3].m_obj;
lean_object* v_h__3_1705_ = stack[4].m_obj;
lean_object* v_res_1709_;
v_res_1709_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(lean_box(0), v_x_1702_, v_h__1_1703_, v_h__2_1704_, v_h__3_1705_);
stack->m_obj
 = v_res_1709_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___boxed(lean_object* v_motive_1710_, lean_object* v_x_1711_, lean_object* v_h__1_1712_, lean_object* v_h__2_1713_, lean_object* v_h__3_1714_){
_start:
{
uint8_t v_x_47__boxed_1715_; lean_object* v_res_1716_; 
v_x_47__boxed_1715_ = lean_unbox(v_x_1711_);
v_res_1716_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(v_motive_1710_, v_x_47__boxed_1715_, v_h__1_1712_, v_h__2_1713_, v_h__3_1714_);
return v_res_1716_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(uint8_t v_x_1717_, lean_object* v_h__1_1718_, lean_object* v_h__2_1719_, lean_object* v_h__3_1720_){
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
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1717_ = stack[0].m_num;
lean_object* v_h__1_1718_ = stack[1].m_obj;
lean_object* v_h__2_1719_ = stack[2].m_obj;
lean_object* v_h__3_1720_ = stack[3].m_obj;
lean_object* v_res_1727_;
v_res_1727_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_1717_, v_h__1_1718_, v_h__2_1719_, v_h__3_1720_);
stack->m_obj
 = v_res_1727_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_1728_, lean_object* v_h__1_1729_, lean_object* v_h__2_1730_, lean_object* v_h__3_1731_){
_start:
{
uint8_t v_x_33__boxed_1732_; lean_object* v_res_1733_; 
v_x_33__boxed_1732_ = lean_unbox(v_x_1728_);
v_res_1733_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_33__boxed_1732_, v_h__1_1729_, v_h__2_1730_, v_h__3_1731_);
return v_res_1733_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_object* v_motive_1734_, uint8_t v_x_1735_, lean_object* v_h__1_1736_, lean_object* v_h__2_1737_, lean_object* v_h__3_1738_){
_start:
{
switch(v_x_1735_)
{
case 0:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_dec(v_h__3_1738_);
lean_dec(v_h__2_1737_);
v___x_1739_ = lean_box(0);
v___x_1740_ = lean_apply_1(v_h__1_1736_, v___x_1739_);
return v___x_1740_;
}
case 1:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_dec(v_h__3_1738_);
lean_dec(v_h__1_1736_);
v___x_1741_ = lean_box(0);
v___x_1742_ = lean_apply_1(v_h__2_1737_, v___x_1741_);
return v___x_1742_;
}
default: 
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec(v_h__2_1737_);
lean_dec(v_h__1_1736_);
v___x_1743_ = lean_box(0);
v___x_1744_ = lean_apply_1(v_h__3_1738_, v___x_1743_);
return v___x_1744_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1735_ = stack[1].m_num;
lean_object* v_h__1_1736_ = stack[2].m_obj;
lean_object* v_h__2_1737_ = stack[3].m_obj;
lean_object* v_h__3_1738_ = stack[4].m_obj;
lean_object* v_res_1745_;
v_res_1745_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(lean_box(0), v_x_1735_, v_h__1_1736_, v_h__2_1737_, v_h__3_1738_);
stack->m_obj
 = v_res_1745_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(lean_object* v_motive_1746_, lean_object* v_x_1747_, lean_object* v_h__1_1748_, lean_object* v_h__2_1749_, lean_object* v_h__3_1750_){
_start:
{
uint8_t v_x_56__boxed_1751_; lean_object* v_res_1752_; 
v_x_56__boxed_1751_ = lean_unbox(v_x_1747_);
v_res_1752_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(v_motive_1746_, v_x_56__boxed_1751_, v_h__1_1748_, v_h__2_1749_, v_h__3_1750_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(lean_object* v_x_1753_, lean_object* v_x_1754_, lean_object* v_h__1_1755_, lean_object* v_h__2_1756_){
_start:
{
if (lean_obj_tag(v_x_1753_) == 0)
{
lean_object* v_size_1757_; lean_object* v_k_1758_; lean_object* v_v_1759_; lean_object* v_l_1760_; lean_object* v_r_1761_; lean_object* v___x_1762_; 
lean_dec(v_h__1_1755_);
v_size_1757_ = lean_ctor_get(v_x_1753_, 0);
lean_inc(v_size_1757_);
v_k_1758_ = lean_ctor_get(v_x_1753_, 1);
lean_inc(v_k_1758_);
v_v_1759_ = lean_ctor_get(v_x_1753_, 2);
lean_inc(v_v_1759_);
v_l_1760_ = lean_ctor_get(v_x_1753_, 3);
lean_inc(v_l_1760_);
v_r_1761_ = lean_ctor_get(v_x_1753_, 4);
lean_inc(v_r_1761_);
lean_dec_ref_known(v_x_1753_, 5);
v___x_1762_ = lean_apply_6(v_h__2_1756_, v_size_1757_, v_k_1758_, v_v_1759_, v_l_1760_, v_r_1761_, v_x_1754_);
return v___x_1762_;
}
else
{
lean_object* v___x_1763_; 
lean_dec(v_h__2_1756_);
v___x_1763_ = lean_apply_1(v_h__1_1755_, v_x_1754_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(lean_object* v_00_u03b1_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_motive_1766_, lean_object* v_x_1767_, lean_object* v_x_1768_, lean_object* v_h__1_1769_, lean_object* v_h__2_1770_){
_start:
{
if (lean_obj_tag(v_x_1767_) == 0)
{
lean_object* v_size_1771_; lean_object* v_k_1772_; lean_object* v_v_1773_; lean_object* v_l_1774_; lean_object* v_r_1775_; lean_object* v___x_1776_; 
lean_dec(v_h__1_1769_);
v_size_1771_ = lean_ctor_get(v_x_1767_, 0);
lean_inc(v_size_1771_);
v_k_1772_ = lean_ctor_get(v_x_1767_, 1);
lean_inc(v_k_1772_);
v_v_1773_ = lean_ctor_get(v_x_1767_, 2);
lean_inc(v_v_1773_);
v_l_1774_ = lean_ctor_get(v_x_1767_, 3);
lean_inc(v_l_1774_);
v_r_1775_ = lean_ctor_get(v_x_1767_, 4);
lean_inc(v_r_1775_);
lean_dec_ref_known(v_x_1767_, 5);
v___x_1776_ = lean_apply_6(v_h__2_1770_, v_size_1771_, v_k_1772_, v_v_1773_, v_l_1774_, v_r_1775_, v_x_1768_);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; 
lean_dec(v_h__2_1770_);
v___x_1777_ = lean_apply_1(v_h__1_1769_, v_x_1768_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(lean_object* v_x_1778_, lean_object* v_c_1779_, lean_object* v_x_1780_, lean_object* v_r_1781_){
_start:
{
if (lean_obj_tag(v_c_1779_) == 0)
{
lean_object* v___x_1782_; 
v___x_1782_ = l_List_head_x3f___redArg(v_r_1781_);
return v___x_1782_;
}
else
{
lean_object* v_val_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
v_val_1783_ = lean_ctor_get(v_c_1779_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_c_1779_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v_c_1779_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_val_1783_);
lean_dec(v_c_1779_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_val_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed(lean_object* v_x_1791_, lean_object* v_c_1792_, lean_object* v_x_1793_, lean_object* v_r_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(v_x_1791_, v_c_1792_, v_x_1793_, v_r_1794_);
lean_dec(v_r_1794_);
lean_dec(v_x_1791_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(lean_object* v_inst_1797_, lean_object* v_k_1798_, lean_object* v_t_1799_){
_start:
{
lean_object* v___f_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___f_1800_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0));
v___x_1801_ = lean_apply_1(v_inst_1797_, v_k_1798_);
v___x_1802_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___x_1801_, v_t_1799_, v___f_1800_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098(lean_object* v_00_u03b1_1803_, lean_object* v_00_u03b2_1804_, lean_object* v_inst_1805_, lean_object* v_k_1806_, lean_object* v_t_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(v_inst_1805_, v_k_1806_, v_t_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(lean_object* v_x_1809_, lean_object* v_x_1810_){
_start:
{
switch(lean_obj_tag(v_x_1810_))
{
case 0:
{
lean_object* v_a_1811_; lean_object* v_a_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v_a_1811_ = lean_ctor_get(v_x_1810_, 0);
lean_inc(v_a_1811_);
v_a_1812_ = lean_ctor_get(v_x_1810_, 1);
lean_inc(v_a_1812_);
lean_dec_ref_known(v_x_1810_, 3);
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v_a_1811_);
lean_ctor_set(v___x_1813_, 1, v_a_1812_);
v___x_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
return v___x_1814_;
}
case 1:
{
lean_object* v_a_1815_; 
v_a_1815_ = lean_ctor_get(v_x_1810_, 1);
lean_inc(v_a_1815_);
if (lean_obj_tag(v_a_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1817_; 
v_a_1816_ = lean_ctor_get(v_x_1810_, 2);
lean_inc(v_a_1816_);
lean_dec_ref_known(v_x_1810_, 3);
v___x_1817_ = l_List_head_x3f___redArg(v_a_1816_);
lean_dec(v_a_1816_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_inc(v_x_1809_);
return v_x_1809_;
}
else
{
return v___x_1817_;
}
}
else
{
lean_object* v_val_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec_ref_known(v_x_1810_, 3);
v_val_1818_ = lean_ctor_get(v_a_1815_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_a_1815_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v_a_1815_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_val_1818_);
lean_dec(v_a_1815_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_val_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
default: 
{
lean_dec_ref_known(v_x_1810_, 3);
lean_inc(v_x_1809_);
return v_x_1809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed(lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(v_x_1826_, v_x_1827_);
lean_dec(v_x_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(lean_object* v_inst_1830_, lean_object* v_k_1831_, lean_object* v_t_1832_){
_start:
{
lean_object* v___f_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___f_1833_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0));
v___x_1834_ = lean_apply_1(v_inst_1830_, v_k_1831_);
v___x_1835_ = lean_box(0);
v___x_1836_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___x_1834_, v___x_1835_, v___f_1833_, v_t_1832_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27(lean_object* v_00_u03b1_1837_, lean_object* v_00_u03b2_1838_, lean_object* v_inst_1839_, lean_object* v_k_1840_, lean_object* v_t_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(v_inst_1839_, v_k_1840_, v_t_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_x_1843_, lean_object* v_x_1844_, lean_object* v_h__1_1845_, lean_object* v_h__2_1846_, lean_object* v_h__3_1847_){
_start:
{
switch(lean_obj_tag(v_x_1844_))
{
case 0:
{
lean_object* v_a_1848_; lean_object* v_a_1849_; lean_object* v_a_1850_; lean_object* v___x_1851_; 
lean_dec(v_h__3_1847_);
lean_dec(v_h__2_1846_);
v_a_1848_ = lean_ctor_get(v_x_1844_, 0);
lean_inc(v_a_1848_);
v_a_1849_ = lean_ctor_get(v_x_1844_, 1);
lean_inc(v_a_1849_);
v_a_1850_ = lean_ctor_get(v_x_1844_, 2);
lean_inc(v_a_1850_);
lean_dec_ref_known(v_x_1844_, 3);
v___x_1851_ = lean_apply_5(v_h__1_1845_, v_x_1843_, v_a_1848_, lean_box(0), v_a_1849_, v_a_1850_);
return v___x_1851_;
}
case 1:
{
lean_object* v_a_1852_; lean_object* v_a_1853_; lean_object* v_a_1854_; lean_object* v___x_1855_; 
lean_dec(v_h__3_1847_);
lean_dec(v_h__1_1845_);
v_a_1852_ = lean_ctor_get(v_x_1844_, 0);
lean_inc(v_a_1852_);
v_a_1853_ = lean_ctor_get(v_x_1844_, 1);
lean_inc(v_a_1853_);
v_a_1854_ = lean_ctor_get(v_x_1844_, 2);
lean_inc(v_a_1854_);
lean_dec_ref_known(v_x_1844_, 3);
v___x_1855_ = lean_apply_4(v_h__2_1846_, v_x_1843_, v_a_1852_, v_a_1853_, v_a_1854_);
return v___x_1855_;
}
default: 
{
lean_object* v_a_1856_; lean_object* v_a_1857_; lean_object* v_a_1858_; lean_object* v___x_1859_; 
lean_dec(v_h__2_1846_);
lean_dec(v_h__1_1845_);
v_a_1856_ = lean_ctor_get(v_x_1844_, 0);
lean_inc(v_a_1856_);
v_a_1857_ = lean_ctor_get(v_x_1844_, 1);
lean_inc(v_a_1857_);
v_a_1858_ = lean_ctor_get(v_x_1844_, 2);
lean_inc(v_a_1858_);
lean_dec_ref_known(v_x_1844_, 3);
v___x_1859_ = lean_apply_5(v_h__3_1847_, v_x_1843_, v_a_1856_, v_a_1857_, lean_box(0), v_a_1858_);
return v___x_1859_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_1860_, lean_object* v_00_u03b2_1861_, lean_object* v_inst_1862_, lean_object* v_k_1863_, lean_object* v_motive_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v_h__1_1867_, lean_object* v_h__2_1868_, lean_object* v_h__3_1869_){
_start:
{
switch(lean_obj_tag(v_x_1866_))
{
case 0:
{
lean_object* v_a_1870_; lean_object* v_a_1871_; lean_object* v_a_1872_; lean_object* v___x_1873_; 
lean_dec(v_h__3_1869_);
lean_dec(v_h__2_1868_);
v_a_1870_ = lean_ctor_get(v_x_1866_, 0);
lean_inc(v_a_1870_);
v_a_1871_ = lean_ctor_get(v_x_1866_, 1);
lean_inc(v_a_1871_);
v_a_1872_ = lean_ctor_get(v_x_1866_, 2);
lean_inc(v_a_1872_);
lean_dec_ref_known(v_x_1866_, 3);
v___x_1873_ = lean_apply_5(v_h__1_1867_, v_x_1865_, v_a_1870_, lean_box(0), v_a_1871_, v_a_1872_);
return v___x_1873_;
}
case 1:
{
lean_object* v_a_1874_; lean_object* v_a_1875_; lean_object* v_a_1876_; lean_object* v___x_1877_; 
lean_dec(v_h__3_1869_);
lean_dec(v_h__1_1867_);
v_a_1874_ = lean_ctor_get(v_x_1866_, 0);
lean_inc(v_a_1874_);
v_a_1875_ = lean_ctor_get(v_x_1866_, 1);
lean_inc(v_a_1875_);
v_a_1876_ = lean_ctor_get(v_x_1866_, 2);
lean_inc(v_a_1876_);
lean_dec_ref_known(v_x_1866_, 3);
v___x_1877_ = lean_apply_4(v_h__2_1868_, v_x_1865_, v_a_1874_, v_a_1875_, v_a_1876_);
return v___x_1877_;
}
default: 
{
lean_object* v_a_1878_; lean_object* v_a_1879_; lean_object* v_a_1880_; lean_object* v___x_1881_; 
lean_dec(v_h__2_1868_);
lean_dec(v_h__1_1867_);
v_a_1878_ = lean_ctor_get(v_x_1866_, 0);
lean_inc(v_a_1878_);
v_a_1879_ = lean_ctor_get(v_x_1866_, 1);
lean_inc(v_a_1879_);
v_a_1880_ = lean_ctor_get(v_x_1866_, 2);
lean_inc(v_a_1880_);
lean_dec_ref_known(v_x_1866_, 3);
v___x_1881_ = lean_apply_5(v_h__3_1869_, v_x_1865_, v_a_1878_, v_a_1879_, lean_box(0), v_a_1880_);
return v___x_1881_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_1882_, lean_object* v_00_u03b2_1883_, lean_object* v_inst_1884_, lean_object* v_k_1885_, lean_object* v_motive_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v_h__1_1889_, lean_object* v_h__2_1890_, lean_object* v_h__3_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(v_00_u03b1_1882_, v_00_u03b2_1883_, v_inst_1884_, v_k_1885_, v_motive_1886_, v_x_1887_, v_x_1888_, v_h__1_1889_, v_h__2_1890_, v_h__3_1891_);
lean_dec(v_k_1885_);
lean_dec_ref(v_inst_1884_);
return v_res_1892_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(lean_object* v_inst_1893_, lean_object* v_k_1894_, lean_object* v_k_x27_1895_){
_start:
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = lean_apply_2(v_inst_1893_, v_k_1894_, v_k_x27_1895_);
v___x_1897_ = lean_unbox(v___x_1896_);
if (v___x_1897_ == 1)
{
uint8_t v___x_1898_; 
v___x_1898_ = 2;
return v___x_1898_;
}
else
{
uint8_t v___x_1899_; 
v___x_1899_ = lean_unbox(v___x_1896_);
return v___x_1899_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1893_ = stack[0].m_obj;
lean_object* v_k_1894_ = stack[1].m_obj;
lean_object* v_k_x27_1895_ = stack[2].m_obj;
uint8_t v_res_1900_;
v_res_1900_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(v_inst_1893_, v_k_1894_, v_k_x27_1895_);
stack->m_num = v_res_1900_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed(lean_object* v_inst_1901_, lean_object* v_k_1902_, lean_object* v_k_x27_1903_){
_start:
{
uint8_t v_res_1904_; lean_object* v_r_1905_; 
v_res_1904_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(v_inst_1901_, v_k_1902_, v_k_x27_1903_);
v_r_1905_ = lean_box(v_res_1904_);
return v_r_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(lean_object* v_inst_1906_, lean_object* v_k_1907_, lean_object* v_t_1908_){
_start:
{
lean_object* v___f_1909_; lean_object* v___f_1910_; lean_object* v___x_1911_; 
v___f_1909_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1909_, 0, v_inst_1906_);
lean_closure_set(v___f_1909_, 1, v_k_1907_);
v___f_1910_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0));
v___x_1911_ = l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_1909_, v_t_1908_, v___f_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098(lean_object* v_00_u03b1_1912_, lean_object* v_00_u03b2_1913_, lean_object* v_inst_1914_, lean_object* v_k_1915_, lean_object* v_t_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(v_inst_1914_, v_k_1915_, v_t_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(lean_object* v_x_1918_, lean_object* v_x_1919_){
_start:
{
switch(lean_obj_tag(v_x_1919_))
{
case 0:
{
lean_object* v_a_1920_; lean_object* v_a_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_a_1920_ = lean_ctor_get(v_x_1919_, 0);
v_a_1921_ = lean_ctor_get(v_x_1919_, 1);
lean_inc(v_a_1921_);
lean_inc(v_a_1920_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v_a_1920_);
lean_ctor_set(v___x_1922_, 1, v_a_1921_);
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
return v___x_1923_;
}
case 1:
{
lean_object* v_a_1924_; lean_object* v___x_1925_; 
v_a_1924_ = lean_ctor_get(v_x_1919_, 2);
v___x_1925_ = l_List_head_x3f___redArg(v_a_1924_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_inc(v_x_1918_);
return v_x_1918_;
}
else
{
return v___x_1925_;
}
}
default: 
{
lean_inc(v_x_1918_);
return v_x_1918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed(lean_object* v_x_1926_, lean_object* v_x_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(v_x_1926_, v_x_1927_);
lean_dec_ref(v_x_1927_);
lean_dec(v_x_1926_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(lean_object* v_inst_1930_, lean_object* v_k_1931_, lean_object* v_t_1932_){
_start:
{
lean_object* v___f_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___f_1933_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1933_, 0, v_inst_1930_);
lean_closure_set(v___f_1933_, 1, v_k_1931_);
v___f_1934_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0));
v___x_1935_ = lean_box(0);
v___x_1936_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(v___f_1933_, v___x_1935_, v___f_1934_, v_t_1932_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27(lean_object* v_00_u03b1_1937_, lean_object* v_00_u03b2_1938_, lean_object* v_inst_1939_, lean_object* v_k_1940_, lean_object* v_t_1941_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(v_inst_1939_, v_k_1940_, v_t_1941_);
return v___x_1942_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(uint8_t v_x_1943_, lean_object* v_h__1_1944_, lean_object* v_h__2_1945_){
_start:
{
if (v_x_1943_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
lean_dec(v_h__2_1945_);
v___x_1946_ = lean_box(0);
v___x_1947_ = lean_apply_1(v_h__1_1944_, v___x_1946_);
return v___x_1947_;
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec(v_h__1_1944_);
v___x_1948_ = lean_box(v_x_1943_);
v___x_1949_ = lean_apply_2(v_h__2_1945_, v___x_1948_, lean_box(0));
return v___x_1949_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1943_ = stack[0].m_num;
lean_object* v_h__1_1944_ = stack[1].m_obj;
lean_object* v_h__2_1945_ = stack[2].m_obj;
lean_object* v_res_1950_;
v_res_1950_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(v_x_1943_, v_h__1_1944_, v_h__2_1945_);
stack->m_obj
 = v_res_1950_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg___boxed(lean_object* v_x_1951_, lean_object* v_h__1_1952_, lean_object* v_h__2_1953_){
_start:
{
uint8_t v_x_13__boxed_1954_; lean_object* v_res_1955_; 
v_x_13__boxed_1954_ = lean_unbox(v_x_1951_);
v_res_1955_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(v_x_13__boxed_1954_, v_h__1_1952_, v_h__2_1953_);
return v_res_1955_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(lean_object* v_motive_1956_, uint8_t v_x_1957_, lean_object* v_h__1_1958_, lean_object* v_h__2_1959_){
_start:
{
if (v_x_1957_ == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec(v_h__2_1959_);
v___x_1960_ = lean_box(0);
v___x_1961_ = lean_apply_1(v_h__1_1958_, v___x_1960_);
return v___x_1961_;
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_dec(v_h__1_1958_);
v___x_1962_ = lean_box(v_x_1957_);
v___x_1963_ = lean_apply_2(v_h__2_1959_, v___x_1962_, lean_box(0));
return v___x_1963_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1957_ = stack[1].m_num;
lean_object* v_h__1_1958_ = stack[2].m_obj;
lean_object* v_h__2_1959_ = stack[3].m_obj;
lean_object* v_res_1964_;
v_res_1964_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(lean_box(0), v_x_1957_, v_h__1_1958_, v_h__2_1959_);
stack->m_obj
 = v_res_1964_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___boxed(lean_object* v_motive_1965_, lean_object* v_x_1966_, lean_object* v_h__1_1967_, lean_object* v_h__2_1968_){
_start:
{
uint8_t v_x_30__boxed_1969_; lean_object* v_res_1970_; 
v_x_30__boxed_1969_ = lean_unbox(v_x_1966_);
v_res_1970_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(v_motive_1965_, v_x_30__boxed_1969_, v_h__1_1967_, v_h__2_1968_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___redArg(lean_object* v_x_1971_, lean_object* v_x_1972_, lean_object* v_h__1_1973_, lean_object* v_h__2_1974_, lean_object* v_h__3_1975_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(lean_object* v_00_u03b1_1988_, lean_object* v_00_u03b2_1989_, lean_object* v_inst_1990_, lean_object* v_k_1991_, lean_object* v_motive_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v_h__1_1995_, lean_object* v_h__2_1996_, lean_object* v_h__3_1997_){
_start:
{
switch(lean_obj_tag(v_x_1994_))
{
case 0:
{
lean_object* v_a_1998_; lean_object* v_a_1999_; lean_object* v_a_2000_; lean_object* v___x_2001_; 
lean_dec(v_h__3_1997_);
lean_dec(v_h__2_1996_);
v_a_1998_ = lean_ctor_get(v_x_1994_, 0);
lean_inc(v_a_1998_);
v_a_1999_ = lean_ctor_get(v_x_1994_, 1);
lean_inc(v_a_1999_);
v_a_2000_ = lean_ctor_get(v_x_1994_, 2);
lean_inc(v_a_2000_);
lean_dec_ref_known(v_x_1994_, 3);
v___x_2001_ = lean_apply_5(v_h__1_1995_, v_x_1993_, v_a_1998_, lean_box(0), v_a_1999_, v_a_2000_);
return v___x_2001_;
}
case 1:
{
lean_object* v_a_2002_; lean_object* v_a_2003_; lean_object* v_a_2004_; lean_object* v___x_2005_; 
lean_dec(v_h__3_1997_);
lean_dec(v_h__1_1995_);
v_a_2002_ = lean_ctor_get(v_x_1994_, 0);
lean_inc(v_a_2002_);
v_a_2003_ = lean_ctor_get(v_x_1994_, 1);
lean_inc(v_a_2003_);
v_a_2004_ = lean_ctor_get(v_x_1994_, 2);
lean_inc(v_a_2004_);
lean_dec_ref_known(v_x_1994_, 3);
v___x_2005_ = lean_apply_4(v_h__2_1996_, v_x_1993_, v_a_2002_, v_a_2003_, v_a_2004_);
return v___x_2005_;
}
default: 
{
lean_object* v_a_2006_; lean_object* v_a_2007_; lean_object* v_a_2008_; lean_object* v___x_2009_; 
lean_dec(v_h__2_1996_);
lean_dec(v_h__1_1995_);
v_a_2006_ = lean_ctor_get(v_x_1994_, 0);
lean_inc(v_a_2006_);
v_a_2007_ = lean_ctor_get(v_x_1994_, 1);
lean_inc(v_a_2007_);
v_a_2008_ = lean_ctor_get(v_x_1994_, 2);
lean_inc(v_a_2008_);
lean_dec_ref_known(v_x_1994_, 3);
v___x_2009_ = lean_apply_5(v_h__3_1997_, v_x_1993_, v_a_2006_, v_a_2007_, lean_box(0), v_a_2008_);
return v___x_2009_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_2010_, lean_object* v_00_u03b2_2011_, lean_object* v_inst_2012_, lean_object* v_k_2013_, lean_object* v_motive_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_, lean_object* v_h__1_2017_, lean_object* v_h__2_2018_, lean_object* v_h__3_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(v_00_u03b1_2010_, v_00_u03b2_2011_, v_inst_2012_, v_k_2013_, v_motive_2014_, v_x_2015_, v_x_2016_, v_h__1_2017_, v_h__2_2018_, v_h__3_2019_);
lean_dec(v_k_2013_);
lean_dec_ref(v_inst_2012_);
return v_res_2020_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(uint8_t v_x_2021_, lean_object* v_h__1_2022_, lean_object* v_h__2_2023_){
_start:
{
if (v_x_2021_ == 2)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
lean_dec(v_h__2_2023_);
v___x_2024_ = lean_box(0);
v___x_2025_ = lean_apply_1(v_h__1_2022_, v___x_2024_);
return v___x_2025_;
}
else
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_dec(v_h__1_2022_);
v___x_2026_ = lean_box(v_x_2021_);
v___x_2027_ = lean_apply_2(v_h__2_2023_, v___x_2026_, lean_box(0));
return v___x_2027_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2021_ = stack[0].m_num;
lean_object* v_h__1_2022_ = stack[1].m_obj;
lean_object* v_h__2_2023_ = stack[2].m_obj;
lean_object* v_res_2028_;
v_res_2028_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(v_x_2021_, v_h__1_2022_, v_h__2_2023_);
stack->m_obj
 = v_res_2028_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg___boxed(lean_object* v_x_2029_, lean_object* v_h__1_2030_, lean_object* v_h__2_2031_){
_start:
{
uint8_t v_x_13__boxed_2032_; lean_object* v_res_2033_; 
v_x_13__boxed_2032_ = lean_unbox(v_x_2029_);
v_res_2033_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(v_x_13__boxed_2032_, v_h__1_2030_, v_h__2_2031_);
return v_res_2033_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(lean_object* v_motive_2034_, uint8_t v_x_2035_, lean_object* v_h__1_2036_, lean_object* v_h__2_2037_){
_start:
{
if (v_x_2035_ == 2)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec(v_h__2_2037_);
v___x_2038_ = lean_box(0);
v___x_2039_ = lean_apply_1(v_h__1_2036_, v___x_2038_);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
lean_dec(v_h__1_2036_);
v___x_2040_ = lean_box(v_x_2035_);
v___x_2041_ = lean_apply_2(v_h__2_2037_, v___x_2040_, lean_box(0));
return v___x_2041_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2035_ = stack[1].m_num;
lean_object* v_h__1_2036_ = stack[2].m_obj;
lean_object* v_h__2_2037_ = stack[3].m_obj;
lean_object* v_res_2042_;
v_res_2042_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(lean_box(0), v_x_2035_, v_h__1_2036_, v_h__2_2037_);
stack->m_obj
 = v_res_2042_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___boxed(lean_object* v_motive_2043_, lean_object* v_x_2044_, lean_object* v_h__1_2045_, lean_object* v_h__2_2046_){
_start:
{
uint8_t v_x_30__boxed_2047_; lean_object* v_res_2048_; 
v_x_30__boxed_2047_ = lean_unbox(v_x_2044_);
v_res_2048_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(v_motive_2043_, v_x_30__boxed_2047_, v_h__1_2045_, v_h__2_2046_);
return v_res_2048_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(uint8_t v_x_2049_, lean_object* v_h__1_2050_, lean_object* v_h__2_2051_, lean_object* v_h__3_2052_){
_start:
{
switch(v_x_2049_)
{
case 0:
{
lean_object* v___x_2053_; 
lean_dec(v_h__2_2051_);
lean_dec(v_h__1_2050_);
v___x_2053_ = lean_apply_1(v_h__3_2052_, lean_box(0));
return v___x_2053_;
}
case 1:
{
lean_object* v___x_2054_; 
lean_dec(v_h__3_2052_);
lean_dec(v_h__1_2050_);
v___x_2054_ = lean_apply_1(v_h__2_2051_, lean_box(0));
return v___x_2054_;
}
default: 
{
lean_object* v___x_2055_; 
lean_dec(v_h__3_2052_);
lean_dec(v_h__2_2051_);
v___x_2055_ = lean_apply_1(v_h__1_2050_, lean_box(0));
return v___x_2055_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2049_ = stack[0].m_num;
lean_object* v_h__1_2050_ = stack[1].m_obj;
lean_object* v_h__2_2051_ = stack[2].m_obj;
lean_object* v_h__3_2052_ = stack[3].m_obj;
lean_object* v_res_2056_;
v_res_2056_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(v_x_2049_, v_h__1_2050_, v_h__2_2051_, v_h__3_2052_);
stack->m_obj
 = v_res_2056_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg___boxed(lean_object* v_x_2057_, lean_object* v_h__1_2058_, lean_object* v_h__2_2059_, lean_object* v_h__3_2060_){
_start:
{
uint8_t v_x_33__boxed_2061_; lean_object* v_res_2062_; 
v_x_33__boxed_2061_ = lean_unbox(v_x_2057_);
v_res_2062_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(v_x_33__boxed_2061_, v_h__1_2058_, v_h__2_2059_, v_h__3_2060_);
return v_res_2062_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(lean_object* v_motive_2063_, uint8_t v_x_2064_, lean_object* v_h__1_2065_, lean_object* v_h__2_2066_, lean_object* v_h__3_2067_){
_start:
{
switch(v_x_2064_)
{
case 0:
{
lean_object* v___x_2068_; 
lean_dec(v_h__2_2066_);
lean_dec(v_h__1_2065_);
v___x_2068_ = lean_apply_1(v_h__3_2067_, lean_box(0));
return v___x_2068_;
}
case 1:
{
lean_object* v___x_2069_; 
lean_dec(v_h__3_2067_);
lean_dec(v_h__1_2065_);
v___x_2069_ = lean_apply_1(v_h__2_2066_, lean_box(0));
return v___x_2069_;
}
default: 
{
lean_object* v___x_2070_; 
lean_dec(v_h__3_2067_);
lean_dec(v_h__2_2066_);
v___x_2070_ = lean_apply_1(v_h__1_2065_, lean_box(0));
return v___x_2070_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2064_ = stack[1].m_num;
lean_object* v_h__1_2065_ = stack[2].m_obj;
lean_object* v_h__2_2066_ = stack[3].m_obj;
lean_object* v_h__3_2067_ = stack[4].m_obj;
lean_object* v_res_2071_;
v_res_2071_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(lean_box(0), v_x_2064_, v_h__1_2065_, v_h__2_2066_, v_h__3_2067_);
stack->m_obj
 = v_res_2071_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___boxed(lean_object* v_motive_2072_, lean_object* v_x_2073_, lean_object* v_h__1_2074_, lean_object* v_h__2_2075_, lean_object* v_h__3_2076_){
_start:
{
uint8_t v_x_47__boxed_2077_; lean_object* v_res_2078_; 
v_x_47__boxed_2077_ = lean_unbox(v_x_2073_);
v_res_2078_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(v_motive_2072_, v_x_47__boxed_2077_, v_h__1_2074_, v_h__2_2075_, v_h__3_2076_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(lean_object* v_x_2079_, lean_object* v_x_2080_, lean_object* v_h__1_2081_, lean_object* v_h__2_2082_){
_start:
{
if (lean_obj_tag(v_x_2079_) == 0)
{
lean_object* v_size_2083_; lean_object* v_k_2084_; lean_object* v_v_2085_; lean_object* v_l_2086_; lean_object* v_r_2087_; lean_object* v___x_2088_; 
lean_dec(v_h__1_2081_);
v_size_2083_ = lean_ctor_get(v_x_2079_, 0);
lean_inc(v_size_2083_);
v_k_2084_ = lean_ctor_get(v_x_2079_, 1);
lean_inc(v_k_2084_);
v_v_2085_ = lean_ctor_get(v_x_2079_, 2);
lean_inc(v_v_2085_);
v_l_2086_ = lean_ctor_get(v_x_2079_, 3);
lean_inc(v_l_2086_);
v_r_2087_ = lean_ctor_get(v_x_2079_, 4);
lean_inc(v_r_2087_);
lean_dec_ref_known(v_x_2079_, 5);
v___x_2088_ = lean_apply_6(v_h__2_2082_, v_size_2083_, v_k_2084_, v_v_2085_, v_l_2086_, v_r_2087_, v_x_2080_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; 
lean_dec(v_h__2_2082_);
v___x_2089_ = lean_apply_1(v_h__1_2081_, v_x_2080_);
return v___x_2089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter(lean_object* v_00_u03b1_2090_, lean_object* v_00_u03b2_2091_, lean_object* v_motive_2092_, lean_object* v_x_2093_, lean_object* v_x_2094_, lean_object* v_h__1_2095_, lean_object* v_h__2_2096_){
_start:
{
if (lean_obj_tag(v_x_2093_) == 0)
{
lean_object* v_size_2097_; lean_object* v_k_2098_; lean_object* v_v_2099_; lean_object* v_l_2100_; lean_object* v_r_2101_; lean_object* v___x_2102_; 
lean_dec(v_h__1_2095_);
v_size_2097_ = lean_ctor_get(v_x_2093_, 0);
lean_inc(v_size_2097_);
v_k_2098_ = lean_ctor_get(v_x_2093_, 1);
lean_inc(v_k_2098_);
v_v_2099_ = lean_ctor_get(v_x_2093_, 2);
lean_inc(v_v_2099_);
v_l_2100_ = lean_ctor_get(v_x_2093_, 3);
lean_inc(v_l_2100_);
v_r_2101_ = lean_ctor_get(v_x_2093_, 4);
lean_inc(v_r_2101_);
lean_dec_ref_known(v_x_2093_, 5);
v___x_2102_ = lean_apply_6(v_h__2_2096_, v_size_2097_, v_k_2098_, v_v_2099_, v_l_2100_, v_r_2101_, v_x_2094_);
return v___x_2102_;
}
else
{
lean_object* v___x_2103_; 
lean_dec(v_h__2_2096_);
v___x_2103_ = lean_apply_1(v_h__1_2095_, v_x_2094_);
return v___x_2103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(lean_object* v_x_2104_, lean_object* v_x_2105_, lean_object* v_h__1_2106_){
_start:
{
lean_object* v_size_2107_; lean_object* v_k_2108_; lean_object* v_v_2109_; lean_object* v_l_2110_; lean_object* v_r_2111_; lean_object* v___x_2112_; 
v_size_2107_ = lean_ctor_get(v_x_2104_, 0);
lean_inc(v_size_2107_);
v_k_2108_ = lean_ctor_get(v_x_2104_, 1);
lean_inc(v_k_2108_);
v_v_2109_ = lean_ctor_get(v_x_2104_, 2);
lean_inc(v_v_2109_);
v_l_2110_ = lean_ctor_get(v_x_2104_, 3);
lean_inc(v_l_2110_);
v_r_2111_ = lean_ctor_get(v_x_2104_, 4);
lean_inc(v_r_2111_);
lean_dec(v_x_2104_);
v___x_2112_ = lean_apply_8(v_h__1_2106_, v_size_2107_, v_k_2108_, v_v_2109_, v_l_2110_, v_r_2111_, lean_box(0), v_x_2105_, lean_box(0));
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter(lean_object* v_00_u03b1_2113_, lean_object* v_00_u03b2_2114_, lean_object* v_motive_2115_, lean_object* v_x_2116_, lean_object* v_x_2117_, lean_object* v_x_2118_, lean_object* v_x_2119_, lean_object* v_h__1_2120_){
_start:
{
lean_object* v_size_2121_; lean_object* v_k_2122_; lean_object* v_v_2123_; lean_object* v_l_2124_; lean_object* v_r_2125_; lean_object* v___x_2126_; 
v_size_2121_ = lean_ctor_get(v_x_2116_, 0);
lean_inc(v_size_2121_);
v_k_2122_ = lean_ctor_get(v_x_2116_, 1);
lean_inc(v_k_2122_);
v_v_2123_ = lean_ctor_get(v_x_2116_, 2);
lean_inc(v_v_2123_);
v_l_2124_ = lean_ctor_get(v_x_2116_, 3);
lean_inc(v_l_2124_);
v_r_2125_ = lean_ctor_get(v_x_2116_, 4);
lean_inc(v_r_2125_);
lean_dec(v_x_2116_);
v___x_2126_ = lean_apply_8(v_h__1_2120_, v_size_2121_, v_k_2122_, v_v_2123_, v_l_2124_, v_r_2125_, lean_box(0), v_x_2118_, lean_box(0));
return v___x_2126_;
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
