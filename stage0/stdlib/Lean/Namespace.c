// Lean compiler output
// Module: Lean.Namespace
// Imports: public import Lean.EnvExtension
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
extern lean_object* l_Lean_NameSSet_instInhabited;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_initFn___lam__2___closed__0_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__2___closed__0_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___lam__2___closed__1_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__2___closed__1_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__1_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__2_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__2_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__4_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namespacesExt"};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 94, 96, 124, 50, 240, 248, 210)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_namespacesExt;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_isNamespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_isNamespace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getNamespaceSet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__3___redArg(lean_object* v_m_1_){
_start:
{
uint8_t v_stage_u2081_2_; 
v_stage_u2081_2_ = lean_ctor_get_uint8(v_m_1_, sizeof(void*)*2);
if (v_stage_u2081_2_ == 0)
{
return v_m_1_;
}
else
{
lean_object* v_map_u2081_3_; lean_object* v_map_u2082_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_12_; 
v_map_u2081_3_ = lean_ctor_get(v_m_1_, 0);
v_map_u2082_4_ = lean_ctor_get(v_m_1_, 1);
v_isSharedCheck_12_ = !lean_is_exclusive(v_m_1_);
if (v_isSharedCheck_12_ == 0)
{
v___x_6_ = v_m_1_;
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_map_u2082_4_);
lean_inc(v_map_u2081_3_);
lean_dec(v_m_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
uint8_t v___x_8_; lean_object* v___x_10_; 
v___x_8_ = 0;
if (v_isShared_7_ == 0)
{
v___x_10_ = v___x_6_;
goto v_reusejp_9_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_11_, 0, v_map_u2081_3_);
lean_ctor_set(v_reuseFailAlloc_11_, 1, v_map_u2082_4_);
v___x_10_ = v_reuseFailAlloc_11_;
goto v_reusejp_9_;
}
v_reusejp_9_:
{
lean_ctor_set_uint8(v___x_10_, sizeof(void*)*2, v___x_8_);
return v___x_10_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_13_, lean_object* v_m_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__3___redArg(v_m_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_(lean_object* v_es_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_array_mk(v_es_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__12___redArg(lean_object* v_x_18_, lean_object* v_x_19_, lean_object* v_x_20_, lean_object* v_x_21_){
_start:
{
lean_object* v_ks_22_; lean_object* v_vs_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_47_; 
v_ks_22_ = lean_ctor_get(v_x_18_, 0);
v_vs_23_ = lean_ctor_get(v_x_18_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v_x_18_);
if (v_isSharedCheck_47_ == 0)
{
v___x_25_ = v_x_18_;
v_isShared_26_ = v_isSharedCheck_47_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_vs_23_);
lean_inc(v_ks_22_);
lean_dec(v_x_18_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_47_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_27_ = lean_array_get_size(v_ks_22_);
v___x_28_ = lean_nat_dec_lt(v_x_19_, v___x_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_32_; 
lean_dec(v_x_19_);
v___x_29_ = lean_array_push(v_ks_22_, v_x_20_);
v___x_30_ = lean_array_push(v_vs_23_, v_x_21_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 1, v___x_30_);
lean_ctor_set(v___x_25_, 0, v___x_29_);
v___x_32_ = v___x_25_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v___x_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
else
{
lean_object* v_k_x27_34_; uint8_t v___x_35_; 
v_k_x27_34_ = lean_array_fget_borrowed(v_ks_22_, v_x_19_);
v___x_35_ = lean_name_eq(v_x_20_, v_k_x27_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_37_; 
if (v_isShared_26_ == 0)
{
v___x_37_ = v___x_25_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_ks_22_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v_vs_23_);
v___x_37_ = v_reuseFailAlloc_41_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = lean_nat_add(v_x_19_, v___x_38_);
lean_dec(v_x_19_);
v_x_18_ = v___x_37_;
v_x_19_ = v___x_39_;
goto _start;
}
}
else
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_45_; 
v___x_42_ = lean_array_fset(v_ks_22_, v_x_19_, v_x_20_);
v___x_43_ = lean_array_fset(v_vs_23_, v_x_19_, v_x_21_);
lean_dec(v_x_19_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 1, v___x_43_);
lean_ctor_set(v___x_25_, 0, v___x_42_);
v___x_45_ = v___x_25_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_42_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v___x_43_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_n_48_, lean_object* v_k_49_, lean_object* v_v_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_n_48_, v___x_51_, v_k_49_, v_v_50_);
return v___x_52_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_53_; uint64_t v___x_54_; 
v___x_53_ = lean_unsigned_to_nat(1723u);
v___x_54_ = lean_uint64_of_nat(v___x_53_);
return v___x_54_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_55_; size_t v___x_56_; size_t v___x_57_; 
v___x_55_ = ((size_t)5ULL);
v___x_56_ = ((size_t)1ULL);
v___x_57_ = lean_usize_shift_left(v___x_56_, v___x_55_);
return v___x_57_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_58_; size_t v___x_59_; size_t v___x_60_; 
v___x_58_ = ((size_t)1ULL);
v___x_59_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0);
v___x_60_ = lean_usize_sub(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_x_62_, size_t v_x_63_, size_t v_x_64_, lean_object* v_x_65_, lean_object* v_x_66_){
_start:
{
if (lean_obj_tag(v_x_62_) == 0)
{
lean_object* v_es_67_; size_t v___x_68_; size_t v___x_69_; size_t v___x_70_; size_t v___x_71_; lean_object* v_j_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v_es_67_ = lean_ctor_get(v_x_62_, 0);
v___x_68_ = ((size_t)5ULL);
v___x_69_ = ((size_t)1ULL);
v___x_70_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1);
v___x_71_ = lean_usize_land(v_x_63_, v___x_70_);
v_j_72_ = lean_usize_to_nat(v___x_71_);
v___x_73_ = lean_array_get_size(v_es_67_);
v___x_74_ = lean_nat_dec_lt(v_j_72_, v___x_73_);
if (v___x_74_ == 0)
{
lean_dec(v_j_72_);
lean_dec(v_x_66_);
lean_dec(v_x_65_);
return v_x_62_;
}
else
{
lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_111_; 
lean_inc_ref(v_es_67_);
v_isSharedCheck_111_ = !lean_is_exclusive(v_x_62_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; 
v_unused_112_ = lean_ctor_get(v_x_62_, 0);
lean_dec(v_unused_112_);
v___x_76_ = v_x_62_;
v_isShared_77_ = v_isSharedCheck_111_;
goto v_resetjp_75_;
}
else
{
lean_dec(v_x_62_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_111_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v_v_78_; lean_object* v___x_79_; lean_object* v_xs_x27_80_; lean_object* v___y_82_; 
v_v_78_ = lean_array_fget(v_es_67_, v_j_72_);
v___x_79_ = lean_box(0);
v_xs_x27_80_ = lean_array_fset(v_es_67_, v_j_72_, v___x_79_);
switch(lean_obj_tag(v_v_78_))
{
case 0:
{
lean_object* v_key_87_; lean_object* v_val_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_98_; 
v_key_87_ = lean_ctor_get(v_v_78_, 0);
v_val_88_ = lean_ctor_get(v_v_78_, 1);
v_isSharedCheck_98_ = !lean_is_exclusive(v_v_78_);
if (v_isSharedCheck_98_ == 0)
{
v___x_90_ = v_v_78_;
v_isShared_91_ = v_isSharedCheck_98_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_val_88_);
lean_inc(v_key_87_);
lean_dec(v_v_78_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_98_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
uint8_t v___x_92_; 
v___x_92_ = lean_name_eq(v_x_65_, v_key_87_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; 
lean_del_object(v___x_90_);
v___x_93_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_87_, v_val_88_, v_x_65_, v_x_66_);
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
v___y_82_ = v___x_94_;
goto v___jp_81_;
}
else
{
lean_object* v___x_96_; 
lean_dec(v_val_88_);
lean_dec(v_key_87_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v_x_66_);
lean_ctor_set(v___x_90_, 0, v_x_65_);
v___x_96_ = v___x_90_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_x_65_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_x_66_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
v___y_82_ = v___x_96_;
goto v___jp_81_;
}
}
}
}
case 1:
{
lean_object* v_node_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_109_; 
v_node_99_ = lean_ctor_get(v_v_78_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v_v_78_);
if (v_isSharedCheck_109_ == 0)
{
v___x_101_ = v_v_78_;
v_isShared_102_ = v_isSharedCheck_109_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_node_99_);
lean_dec(v_v_78_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_109_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
size_t v___x_103_; size_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_103_ = lean_usize_shift_right(v_x_63_, v___x_68_);
v___x_104_ = lean_usize_add(v_x_64_, v___x_69_);
v___x_105_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_node_99_, v___x_103_, v___x_104_, v_x_65_, v_x_66_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_105_);
v___x_107_ = v___x_101_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
v___y_82_ = v___x_107_;
goto v___jp_81_;
}
}
}
default: 
{
lean_object* v___x_110_; 
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v_x_65_);
lean_ctor_set(v___x_110_, 1, v_x_66_);
v___y_82_ = v___x_110_;
goto v___jp_81_;
}
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_83_ = lean_array_fset(v_xs_x27_80_, v_j_72_, v___y_82_);
lean_dec(v_j_72_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v___x_83_);
v___x_85_ = v___x_76_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
}
else
{
lean_object* v_ks_113_; lean_object* v_vs_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_134_; 
v_ks_113_ = lean_ctor_get(v_x_62_, 0);
v_vs_114_ = lean_ctor_get(v_x_62_, 1);
v_isSharedCheck_134_ = !lean_is_exclusive(v_x_62_);
if (v_isSharedCheck_134_ == 0)
{
v___x_116_ = v_x_62_;
v_isShared_117_ = v_isSharedCheck_134_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_vs_114_);
lean_inc(v_ks_113_);
lean_dec(v_x_62_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_134_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_ks_113_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_vs_114_);
v___x_119_ = v_reuseFailAlloc_133_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v_newNode_120_; uint8_t v___y_122_; size_t v___x_128_; uint8_t v___x_129_; 
v_newNode_120_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(v___x_119_, v_x_65_, v_x_66_);
v___x_128_ = ((size_t)7ULL);
v___x_129_ = lean_usize_dec_le(v___x_128_, v_x_64_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_130_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_120_);
v___x_131_ = lean_unsigned_to_nat(4u);
v___x_132_ = lean_nat_dec_lt(v___x_130_, v___x_131_);
lean_dec(v___x_130_);
v___y_122_ = v___x_132_;
goto v___jp_121_;
}
else
{
v___y_122_ = v___x_129_;
goto v___jp_121_;
}
v___jp_121_:
{
if (v___y_122_ == 0)
{
lean_object* v_ks_123_; lean_object* v_vs_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v_ks_123_ = lean_ctor_get(v_newNode_120_, 0);
lean_inc_ref(v_ks_123_);
v_vs_124_ = lean_ctor_get(v_newNode_120_, 1);
lean_inc_ref(v_vs_124_);
lean_dec_ref(v_newNode_120_);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2);
v___x_127_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_x_64_, v_ks_123_, v_vs_124_, v___x_125_, v___x_126_);
lean_dec_ref(v_vs_124_);
lean_dec_ref(v_ks_123_);
return v___x_127_;
}
else
{
return v_newNode_120_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(size_t v_depth_135_, lean_object* v_keys_136_, lean_object* v_vals_137_, lean_object* v_i_138_, lean_object* v_entries_139_){
_start:
{
lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_140_ = lean_array_get_size(v_keys_136_);
v___x_141_ = lean_nat_dec_lt(v_i_138_, v___x_140_);
if (v___x_141_ == 0)
{
lean_dec(v_i_138_);
return v_entries_139_;
}
else
{
lean_object* v_k_142_; lean_object* v_v_143_; uint64_t v___y_145_; 
v_k_142_ = lean_array_fget_borrowed(v_keys_136_, v_i_138_);
v_v_143_ = lean_array_fget_borrowed(v_vals_137_, v_i_138_);
if (lean_obj_tag(v_k_142_) == 0)
{
uint64_t v___x_156_; 
v___x_156_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0);
v___y_145_ = v___x_156_;
goto v___jp_144_;
}
else
{
uint64_t v_hash_157_; 
v_hash_157_ = lean_ctor_get_uint64(v_k_142_, sizeof(void*)*2);
v___y_145_ = v_hash_157_;
goto v___jp_144_;
}
v___jp_144_:
{
size_t v_h_146_; size_t v___x_147_; lean_object* v___x_148_; size_t v___x_149_; size_t v___x_150_; size_t v___x_151_; size_t v_h_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_h_146_ = lean_uint64_to_usize(v___y_145_);
v___x_147_ = ((size_t)5ULL);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = ((size_t)1ULL);
v___x_150_ = lean_usize_sub(v_depth_135_, v___x_149_);
v___x_151_ = lean_usize_mul(v___x_147_, v___x_150_);
v_h_152_ = lean_usize_shift_right(v_h_146_, v___x_151_);
v___x_153_ = lean_nat_add(v_i_138_, v___x_148_);
lean_dec(v_i_138_);
lean_inc(v_v_143_);
lean_inc(v_k_142_);
v___x_154_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_entries_139_, v_h_152_, v_depth_135_, v_k_142_, v_v_143_);
v_i_138_ = v___x_153_;
v_entries_139_ = v___x_154_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_depth_158_, lean_object* v_keys_159_, lean_object* v_vals_160_, lean_object* v_i_161_, lean_object* v_entries_162_){
_start:
{
size_t v_depth_boxed_163_; lean_object* v_res_164_; 
v_depth_boxed_163_ = lean_unbox_usize(v_depth_158_);
lean_dec(v_depth_158_);
v_res_164_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_depth_boxed_163_, v_keys_159_, v_vals_160_, v_i_161_, v_entries_162_);
lean_dec_ref(v_vals_160_);
lean_dec_ref(v_keys_159_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_165_, lean_object* v_x_166_, lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v_x_169_){
_start:
{
size_t v_x_1470__boxed_170_; size_t v_x_1471__boxed_171_; lean_object* v_res_172_; 
v_x_1470__boxed_170_ = lean_unbox_usize(v_x_166_);
lean_dec(v_x_166_);
v_x_1471__boxed_171_ = lean_unbox_usize(v_x_167_);
lean_dec(v_x_167_);
v_res_172_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_x_165_, v_x_1470__boxed_170_, v_x_1471__boxed_171_, v_x_168_, v_x_169_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_173_, lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
uint64_t v___y_177_; 
if (lean_obj_tag(v_x_174_) == 0)
{
uint64_t v___x_181_; 
v___x_181_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0);
v___y_177_ = v___x_181_;
goto v___jp_176_;
}
else
{
uint64_t v_hash_182_; 
v_hash_182_ = lean_ctor_get_uint64(v_x_174_, sizeof(void*)*2);
v___y_177_ = v_hash_182_;
goto v___jp_176_;
}
v___jp_176_:
{
size_t v___x_178_; size_t v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_uint64_to_usize(v___y_177_);
v___x_179_ = ((size_t)1ULL);
v___x_180_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_x_173_, v___x_178_, v___x_179_, v_x_174_, v_x_175_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__11___redArg(lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
return v_x_183_;
}
else
{
lean_object* v_key_185_; lean_object* v_value_186_; lean_object* v_tail_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_213_; 
v_key_185_ = lean_ctor_get(v_x_184_, 0);
v_value_186_ = lean_ctor_get(v_x_184_, 1);
v_tail_187_ = lean_ctor_get(v_x_184_, 2);
v_isSharedCheck_213_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_213_ == 0)
{
v___x_189_ = v_x_184_;
v_isShared_190_ = v_isSharedCheck_213_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_tail_187_);
lean_inc(v_value_186_);
lean_inc(v_key_185_);
lean_dec(v_x_184_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_213_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; uint64_t v___y_193_; 
v___x_191_ = lean_array_get_size(v_x_183_);
if (lean_obj_tag(v_key_185_) == 0)
{
uint64_t v___x_211_; 
v___x_211_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0);
v___y_193_ = v___x_211_;
goto v___jp_192_;
}
else
{
uint64_t v_hash_212_; 
v_hash_212_ = lean_ctor_get_uint64(v_key_185_, sizeof(void*)*2);
v___y_193_ = v_hash_212_;
goto v___jp_192_;
}
v___jp_192_:
{
uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v_fold_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v___x_199_; size_t v___x_200_; size_t v___x_201_; size_t v___x_202_; size_t v___x_203_; size_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_194_ = 32ULL;
v___x_195_ = lean_uint64_shift_right(v___y_193_, v___x_194_);
v_fold_196_ = lean_uint64_xor(v___y_193_, v___x_195_);
v___x_197_ = 16ULL;
v___x_198_ = lean_uint64_shift_right(v_fold_196_, v___x_197_);
v___x_199_ = lean_uint64_xor(v_fold_196_, v___x_198_);
v___x_200_ = lean_uint64_to_usize(v___x_199_);
v___x_201_ = lean_usize_of_nat(v___x_191_);
v___x_202_ = ((size_t)1ULL);
v___x_203_ = lean_usize_sub(v___x_201_, v___x_202_);
v___x_204_ = lean_usize_land(v___x_200_, v___x_203_);
v___x_205_ = lean_array_uget_borrowed(v_x_183_, v___x_204_);
lean_inc(v___x_205_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 2, v___x_205_);
v___x_207_ = v___x_189_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_key_185_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_value_186_);
lean_ctor_set(v_reuseFailAlloc_210_, 2, v___x_205_);
v___x_207_ = v_reuseFailAlloc_210_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; 
v___x_208_ = lean_array_uset(v_x_183_, v___x_204_, v___x_207_);
v_x_183_ = v___x_208_;
v_x_184_ = v_tail_187_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(lean_object* v_i_214_, lean_object* v_source_215_, lean_object* v_target_216_){
_start:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_array_get_size(v_source_215_);
v___x_218_ = lean_nat_dec_lt(v_i_214_, v___x_217_);
if (v___x_218_ == 0)
{
lean_dec_ref(v_source_215_);
lean_dec(v_i_214_);
return v_target_216_;
}
else
{
lean_object* v_es_219_; lean_object* v___x_220_; lean_object* v_source_221_; lean_object* v_target_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_es_219_ = lean_array_fget(v_source_215_, v_i_214_);
v___x_220_ = lean_box(0);
v_source_221_ = lean_array_fset(v_source_215_, v_i_214_, v___x_220_);
v_target_222_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__11___redArg(v_target_216_, v_es_219_);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_nat_add(v_i_214_, v___x_223_);
lean_dec(v_i_214_);
v_i_214_ = v___x_224_;
v_source_215_ = v_source_221_;
v_target_216_ = v_target_222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3___redArg(lean_object* v_data_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v_nbuckets_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_227_ = lean_array_get_size(v_data_226_);
v___x_228_ = lean_unsigned_to_nat(2u);
v_nbuckets_229_ = lean_nat_mul(v___x_227_, v___x_228_);
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_box(0);
v___x_232_ = lean_mk_array(v_nbuckets_229_, v___x_231_);
v___x_233_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(v___x_230_, v_data_226_, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__4___redArg(lean_object* v_a_234_, lean_object* v_b_235_, lean_object* v_x_236_){
_start:
{
if (lean_obj_tag(v_x_236_) == 0)
{
lean_dec(v_b_235_);
lean_dec(v_a_234_);
return v_x_236_;
}
else
{
lean_object* v_key_237_; lean_object* v_value_238_; lean_object* v_tail_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_251_; 
v_key_237_ = lean_ctor_get(v_x_236_, 0);
v_value_238_ = lean_ctor_get(v_x_236_, 1);
v_tail_239_ = lean_ctor_get(v_x_236_, 2);
v_isSharedCheck_251_ = !lean_is_exclusive(v_x_236_);
if (v_isSharedCheck_251_ == 0)
{
v___x_241_ = v_x_236_;
v_isShared_242_ = v_isSharedCheck_251_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_tail_239_);
lean_inc(v_value_238_);
lean_inc(v_key_237_);
lean_dec(v_x_236_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_251_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
uint8_t v___x_243_; 
v___x_243_ = lean_name_eq(v_key_237_, v_a_234_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_244_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__4___redArg(v_a_234_, v_b_235_, v_tail_239_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 2, v___x_244_);
v___x_246_ = v___x_241_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_key_237_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_value_238_);
lean_ctor_set(v_reuseFailAlloc_247_, 2, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
else
{
lean_object* v___x_249_; 
lean_dec(v_value_238_);
lean_dec(v_key_237_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v_b_235_);
lean_ctor_set(v___x_241_, 0, v_a_234_);
v___x_249_ = v___x_241_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_234_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_b_235_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_tail_239_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_a_252_, lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
uint8_t v___x_254_; 
v___x_254_ = 0;
return v___x_254_;
}
else
{
lean_object* v_key_255_; lean_object* v_tail_256_; uint8_t v___x_257_; 
v_key_255_ = lean_ctor_get(v_x_253_, 0);
v_tail_256_ = lean_ctor_get(v_x_253_, 2);
v___x_257_ = lean_name_eq(v_key_255_, v_a_252_);
if (v___x_257_ == 0)
{
v_x_253_ = v_tail_256_;
goto _start;
}
else
{
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_a_259_, lean_object* v_x_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__2___redArg(v_a_259_, v_x_260_);
lean_dec(v_x_260_);
lean_dec(v_a_259_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_263_, lean_object* v_a_264_, lean_object* v_b_265_){
_start:
{
lean_object* v_size_266_; lean_object* v_buckets_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_313_; 
v_size_266_ = lean_ctor_get(v_m_263_, 0);
v_buckets_267_ = lean_ctor_get(v_m_263_, 1);
v_isSharedCheck_313_ = !lean_is_exclusive(v_m_263_);
if (v_isSharedCheck_313_ == 0)
{
v___x_269_ = v_m_263_;
v_isShared_270_ = v_isSharedCheck_313_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_buckets_267_);
lean_inc(v_size_266_);
lean_dec(v_m_263_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_313_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; uint64_t v___y_273_; 
v___x_271_ = lean_array_get_size(v_buckets_267_);
if (lean_obj_tag(v_a_264_) == 0)
{
uint64_t v___x_311_; 
v___x_311_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0);
v___y_273_ = v___x_311_;
goto v___jp_272_;
}
else
{
uint64_t v_hash_312_; 
v_hash_312_ = lean_ctor_get_uint64(v_a_264_, sizeof(void*)*2);
v___y_273_ = v_hash_312_;
goto v___jp_272_;
}
v___jp_272_:
{
uint64_t v___x_274_; uint64_t v___x_275_; uint64_t v_fold_276_; uint64_t v___x_277_; uint64_t v___x_278_; uint64_t v___x_279_; size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; lean_object* v_bkt_285_; uint8_t v___x_286_; 
v___x_274_ = 32ULL;
v___x_275_ = lean_uint64_shift_right(v___y_273_, v___x_274_);
v_fold_276_ = lean_uint64_xor(v___y_273_, v___x_275_);
v___x_277_ = 16ULL;
v___x_278_ = lean_uint64_shift_right(v_fold_276_, v___x_277_);
v___x_279_ = lean_uint64_xor(v_fold_276_, v___x_278_);
v___x_280_ = lean_uint64_to_usize(v___x_279_);
v___x_281_ = lean_usize_of_nat(v___x_271_);
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_sub(v___x_281_, v___x_282_);
v___x_284_ = lean_usize_land(v___x_280_, v___x_283_);
v_bkt_285_ = lean_array_uget_borrowed(v_buckets_267_, v___x_284_);
v___x_286_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__2___redArg(v_a_264_, v_bkt_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v_size_x27_288_; lean_object* v___x_289_; lean_object* v_buckets_x27_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_287_ = lean_unsigned_to_nat(1u);
v_size_x27_288_ = lean_nat_add(v_size_266_, v___x_287_);
lean_dec(v_size_266_);
lean_inc(v_bkt_285_);
v___x_289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_289_, 0, v_a_264_);
lean_ctor_set(v___x_289_, 1, v_b_265_);
lean_ctor_set(v___x_289_, 2, v_bkt_285_);
v_buckets_x27_290_ = lean_array_uset(v_buckets_267_, v___x_284_, v___x_289_);
v___x_291_ = lean_unsigned_to_nat(4u);
v___x_292_ = lean_nat_mul(v_size_x27_288_, v___x_291_);
v___x_293_ = lean_unsigned_to_nat(3u);
v___x_294_ = lean_nat_div(v___x_292_, v___x_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_array_get_size(v_buckets_x27_290_);
v___x_296_ = lean_nat_dec_le(v___x_294_, v___x_295_);
lean_dec(v___x_294_);
if (v___x_296_ == 0)
{
lean_object* v_val_297_; lean_object* v___x_299_; 
v_val_297_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3___redArg(v_buckets_x27_290_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v_val_297_);
lean_ctor_set(v___x_269_, 0, v_size_x27_288_);
v___x_299_ = v___x_269_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_size_x27_288_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_val_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
else
{
lean_object* v___x_302_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v_buckets_x27_290_);
lean_ctor_set(v___x_269_, 0, v_size_x27_288_);
v___x_302_ = v___x_269_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_size_x27_288_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_buckets_x27_290_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
else
{
lean_object* v___x_304_; lean_object* v_buckets_x27_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
lean_inc(v_bkt_285_);
v___x_304_ = lean_box(0);
v_buckets_x27_305_ = lean_array_uset(v_buckets_267_, v___x_284_, v___x_304_);
v___x_306_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__4___redArg(v_a_264_, v_b_265_, v_bkt_285_);
v___x_307_ = lean_array_uset(v_buckets_x27_305_, v___x_284_, v___x_306_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_307_);
v___x_309_ = v___x_269_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_size_266_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
uint8_t v_stage_u2081_317_; 
v_stage_u2081_317_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*2);
if (v_stage_u2081_317_ == 0)
{
lean_object* v_map_u2081_318_; lean_object* v_map_u2082_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_327_; 
v_map_u2081_318_ = lean_ctor_get(v_x_314_, 0);
v_map_u2082_319_ = lean_ctor_get(v_x_314_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_x_314_);
if (v_isSharedCheck_327_ == 0)
{
v___x_321_ = v_x_314_;
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_map_u2082_319_);
lean_inc(v_map_u2081_318_);
lean_dec(v_x_314_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_u2082_319_, v_x_315_, v_x_316_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 1, v___x_323_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_map_u2081_318_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_323_);
lean_ctor_set_uint8(v_reuseFailAlloc_326_, sizeof(void*)*2, v_stage_u2081_317_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
else
{
lean_object* v_map_u2081_328_; lean_object* v_map_u2082_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_337_; 
v_map_u2081_328_ = lean_ctor_get(v_x_314_, 0);
v_map_u2082_329_ = lean_ctor_get(v_x_314_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_314_);
if (v_isSharedCheck_337_ == 0)
{
v___x_331_ = v_x_314_;
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_map_u2082_329_);
lean_inc(v_map_u2081_328_);
lean_dec(v_x_314_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1___redArg(v_map_u2081_328_, v_x_315_, v_x_316_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_333_);
v___x_335_ = v___x_331_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_map_u2082_329_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*2, v_stage_u2081_317_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_(lean_object* v_s_338_, lean_object* v_n_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_box(0);
v___x_341_ = l_Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0___redArg(v_s_338_, v_n_339_, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_as_342_, size_t v_i_343_, size_t v_stop_344_, lean_object* v_b_345_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = lean_usize_dec_eq(v_i_343_, v_stop_344_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; size_t v___x_350_; size_t v___x_351_; 
v___x_347_ = lean_array_uget_borrowed(v_as_342_, v_i_343_);
v___x_348_ = lean_box(0);
lean_inc(v___x_347_);
v___x_349_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1___redArg(v_b_345_, v___x_347_, v___x_348_);
v___x_350_ = ((size_t)1ULL);
v___x_351_ = lean_usize_add(v_i_343_, v___x_350_);
v_i_343_ = v___x_351_;
v_b_345_ = v___x_349_;
goto _start;
}
else
{
return v_b_345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_as_353_, lean_object* v_i_354_, lean_object* v_stop_355_, lean_object* v_b_356_){
_start:
{
size_t v_i_boxed_357_; size_t v_stop_boxed_358_; lean_object* v_res_359_; 
v_i_boxed_357_ = lean_unbox_usize(v_i_354_);
lean_dec(v_i_354_);
v_stop_boxed_358_ = lean_unbox_usize(v_stop_355_);
lean_dec(v_stop_355_);
v_res_359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2_spec__6(v_as_353_, v_i_boxed_357_, v_stop_boxed_358_, v_b_356_);
lean_dec_ref(v_as_353_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2_spec__7(lean_object* v_as_360_, size_t v_i_361_, size_t v_stop_362_, lean_object* v_b_363_){
_start:
{
lean_object* v___y_365_; uint8_t v___x_369_; 
v___x_369_ = lean_usize_dec_eq(v_i_361_, v_stop_362_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_370_ = lean_array_uget_borrowed(v_as_360_, v_i_361_);
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = lean_array_get_size(v___x_370_);
v___x_373_ = lean_nat_dec_lt(v___x_371_, v___x_372_);
if (v___x_373_ == 0)
{
v___y_365_ = v_b_363_;
goto v___jp_364_;
}
else
{
uint8_t v___x_374_; 
v___x_374_ = lean_nat_dec_le(v___x_372_, v___x_372_);
if (v___x_374_ == 0)
{
if (v___x_373_ == 0)
{
v___y_365_ = v_b_363_;
goto v___jp_364_;
}
else
{
size_t v___x_375_; size_t v___x_376_; lean_object* v___x_377_; 
v___x_375_ = ((size_t)0ULL);
v___x_376_ = lean_usize_of_nat(v___x_372_);
v___x_377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2_spec__6(v___x_370_, v___x_375_, v___x_376_, v_b_363_);
v___y_365_ = v___x_377_;
goto v___jp_364_;
}
}
else
{
size_t v___x_378_; size_t v___x_379_; lean_object* v___x_380_; 
v___x_378_ = ((size_t)0ULL);
v___x_379_ = lean_usize_of_nat(v___x_372_);
v___x_380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2_spec__6(v___x_370_, v___x_378_, v___x_379_, v_b_363_);
v___y_365_ = v___x_380_;
goto v___jp_364_;
}
}
}
else
{
return v_b_363_;
}
v___jp_364_:
{
size_t v___x_366_; size_t v___x_367_; 
v___x_366_ = ((size_t)1ULL);
v___x_367_ = lean_usize_add(v_i_361_, v___x_366_);
v_i_361_ = v___x_367_;
v_b_363_ = v___y_365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2_spec__7___boxed(lean_object* v_as_381_, lean_object* v_i_382_, lean_object* v_stop_383_, lean_object* v_b_384_){
_start:
{
size_t v_i_boxed_385_; size_t v_stop_boxed_386_; lean_object* v_res_387_; 
v_i_boxed_385_ = lean_unbox_usize(v_i_382_);
lean_dec(v_i_382_);
v_stop_boxed_386_ = lean_unbox_usize(v_stop_383_);
lean_dec(v_stop_383_);
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2_spec__7(v_as_381_, v_i_boxed_385_, v_stop_boxed_386_, v_b_384_);
lean_dec_ref(v_as_381_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2(lean_object* v_initState_388_, lean_object* v_as_389_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_array_get_size(v_as_389_);
v___x_392_ = lean_nat_dec_lt(v___x_390_, v___x_391_);
if (v___x_392_ == 0)
{
return v_initState_388_;
}
else
{
uint8_t v___x_393_; 
v___x_393_ = lean_nat_dec_le(v___x_391_, v___x_391_);
if (v___x_393_ == 0)
{
if (v___x_392_ == 0)
{
return v_initState_388_;
}
else
{
size_t v___x_394_; size_t v___x_395_; lean_object* v___x_396_; 
v___x_394_ = ((size_t)0ULL);
v___x_395_ = lean_usize_of_nat(v___x_391_);
v___x_396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2_spec__7(v_as_389_, v___x_394_, v___x_395_, v_initState_388_);
return v___x_396_;
}
}
else
{
size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_397_ = ((size_t)0ULL);
v___x_398_ = lean_usize_of_nat(v___x_391_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2_spec__7(v_as_389_, v___x_397_, v___x_398_, v_initState_388_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2___boxed(lean_object* v_initState_400_, lean_object* v_as_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2(v_initState_400_, v_as_401_);
lean_dec_ref(v_as_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__4(lean_object* v_as_403_, size_t v_i_404_, size_t v_stop_405_, lean_object* v_b_406_){
_start:
{
uint8_t v___x_407_; 
v___x_407_ = lean_usize_dec_eq(v_i_404_, v_stop_405_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; size_t v___x_411_; size_t v___x_412_; 
v___x_408_ = lean_array_uget_borrowed(v_as_403_, v_i_404_);
v___x_409_ = lean_array_get_size(v___x_408_);
v___x_410_ = lean_nat_add(v_b_406_, v___x_409_);
lean_dec(v_b_406_);
v___x_411_ = ((size_t)1ULL);
v___x_412_ = lean_usize_add(v_i_404_, v___x_411_);
v_i_404_ = v___x_412_;
v_b_406_ = v___x_410_;
goto _start;
}
else
{
return v_b_406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__4___boxed(lean_object* v_as_414_, lean_object* v_i_415_, lean_object* v_stop_416_, lean_object* v_b_417_){
_start:
{
size_t v_i_boxed_418_; size_t v_stop_boxed_419_; lean_object* v_res_420_; 
v_i_boxed_418_ = lean_unbox_usize(v_i_415_);
lean_dec(v_i_415_);
v_stop_boxed_419_ = lean_unbox_usize(v_stop_416_);
lean_dec(v_stop_416_);
v_res_420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__4(v_as_414_, v_i_boxed_418_, v_stop_boxed_419_, v_b_417_);
lean_dec_ref(v_as_414_);
return v_res_420_;
}
}
static lean_object* _init_l_Lean_initFn___lam__2___closed__0_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_421_;
}
}
static lean_object* _init_l_Lean_initFn___lam__2___closed__1_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l_Lean_initFn___lam__2___closed__0_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_, &l_Lean_initFn___lam__2___closed__0_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__2___closed__0_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_(lean_object* v_as_424_){
_start:
{
lean_object* v___y_426_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_array_get_size(v_as_424_);
v___x_443_ = lean_nat_dec_lt(v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
v___y_426_ = v___x_441_;
goto v___jp_425_;
}
else
{
uint8_t v___x_444_; 
v___x_444_ = lean_nat_dec_le(v___x_442_, v___x_442_);
if (v___x_444_ == 0)
{
if (v___x_443_ == 0)
{
v___y_426_ = v___x_441_;
goto v___jp_425_;
}
else
{
size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v___x_445_ = ((size_t)0ULL);
v___x_446_ = lean_usize_of_nat(v___x_442_);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__4(v_as_424_, v___x_445_, v___x_446_, v___x_441_);
v___y_426_ = v___x_447_;
goto v___jp_425_;
}
}
else
{
size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v___x_448_ = ((size_t)0ULL);
v___x_449_ = lean_usize_of_nat(v___x_442_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__4(v_as_424_, v___x_448_, v___x_449_, v___x_441_);
v___y_426_ = v___x_450_;
goto v___jp_425_;
}
}
v___jp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_map_435_; lean_object* v_map_436_; uint8_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_unsigned_to_nat(4u);
v___x_429_ = lean_nat_mul(v___y_426_, v___x_428_);
lean_dec(v___y_426_);
v___x_430_ = lean_unsigned_to_nat(3u);
v___x_431_ = lean_nat_div(v___x_429_, v___x_430_);
lean_dec(v___x_429_);
v___x_432_ = l_Nat_nextPowerOfTwo(v___x_431_);
lean_dec(v___x_431_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_mk_array(v___x_432_, v___x_433_);
v_map_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_map_435_, 0, v___x_427_);
lean_ctor_set(v_map_435_, 1, v___x_434_);
v_map_436_ = l_Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__2(v_map_435_, v_as_424_);
v___x_437_ = 1;
v___x_438_ = lean_obj_once(&l_Lean_initFn___lam__2___closed__1_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_, &l_Lean_initFn___lam__2___closed__1_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__2___closed__1_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_);
v___x_439_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_439_, 0, v_map_436_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
lean_ctor_set_uint8(v___x_439_, sizeof(void*)*2, v___x_437_);
v___x_440_ = l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__3___redArg(v___x_439_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2____boxed(lean_object* v_as_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_initFn___lam__2_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_(v_as_451_);
lean_dec_ref(v_as_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_));
v___x_470_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2____boxed(lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_();
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_473_, lean_object* v_x_474_, lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0___redArg(v_x_474_, v_x_475_, v_x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_478_, lean_object* v_m_479_, lean_object* v_a_480_, lean_object* v_b_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1___redArg(v_m_479_, v_a_480_, v_b_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_483_, lean_object* v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_484_, v_x_485_, v_x_486_);
return v___x_487_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b2_488_, lean_object* v_a_489_, lean_object* v_x_490_){
_start:
{
uint8_t v___x_491_; 
v___x_491_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__2___redArg(v_a_489_, v_x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b2_492_, lean_object* v_a_493_, lean_object* v_x_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b2_492_, v_a_493_, v_x_494_);
lean_dec(v_x_494_);
lean_dec(v_a_493_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_00_u03b2_497_, lean_object* v_data_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3___redArg(v_data_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_00_u03b2_500_, lean_object* v_a_501_, lean_object* v_b_502_, lean_object* v_x_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__4___redArg(v_a_501_, v_b_502_, v_x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_00_u03b2_505_, lean_object* v_x_506_, size_t v_x_507_, size_t v_x_508_, lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_x_506_, v_x_507_, v_x_508_, v_x_509_, v_x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_512_, lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
size_t v_x_2149__boxed_518_; size_t v_x_2150__boxed_519_; lean_object* v_res_520_; 
v_x_2149__boxed_518_ = lean_unbox_usize(v_x_514_);
lean_dec(v_x_514_);
v_x_2150__boxed_519_ = lean_unbox_usize(v_x_515_);
lean_dec(v_x_515_);
v_res_520_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b2_512_, v_x_513_, v_x_2149__boxed_518_, v_x_2150__boxed_519_, v_x_516_, v_x_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3_spec__6(lean_object* v_00_u03b2_521_, lean_object* v_i_522_, lean_object* v_source_523_, lean_object* v_target_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(v_i_522_, v_source_523_, v_target_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_526_, lean_object* v_n_527_, lean_object* v_k_528_, lean_object* v_v_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(v_n_527_, v_k_528_, v_v_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(lean_object* v_00_u03b2_531_, size_t v_depth_532_, lean_object* v_keys_533_, lean_object* v_vals_534_, lean_object* v_heq_535_, lean_object* v_i_536_, lean_object* v_entries_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_depth_532_, v_keys_533_, v_vals_534_, v_i_536_, v_entries_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_00_u03b2_539_, lean_object* v_depth_540_, lean_object* v_keys_541_, lean_object* v_vals_542_, lean_object* v_heq_543_, lean_object* v_i_544_, lean_object* v_entries_545_){
_start:
{
size_t v_depth_boxed_546_; lean_object* v_res_547_; 
v_depth_boxed_546_ = lean_unbox_usize(v_depth_540_);
lean_dec(v_depth_540_);
v_res_547_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(v_00_u03b2_539_, v_depth_boxed_546_, v_keys_541_, v_vals_542_, v_heq_543_, v_i_544_, v_entries_545_);
lean_dec_ref(v_vals_542_);
lean_dec_ref(v_keys_541_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__11(lean_object* v_00_u03b2_548_, lean_object* v_x_549_, lean_object* v_x_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__11___redArg(v_x_549_, v_x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_552_, lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_x_553_, v_x_554_, v_x_555_, v_x_556_);
return v___x_557_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__0___redArg(lean_object* v_m_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_buckets_560_; lean_object* v___x_561_; uint64_t v___y_563_; 
v_buckets_560_ = lean_ctor_get(v_m_558_, 1);
v___x_561_ = lean_array_get_size(v_buckets_560_);
if (lean_obj_tag(v_a_559_) == 0)
{
uint64_t v___x_577_; 
v___x_577_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0);
v___y_563_ = v___x_577_;
goto v___jp_562_;
}
else
{
uint64_t v_hash_578_; 
v_hash_578_ = lean_ctor_get_uint64(v_a_559_, sizeof(void*)*2);
v___y_563_ = v_hash_578_;
goto v___jp_562_;
}
v___jp_562_:
{
uint64_t v___x_564_; uint64_t v___x_565_; uint64_t v_fold_566_; uint64_t v___x_567_; uint64_t v___x_568_; uint64_t v___x_569_; size_t v___x_570_; size_t v___x_571_; size_t v___x_572_; size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_564_ = 32ULL;
v___x_565_ = lean_uint64_shift_right(v___y_563_, v___x_564_);
v_fold_566_ = lean_uint64_xor(v___y_563_, v___x_565_);
v___x_567_ = 16ULL;
v___x_568_ = lean_uint64_shift_right(v_fold_566_, v___x_567_);
v___x_569_ = lean_uint64_xor(v_fold_566_, v___x_568_);
v___x_570_ = lean_uint64_to_usize(v___x_569_);
v___x_571_ = lean_usize_of_nat(v___x_561_);
v___x_572_ = ((size_t)1ULL);
v___x_573_ = lean_usize_sub(v___x_571_, v___x_572_);
v___x_574_ = lean_usize_land(v___x_570_, v___x_573_);
v___x_575_ = lean_array_uget_borrowed(v_buckets_560_, v___x_574_);
v___x_576_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__1_spec__2___redArg(v_a_559_, v___x_575_);
return v___x_576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__0___redArg___boxed(lean_object* v_m_579_, lean_object* v_a_580_){
_start:
{
uint8_t v_res_581_; lean_object* v_r_582_; 
v_res_581_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__0___redArg(v_m_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_m_579_);
v_r_582_ = lean_box(v_res_581_);
return v_r_582_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_583_, lean_object* v_i_584_, lean_object* v_k_585_){
_start:
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_array_get_size(v_keys_583_);
v___x_587_ = lean_nat_dec_lt(v_i_584_, v___x_586_);
if (v___x_587_ == 0)
{
lean_dec(v_i_584_);
return v___x_587_;
}
else
{
lean_object* v_k_x27_588_; uint8_t v___x_589_; 
v_k_x27_588_ = lean_array_fget_borrowed(v_keys_583_, v_i_584_);
v___x_589_ = lean_name_eq(v_k_585_, v_k_x27_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_nat_add(v_i_584_, v___x_590_);
lean_dec(v_i_584_);
v_i_584_ = v___x_591_;
goto _start;
}
else
{
lean_dec(v_i_584_);
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_593_, lean_object* v_i_594_, lean_object* v_k_595_){
_start:
{
uint8_t v_res_596_; lean_object* v_r_597_; 
v_res_596_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_593_, v_i_594_, v_k_595_);
lean_dec(v_k_595_);
lean_dec_ref(v_keys_593_);
v_r_597_ = lean_box(v_res_596_);
return v_r_597_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2___redArg(lean_object* v_x_598_, size_t v_x_599_, lean_object* v_x_600_){
_start:
{
if (lean_obj_tag(v_x_598_) == 0)
{
lean_object* v_es_601_; lean_object* v___x_602_; size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; lean_object* v_j_606_; lean_object* v___x_607_; 
v_es_601_ = lean_ctor_get(v_x_598_, 0);
lean_inc_ref(v_es_601_);
lean_dec_ref(v_x_598_);
v___x_602_ = lean_box(2);
v___x_603_ = ((size_t)5ULL);
v___x_604_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1);
v___x_605_ = lean_usize_land(v_x_599_, v___x_604_);
v_j_606_ = lean_usize_to_nat(v___x_605_);
v___x_607_ = lean_array_get(v___x_602_, v_es_601_, v_j_606_);
lean_dec(v_j_606_);
lean_dec_ref(v_es_601_);
switch(lean_obj_tag(v___x_607_))
{
case 0:
{
lean_object* v_key_608_; uint8_t v___x_609_; 
v_key_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_key_608_);
lean_dec_ref(v___x_607_);
v___x_609_ = lean_name_eq(v_x_600_, v_key_608_);
lean_dec(v_key_608_);
return v___x_609_;
}
case 1:
{
lean_object* v_node_610_; size_t v___x_611_; 
v_node_610_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_node_610_);
lean_dec_ref(v___x_607_);
v___x_611_ = lean_usize_shift_right(v_x_599_, v___x_603_);
v_x_598_ = v_node_610_;
v_x_599_ = v___x_611_;
goto _start;
}
default: 
{
uint8_t v___x_613_; 
v___x_613_ = 0;
return v___x_613_;
}
}
}
else
{
lean_object* v_ks_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_ks_614_ = lean_ctor_get(v_x_598_, 0);
lean_inc_ref(v_ks_614_);
lean_dec_ref(v_x_598_);
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2_spec__3___redArg(v_ks_614_, v___x_615_, v_x_600_);
lean_dec_ref(v_ks_614_);
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
size_t v_x_284__boxed_620_; uint8_t v_res_621_; lean_object* v_r_622_; 
v_x_284__boxed_620_ = lean_unbox_usize(v_x_618_);
lean_dec(v_x_618_);
v_res_621_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2___redArg(v_x_617_, v_x_284__boxed_620_, v_x_619_);
lean_dec(v_x_619_);
v_r_622_ = lean_box(v_res_621_);
return v_r_622_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1___redArg(lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
uint64_t v___y_626_; 
if (lean_obj_tag(v_x_624_) == 0)
{
uint64_t v___x_629_; 
v___x_629_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___closed__0);
v___y_626_ = v___x_629_;
goto v___jp_625_;
}
else
{
uint64_t v_hash_630_; 
v_hash_630_ = lean_ctor_get_uint64(v_x_624_, sizeof(void*)*2);
v___y_626_ = v_hash_630_;
goto v___jp_625_;
}
v___jp_625_:
{
size_t v___x_627_; uint8_t v___x_628_; 
v___x_627_ = lean_uint64_to_usize(v___y_626_);
v___x_628_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2___redArg(v_x_623_, v___x_627_, v_x_624_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1___redArg___boxed(lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
uint8_t v_res_633_; lean_object* v_r_634_; 
v_res_633_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1___redArg(v_x_631_, v_x_632_);
lean_dec(v_x_632_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0___redArg(lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
uint8_t v_stage_u2081_637_; 
v_stage_u2081_637_ = lean_ctor_get_uint8(v_x_635_, sizeof(void*)*2);
if (v_stage_u2081_637_ == 0)
{
lean_object* v_map_u2081_638_; lean_object* v_map_u2082_639_; uint8_t v___x_640_; 
v_map_u2081_638_ = lean_ctor_get(v_x_635_, 0);
lean_inc_ref(v_map_u2081_638_);
v_map_u2082_639_ = lean_ctor_get(v_x_635_, 1);
lean_inc_ref(v_map_u2082_639_);
lean_dec_ref(v_x_635_);
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__0___redArg(v_map_u2081_638_, v_x_636_);
lean_dec_ref(v_map_u2081_638_);
if (v___x_640_ == 0)
{
uint8_t v___x_641_; 
v___x_641_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1___redArg(v_map_u2082_639_, v_x_636_);
return v___x_641_;
}
else
{
lean_dec_ref(v_map_u2082_639_);
return v___x_640_;
}
}
else
{
lean_object* v_map_u2081_642_; uint8_t v___x_643_; 
v_map_u2081_642_ = lean_ctor_get(v_x_635_, 0);
lean_inc_ref(v_map_u2081_642_);
lean_dec_ref(v_x_635_);
v___x_643_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__0___redArg(v_map_u2081_642_, v_x_636_);
lean_dec_ref(v_map_u2081_642_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0___redArg___boxed(lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
uint8_t v_res_646_; lean_object* v_r_647_; 
v_res_646_ = l_Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0___redArg(v_x_644_, v_x_645_);
lean_dec(v_x_645_);
v_r_647_ = lean_box(v_res_646_);
return v_r_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_registerNamespace(lean_object* v_env_648_, lean_object* v_n_649_){
_start:
{
lean_object* v___x_650_; lean_object* v_toEnvExtension_651_; lean_object* v_asyncMode_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_650_ = l_Lean_namespacesExt;
v_toEnvExtension_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc_ref(v_toEnvExtension_651_);
v_asyncMode_652_ = lean_ctor_get(v_toEnvExtension_651_, 2);
lean_inc(v_asyncMode_652_);
lean_dec_ref(v_toEnvExtension_651_);
v___x_653_ = l_Lean_NameSSet_instInhabited;
v___x_654_ = lean_box(0);
lean_inc_ref(v_env_648_);
v___x_655_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_653_, v___x_650_, v_env_648_, v_asyncMode_652_, v___x_654_);
v___x_656_ = l_Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0___redArg(v___x_655_, v_n_649_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_650_, v_env_648_, v_n_649_, v_asyncMode_652_, v___x_654_);
lean_dec(v_asyncMode_652_);
return v___x_657_;
}
else
{
lean_dec(v_asyncMode_652_);
lean_dec(v_n_649_);
return v_env_648_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0(lean_object* v_00_u03b2_658_, lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
uint8_t v___x_661_; 
v___x_661_ = l_Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0___redArg(v_x_659_, v_x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0___boxed(lean_object* v_00_u03b2_662_, lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l_Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0(v_00_u03b2_662_, v_x_663_, v_x_664_);
lean_dec(v_x_664_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__0(lean_object* v_00_u03b2_667_, lean_object* v_m_668_, lean_object* v_a_669_){
_start:
{
uint8_t v___x_670_; 
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__0___redArg(v_m_668_, v_a_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__0___boxed(lean_object* v_00_u03b2_671_, lean_object* v_m_672_, lean_object* v_a_673_){
_start:
{
uint8_t v_res_674_; lean_object* v_r_675_; 
v_res_674_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__0(v_00_u03b2_671_, v_m_672_, v_a_673_);
lean_dec(v_a_673_);
lean_dec_ref(v_m_672_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1(lean_object* v_00_u03b2_676_, lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
uint8_t v___x_679_; 
v___x_679_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1___redArg(v_x_677_, v_x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1___boxed(lean_object* v_00_u03b2_680_, lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
uint8_t v_res_683_; lean_object* v_r_684_; 
v_res_683_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1(v_00_u03b2_680_, v_x_681_, v_x_682_);
lean_dec(v_x_682_);
v_r_684_ = lean_box(v_res_683_);
return v_r_684_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_685_, lean_object* v_x_686_, size_t v_x_687_, lean_object* v_x_688_){
_start:
{
uint8_t v___x_689_; 
v___x_689_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2___redArg(v_x_686_, v_x_687_, v_x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_690_, lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
size_t v_x_396__boxed_694_; uint8_t v_res_695_; lean_object* v_r_696_; 
v_x_396__boxed_694_ = lean_unbox_usize(v_x_692_);
lean_dec(v_x_692_);
v_res_695_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2(v_00_u03b2_690_, v_x_691_, v_x_396__boxed_694_, v_x_693_);
lean_dec(v_x_693_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_697_, lean_object* v_keys_698_, lean_object* v_vals_699_, lean_object* v_heq_700_, lean_object* v_i_701_, lean_object* v_k_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_698_, v_i_701_, v_k_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_704_, lean_object* v_keys_705_, lean_object* v_vals_706_, lean_object* v_heq_707_, lean_object* v_i_708_, lean_object* v_k_709_){
_start:
{
uint8_t v_res_710_; lean_object* v_r_711_; 
v_res_710_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__2_spec__3(v_00_u03b2_704_, v_keys_705_, v_vals_706_, v_heq_707_, v_i_708_, v_k_709_);
lean_dec(v_k_709_);
lean_dec_ref(v_vals_706_);
lean_dec_ref(v_keys_705_);
v_r_711_ = lean_box(v_res_710_);
return v_r_711_;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_isNamespace(lean_object* v_env_712_, lean_object* v_n_713_){
_start:
{
lean_object* v___x_714_; lean_object* v_toEnvExtension_715_; lean_object* v_asyncMode_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_714_ = l_Lean_namespacesExt;
v_toEnvExtension_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc_ref(v_toEnvExtension_715_);
v_asyncMode_716_ = lean_ctor_get(v_toEnvExtension_715_, 2);
lean_inc(v_asyncMode_716_);
lean_dec_ref(v_toEnvExtension_715_);
v___x_717_ = l_Lean_NameSSet_instInhabited;
v___x_718_ = lean_box(0);
v___x_719_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_717_, v___x_714_, v_env_712_, v_asyncMode_716_, v___x_718_);
lean_dec(v_asyncMode_716_);
v___x_720_ = l_Lean_SMap_contains___at___00Lean_Environment_registerNamespace_spec__0___redArg(v___x_719_, v_n_713_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_isNamespace___boxed(lean_object* v_env_721_, lean_object* v_n_722_){
_start:
{
uint8_t v_res_723_; lean_object* v_r_724_; 
v_res_723_ = l_Lean_Environment_isNamespace(v_env_721_, v_n_722_);
lean_dec(v_n_722_);
v_r_724_ = lean_box(v_res_723_);
return v_r_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getNamespaceSet(lean_object* v_env_725_){
_start:
{
lean_object* v___x_726_; lean_object* v_toEnvExtension_727_; lean_object* v_asyncMode_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_726_ = l_Lean_namespacesExt;
v_toEnvExtension_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_toEnvExtension_727_);
v_asyncMode_728_ = lean_ctor_get(v_toEnvExtension_727_, 2);
lean_inc(v_asyncMode_728_);
lean_dec_ref(v_toEnvExtension_727_);
v___x_729_ = l_Lean_NameSSet_instInhabited;
v___x_730_ = lean_box(0);
v___x_731_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_729_, v___x_726_, v_env_725_, v_asyncMode_728_, v___x_730_);
lean_dec(v_asyncMode_728_);
return v___x_731_;
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Namespace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Namespace_3179752022____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_namespacesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_namespacesExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Namespace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Namespace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Namespace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Namespace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Namespace(builtin);
}
#ifdef __cplusplus
}
#endif
