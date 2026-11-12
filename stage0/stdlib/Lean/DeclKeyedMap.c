// Lean compiler output
// Module: Lean.DeclKeyedMap
// Imports: public import Lean.ResolveName import Init.Data.Array.QSort
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Except_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_imported_consts_find_mod_idx_cached(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_ImportedConsts_empty___redArg();
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Except_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_quickLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
uint8_t lean_is_reserved_name(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instKeyName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_instKeyName___closed__0 = (const lean_object*)&l_Lean_instKeyName___closed__0_value;
static const lean_closure_object l_Lean_instKeyName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_quickLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instKeyName___closed__1 = (const lean_object*)&l_Lean_instKeyName___closed__1_value;
static const lean_ctor_object l_Lean_instKeyName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instKeyName___closed__0_value),((lean_object*)&l_Lean_instKeyName___closed__1_value)}};
static const lean_object* l_Lean_instKeyName___closed__2 = (const lean_object*)&l_Lean_instKeyName___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instKeyName = (const lean_object*)&l_Lean_instKeyName___closed__2_value;
static lean_once_cell_t l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__0;
static const lean_array_object l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__1_value;
static lean_once_cell_t l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__2;
static lean_once_cell_t l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__3;
static lean_once_cell_t l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedImportedDeclKeyedMap_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedImportedDeclKeyedMap_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap_default(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap_default___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ImportedDeclKeyedMap_isOwned(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_isOwned___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___lam__1, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__0 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__0_value;
static const lean_closure_object l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__1 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__1_value;
static const lean_closure_object l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__2 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__2_value;
static const lean_closure_object l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__3 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__3_value;
static const lean_closure_object l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__4 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__4_value;
static const lean_closure_object l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__5 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__5_value;
static const lean_closure_object l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__6 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__6_value;
static const lean_closure_object l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__7 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__7_value;
static const lean_ctor_object l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__1_value),((lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__2_value)}};
static const lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__8 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__8_value;
static const lean_ctor_object l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__8_value),((lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__3_value),((lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__4_value),((lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__5_value),((lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__6_value)}};
static const lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__9 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__9_value;
static const lean_ctor_object l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__9_value),((lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__7_value)}};
static const lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__10 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__10_value;
static const lean_array_object l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__11 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__11_value;
static const lean_ctor_object l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__11_value),((lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__11_value)}};
static const lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__12 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_valAt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_valAt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_valAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_valAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_ImportedDeclKeyedMap_ofModules___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___closed__0 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_ofModules___redArg___closed__0_value;
static const lean_closure_object l_Lean_ImportedDeclKeyedMap_ofModules___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___closed__1 = (const lean_object*)&l_Lean_ImportedDeclKeyedMap_ofModules___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_find_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ImportedDeclKeyedMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ImportedDeclKeyedMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedDeclKeyedMap_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedDeclKeyedMap_default___redArg___closed__0;
static lean_once_cell_t l_Lean_instInhabitedDeclKeyedMap_default___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedDeclKeyedMap_default___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedDeclKeyedMap_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedDeclKeyedMap_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap_default(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap_default___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_DeclKeyedMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_DeclKeyedMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_foldM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_DeclKeyedMap_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_DeclKeyedMap_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_DeclKeyedMap_toList___redArg___closed__0 = (const lean_object*)&l_Lean_DeclKeyedMap_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_toList___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_DeclKeyedMap_isEmpty___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_DeclKeyedMap_isEmpty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_DeclKeyedMap_isEmpty___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___closed__0 = (const lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__0_value;
static const lean_closure_object l_Lean_DeclKeyedMap_isEmpty___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___closed__1 = (const lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__1_value;
static const lean_closure_object l_Lean_DeclKeyedMap_isEmpty___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___closed__2 = (const lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__2_value;
static const lean_closure_object l_Lean_DeclKeyedMap_isEmpty___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___closed__3 = (const lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__3_value;
static const lean_closure_object l_Lean_DeclKeyedMap_isEmpty___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___closed__4 = (const lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__4_value;
static const lean_closure_object l_Lean_DeclKeyedMap_isEmpty___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___closed__5 = (const lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__5_value;
static const lean_ctor_object l_Lean_DeclKeyedMap_isEmpty___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__5_value),((lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__1_value)}};
static const lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___closed__6 = (const lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__6_value;
static const lean_closure_object l_Lean_DeclKeyedMap_isEmpty___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_pure, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___closed__7 = (const lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__7_value;
static const lean_ctor_object l_Lean_DeclKeyedMap_isEmpty___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__6_value),((lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__7_value),((lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__2_value),((lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__3_value),((lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__4_value)}};
static const lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___closed__8 = (const lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__8_value;
static const lean_closure_object l_Lean_DeclKeyedMap_isEmpty___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_bind, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___closed__9 = (const lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__9_value;
static const lean_ctor_object l_Lean_DeclKeyedMap_isEmpty___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__8_value),((lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__9_value)}};
static const lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___closed__10 = (const lean_object*)&l_Lean_DeclKeyedMap_isEmpty___redArg___closed__10_value;
LEAN_EXPORT uint8_t l_Lean_DeclKeyedMap_isEmpty___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_DeclKeyedMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_ImportedConsts_empty___redArg();
return v___x_7_;
}
}
static lean_object* _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__2(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_10_;
}
}
static lean_object* _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__3(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_obj_once(&l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__2, &l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__2_once, _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__2);
v___x_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_13_ = lean_obj_once(&l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__3, &l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__3_once, _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__3);
v___x_14_ = ((lean_object*)(l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__1));
v___x_15_ = lean_obj_once(&l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__0, &l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__0_once, _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__0);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
lean_ctor_set(v___x_16_, 2, v___x_14_);
lean_ctor_set(v___x_16_, 3, v___x_13_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg(){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_obj_once(&l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__4, &l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__4_once, _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__4);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___boxed(lean_object* v___dummy_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg();
return v_res_20_;
}
}
static lean_object* _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___closed__0(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg();
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap_default(lean_object* v_00_u03ba_22_, lean_object* v_00_u03b1_23_, lean_object* v_inst_24_, lean_object* v_inst_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_obj_once(&l_Lean_instInhabitedImportedDeclKeyedMap_default___closed__0, &l_Lean_instInhabitedImportedDeclKeyedMap_default___closed__0_once, _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___closed__0);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap_default___boxed(lean_object* v_00_u03ba_27_, lean_object* v_00_u03b1_28_, lean_object* v_inst_29_, lean_object* v_inst_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_instInhabitedImportedDeclKeyedMap_default(v_00_u03ba_27_, v_00_u03b1_28_, v_inst_29_, v_inst_30_);
lean_dec_ref(v_inst_30_);
lean_dec_ref(v_inst_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap___redArg(){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_obj_once(&l_Lean_instInhabitedImportedDeclKeyedMap_default___closed__0, &l_Lean_instInhabitedImportedDeclKeyedMap_default___closed__0_once, _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___closed__0);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap___redArg___boxed(lean_object* v___dummy_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_instInhabitedImportedDeclKeyedMap___redArg();
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap(lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Lean_instInhabitedImportedDeclKeyedMap_default___closed__0, &l_Lean_instInhabitedImportedDeclKeyedMap_default___closed__0_once, _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___closed__0);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedImportedDeclKeyedMap___boxed(lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_instInhabitedImportedDeclKeyedMap(v_a_41_, v_a_42_, v_a_43_, v_a_44_);
lean_dec_ref(v_a_44_);
lean_dec_ref(v_a_43_);
return v_res_45_;
}
}
LEAN_EXPORT uint8_t l_Lean_ImportedDeclKeyedMap_isOwned(lean_object* v_env_46_, lean_object* v_n_47_){
_start:
{
uint8_t v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = 0;
lean_inc_ref(v_env_46_);
v___x_49_ = l_Lean_Environment_setExporting(v_env_46_, v___x_48_);
v___x_50_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_49_, v_n_47_);
lean_dec_ref(v___x_49_);
if (lean_obj_tag(v___x_50_) == 0)
{
uint8_t v___x_51_; 
v___x_51_ = lean_is_reserved_name(v_env_46_, v_n_47_);
if (v___x_51_ == 0)
{
uint8_t v___x_52_; 
v___x_52_ = 1;
return v___x_52_;
}
else
{
return v___x_48_;
}
}
else
{
lean_dec_ref_known(v___x_50_, 1);
lean_dec(v_n_47_);
lean_dec_ref(v_env_46_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_isOwned___boxed(lean_object* v_env_53_, lean_object* v_n_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l_Lean_ImportedDeclKeyedMap_isOwned(v_env_53_, v_n_54_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___lam__0(lean_object* v_inst_57_, lean_object* v_x1_58_, lean_object* v_x2_59_){
_start:
{
lean_object* v_snd_60_; lean_object* v_fst_61_; lean_object* v_snd_62_; lean_object* v_fst_63_; lean_object* v_snd_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_81_; 
v_snd_60_ = lean_ctor_get(v_x2_59_, 1);
lean_inc(v_snd_60_);
lean_dec_ref(v_x2_59_);
v_fst_61_ = lean_ctor_get(v_x1_58_, 0);
v_snd_62_ = lean_ctor_get(v_x1_58_, 1);
v_fst_63_ = lean_ctor_get(v_snd_60_, 0);
v_snd_64_ = lean_ctor_get(v_snd_60_, 1);
v_isSharedCheck_81_ = !lean_is_exclusive(v_snd_60_);
if (v_isSharedCheck_81_ == 0)
{
v___x_66_ = v_snd_60_;
v_isShared_67_ = v_isSharedCheck_81_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_snd_64_);
lean_inc(v_fst_63_);
lean_dec(v_snd_60_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_81_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_74_ = lean_array_get_size(v_fst_61_);
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_sub(v___x_74_, v___x_75_);
v___x_77_ = lean_nat_dec_lt(v___x_76_, v___x_74_);
if (v___x_77_ == 0)
{
lean_inc(v_snd_62_);
lean_inc(v_fst_61_);
lean_dec(v___x_76_);
lean_dec_ref(v_x1_58_);
lean_dec_ref(v_inst_57_);
goto v___jp_68_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_78_ = lean_array_fget_borrowed(v_fst_61_, v___x_76_);
lean_dec(v___x_76_);
lean_inc(v_fst_63_);
lean_inc(v___x_78_);
v___x_79_ = lean_apply_2(v_inst_57_, v___x_78_, v_fst_63_);
v___x_80_ = lean_unbox(v___x_79_);
if (v___x_80_ == 0)
{
lean_inc(v_snd_62_);
lean_inc(v_fst_61_);
lean_dec_ref(v_x1_58_);
goto v___jp_68_;
}
else
{
lean_del_object(v___x_66_);
lean_dec(v_snd_64_);
lean_dec(v_fst_63_);
return v_x1_58_;
}
}
v___jp_68_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_69_ = lean_array_push(v_fst_61_, v_fst_63_);
v___x_70_ = lean_array_push(v_snd_62_, v_snd_64_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_70_);
lean_ctor_set(v___x_66_, 0, v___x_69_);
v___x_72_ = v___x_66_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_69_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___lam__1(lean_object* v_i_82_, lean_object* v_a_83_, lean_object* v_x_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v_i_82_);
lean_ctor_set(v___x_85_, 1, v_a_83_);
return v___x_85_;
}
}
LEAN_EXPORT uint8_t l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___lam__2(lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
lean_object* v_snd_90_; lean_object* v_snd_91_; lean_object* v_fst_92_; lean_object* v_fst_93_; lean_object* v_fst_94_; lean_object* v_fst_95_; lean_object* v_lt_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v_snd_90_ = lean_ctor_get(v_x_88_, 1);
lean_inc(v_snd_90_);
v_snd_91_ = lean_ctor_get(v_x_89_, 1);
lean_inc(v_snd_91_);
v_fst_92_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_fst_92_);
lean_dec_ref(v_x_88_);
v_fst_93_ = lean_ctor_get(v_snd_90_, 0);
lean_inc_n(v_fst_93_, 2);
lean_dec(v_snd_90_);
v_fst_94_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_fst_94_);
lean_dec_ref(v_x_89_);
v_fst_95_ = lean_ctor_get(v_snd_91_, 0);
lean_inc_n(v_fst_95_, 2);
lean_dec(v_snd_91_);
v_lt_96_ = lean_ctor_get(v_inst_86_, 1);
lean_inc_ref(v_lt_96_);
lean_dec_ref(v_inst_86_);
v___x_97_ = lean_apply_2(v_lt_96_, v_fst_93_, v_fst_95_);
v___x_98_ = lean_unbox(v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_apply_2(v_inst_87_, v_fst_93_, v_fst_95_);
v___x_100_ = lean_unbox(v___x_99_);
if (v___x_100_ == 0)
{
uint8_t v___x_101_; 
lean_dec(v_fst_94_);
lean_dec(v_fst_92_);
v___x_101_ = lean_unbox(v___x_99_);
return v___x_101_;
}
else
{
uint8_t v___x_102_; 
v___x_102_ = lean_nat_dec_lt(v_fst_94_, v_fst_92_);
lean_dec(v_fst_92_);
lean_dec(v_fst_94_);
return v___x_102_;
}
}
else
{
uint8_t v___x_103_; 
lean_dec(v_fst_95_);
lean_dec(v_fst_94_);
lean_dec(v_fst_93_);
lean_dec(v_fst_92_);
lean_dec_ref(v_inst_87_);
v___x_103_ = lean_unbox(v___x_97_);
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___lam__2___boxed(lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___lam__2(v_inst_104_, v_inst_105_, v_x_106_, v_x_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned___redArg(lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_es_136_){
_start:
{
lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; size_t v_sz_140_; size_t v___x_141_; lean_object* v_es_142_; lean_object* v___x_143_; lean_object* v___y_145_; lean_object* v___x_151_; uint8_t v___x_152_; 
lean_inc_ref(v_inst_134_);
v___f_137_ = lean_alloc_closure((void*)(l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___lam__0), 3, 1);
lean_closure_set(v___f_137_, 0, v_inst_134_);
v___f_138_ = ((lean_object*)(l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__0));
v___x_139_ = ((lean_object*)(l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__10));
v_sz_140_ = lean_array_size(v_es_136_);
v___x_141_ = ((size_t)0ULL);
lean_inc_ref(v_es_136_);
v_es_142_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_139_, v_es_136_, v___f_138_, v_sz_140_, v___x_141_, v_es_136_);
lean_dec_ref(v_es_136_);
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_array_get_size(v_es_142_);
v___x_152_ = lean_nat_dec_eq(v___x_151_, v___x_143_);
if (v___x_152_ == 0)
{
lean_object* v___f_153_; lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___y_161_; uint8_t v___x_163_; 
v___f_153_ = lean_alloc_closure((void*)(l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_153_, 0, v_inst_135_);
lean_closure_set(v___f_153_, 1, v_inst_134_);
v___x_158_ = lean_unsigned_to_nat(1u);
v___x_159_ = lean_nat_sub(v___x_151_, v___x_158_);
v___x_163_ = lean_nat_dec_le(v___x_143_, v___x_159_);
if (v___x_163_ == 0)
{
lean_inc(v___x_159_);
v___y_161_ = v___x_159_;
goto v___jp_160_;
}
else
{
v___y_161_ = v___x_143_;
goto v___jp_160_;
}
v___jp_154_:
{
lean_object* v___x_157_; 
v___x_157_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_153_, v___x_151_, v_es_142_, v___y_155_, v___y_156_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_156_);
v___y_145_ = v___x_157_;
goto v___jp_144_;
}
v___jp_160_:
{
uint8_t v___x_162_; 
v___x_162_ = lean_nat_dec_le(v___y_161_, v___x_159_);
if (v___x_162_ == 0)
{
lean_dec(v___x_159_);
lean_inc(v___y_161_);
v___y_155_ = v___y_161_;
v___y_156_ = v___y_161_;
goto v___jp_154_;
}
else
{
v___y_155_ = v___y_161_;
v___y_156_ = v___x_159_;
goto v___jp_154_;
}
}
}
else
{
lean_dec_ref(v_inst_135_);
lean_dec_ref(v_inst_134_);
v___y_145_ = v_es_142_;
goto v___jp_144_;
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_146_ = ((lean_object*)(l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__12));
v___x_147_ = lean_array_get_size(v___y_145_);
v___x_148_ = lean_nat_dec_lt(v___x_143_, v___x_147_);
if (v___x_148_ == 0)
{
lean_dec_ref(v___y_145_);
lean_dec_ref(v___f_137_);
return v___x_146_;
}
else
{
size_t v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_usize_of_nat(v___x_147_);
v___x_150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_139_, v___f_137_, v___y_145_, v___x_141_, v___x_149_, v___x_146_);
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_sortOwned(lean_object* v_00_u03ba_164_, lean_object* v_00_u03b1_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_es_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_ImportedDeclKeyedMap_sortOwned___redArg(v_inst_166_, v_inst_167_, v_es_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f_go___redArg(lean_object* v_inst_170_, lean_object* v_ks_171_, lean_object* v_k_172_, lean_object* v_lo_173_, lean_object* v_hi_174_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = lean_nat_dec_lt(v_lo_173_, v_hi_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
lean_dec(v_hi_174_);
lean_dec(v_lo_173_);
lean_dec(v_k_172_);
lean_dec_ref(v_inst_170_);
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v_mid_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_177_ = lean_nat_add(v_lo_173_, v_hi_174_);
v___x_178_ = lean_unsigned_to_nat(1u);
v_mid_179_ = lean_nat_shiftr(v___x_177_, v___x_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_array_get_size(v_ks_171_);
v___x_181_ = lean_nat_dec_lt(v_mid_179_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec(v_mid_179_);
lean_dec(v_hi_174_);
lean_dec(v_lo_173_);
lean_dec(v_k_172_);
lean_dec_ref(v_inst_170_);
v___x_182_ = lean_box(0);
return v___x_182_;
}
else
{
lean_object* v_lt_183_; lean_object* v_k_x27_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_lt_183_ = lean_ctor_get(v_inst_170_, 1);
v_k_x27_184_ = lean_array_fget_borrowed(v_ks_171_, v_mid_179_);
lean_inc_ref(v_lt_183_);
lean_inc(v_k_172_);
lean_inc(v_k_x27_184_);
v___x_185_ = lean_apply_2(v_lt_183_, v_k_x27_184_, v_k_172_);
v___x_186_ = lean_unbox(v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; uint8_t v___x_188_; 
lean_dec(v_hi_174_);
lean_inc_ref(v_lt_183_);
lean_inc(v_k_x27_184_);
lean_inc(v_k_172_);
v___x_187_ = lean_apply_2(v_lt_183_, v_k_172_, v_k_x27_184_);
v___x_188_ = lean_unbox(v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
lean_dec(v_lo_173_);
lean_dec(v_k_172_);
lean_dec_ref(v_inst_170_);
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v_mid_179_);
return v___x_189_;
}
else
{
v_hi_174_ = v_mid_179_;
goto _start;
}
}
else
{
lean_object* v___x_191_; 
lean_dec(v_lo_173_);
v___x_191_ = lean_nat_add(v_mid_179_, v___x_178_);
lean_dec(v_mid_179_);
v_lo_173_ = v___x_191_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f_go___redArg___boxed(lean_object* v_inst_193_, lean_object* v_ks_194_, lean_object* v_k_195_, lean_object* v_lo_196_, lean_object* v_hi_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f_go___redArg(v_inst_193_, v_ks_194_, v_k_195_, v_lo_196_, v_hi_197_);
lean_dec_ref(v_ks_194_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f_go(lean_object* v_00_u03ba_199_, lean_object* v_inst_200_, lean_object* v_ks_201_, lean_object* v_k_202_, lean_object* v_lo_203_, lean_object* v_hi_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f_go___redArg(v_inst_200_, v_ks_201_, v_k_202_, v_lo_203_, v_hi_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f_go___boxed(lean_object* v_00_u03ba_206_, lean_object* v_inst_207_, lean_object* v_ks_208_, lean_object* v_k_209_, lean_object* v_lo_210_, lean_object* v_hi_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f_go(v_00_u03ba_206_, v_inst_207_, v_ks_208_, v_k_209_, v_lo_210_, v_hi_211_);
lean_dec_ref(v_ks_208_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f___redArg(lean_object* v_inst_213_, lean_object* v_ks_214_, lean_object* v_k_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_array_get_size(v_ks_214_);
v___x_218_ = l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f_go___redArg(v_inst_213_, v_ks_214_, v_k_215_, v___x_216_, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f___redArg___boxed(lean_object* v_inst_219_, lean_object* v_ks_220_, lean_object* v_k_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f___redArg(v_inst_219_, v_ks_220_, v_k_221_);
lean_dec_ref(v_ks_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f(lean_object* v_00_u03ba_223_, lean_object* v_inst_224_, lean_object* v_ks_225_, lean_object* v_k_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f___redArg(v_inst_224_, v_ks_225_, v_k_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f___boxed(lean_object* v_00_u03ba_228_, lean_object* v_inst_229_, lean_object* v_ks_230_, lean_object* v_k_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f(v_00_u03ba_228_, v_inst_229_, v_ks_230_, v_k_231_);
lean_dec_ref(v_ks_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_valAt___redArg(lean_object* v_inst_233_, lean_object* v_vs_234_, lean_object* v_j_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_236_ = lean_array_get_size(v_vs_234_);
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_nat_dec_eq(v___x_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
v___x_239_ = lean_array_get_borrowed(v_inst_233_, v_vs_234_, v_j_235_);
lean_inc(v___x_239_);
return v___x_239_;
}
else
{
lean_inc(v_inst_233_);
return v_inst_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_valAt___redArg___boxed(lean_object* v_inst_240_, lean_object* v_vs_241_, lean_object* v_j_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_valAt___redArg(v_inst_240_, v_vs_241_, v_j_242_);
lean_dec(v_j_242_);
lean_dec_ref(v_vs_241_);
lean_dec(v_inst_240_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_valAt(lean_object* v_00_u03b1_244_, lean_object* v_inst_245_, lean_object* v_vs_246_, lean_object* v_j_247_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_248_ = lean_array_get_size(v_vs_246_);
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = lean_nat_dec_eq(v___x_248_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
v___x_251_ = lean_array_get_borrowed(v_inst_245_, v_vs_246_, v_j_247_);
lean_inc(v___x_251_);
return v___x_251_;
}
else
{
lean_inc(v_inst_245_);
return v_inst_245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_valAt___boxed(lean_object* v_00_u03b1_252_, lean_object* v_inst_253_, lean_object* v_vs_254_, lean_object* v_j_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_valAt(v_00_u03b1_252_, v_inst_253_, v_vs_254_, v_j_255_);
lean_dec(v_j_255_);
lean_dec_ref(v_vs_254_);
lean_dec(v_inst_253_);
return v_res_256_;
}
}
static lean_object* _init_l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Array_instInhabited___redArg();
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg(lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_m_260_, lean_object* v_k_261_){
_start:
{
lean_object* v_consts_262_; lean_object* v_ownedKeys_263_; lean_object* v_ownedVals_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_consts_262_ = lean_ctor_get(v_m_260_, 0);
v_ownedKeys_263_ = lean_ctor_get(v_m_260_, 1);
v_ownedVals_264_ = lean_ctor_get(v_m_260_, 2);
v___x_265_ = lean_array_get_size(v_ownedKeys_263_);
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = lean_nat_dec_eq(v___x_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v_declName_268_; lean_object* v_cache_x3f_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v_isZero_272_; 
v_declName_268_ = lean_ctor_get(v_inst_258_, 0);
v_cache_x3f_269_ = lean_ctor_get(v_consts_262_, 0);
lean_inc_ref(v_declName_268_);
lean_inc(v_k_261_);
v___x_270_ = lean_apply_1(v_declName_268_, v_k_261_);
v___x_271_ = lean_imported_consts_find_mod_idx_cached(v_cache_x3f_269_, v_consts_262_, v___x_270_);
lean_dec(v___x_270_);
v_isZero_272_ = lean_nat_dec_eq(v___x_271_, v___x_266_);
if (v_isZero_272_ == 1)
{
lean_object* v___x_273_; 
lean_dec(v___x_271_);
lean_dec(v_k_261_);
lean_dec(v_inst_259_);
lean_dec_ref(v_inst_258_);
v___x_273_ = lean_box(0);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v_one_275_; lean_object* v_n_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_274_ = lean_obj_once(&l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg___closed__0, &l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg___closed__0_once, _init_l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg___closed__0);
v_one_275_ = lean_unsigned_to_nat(1u);
v_n_276_ = lean_nat_sub(v___x_271_, v_one_275_);
lean_dec(v___x_271_);
v___x_277_ = lean_array_get_borrowed(v___x_274_, v_ownedKeys_263_, v_n_276_);
v___x_278_ = l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findIdx_x3f___redArg(v_inst_258_, v___x_277_, v_k_261_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_279_; 
lean_dec(v_n_276_);
lean_dec(v_inst_259_);
v___x_279_ = lean_box(0);
return v___x_279_;
}
else
{
lean_object* v_val_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_294_; 
v_val_280_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_294_ == 0)
{
v___x_282_ = v___x_278_;
v_isShared_283_ = v_isSharedCheck_294_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_val_280_);
lean_dec(v___x_278_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_294_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_284_ = lean_array_get_borrowed(v___x_274_, v_ownedVals_264_, v_n_276_);
lean_dec(v_n_276_);
v___x_285_ = lean_array_get_size(v___x_284_);
v___x_286_ = lean_nat_dec_eq(v___x_285_, v___x_266_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_287_ = lean_array_get(v_inst_259_, v___x_284_, v_val_280_);
lean_dec(v_val_280_);
lean_dec(v_inst_259_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_287_);
v___x_289_ = v___x_282_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
else
{
lean_object* v___x_292_; 
lean_dec(v_val_280_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v_inst_259_);
v___x_292_ = v___x_282_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_inst_259_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
}
else
{
lean_object* v___x_295_; 
lean_dec(v_k_261_);
lean_dec(v_inst_259_);
lean_dec_ref(v_inst_258_);
v___x_295_ = lean_box(0);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg___boxed(lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_m_298_, lean_object* v_k_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg(v_inst_296_, v_inst_297_, v_m_298_, v_k_299_);
lean_dec_ref(v_m_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f(lean_object* v_00_u03ba_301_, lean_object* v_00_u03b1_302_, lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_m_307_, lean_object* v_k_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg(v_inst_305_, v_inst_306_, v_m_307_, v_k_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___boxed(lean_object* v_00_u03ba_310_, lean_object* v_00_u03b1_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_m_316_, lean_object* v_k_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f(v_00_u03ba_310_, v_00_u03b1_311_, v_inst_312_, v_inst_313_, v_inst_314_, v_inst_315_, v_m_316_, v_k_317_);
lean_dec_ref(v_m_316_);
lean_dec_ref(v_inst_313_);
lean_dec_ref(v_inst_312_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__0(lean_object* v_x_319_){
_start:
{
lean_object* v_fst_320_; 
v_fst_320_ = lean_ctor_get(v_x_319_, 0);
lean_inc(v_fst_320_);
return v_fst_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__0___boxed(lean_object* v_x_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__0(v_x_321_);
lean_dec_ref(v_x_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__1(lean_object* v_x_323_){
_start:
{
lean_object* v_snd_324_; 
v_snd_324_ = lean_ctor_get(v_x_323_, 1);
lean_inc(v_snd_324_);
return v_snd_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__1___boxed(lean_object* v_x_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__1(v_x_325_);
lean_dec_ref(v_x_325_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__2(lean_object* v_fst_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_snd_330_, lean_object* v_inst_331_, lean_object* v_j_332_, lean_object* v_h_333_, lean_object* v_____s_334_){
_start:
{
lean_object* v_consts_335_; lean_object* v_ownedKeys_336_; lean_object* v_ownedVals_337_; lean_object* v_foreign_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_354_; 
v_consts_335_ = lean_ctor_get(v_____s_334_, 0);
v_ownedKeys_336_ = lean_ctor_get(v_____s_334_, 1);
v_ownedVals_337_ = lean_ctor_get(v_____s_334_, 2);
v_foreign_338_ = lean_ctor_get(v_____s_334_, 3);
v_isSharedCheck_354_ = !lean_is_exclusive(v_____s_334_);
if (v_isSharedCheck_354_ == 0)
{
v___x_340_ = v_____s_334_;
v_isShared_341_ = v_isSharedCheck_354_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_foreign_338_);
lean_inc(v_ownedVals_337_);
lean_inc(v_ownedKeys_336_);
lean_inc(v_consts_335_);
lean_dec(v_____s_334_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_354_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___y_344_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_342_ = lean_array_fget_borrowed(v_fst_327_, v_j_332_);
v___x_350_ = lean_array_get_size(v_snd_330_);
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = lean_nat_dec_eq(v___x_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
v___x_353_ = lean_array_get(v_inst_331_, v_snd_330_, v_j_332_);
lean_dec(v_inst_331_);
v___y_344_ = v___x_353_;
goto v___jp_343_;
}
else
{
v___y_344_ = v_inst_331_;
goto v___jp_343_;
}
v___jp_343_:
{
lean_object* v___x_345_; lean_object* v___x_347_; 
lean_inc(v___x_342_);
v___x_345_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_328_, v_inst_329_, v_foreign_338_, v___x_342_, v___y_344_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 3, v___x_345_);
v___x_347_ = v___x_340_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_consts_335_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_ownedKeys_336_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v_ownedVals_337_);
lean_ctor_set(v_reuseFailAlloc_349_, 3, v___x_345_);
v___x_347_ = v_reuseFailAlloc_349_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_348_; 
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__2___boxed(lean_object* v_fst_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_snd_358_, lean_object* v_inst_359_, lean_object* v_j_360_, lean_object* v_h_361_, lean_object* v_____s_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__2(v_fst_355_, v_inst_356_, v_inst_357_, v_snd_358_, v_inst_359_, v_j_360_, v_h_361_, v_____s_362_);
lean_dec(v_j_360_);
lean_dec_ref(v_snd_358_);
lean_dec_ref(v_fst_355_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__3(lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v___x_367_, lean_object* v_a_368_, lean_object* v_x_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_fst_371_; lean_object* v_snd_372_; lean_object* v___f_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_fst_371_ = lean_ctor_get(v_a_368_, 0);
lean_inc_n(v_fst_371_, 2);
v_snd_372_ = lean_ctor_get(v_a_368_, 1);
lean_inc(v_snd_372_);
lean_dec_ref(v_a_368_);
v___f_373_ = lean_alloc_closure((void*)(l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_373_, 0, v_fst_371_);
lean_closure_set(v___f_373_, 1, v_inst_364_);
lean_closure_set(v___f_373_, 2, v_inst_365_);
lean_closure_set(v___f_373_, 3, v_snd_372_);
lean_closure_set(v___f_373_, 4, v_inst_366_);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_array_get_size(v_fst_371_);
lean_dec(v_fst_371_);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_377_, 0, v___x_374_);
lean_ctor_set(v___x_377_, 1, v___x_375_);
lean_ctor_set(v___x_377_, 2, v___x_376_);
v___x_378_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_box(0), lean_box(0), v___x_367_, v___x_377_, v___f_373_, v___y_370_, v___x_374_, lean_box(0), lean_box(0));
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules___redArg(lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_consts_385_, lean_object* v_owned_386_, lean_object* v_foreign_387_){
_start:
{
lean_object* v___f_388_; lean_object* v___f_389_; lean_object* v___x_390_; lean_object* v___f_391_; size_t v_sz_392_; size_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v_m_397_; size_t v_sz_398_; lean_object* v___x_399_; 
v___f_388_ = ((lean_object*)(l_Lean_ImportedDeclKeyedMap_ofModules___redArg___closed__0));
v___f_389_ = ((lean_object*)(l_Lean_ImportedDeclKeyedMap_ofModules___redArg___closed__1));
v___x_390_ = ((lean_object*)(l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__10));
v___f_391_ = lean_alloc_closure((void*)(l_Lean_ImportedDeclKeyedMap_ofModules___redArg___lam__3), 7, 4);
lean_closure_set(v___f_391_, 0, v_inst_382_);
lean_closure_set(v___f_391_, 1, v_inst_383_);
lean_closure_set(v___f_391_, 2, v_inst_384_);
lean_closure_set(v___f_391_, 3, v___x_390_);
v_sz_392_ = lean_array_size(v_owned_386_);
v___x_393_ = ((size_t)0ULL);
lean_inc_ref(v_owned_386_);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_390_, v___f_388_, v_sz_392_, v___x_393_, v_owned_386_);
v___x_395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_390_, v___f_389_, v_sz_392_, v___x_393_, v_owned_386_);
v___x_396_ = lean_obj_once(&l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__3, &l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__3_once, _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__3);
v_m_397_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_m_397_, 0, v_consts_385_);
lean_ctor_set(v_m_397_, 1, v___x_394_);
lean_ctor_set(v_m_397_, 2, v___x_395_);
lean_ctor_set(v_m_397_, 3, v___x_396_);
v_sz_398_ = lean_array_size(v_foreign_387_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_390_, v_foreign_387_, v___f_391_, v_sz_398_, v___x_393_, v_m_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_ofModules(lean_object* v_00_u03ba_400_, lean_object* v_00_u03b1_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_consts_405_, lean_object* v_owned_406_, lean_object* v_foreign_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_ImportedDeclKeyedMap_ofModules___redArg(v_inst_402_, v_inst_403_, v_inst_404_, v_consts_405_, v_owned_406_, v_foreign_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_find_x3f___redArg(lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_m_413_, lean_object* v_k_414_){
_start:
{
lean_object* v_foreign_415_; lean_object* v___x_416_; 
v_foreign_415_ = lean_ctor_get(v_m_413_, 3);
lean_inc(v_k_414_);
v___x_416_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_409_, v_inst_410_, v_foreign_415_, v_k_414_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v___x_417_; 
v___x_417_ = l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg(v_inst_411_, v_inst_412_, v_m_413_, v_k_414_);
return v___x_417_;
}
else
{
lean_dec(v_k_414_);
lean_dec(v_inst_412_);
lean_dec_ref(v_inst_411_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_find_x3f___redArg___boxed(lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_m_422_, lean_object* v_k_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_ImportedDeclKeyedMap_find_x3f___redArg(v_inst_418_, v_inst_419_, v_inst_420_, v_inst_421_, v_m_422_, v_k_423_);
lean_dec_ref(v_m_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_find_x3f(lean_object* v_00_u03ba_425_, lean_object* v_00_u03b1_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_m_431_, lean_object* v_k_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_ImportedDeclKeyedMap_find_x3f___redArg(v_inst_427_, v_inst_428_, v_inst_429_, v_inst_430_, v_m_431_, v_k_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_find_x3f___boxed(lean_object* v_00_u03ba_434_, lean_object* v_00_u03b1_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_m_440_, lean_object* v_k_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_ImportedDeclKeyedMap_find_x3f(v_00_u03ba_434_, v_00_u03b1_435_, v_inst_436_, v_inst_437_, v_inst_438_, v_inst_439_, v_m_440_, v_k_441_);
lean_dec_ref(v_m_440_);
return v_res_442_;
}
}
LEAN_EXPORT uint8_t l_Lean_ImportedDeclKeyedMap_contains___redArg(lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_m_447_, lean_object* v_k_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_ImportedDeclKeyedMap_find_x3f___redArg(v_inst_443_, v_inst_444_, v_inst_445_, v_inst_446_, v_m_447_, v_k_448_);
if (lean_obj_tag(v___x_449_) == 0)
{
uint8_t v___x_450_; 
v___x_450_ = 0;
return v___x_450_;
}
else
{
uint8_t v___x_451_; 
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = 1;
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_contains___redArg___boxed(lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_m_456_, lean_object* v_k_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Lean_ImportedDeclKeyedMap_contains___redArg(v_inst_452_, v_inst_453_, v_inst_454_, v_inst_455_, v_m_456_, v_k_457_);
lean_dec_ref(v_m_456_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT uint8_t l_Lean_ImportedDeclKeyedMap_contains(lean_object* v_00_u03ba_460_, lean_object* v_00_u03b1_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_m_466_, lean_object* v_k_467_){
_start:
{
uint8_t v___x_468_; 
v___x_468_ = l_Lean_ImportedDeclKeyedMap_contains___redArg(v_inst_462_, v_inst_463_, v_inst_464_, v_inst_465_, v_m_466_, v_k_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_contains___boxed(lean_object* v_00_u03ba_469_, lean_object* v_00_u03b1_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_m_475_, lean_object* v_k_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_Lean_ImportedDeclKeyedMap_contains(v_00_u03ba_469_, v_00_u03b1_470_, v_inst_471_, v_inst_472_, v_inst_473_, v_inst_474_, v_m_475_, v_k_476_);
lean_dec_ref(v_m_475_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__0(lean_object* v_inst_479_, lean_object* v_f_480_, lean_object* v_foreign_481_, lean_object* v_____s_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_479_, v_f_480_, v_foreign_481_, v_____s_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__1(lean_object* v_toPure_484_, lean_object* v_____s_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_486_, 0, v_____s_485_);
v___x_487_ = lean_apply_2(v_toPure_484_, lean_box(0), v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__2(lean_object* v_toPure_488_, lean_object* v_____x_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v_____x_489_);
v___x_491_ = lean_apply_2(v_toPure_488_, lean_box(0), v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__3(lean_object* v___x_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_foreign_495_, lean_object* v_f_496_, lean_object* v_toBind_497_, lean_object* v___f_498_, lean_object* v_vs_499_, lean_object* v___x_500_, lean_object* v_inst_501_, lean_object* v_toPure_502_, lean_object* v_j_503_, lean_object* v_h_504_, lean_object* v_____s_505_){
_start:
{
lean_object* v_k_506_; lean_object* v___y_508_; uint8_t v___x_511_; 
v_k_506_ = lean_array_fget_borrowed(v___x_492_, v_j_503_);
lean_inc(v_k_506_);
v___x_511_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_493_, v_inst_494_, v_foreign_495_, v_k_506_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; uint8_t v___x_513_; 
lean_dec(v_toPure_502_);
v___x_512_ = lean_array_get_size(v_vs_499_);
v___x_513_ = lean_nat_dec_eq(v___x_512_, v___x_500_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_array_get(v_inst_501_, v_vs_499_, v_j_503_);
lean_dec(v_inst_501_);
v___y_508_ = v___x_514_;
goto v___jp_507_;
}
else
{
v___y_508_ = v_inst_501_;
goto v___jp_507_;
}
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v_inst_501_);
lean_dec(v___f_498_);
lean_dec(v_toBind_497_);
lean_dec(v_f_496_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v_____s_505_);
v___x_516_ = lean_apply_2(v_toPure_502_, lean_box(0), v___x_515_);
return v___x_516_;
}
v___jp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_inc(v_k_506_);
v___x_509_ = lean_apply_3(v_f_496_, v_____s_505_, v_k_506_, v___y_508_);
v___x_510_ = lean_apply_4(v_toBind_497_, lean_box(0), lean_box(0), v___x_509_, v___f_498_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__3___boxed(lean_object* v___x_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_foreign_520_, lean_object* v_f_521_, lean_object* v_toBind_522_, lean_object* v___f_523_, lean_object* v_vs_524_, lean_object* v___x_525_, lean_object* v_inst_526_, lean_object* v_toPure_527_, lean_object* v_j_528_, lean_object* v_h_529_, lean_object* v_____s_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__3(v___x_517_, v_inst_518_, v_inst_519_, v_foreign_520_, v_f_521_, v_toBind_522_, v___f_523_, v_vs_524_, v___x_525_, v_inst_526_, v_toPure_527_, v_j_528_, v_h_529_, v_____s_530_);
lean_dec(v_j_528_);
lean_dec(v___x_525_);
lean_dec_ref(v_vs_524_);
lean_dec_ref(v___x_517_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__4(lean_object* v___x_532_, lean_object* v_ownedVals_533_, lean_object* v_ownedKeys_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_foreign_537_, lean_object* v_f_538_, lean_object* v_toBind_539_, lean_object* v___f_540_, lean_object* v___x_541_, lean_object* v_inst_542_, lean_object* v_toPure_543_, lean_object* v___x_544_, lean_object* v_inst_545_, lean_object* v___f_546_, lean_object* v_i_547_, lean_object* v_h_548_, lean_object* v_____s_549_){
_start:
{
lean_object* v_vs_550_; lean_object* v___x_551_; lean_object* v___f_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_vs_550_ = lean_array_get_borrowed(v___x_532_, v_ownedVals_533_, v_i_547_);
v___x_551_ = lean_array_fget_borrowed(v_ownedKeys_534_, v_i_547_);
lean_inc_n(v___x_541_, 2);
lean_inc(v_vs_550_);
lean_inc(v_toBind_539_);
lean_inc(v___x_551_);
v___f_552_ = lean_alloc_closure((void*)(l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__3___boxed), 14, 11);
lean_closure_set(v___f_552_, 0, v___x_551_);
lean_closure_set(v___f_552_, 1, v_inst_535_);
lean_closure_set(v___f_552_, 2, v_inst_536_);
lean_closure_set(v___f_552_, 3, v_foreign_537_);
lean_closure_set(v___f_552_, 4, v_f_538_);
lean_closure_set(v___f_552_, 5, v_toBind_539_);
lean_closure_set(v___f_552_, 6, v___f_540_);
lean_closure_set(v___f_552_, 7, v_vs_550_);
lean_closure_set(v___f_552_, 8, v___x_541_);
lean_closure_set(v___f_552_, 9, v_inst_542_);
lean_closure_set(v___f_552_, 10, v_toPure_543_);
v___x_553_ = lean_array_get_size(v___x_551_);
v___x_554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_554_, 0, v___x_541_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
lean_ctor_set(v___x_554_, 2, v___x_544_);
v___x_555_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_box(0), lean_box(0), v_inst_545_, v___x_554_, v___f_552_, v_____s_549_, v___x_541_, lean_box(0), lean_box(0));
v___x_556_ = lean_apply_4(v_toBind_539_, lean_box(0), lean_box(0), v___x_555_, v___f_546_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_557_ = _args[0];
lean_object* v_ownedVals_558_ = _args[1];
lean_object* v_ownedKeys_559_ = _args[2];
lean_object* v_inst_560_ = _args[3];
lean_object* v_inst_561_ = _args[4];
lean_object* v_foreign_562_ = _args[5];
lean_object* v_f_563_ = _args[6];
lean_object* v_toBind_564_ = _args[7];
lean_object* v___f_565_ = _args[8];
lean_object* v___x_566_ = _args[9];
lean_object* v_inst_567_ = _args[10];
lean_object* v_toPure_568_ = _args[11];
lean_object* v___x_569_ = _args[12];
lean_object* v_inst_570_ = _args[13];
lean_object* v___f_571_ = _args[14];
lean_object* v_i_572_ = _args[15];
lean_object* v_h_573_ = _args[16];
lean_object* v_____s_574_ = _args[17];
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__4(v___x_557_, v_ownedVals_558_, v_ownedKeys_559_, v_inst_560_, v_inst_561_, v_foreign_562_, v_f_563_, v_toBind_564_, v___f_565_, v___x_566_, v_inst_567_, v_toPure_568_, v___x_569_, v_inst_570_, v___f_571_, v_i_572_, v_h_573_, v_____s_574_);
lean_dec(v_i_572_);
lean_dec_ref(v_ownedKeys_559_);
lean_dec_ref(v_ownedVals_558_);
lean_dec_ref(v___x_557_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM___redArg(lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_f_580_, lean_object* v_init_581_, lean_object* v_d_582_){
_start:
{
lean_object* v_toApplicative_583_; lean_object* v_toBind_584_; lean_object* v_ownedKeys_585_; lean_object* v_ownedVals_586_; lean_object* v_foreign_587_; lean_object* v_toPure_588_; lean_object* v___f_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_toApplicative_583_ = lean_ctor_get(v_inst_579_, 0);
v_toBind_584_ = lean_ctor_get(v_inst_579_, 1);
lean_inc_n(v_toBind_584_, 2);
v_ownedKeys_585_ = lean_ctor_get(v_d_582_, 1);
lean_inc_ref(v_ownedKeys_585_);
v_ownedVals_586_ = lean_ctor_get(v_d_582_, 2);
lean_inc_ref(v_ownedVals_586_);
v_foreign_587_ = lean_ctor_get(v_d_582_, 3);
lean_inc_ref_n(v_foreign_587_, 2);
lean_dec_ref(v_d_582_);
v_toPure_588_ = lean_ctor_get(v_toApplicative_583_, 1);
lean_inc(v_f_580_);
lean_inc_ref_n(v_inst_579_, 2);
v___f_589_ = lean_alloc_closure((void*)(l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_589_, 0, v_inst_579_);
lean_closure_set(v___f_589_, 1, v_f_580_);
lean_closure_set(v___f_589_, 2, v_foreign_587_);
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = lean_array_get_size(v_ownedKeys_585_);
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_593_, 0, v___x_590_);
lean_ctor_set(v___x_593_, 1, v___x_591_);
lean_ctor_set(v___x_593_, 2, v___x_592_);
v___x_594_ = lean_obj_once(&l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg___closed__0, &l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg___closed__0_once, _init_l___private_Lean_DeclKeyedMap_0__Lean_ImportedDeclKeyedMap_findOwned_x3f___redArg___closed__0);
lean_inc_n(v_toPure_588_, 3);
v___f_595_ = lean_alloc_closure((void*)(l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_595_, 0, v_toPure_588_);
v___f_596_ = lean_alloc_closure((void*)(l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__2), 2, 1);
lean_closure_set(v___f_596_, 0, v_toPure_588_);
v___f_597_ = lean_alloc_closure((void*)(l_Lean_ImportedDeclKeyedMap_foldM___redArg___lam__4___boxed), 18, 15);
lean_closure_set(v___f_597_, 0, v___x_594_);
lean_closure_set(v___f_597_, 1, v_ownedVals_586_);
lean_closure_set(v___f_597_, 2, v_ownedKeys_585_);
lean_closure_set(v___f_597_, 3, v_inst_576_);
lean_closure_set(v___f_597_, 4, v_inst_577_);
lean_closure_set(v___f_597_, 5, v_foreign_587_);
lean_closure_set(v___f_597_, 6, v_f_580_);
lean_closure_set(v___f_597_, 7, v_toBind_584_);
lean_closure_set(v___f_597_, 8, v___f_596_);
lean_closure_set(v___f_597_, 9, v___x_590_);
lean_closure_set(v___f_597_, 10, v_inst_578_);
lean_closure_set(v___f_597_, 11, v_toPure_588_);
lean_closure_set(v___f_597_, 12, v___x_592_);
lean_closure_set(v___f_597_, 13, v_inst_579_);
lean_closure_set(v___f_597_, 14, v___f_595_);
v___x_598_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_box(0), lean_box(0), v_inst_579_, v___x_593_, v___f_597_, v_init_581_, v___x_590_, lean_box(0), lean_box(0));
v___x_599_ = lean_apply_4(v_toBind_584_, lean_box(0), lean_box(0), v___x_598_, v___f_589_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedDeclKeyedMap_foldM(lean_object* v_00_u03ba_600_, lean_object* v_00_u03b1_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_m_605_, lean_object* v_00_u03b2_606_, lean_object* v_inst_607_, lean_object* v_f_608_, lean_object* v_init_609_, lean_object* v_d_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_ImportedDeclKeyedMap_foldM___redArg(v_inst_602_, v_inst_603_, v_inst_604_, v_inst_607_, v_f_608_, v_init_609_, v_d_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclKeyedMap_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_612_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclKeyedMap_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_613_ = lean_obj_once(&l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__3, &l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__3_once, _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__3);
v___x_614_ = lean_obj_once(&l_Lean_instInhabitedDeclKeyedMap_default___redArg___closed__0, &l_Lean_instInhabitedDeclKeyedMap_default___redArg___closed__0_once, _init_l_Lean_instInhabitedDeclKeyedMap_default___redArg___closed__0);
v___x_615_ = lean_obj_once(&l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__4, &l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__4_once, _init_l_Lean_instInhabitedImportedDeclKeyedMap_default___redArg___closed__4);
v___x_616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v___x_614_);
lean_ctor_set(v___x_616_, 2, v___x_613_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap_default___redArg(){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_obj_once(&l_Lean_instInhabitedDeclKeyedMap_default___redArg___closed__1, &l_Lean_instInhabitedDeclKeyedMap_default___redArg___closed__1_once, _init_l_Lean_instInhabitedDeclKeyedMap_default___redArg___closed__1);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap_default___redArg___boxed(lean_object* v___dummy_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_instInhabitedDeclKeyedMap_default___redArg();
return v_res_620_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclKeyedMap_default___closed__0(void){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_instInhabitedDeclKeyedMap_default___redArg();
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap_default(lean_object* v_00_u03ba_622_, lean_object* v_00_u03b1_623_, lean_object* v_inst_624_, lean_object* v_inst_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = lean_obj_once(&l_Lean_instInhabitedDeclKeyedMap_default___closed__0, &l_Lean_instInhabitedDeclKeyedMap_default___closed__0_once, _init_l_Lean_instInhabitedDeclKeyedMap_default___closed__0);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap_default___boxed(lean_object* v_00_u03ba_627_, lean_object* v_00_u03b1_628_, lean_object* v_inst_629_, lean_object* v_inst_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_instInhabitedDeclKeyedMap_default(v_00_u03ba_627_, v_00_u03b1_628_, v_inst_629_, v_inst_630_);
lean_dec_ref(v_inst_630_);
lean_dec_ref(v_inst_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap___redArg(){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = lean_obj_once(&l_Lean_instInhabitedDeclKeyedMap_default___closed__0, &l_Lean_instInhabitedDeclKeyedMap_default___closed__0_once, _init_l_Lean_instInhabitedDeclKeyedMap_default___closed__0);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap___redArg___boxed(lean_object* v___dummy_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_instInhabitedDeclKeyedMap___redArg();
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap(lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = lean_obj_once(&l_Lean_instInhabitedDeclKeyedMap_default___closed__0, &l_Lean_instInhabitedDeclKeyedMap_default___closed__0_once, _init_l_Lean_instInhabitedDeclKeyedMap_default___closed__0);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclKeyedMap___boxed(lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_instInhabitedDeclKeyedMap(v_a_641_, v_a_642_, v_a_643_, v_a_644_);
lean_dec_ref(v_a_644_);
lean_dec_ref(v_a_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_find_x3f___redArg(lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_m_650_, lean_object* v_k_651_){
_start:
{
lean_object* v_imported_652_; lean_object* v_removed_653_; lean_object* v_added_654_; lean_object* v___x_655_; 
v_imported_652_ = lean_ctor_get(v_m_650_, 0);
lean_inc_ref(v_imported_652_);
v_removed_653_ = lean_ctor_get(v_m_650_, 1);
lean_inc_ref(v_removed_653_);
v_added_654_ = lean_ctor_get(v_m_650_, 2);
lean_inc_ref(v_added_654_);
lean_dec_ref(v_m_650_);
lean_inc(v_k_651_);
lean_inc_ref(v_inst_647_);
lean_inc_ref(v_inst_646_);
v___x_655_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_646_, v_inst_647_, v_added_654_, v_k_651_);
lean_dec_ref(v_added_654_);
if (lean_obj_tag(v___x_655_) == 0)
{
uint8_t v___x_656_; 
lean_inc(v_k_651_);
lean_inc_ref(v_inst_647_);
lean_inc_ref(v_inst_646_);
v___x_656_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_646_, v_inst_647_, v_removed_653_, v_k_651_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_ImportedDeclKeyedMap_find_x3f___redArg(v_inst_646_, v_inst_647_, v_inst_648_, v_inst_649_, v_imported_652_, v_k_651_);
lean_dec_ref(v_imported_652_);
return v___x_657_;
}
else
{
lean_dec_ref(v_imported_652_);
lean_dec(v_k_651_);
lean_dec(v_inst_649_);
lean_dec_ref(v_inst_648_);
lean_dec_ref(v_inst_647_);
lean_dec_ref(v_inst_646_);
return v___x_655_;
}
}
else
{
lean_dec_ref(v_removed_653_);
lean_dec_ref(v_imported_652_);
lean_dec(v_k_651_);
lean_dec(v_inst_649_);
lean_dec_ref(v_inst_648_);
lean_dec_ref(v_inst_647_);
lean_dec_ref(v_inst_646_);
return v___x_655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_find_x3f(lean_object* v_00_u03ba_658_, lean_object* v_00_u03b1_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_m_664_, lean_object* v_k_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_DeclKeyedMap_find_x3f___redArg(v_inst_660_, v_inst_661_, v_inst_662_, v_inst_663_, v_m_664_, v_k_665_);
return v___x_666_;
}
}
LEAN_EXPORT uint8_t l_Lean_DeclKeyedMap_contains___redArg(lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_m_671_, lean_object* v_k_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_DeclKeyedMap_find_x3f___redArg(v_inst_667_, v_inst_668_, v_inst_669_, v_inst_670_, v_m_671_, v_k_672_);
if (lean_obj_tag(v___x_673_) == 0)
{
uint8_t v___x_674_; 
v___x_674_ = 0;
return v___x_674_;
}
else
{
uint8_t v___x_675_; 
lean_dec_ref_known(v___x_673_, 1);
v___x_675_ = 1;
return v___x_675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_contains___redArg___boxed(lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_m_680_, lean_object* v_k_681_){
_start:
{
uint8_t v_res_682_; lean_object* v_r_683_; 
v_res_682_ = l_Lean_DeclKeyedMap_contains___redArg(v_inst_676_, v_inst_677_, v_inst_678_, v_inst_679_, v_m_680_, v_k_681_);
v_r_683_ = lean_box(v_res_682_);
return v_r_683_;
}
}
LEAN_EXPORT uint8_t l_Lean_DeclKeyedMap_contains(lean_object* v_00_u03ba_684_, lean_object* v_00_u03b1_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_m_690_, lean_object* v_k_691_){
_start:
{
uint8_t v___x_692_; 
v___x_692_ = l_Lean_DeclKeyedMap_contains___redArg(v_inst_686_, v_inst_687_, v_inst_688_, v_inst_689_, v_m_690_, v_k_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_contains___boxed(lean_object* v_00_u03ba_693_, lean_object* v_00_u03b1_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_m_699_, lean_object* v_k_700_){
_start:
{
uint8_t v_res_701_; lean_object* v_r_702_; 
v_res_701_ = l_Lean_DeclKeyedMap_contains(v_00_u03ba_693_, v_00_u03b1_694_, v_inst_695_, v_inst_696_, v_inst_697_, v_inst_698_, v_m_699_, v_k_700_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_insert___redArg(lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_m_705_, lean_object* v_k_706_, lean_object* v_v_707_){
_start:
{
lean_object* v_imported_708_; lean_object* v_removed_709_; lean_object* v_added_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_719_; 
v_imported_708_ = lean_ctor_get(v_m_705_, 0);
v_removed_709_ = lean_ctor_get(v_m_705_, 1);
v_added_710_ = lean_ctor_get(v_m_705_, 2);
v_isSharedCheck_719_ = !lean_is_exclusive(v_m_705_);
if (v_isSharedCheck_719_ == 0)
{
v___x_712_ = v_m_705_;
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_added_710_);
lean_inc(v_removed_709_);
lean_inc(v_imported_708_);
lean_dec(v_m_705_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
lean_inc(v_k_706_);
lean_inc_ref(v_inst_704_);
lean_inc_ref(v_inst_703_);
v___x_714_ = l_Lean_PersistentHashMap_erase___redArg(v_inst_703_, v_inst_704_, v_removed_709_, v_k_706_);
v___x_715_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_703_, v_inst_704_, v_added_710_, v_k_706_, v_v_707_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 2, v___x_715_);
lean_ctor_set(v___x_712_, 1, v___x_714_);
v___x_717_ = v___x_712_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_imported_708_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_insert(lean_object* v_00_u03ba_720_, lean_object* v_00_u03b1_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_m_724_, lean_object* v_k_725_, lean_object* v_v_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_DeclKeyedMap_insert___redArg(v_inst_722_, v_inst_723_, v_m_724_, v_k_725_, v_v_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_erase___redArg(lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_m_732_, lean_object* v_k_733_){
_start:
{
lean_object* v_imported_734_; lean_object* v_removed_735_; lean_object* v_added_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_749_; 
v_imported_734_ = lean_ctor_get(v_m_732_, 0);
v_removed_735_ = lean_ctor_get(v_m_732_, 1);
v_added_736_ = lean_ctor_get(v_m_732_, 2);
v_isSharedCheck_749_ = !lean_is_exclusive(v_m_732_);
if (v_isSharedCheck_749_ == 0)
{
v___x_738_ = v_m_732_;
v_isShared_739_ = v_isSharedCheck_749_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_added_736_);
lean_inc(v_removed_735_);
lean_inc(v_imported_734_);
lean_dec(v_m_732_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_749_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___y_741_; uint8_t v___x_746_; 
lean_inc(v_k_733_);
lean_inc_ref(v_inst_729_);
lean_inc_ref(v_inst_728_);
v___x_746_ = l_Lean_ImportedDeclKeyedMap_contains___redArg(v_inst_728_, v_inst_729_, v_inst_730_, v_inst_731_, v_imported_734_, v_k_733_);
if (v___x_746_ == 0)
{
v___y_741_ = v_removed_735_;
goto v___jp_740_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_box(0);
lean_inc(v_k_733_);
lean_inc_ref(v_inst_729_);
lean_inc_ref(v_inst_728_);
v___x_748_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_728_, v_inst_729_, v_removed_735_, v_k_733_, v___x_747_);
v___y_741_ = v___x_748_;
goto v___jp_740_;
}
v___jp_740_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = l_Lean_PersistentHashMap_erase___redArg(v_inst_728_, v_inst_729_, v_added_736_, v_k_733_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 2, v___x_742_);
lean_ctor_set(v___x_738_, 1, v___y_741_);
v___x_744_ = v___x_738_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_imported_734_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___y_741_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_erase(lean_object* v_00_u03ba_750_, lean_object* v_00_u03b1_751_, lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_m_756_, lean_object* v_k_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_DeclKeyedMap_erase___redArg(v_inst_752_, v_inst_753_, v_inst_754_, v_inst_755_, v_m_756_, v_k_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_foldM___redArg___lam__0(lean_object* v_inst_759_, lean_object* v_f_760_, lean_object* v_added_761_, lean_object* v_b_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_759_, v_f_760_, v_added_761_, v_b_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_foldM___redArg___lam__1(lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_removed_766_, lean_object* v_added_767_, lean_object* v_f_768_, lean_object* v_toPure_769_, lean_object* v_b_770_, lean_object* v_k_771_, lean_object* v_v_772_){
_start:
{
uint8_t v___x_773_; 
lean_inc(v_k_771_);
lean_inc_ref(v_inst_765_);
lean_inc_ref(v_inst_764_);
v___x_773_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_764_, v_inst_765_, v_removed_766_, v_k_771_);
if (v___x_773_ == 0)
{
uint8_t v___x_774_; 
lean_inc(v_k_771_);
v___x_774_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_764_, v_inst_765_, v_added_767_, v_k_771_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_dec(v_toPure_769_);
v___x_775_ = lean_apply_3(v_f_768_, v_b_770_, v_k_771_, v_v_772_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; 
lean_dec(v_v_772_);
lean_dec(v_k_771_);
lean_dec(v_f_768_);
v___x_776_ = lean_apply_2(v_toPure_769_, lean_box(0), v_b_770_);
return v___x_776_;
}
}
else
{
lean_object* v___x_777_; 
lean_dec(v_v_772_);
lean_dec(v_k_771_);
lean_dec(v_f_768_);
lean_dec_ref(v_added_767_);
lean_dec_ref(v_inst_765_);
lean_dec_ref(v_inst_764_);
v___x_777_ = lean_apply_2(v_toPure_769_, lean_box(0), v_b_770_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_foldM___redArg(lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_f_782_, lean_object* v_init_783_, lean_object* v_d_784_){
_start:
{
lean_object* v_toApplicative_785_; lean_object* v_toBind_786_; lean_object* v_toPure_787_; lean_object* v_imported_788_; lean_object* v_removed_789_; lean_object* v_added_790_; lean_object* v___f_791_; lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_toApplicative_785_ = lean_ctor_get(v_inst_781_, 0);
v_toBind_786_ = lean_ctor_get(v_inst_781_, 1);
lean_inc(v_toBind_786_);
v_toPure_787_ = lean_ctor_get(v_toApplicative_785_, 1);
v_imported_788_ = lean_ctor_get(v_d_784_, 0);
lean_inc_ref(v_imported_788_);
v_removed_789_ = lean_ctor_get(v_d_784_, 1);
lean_inc_ref(v_removed_789_);
v_added_790_ = lean_ctor_get(v_d_784_, 2);
lean_inc_ref_n(v_added_790_, 2);
lean_dec_ref(v_d_784_);
lean_inc(v_f_782_);
lean_inc_ref(v_inst_781_);
v___f_791_ = lean_alloc_closure((void*)(l_Lean_DeclKeyedMap_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_791_, 0, v_inst_781_);
lean_closure_set(v___f_791_, 1, v_f_782_);
lean_closure_set(v___f_791_, 2, v_added_790_);
lean_inc(v_toPure_787_);
lean_inc_ref(v_inst_779_);
lean_inc_ref(v_inst_778_);
v___f_792_ = lean_alloc_closure((void*)(l_Lean_DeclKeyedMap_foldM___redArg___lam__1), 9, 6);
lean_closure_set(v___f_792_, 0, v_inst_778_);
lean_closure_set(v___f_792_, 1, v_inst_779_);
lean_closure_set(v___f_792_, 2, v_removed_789_);
lean_closure_set(v___f_792_, 3, v_added_790_);
lean_closure_set(v___f_792_, 4, v_f_782_);
lean_closure_set(v___f_792_, 5, v_toPure_787_);
v___x_793_ = l_Lean_ImportedDeclKeyedMap_foldM___redArg(v_inst_778_, v_inst_779_, v_inst_780_, v_inst_781_, v___f_792_, v_init_783_, v_imported_788_);
v___x_794_ = lean_apply_4(v_toBind_786_, lean_box(0), lean_box(0), v___x_793_, v___f_791_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_foldM(lean_object* v_00_u03ba_795_, lean_object* v_00_u03b1_796_, lean_object* v_inst_797_, lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_m_800_, lean_object* v_00_u03b2_801_, lean_object* v_inst_802_, lean_object* v_f_803_, lean_object* v_init_804_, lean_object* v_d_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_DeclKeyedMap_foldM___redArg(v_inst_797_, v_inst_798_, v_inst_799_, v_inst_802_, v_f_803_, v_init_804_, v_d_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_fold___redArg___lam__0(lean_object* v_f_807_, lean_object* v_x1_808_, lean_object* v_x2_809_, lean_object* v_x3_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = lean_apply_3(v_f_807_, v_x1_808_, v_x2_809_, v_x3_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_fold___redArg(lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_f_815_, lean_object* v_init_816_, lean_object* v_d_817_){
_start:
{
lean_object* v___f_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___f_818_ = lean_alloc_closure((void*)(l_Lean_DeclKeyedMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_818_, 0, v_f_815_);
v___x_819_ = ((lean_object*)(l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__10));
v___x_820_ = l_Lean_DeclKeyedMap_foldM___redArg(v_inst_812_, v_inst_813_, v_inst_814_, v___x_819_, v___f_818_, v_init_816_, v_d_817_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_fold(lean_object* v_00_u03ba_821_, lean_object* v_00_u03b1_822_, lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_00_u03b2_826_, lean_object* v_f_827_, lean_object* v_init_828_, lean_object* v_d_829_){
_start:
{
lean_object* v___f_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___f_830_ = lean_alloc_closure((void*)(l_Lean_DeclKeyedMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_830_, 0, v_f_827_);
v___x_831_ = ((lean_object*)(l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__10));
v___x_832_ = l_Lean_DeclKeyedMap_foldM___redArg(v_inst_823_, v_inst_824_, v_inst_825_, v___x_831_, v___f_830_, v_init_828_, v_d_829_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_toList___redArg___lam__0(lean_object* v_x1_833_, lean_object* v_x2_834_, lean_object* v_x3_835_){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v_x2_834_);
lean_ctor_set(v___x_836_, 1, v_x3_835_);
v___x_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v_x1_833_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_toList___redArg(lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_d_842_){
_start:
{
lean_object* v___f_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___f_843_ = ((lean_object*)(l_Lean_DeclKeyedMap_toList___redArg___closed__0));
v___x_844_ = lean_box(0);
v___x_845_ = ((lean_object*)(l_Lean_ImportedDeclKeyedMap_sortOwned___redArg___closed__10));
v___x_846_ = l_Lean_DeclKeyedMap_foldM___redArg(v_inst_839_, v_inst_840_, v_inst_841_, v___x_845_, v___f_843_, v___x_844_, v_d_842_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_toList(lean_object* v_00_u03ba_847_, lean_object* v_00_u03b1_848_, lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_d_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_DeclKeyedMap_toList___redArg(v_inst_849_, v_inst_850_, v_inst_851_, v_d_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___lam__0(lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = ((lean_object*)(l_Lean_DeclKeyedMap_isEmpty___redArg___lam__0___closed__0));
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___lam__0___boxed(lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_DeclKeyedMap_isEmpty___redArg___lam__0(v_x_860_, v_x_861_, v_x_862_);
lean_dec(v_x_862_);
lean_dec(v_x_861_);
return v_res_863_;
}
}
LEAN_EXPORT uint8_t l_Lean_DeclKeyedMap_isEmpty___redArg(lean_object* v_inst_884_, lean_object* v_inst_885_, lean_object* v_inst_886_, lean_object* v_d_887_){
_start:
{
lean_object* v___f_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___f_888_ = ((lean_object*)(l_Lean_DeclKeyedMap_isEmpty___redArg___closed__0));
v___x_889_ = ((lean_object*)(l_Lean_DeclKeyedMap_isEmpty___redArg___closed__10));
v___x_890_ = lean_box(0);
v___x_891_ = l_Lean_DeclKeyedMap_foldM___redArg(v_inst_884_, v_inst_885_, v_inst_886_, v___x_889_, v___f_888_, v___x_890_, v_d_887_);
if (lean_obj_tag(v___x_891_) == 1)
{
uint8_t v___x_892_; 
lean_dec_ref_known(v___x_891_, 1);
v___x_892_ = 1;
return v___x_892_;
}
else
{
uint8_t v___x_893_; 
lean_dec(v___x_891_);
v___x_893_ = 0;
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_isEmpty___redArg___boxed(lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_d_897_){
_start:
{
uint8_t v_res_898_; lean_object* v_r_899_; 
v_res_898_ = l_Lean_DeclKeyedMap_isEmpty___redArg(v_inst_894_, v_inst_895_, v_inst_896_, v_d_897_);
v_r_899_ = lean_box(v_res_898_);
return v_r_899_;
}
}
LEAN_EXPORT uint8_t l_Lean_DeclKeyedMap_isEmpty(lean_object* v_00_u03ba_900_, lean_object* v_00_u03b1_901_, lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_d_905_){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = l_Lean_DeclKeyedMap_isEmpty___redArg(v_inst_902_, v_inst_903_, v_inst_904_, v_d_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclKeyedMap_isEmpty___boxed(lean_object* v_00_u03ba_907_, lean_object* v_00_u03b1_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_inst_911_, lean_object* v_d_912_){
_start:
{
uint8_t v_res_913_; lean_object* v_r_914_; 
v_res_913_ = l_Lean_DeclKeyedMap_isEmpty(v_00_u03ba_907_, v_00_u03b1_908_, v_inst_909_, v_inst_910_, v_inst_911_, v_d_912_);
v_r_914_ = lean_box(v_res_913_);
return v_r_914_;
}
}
lean_object* runtime_initialize_Lean_ResolveName(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_QSort(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DeclKeyedMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_ResolveName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_QSort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DeclKeyedMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_ResolveName(uint8_t builtin);
lean_object* initialize_Init_Data_Array_QSort(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DeclKeyedMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ResolveName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_QSort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DeclKeyedMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DeclKeyedMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DeclKeyedMap(builtin);
}
#ifdef __cplusplus
}
#endif
