// Lean compiler output
// Module: Lean.Data.NameMap.Basic
// Imports: public import Std.Data.HashSet.Basic public import Std.Data.TreeSet.Basic public import Lean.Data.SSet public import Lean.Data.Name
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
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link2___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofArray___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_TreeSet_instForInOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_AssocList_length___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
uint8_t l_Lean_SMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec___boxed(lean_object*, lean_object*);
lean_object* l_Std_TreeMap_instRepr___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofList___redArg(lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNameMap(lean_object*);
static const lean_closure_object l_Lean_NameMap_instRepr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_reprPrec___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_instRepr___redArg___closed__0 = (const lean_object*)&l_Lean_NameMap_instRepr___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameMap_contains___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameMap_contains(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_filter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_NameSet_instEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_NameSet_instInhabited;
LEAN_EXPORT lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad(lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameSet_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_append, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSet_instAppend___closed__0 = (const lean_object*)&l_Lean_NameSet_instAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_NameSet_instAppend = (const lean_object*)&l_Lean_NameSet_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameSet_instSingletonName___lam__0(lean_object*);
static const lean_closure_object l_Lean_NameSet_instSingletonName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_instSingletonName___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSet_instSingletonName___closed__0 = (const lean_object*)&l_Lean_NameSet_instSingletonName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_NameSet_instSingletonName = (const lean_object*)&l_Lean_NameSet_instSingletonName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_NameSet_instUnion = (const lean_object*)&l_Lean_NameSet_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameSet_instInter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_instInter___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSet_instInter___closed__0 = (const lean_object*)&l_Lean_NameSet_instInter___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_NameSet_instInter = (const lean_object*)&l_Lean_NameSet_instInter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameSet_instSDiff___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameSet_instSDiff___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSet_instSDiff___lam__1___closed__0 = (const lean_object*)&l_Lean_NameSet_instSDiff___lam__1___closed__0_value;
static const lean_closure_object l_Lean_NameSet_instSDiff___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_instSDiff___lam__0, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_NameSet_instSDiff___lam__1___closed__0_value)} };
static const lean_object* l_Lean_NameSet_instSDiff___lam__1___closed__1 = (const lean_object*)&l_Lean_NameSet_instSDiff___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_NameSet_instSDiff___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameSet_instSDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_instSDiff___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSet_instSDiff___closed__0 = (const lean_object*)&l_Lean_NameSet_instSDiff___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_NameSet_instSDiff = (const lean_object*)&l_Lean_NameSet_instSDiff___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_filter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_ofArray___boxed(lean_object*);
static const lean_closure_object l_Lean_NameSSet_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSSet_empty___closed__0 = (const lean_object*)&l_Lean_NameSSet_empty___closed__0_value;
static const lean_closure_object l_Lean_NameSSet_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSSet_empty___closed__1 = (const lean_object*)&l_Lean_NameSSet_empty___closed__1_value;
static lean_once_cell_t l_Lean_NameSSet_empty___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_NameSSet_empty___closed__2;
LEAN_EXPORT lean_object* l_Lean_NameSSet_empty;
LEAN_EXPORT lean_object* l_Lean_NameSSet_instEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_NameSSet_instInhabited;
LEAN_EXPORT lean_object* l_Lean_NameSSet_insert(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameSSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSSet_contains___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_NameHashSet_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_NameHashSet_empty___closed__0;
static lean_once_cell_t l_Lean_NameHashSet_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_NameHashSet_empty___closed__1;
LEAN_EXPORT lean_object* l_Lean_NameHashSet_empty;
LEAN_EXPORT lean_object* l_Lean_NameHashSet_instEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_NameHashSet_instInhabited;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_filter(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isPrefixOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isSuffixOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNameMap(lean_object* v_00_u03b1_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(1);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___redArg(lean_object* v_inst_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = ((lean_object*)(l_Lean_NameMap_instRepr___redArg___closed__0));
v___x_6_ = l_Std_TreeMap_instRepr___redArg(v___x_5_, v_inst_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr(lean_object* v_00_u03b1_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_NameMap_instRepr___redArg(v_inst_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instEmptyCollection(lean_object* v_00_u03b1_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(1);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInhabited(lean_object* v_00_u03b1_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_box(1);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object* v_k_14_, lean_object* v_v_15_, lean_object* v_t_16_){
_start:
{
if (lean_obj_tag(v_t_16_) == 0)
{
lean_object* v_size_17_; lean_object* v_k_18_; lean_object* v_v_19_; lean_object* v_l_20_; lean_object* v_r_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_301_; 
v_size_17_ = lean_ctor_get(v_t_16_, 0);
v_k_18_ = lean_ctor_get(v_t_16_, 1);
v_v_19_ = lean_ctor_get(v_t_16_, 2);
v_l_20_ = lean_ctor_get(v_t_16_, 3);
v_r_21_ = lean_ctor_get(v_t_16_, 4);
v_isSharedCheck_301_ = !lean_is_exclusive(v_t_16_);
if (v_isSharedCheck_301_ == 0)
{
v___x_23_ = v_t_16_;
v_isShared_24_ = v_isSharedCheck_301_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_r_21_);
lean_inc(v_l_20_);
lean_inc(v_v_19_);
lean_inc(v_k_18_);
lean_inc(v_size_17_);
lean_dec(v_t_16_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_301_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
uint8_t v___x_25_; 
v___x_25_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_14_, v_k_18_);
switch(v___x_25_)
{
case 0:
{
lean_object* v_impl_26_; lean_object* v___x_27_; 
lean_dec(v_size_17_);
v_impl_26_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_14_, v_v_15_, v_l_20_);
v___x_27_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_21_) == 0)
{
lean_object* v_size_28_; lean_object* v_size_29_; lean_object* v_k_30_; lean_object* v_v_31_; lean_object* v_l_32_; lean_object* v_r_33_; lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v_size_28_ = lean_ctor_get(v_r_21_, 0);
v_size_29_ = lean_ctor_get(v_impl_26_, 0);
lean_inc(v_size_29_);
v_k_30_ = lean_ctor_get(v_impl_26_, 1);
lean_inc(v_k_30_);
v_v_31_ = lean_ctor_get(v_impl_26_, 2);
lean_inc(v_v_31_);
v_l_32_ = lean_ctor_get(v_impl_26_, 3);
lean_inc(v_l_32_);
v_r_33_ = lean_ctor_get(v_impl_26_, 4);
lean_inc(v_r_33_);
v___x_34_ = lean_unsigned_to_nat(3u);
v___x_35_ = lean_nat_mul(v___x_34_, v_size_28_);
v___x_36_ = lean_nat_dec_lt(v___x_35_, v_size_29_);
lean_dec(v___x_35_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
lean_dec(v_r_33_);
lean_dec(v_l_32_);
lean_dec(v_v_31_);
lean_dec(v_k_30_);
v___x_37_ = lean_nat_add(v___x_27_, v_size_29_);
lean_dec(v_size_29_);
v___x_38_ = lean_nat_add(v___x_37_, v_size_28_);
lean_dec(v___x_37_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 3, v_impl_26_);
lean_ctor_set(v___x_23_, 0, v___x_38_);
v___x_40_ = v___x_23_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v_k_18_);
lean_ctor_set(v_reuseFailAlloc_41_, 2, v_v_19_);
lean_ctor_set(v_reuseFailAlloc_41_, 3, v_impl_26_);
lean_ctor_set(v_reuseFailAlloc_41_, 4, v_r_21_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
else
{
lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_107_; 
v_isSharedCheck_107_ = !lean_is_exclusive(v_impl_26_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; lean_object* v_unused_109_; lean_object* v_unused_110_; lean_object* v_unused_111_; lean_object* v_unused_112_; 
v_unused_108_ = lean_ctor_get(v_impl_26_, 4);
lean_dec(v_unused_108_);
v_unused_109_ = lean_ctor_get(v_impl_26_, 3);
lean_dec(v_unused_109_);
v_unused_110_ = lean_ctor_get(v_impl_26_, 2);
lean_dec(v_unused_110_);
v_unused_111_ = lean_ctor_get(v_impl_26_, 1);
lean_dec(v_unused_111_);
v_unused_112_ = lean_ctor_get(v_impl_26_, 0);
lean_dec(v_unused_112_);
v___x_43_ = v_impl_26_;
v_isShared_44_ = v_isSharedCheck_107_;
goto v_resetjp_42_;
}
else
{
lean_dec(v_impl_26_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_107_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v_size_45_; lean_object* v_size_46_; lean_object* v_k_47_; lean_object* v_v_48_; lean_object* v_l_49_; lean_object* v_r_50_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v_size_45_ = lean_ctor_get(v_l_32_, 0);
v_size_46_ = lean_ctor_get(v_r_33_, 0);
v_k_47_ = lean_ctor_get(v_r_33_, 1);
v_v_48_ = lean_ctor_get(v_r_33_, 2);
v_l_49_ = lean_ctor_get(v_r_33_, 3);
v_r_50_ = lean_ctor_get(v_r_33_, 4);
v___x_51_ = lean_unsigned_to_nat(2u);
v___x_52_ = lean_nat_mul(v___x_51_, v_size_45_);
v___x_53_ = lean_nat_dec_lt(v_size_46_, v___x_52_);
lean_dec(v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_82_; 
lean_inc(v_r_50_);
lean_inc(v_l_49_);
lean_inc(v_v_48_);
lean_inc(v_k_47_);
v_isSharedCheck_82_ = !lean_is_exclusive(v_r_33_);
if (v_isSharedCheck_82_ == 0)
{
lean_object* v_unused_83_; lean_object* v_unused_84_; lean_object* v_unused_85_; lean_object* v_unused_86_; lean_object* v_unused_87_; 
v_unused_83_ = lean_ctor_get(v_r_33_, 4);
lean_dec(v_unused_83_);
v_unused_84_ = lean_ctor_get(v_r_33_, 3);
lean_dec(v_unused_84_);
v_unused_85_ = lean_ctor_get(v_r_33_, 2);
lean_dec(v_unused_85_);
v_unused_86_ = lean_ctor_get(v_r_33_, 1);
lean_dec(v_unused_86_);
v_unused_87_ = lean_ctor_get(v_r_33_, 0);
lean_dec(v_unused_87_);
v___x_55_ = v_r_33_;
v_isShared_56_ = v_isSharedCheck_82_;
goto v_resetjp_54_;
}
else
{
lean_dec(v_r_33_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_82_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___y_60_; lean_object* v___y_61_; lean_object* v___y_62_; lean_object* v___x_70_; lean_object* v___y_72_; 
v___x_57_ = lean_nat_add(v___x_27_, v_size_29_);
lean_dec(v_size_29_);
v___x_58_ = lean_nat_add(v___x_57_, v_size_28_);
lean_dec(v___x_57_);
v___x_70_ = lean_nat_add(v___x_27_, v_size_45_);
if (lean_obj_tag(v_l_49_) == 0)
{
lean_object* v_size_80_; 
v_size_80_ = lean_ctor_get(v_l_49_, 0);
lean_inc(v_size_80_);
v___y_72_ = v_size_80_;
goto v___jp_71_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_unsigned_to_nat(0u);
v___y_72_ = v___x_81_;
goto v___jp_71_;
}
v___jp_59_:
{
lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_63_ = lean_nat_add(v___y_61_, v___y_62_);
lean_dec(v___y_62_);
lean_dec(v___y_61_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 4, v_r_21_);
lean_ctor_set(v___x_55_, 3, v_r_50_);
lean_ctor_set(v___x_55_, 2, v_v_19_);
lean_ctor_set(v___x_55_, 1, v_k_18_);
lean_ctor_set(v___x_55_, 0, v___x_63_);
v___x_65_ = v___x_55_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_k_18_);
lean_ctor_set(v_reuseFailAlloc_69_, 2, v_v_19_);
lean_ctor_set(v_reuseFailAlloc_69_, 3, v_r_50_);
lean_ctor_set(v_reuseFailAlloc_69_, 4, v_r_21_);
v___x_65_ = v_reuseFailAlloc_69_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
lean_object* v___x_67_; 
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 4, v___x_65_);
lean_ctor_set(v___x_43_, 3, v___y_60_);
lean_ctor_set(v___x_43_, 2, v_v_48_);
lean_ctor_set(v___x_43_, 1, v_k_47_);
lean_ctor_set(v___x_43_, 0, v___x_58_);
v___x_67_ = v___x_43_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_k_47_);
lean_ctor_set(v_reuseFailAlloc_68_, 2, v_v_48_);
lean_ctor_set(v_reuseFailAlloc_68_, 3, v___y_60_);
lean_ctor_set(v_reuseFailAlloc_68_, 4, v___x_65_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
v___jp_71_:
{
lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_73_ = lean_nat_add(v___x_70_, v___y_72_);
lean_dec(v___y_72_);
lean_dec(v___x_70_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 4, v_l_49_);
lean_ctor_set(v___x_23_, 3, v_l_32_);
lean_ctor_set(v___x_23_, 2, v_v_31_);
lean_ctor_set(v___x_23_, 1, v_k_30_);
lean_ctor_set(v___x_23_, 0, v___x_73_);
v___x_75_ = v___x_23_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_k_30_);
lean_ctor_set(v_reuseFailAlloc_79_, 2, v_v_31_);
lean_ctor_set(v_reuseFailAlloc_79_, 3, v_l_32_);
lean_ctor_set(v_reuseFailAlloc_79_, 4, v_l_49_);
v___x_75_ = v_reuseFailAlloc_79_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; 
v___x_76_ = lean_nat_add(v___x_27_, v_size_28_);
if (lean_obj_tag(v_r_50_) == 0)
{
lean_object* v_size_77_; 
v_size_77_ = lean_ctor_get(v_r_50_, 0);
lean_inc(v_size_77_);
v___y_60_ = v___x_75_;
v___y_61_ = v___x_76_;
v___y_62_ = v_size_77_;
goto v___jp_59_;
}
else
{
lean_object* v___x_78_; 
v___x_78_ = lean_unsigned_to_nat(0u);
v___y_60_ = v___x_75_;
v___y_61_ = v___x_76_;
v___y_62_ = v___x_78_;
goto v___jp_59_;
}
}
}
}
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
lean_del_object(v___x_23_);
v___x_88_ = lean_nat_add(v___x_27_, v_size_29_);
lean_dec(v_size_29_);
v___x_89_ = lean_nat_add(v___x_88_, v_size_28_);
lean_dec(v___x_88_);
v___x_90_ = lean_nat_add(v___x_27_, v_size_28_);
v___x_91_ = lean_nat_add(v___x_90_, v_size_46_);
lean_dec(v___x_90_);
lean_inc_ref(v_r_21_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 4, v_r_21_);
lean_ctor_set(v___x_43_, 3, v_r_33_);
lean_ctor_set(v___x_43_, 2, v_v_19_);
lean_ctor_set(v___x_43_, 1, v_k_18_);
lean_ctor_set(v___x_43_, 0, v___x_91_);
v___x_93_ = v___x_43_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_k_18_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v_v_19_);
lean_ctor_set(v_reuseFailAlloc_106_, 3, v_r_33_);
lean_ctor_set(v_reuseFailAlloc_106_, 4, v_r_21_);
v___x_93_ = v_reuseFailAlloc_106_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
v_isSharedCheck_100_ = !lean_is_exclusive(v_r_21_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; lean_object* v_unused_102_; lean_object* v_unused_103_; lean_object* v_unused_104_; lean_object* v_unused_105_; 
v_unused_101_ = lean_ctor_get(v_r_21_, 4);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v_r_21_, 3);
lean_dec(v_unused_102_);
v_unused_103_ = lean_ctor_get(v_r_21_, 2);
lean_dec(v_unused_103_);
v_unused_104_ = lean_ctor_get(v_r_21_, 1);
lean_dec(v_unused_104_);
v_unused_105_ = lean_ctor_get(v_r_21_, 0);
lean_dec(v_unused_105_);
v___x_95_ = v_r_21_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_dec(v_r_21_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 4, v___x_93_);
lean_ctor_set(v___x_95_, 3, v_l_32_);
lean_ctor_set(v___x_95_, 2, v_v_31_);
lean_ctor_set(v___x_95_, 1, v_k_30_);
lean_ctor_set(v___x_95_, 0, v___x_89_);
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_k_30_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v_v_31_);
lean_ctor_set(v_reuseFailAlloc_99_, 3, v_l_32_);
lean_ctor_set(v_reuseFailAlloc_99_, 4, v___x_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_113_; 
v_l_113_ = lean_ctor_get(v_impl_26_, 3);
lean_inc(v_l_113_);
if (lean_obj_tag(v_l_113_) == 0)
{
lean_object* v_r_114_; lean_object* v_k_115_; lean_object* v_v_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_127_; 
v_r_114_ = lean_ctor_get(v_impl_26_, 4);
v_k_115_ = lean_ctor_get(v_impl_26_, 1);
v_v_116_ = lean_ctor_get(v_impl_26_, 2);
v_isSharedCheck_127_ = !lean_is_exclusive(v_impl_26_);
if (v_isSharedCheck_127_ == 0)
{
lean_object* v_unused_128_; lean_object* v_unused_129_; 
v_unused_128_ = lean_ctor_get(v_impl_26_, 3);
lean_dec(v_unused_128_);
v_unused_129_ = lean_ctor_get(v_impl_26_, 0);
lean_dec(v_unused_129_);
v___x_118_ = v_impl_26_;
v_isShared_119_ = v_isSharedCheck_127_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_r_114_);
lean_inc(v_v_116_);
lean_inc(v_k_115_);
lean_dec(v_impl_26_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_127_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_120_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_114_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 3, v_r_114_);
lean_ctor_set(v___x_118_, 2, v_v_19_);
lean_ctor_set(v___x_118_, 1, v_k_18_);
lean_ctor_set(v___x_118_, 0, v___x_27_);
v___x_122_ = v___x_118_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_k_18_);
lean_ctor_set(v_reuseFailAlloc_126_, 2, v_v_19_);
lean_ctor_set(v_reuseFailAlloc_126_, 3, v_r_114_);
lean_ctor_set(v_reuseFailAlloc_126_, 4, v_r_114_);
v___x_122_ = v_reuseFailAlloc_126_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_124_; 
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 4, v___x_122_);
lean_ctor_set(v___x_23_, 3, v_l_113_);
lean_ctor_set(v___x_23_, 2, v_v_116_);
lean_ctor_set(v___x_23_, 1, v_k_115_);
lean_ctor_set(v___x_23_, 0, v___x_120_);
v___x_124_ = v___x_23_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_k_115_);
lean_ctor_set(v_reuseFailAlloc_125_, 2, v_v_116_);
lean_ctor_set(v_reuseFailAlloc_125_, 3, v_l_113_);
lean_ctor_set(v_reuseFailAlloc_125_, 4, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
else
{
lean_object* v_r_130_; 
v_r_130_ = lean_ctor_get(v_impl_26_, 4);
lean_inc(v_r_130_);
if (lean_obj_tag(v_r_130_) == 0)
{
lean_object* v_k_131_; lean_object* v_v_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_155_; 
v_k_131_ = lean_ctor_get(v_impl_26_, 1);
v_v_132_ = lean_ctor_get(v_impl_26_, 2);
v_isSharedCheck_155_ = !lean_is_exclusive(v_impl_26_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; lean_object* v_unused_157_; lean_object* v_unused_158_; 
v_unused_156_ = lean_ctor_get(v_impl_26_, 4);
lean_dec(v_unused_156_);
v_unused_157_ = lean_ctor_get(v_impl_26_, 3);
lean_dec(v_unused_157_);
v_unused_158_ = lean_ctor_get(v_impl_26_, 0);
lean_dec(v_unused_158_);
v___x_134_ = v_impl_26_;
v_isShared_135_ = v_isSharedCheck_155_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_v_132_);
lean_inc(v_k_131_);
lean_dec(v_impl_26_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_155_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v_k_136_; lean_object* v_v_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_151_; 
v_k_136_ = lean_ctor_get(v_r_130_, 1);
v_v_137_ = lean_ctor_get(v_r_130_, 2);
v_isSharedCheck_151_ = !lean_is_exclusive(v_r_130_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; lean_object* v_unused_153_; lean_object* v_unused_154_; 
v_unused_152_ = lean_ctor_get(v_r_130_, 4);
lean_dec(v_unused_152_);
v_unused_153_ = lean_ctor_get(v_r_130_, 3);
lean_dec(v_unused_153_);
v_unused_154_ = lean_ctor_get(v_r_130_, 0);
lean_dec(v_unused_154_);
v___x_139_ = v_r_130_;
v_isShared_140_ = v_isSharedCheck_151_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_v_137_);
lean_inc(v_k_136_);
lean_dec(v_r_130_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_151_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_141_ = lean_unsigned_to_nat(3u);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 4, v_l_113_);
lean_ctor_set(v___x_139_, 3, v_l_113_);
lean_ctor_set(v___x_139_, 2, v_v_132_);
lean_ctor_set(v___x_139_, 1, v_k_131_);
lean_ctor_set(v___x_139_, 0, v___x_27_);
v___x_143_ = v___x_139_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_k_131_);
lean_ctor_set(v_reuseFailAlloc_150_, 2, v_v_132_);
lean_ctor_set(v_reuseFailAlloc_150_, 3, v_l_113_);
lean_ctor_set(v_reuseFailAlloc_150_, 4, v_l_113_);
v___x_143_ = v_reuseFailAlloc_150_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_145_; 
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 4, v_l_113_);
lean_ctor_set(v___x_134_, 2, v_v_19_);
lean_ctor_set(v___x_134_, 1, v_k_18_);
lean_ctor_set(v___x_134_, 0, v___x_27_);
v___x_145_ = v___x_134_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_k_18_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v_v_19_);
lean_ctor_set(v_reuseFailAlloc_149_, 3, v_l_113_);
lean_ctor_set(v_reuseFailAlloc_149_, 4, v_l_113_);
v___x_145_ = v_reuseFailAlloc_149_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_147_; 
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 4, v___x_145_);
lean_ctor_set(v___x_23_, 3, v___x_143_);
lean_ctor_set(v___x_23_, 2, v_v_137_);
lean_ctor_set(v___x_23_, 1, v_k_136_);
lean_ctor_set(v___x_23_, 0, v___x_141_);
v___x_147_ = v___x_23_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_k_136_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_v_137_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_148_, 4, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
}
else
{
lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_159_ = lean_unsigned_to_nat(2u);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 4, v_r_130_);
lean_ctor_set(v___x_23_, 3, v_impl_26_);
lean_ctor_set(v___x_23_, 0, v___x_159_);
v___x_161_ = v___x_23_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_159_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_k_18_);
lean_ctor_set(v_reuseFailAlloc_162_, 2, v_v_19_);
lean_ctor_set(v_reuseFailAlloc_162_, 3, v_impl_26_);
lean_ctor_set(v_reuseFailAlloc_162_, 4, v_r_130_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
case 1:
{
lean_object* v___x_164_; 
lean_dec(v_v_19_);
lean_dec(v_k_18_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 2, v_v_15_);
lean_ctor_set(v___x_23_, 1, v_k_14_);
v___x_164_ = v___x_23_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_size_17_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_k_14_);
lean_ctor_set(v_reuseFailAlloc_165_, 2, v_v_15_);
lean_ctor_set(v_reuseFailAlloc_165_, 3, v_l_20_);
lean_ctor_set(v_reuseFailAlloc_165_, 4, v_r_21_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
default: 
{
lean_object* v_impl_166_; lean_object* v___x_167_; 
lean_dec(v_size_17_);
v_impl_166_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_14_, v_v_15_, v_r_21_);
v___x_167_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_20_) == 0)
{
lean_object* v_size_168_; lean_object* v_size_169_; lean_object* v_k_170_; lean_object* v_v_171_; lean_object* v_l_172_; lean_object* v_r_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_size_168_ = lean_ctor_get(v_l_20_, 0);
v_size_169_ = lean_ctor_get(v_impl_166_, 0);
lean_inc(v_size_169_);
v_k_170_ = lean_ctor_get(v_impl_166_, 1);
lean_inc(v_k_170_);
v_v_171_ = lean_ctor_get(v_impl_166_, 2);
lean_inc(v_v_171_);
v_l_172_ = lean_ctor_get(v_impl_166_, 3);
lean_inc(v_l_172_);
v_r_173_ = lean_ctor_get(v_impl_166_, 4);
lean_inc(v_r_173_);
v___x_174_ = lean_unsigned_to_nat(3u);
v___x_175_ = lean_nat_mul(v___x_174_, v_size_168_);
v___x_176_ = lean_nat_dec_lt(v___x_175_, v_size_169_);
lean_dec(v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
lean_dec(v_r_173_);
lean_dec(v_l_172_);
lean_dec(v_v_171_);
lean_dec(v_k_170_);
v___x_177_ = lean_nat_add(v___x_167_, v_size_168_);
v___x_178_ = lean_nat_add(v___x_177_, v_size_169_);
lean_dec(v_size_169_);
lean_dec(v___x_177_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 4, v_impl_166_);
lean_ctor_set(v___x_23_, 0, v___x_178_);
v___x_180_ = v___x_23_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_k_18_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v_v_19_);
lean_ctor_set(v_reuseFailAlloc_181_, 3, v_l_20_);
lean_ctor_set(v_reuseFailAlloc_181_, 4, v_impl_166_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
else
{
lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_245_; 
v_isSharedCheck_245_ = !lean_is_exclusive(v_impl_166_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; lean_object* v_unused_247_; lean_object* v_unused_248_; lean_object* v_unused_249_; lean_object* v_unused_250_; 
v_unused_246_ = lean_ctor_get(v_impl_166_, 4);
lean_dec(v_unused_246_);
v_unused_247_ = lean_ctor_get(v_impl_166_, 3);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_impl_166_, 2);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_impl_166_, 1);
lean_dec(v_unused_249_);
v_unused_250_ = lean_ctor_get(v_impl_166_, 0);
lean_dec(v_unused_250_);
v___x_183_ = v_impl_166_;
v_isShared_184_ = v_isSharedCheck_245_;
goto v_resetjp_182_;
}
else
{
lean_dec(v_impl_166_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_245_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_size_185_; lean_object* v_k_186_; lean_object* v_v_187_; lean_object* v_l_188_; lean_object* v_r_189_; lean_object* v_size_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_size_185_ = lean_ctor_get(v_l_172_, 0);
v_k_186_ = lean_ctor_get(v_l_172_, 1);
v_v_187_ = lean_ctor_get(v_l_172_, 2);
v_l_188_ = lean_ctor_get(v_l_172_, 3);
v_r_189_ = lean_ctor_get(v_l_172_, 4);
v_size_190_ = lean_ctor_get(v_r_173_, 0);
v___x_191_ = lean_unsigned_to_nat(2u);
v___x_192_ = lean_nat_mul(v___x_191_, v_size_190_);
v___x_193_ = lean_nat_dec_lt(v_size_185_, v___x_192_);
lean_dec(v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_221_; 
lean_inc(v_r_189_);
lean_inc(v_l_188_);
lean_inc(v_v_187_);
lean_inc(v_k_186_);
v_isSharedCheck_221_ = !lean_is_exclusive(v_l_172_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; lean_object* v_unused_223_; lean_object* v_unused_224_; lean_object* v_unused_225_; lean_object* v_unused_226_; 
v_unused_222_ = lean_ctor_get(v_l_172_, 4);
lean_dec(v_unused_222_);
v_unused_223_ = lean_ctor_get(v_l_172_, 3);
lean_dec(v_unused_223_);
v_unused_224_ = lean_ctor_get(v_l_172_, 2);
lean_dec(v_unused_224_);
v_unused_225_ = lean_ctor_get(v_l_172_, 1);
lean_dec(v_unused_225_);
v_unused_226_ = lean_ctor_get(v_l_172_, 0);
lean_dec(v_unused_226_);
v___x_195_ = v_l_172_;
v_isShared_196_ = v_isSharedCheck_221_;
goto v_resetjp_194_;
}
else
{
lean_dec(v_l_172_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_221_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___y_211_; 
v___x_197_ = lean_nat_add(v___x_167_, v_size_168_);
v___x_198_ = lean_nat_add(v___x_197_, v_size_169_);
lean_dec(v_size_169_);
if (lean_obj_tag(v_l_188_) == 0)
{
lean_object* v_size_219_; 
v_size_219_ = lean_ctor_get(v_l_188_, 0);
lean_inc(v_size_219_);
v___y_211_ = v_size_219_;
goto v___jp_210_;
}
else
{
lean_object* v___x_220_; 
v___x_220_ = lean_unsigned_to_nat(0u);
v___y_211_ = v___x_220_;
goto v___jp_210_;
}
v___jp_199_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_203_ = lean_nat_add(v___y_200_, v___y_202_);
lean_dec(v___y_202_);
lean_dec(v___y_200_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 4, v_r_173_);
lean_ctor_set(v___x_195_, 3, v_r_189_);
lean_ctor_set(v___x_195_, 2, v_v_171_);
lean_ctor_set(v___x_195_, 1, v_k_170_);
lean_ctor_set(v___x_195_, 0, v___x_203_);
v___x_205_ = v___x_195_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_k_170_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v_v_171_);
lean_ctor_set(v_reuseFailAlloc_209_, 3, v_r_189_);
lean_ctor_set(v_reuseFailAlloc_209_, 4, v_r_173_);
v___x_205_ = v_reuseFailAlloc_209_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_207_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 4, v___x_205_);
lean_ctor_set(v___x_183_, 3, v___y_201_);
lean_ctor_set(v___x_183_, 2, v_v_187_);
lean_ctor_set(v___x_183_, 1, v_k_186_);
lean_ctor_set(v___x_183_, 0, v___x_198_);
v___x_207_ = v___x_183_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_k_186_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v_v_187_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v___y_201_);
lean_ctor_set(v_reuseFailAlloc_208_, 4, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
v___jp_210_:
{
lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_212_ = lean_nat_add(v___x_197_, v___y_211_);
lean_dec(v___y_211_);
lean_dec(v___x_197_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 4, v_l_188_);
lean_ctor_set(v___x_23_, 0, v___x_212_);
v___x_214_ = v___x_23_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_k_18_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v_v_19_);
lean_ctor_set(v_reuseFailAlloc_218_, 3, v_l_20_);
lean_ctor_set(v_reuseFailAlloc_218_, 4, v_l_188_);
v___x_214_ = v_reuseFailAlloc_218_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; 
v___x_215_ = lean_nat_add(v___x_167_, v_size_190_);
if (lean_obj_tag(v_r_189_) == 0)
{
lean_object* v_size_216_; 
v_size_216_ = lean_ctor_get(v_r_189_, 0);
lean_inc(v_size_216_);
v___y_200_ = v___x_215_;
v___y_201_ = v___x_214_;
v___y_202_ = v_size_216_;
goto v___jp_199_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = lean_unsigned_to_nat(0u);
v___y_200_ = v___x_215_;
v___y_201_ = v___x_214_;
v___y_202_ = v___x_217_;
goto v___jp_199_;
}
}
}
}
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
lean_del_object(v___x_23_);
v___x_227_ = lean_nat_add(v___x_167_, v_size_168_);
v___x_228_ = lean_nat_add(v___x_227_, v_size_169_);
lean_dec(v_size_169_);
v___x_229_ = lean_nat_add(v___x_227_, v_size_185_);
lean_dec(v___x_227_);
lean_inc_ref(v_l_20_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 4, v_l_172_);
lean_ctor_set(v___x_183_, 3, v_l_20_);
lean_ctor_set(v___x_183_, 2, v_v_19_);
lean_ctor_set(v___x_183_, 1, v_k_18_);
lean_ctor_set(v___x_183_, 0, v___x_229_);
v___x_231_ = v___x_183_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_k_18_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v_v_19_);
lean_ctor_set(v_reuseFailAlloc_244_, 3, v_l_20_);
lean_ctor_set(v_reuseFailAlloc_244_, 4, v_l_172_);
v___x_231_ = v_reuseFailAlloc_244_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
v_isSharedCheck_238_ = !lean_is_exclusive(v_l_20_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; lean_object* v_unused_240_; lean_object* v_unused_241_; lean_object* v_unused_242_; lean_object* v_unused_243_; 
v_unused_239_ = lean_ctor_get(v_l_20_, 4);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_l_20_, 3);
lean_dec(v_unused_240_);
v_unused_241_ = lean_ctor_get(v_l_20_, 2);
lean_dec(v_unused_241_);
v_unused_242_ = lean_ctor_get(v_l_20_, 1);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_l_20_, 0);
lean_dec(v_unused_243_);
v___x_233_ = v_l_20_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_dec(v_l_20_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 4, v_r_173_);
lean_ctor_set(v___x_233_, 3, v___x_231_);
lean_ctor_set(v___x_233_, 2, v_v_171_);
lean_ctor_set(v___x_233_, 1, v_k_170_);
lean_ctor_set(v___x_233_, 0, v___x_228_);
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_k_170_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_v_171_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_r_173_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_251_; 
v_l_251_ = lean_ctor_get(v_impl_166_, 3);
lean_inc(v_l_251_);
if (lean_obj_tag(v_l_251_) == 0)
{
lean_object* v_r_252_; lean_object* v_k_253_; lean_object* v_v_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_277_; 
v_r_252_ = lean_ctor_get(v_impl_166_, 4);
v_k_253_ = lean_ctor_get(v_impl_166_, 1);
v_v_254_ = lean_ctor_get(v_impl_166_, 2);
v_isSharedCheck_277_ = !lean_is_exclusive(v_impl_166_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; lean_object* v_unused_279_; 
v_unused_278_ = lean_ctor_get(v_impl_166_, 3);
lean_dec(v_unused_278_);
v_unused_279_ = lean_ctor_get(v_impl_166_, 0);
lean_dec(v_unused_279_);
v___x_256_ = v_impl_166_;
v_isShared_257_ = v_isSharedCheck_277_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_r_252_);
lean_inc(v_v_254_);
lean_inc(v_k_253_);
lean_dec(v_impl_166_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_277_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v_k_258_; lean_object* v_v_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_273_; 
v_k_258_ = lean_ctor_get(v_l_251_, 1);
v_v_259_ = lean_ctor_get(v_l_251_, 2);
v_isSharedCheck_273_ = !lean_is_exclusive(v_l_251_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; lean_object* v_unused_275_; lean_object* v_unused_276_; 
v_unused_274_ = lean_ctor_get(v_l_251_, 4);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_l_251_, 3);
lean_dec(v_unused_275_);
v_unused_276_ = lean_ctor_get(v_l_251_, 0);
lean_dec(v_unused_276_);
v___x_261_ = v_l_251_;
v_isShared_262_ = v_isSharedCheck_273_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_v_259_);
lean_inc(v_k_258_);
lean_dec(v_l_251_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_273_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_252_, 2);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 4, v_r_252_);
lean_ctor_set(v___x_261_, 3, v_r_252_);
lean_ctor_set(v___x_261_, 2, v_v_19_);
lean_ctor_set(v___x_261_, 1, v_k_18_);
lean_ctor_set(v___x_261_, 0, v___x_167_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_k_18_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_v_19_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v_r_252_);
lean_ctor_set(v_reuseFailAlloc_272_, 4, v_r_252_);
v___x_265_ = v_reuseFailAlloc_272_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_267_; 
lean_inc(v_r_252_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 3, v_r_252_);
lean_ctor_set(v___x_256_, 0, v___x_167_);
v___x_267_ = v___x_256_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_k_253_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_v_254_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v_r_252_);
lean_ctor_set(v_reuseFailAlloc_271_, 4, v_r_252_);
v___x_267_ = v_reuseFailAlloc_271_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_269_; 
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 4, v___x_267_);
lean_ctor_set(v___x_23_, 3, v___x_265_);
lean_ctor_set(v___x_23_, 2, v_v_259_);
lean_ctor_set(v___x_23_, 1, v_k_258_);
lean_ctor_set(v___x_23_, 0, v___x_263_);
v___x_269_ = v___x_23_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_k_258_);
lean_ctor_set(v_reuseFailAlloc_270_, 2, v_v_259_);
lean_ctor_set(v_reuseFailAlloc_270_, 3, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_270_, 4, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
}
else
{
lean_object* v_r_280_; 
v_r_280_ = lean_ctor_get(v_impl_166_, 4);
lean_inc(v_r_280_);
if (lean_obj_tag(v_r_280_) == 0)
{
lean_object* v_k_281_; lean_object* v_v_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_293_; 
v_k_281_ = lean_ctor_get(v_impl_166_, 1);
v_v_282_ = lean_ctor_get(v_impl_166_, 2);
v_isSharedCheck_293_ = !lean_is_exclusive(v_impl_166_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; lean_object* v_unused_295_; lean_object* v_unused_296_; 
v_unused_294_ = lean_ctor_get(v_impl_166_, 4);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_impl_166_, 3);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_impl_166_, 0);
lean_dec(v_unused_296_);
v___x_284_ = v_impl_166_;
v_isShared_285_ = v_isSharedCheck_293_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_v_282_);
lean_inc(v_k_281_);
lean_dec(v_impl_166_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_293_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_286_ = lean_unsigned_to_nat(3u);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 4, v_l_251_);
lean_ctor_set(v___x_284_, 2, v_v_19_);
lean_ctor_set(v___x_284_, 1, v_k_18_);
lean_ctor_set(v___x_284_, 0, v___x_167_);
v___x_288_ = v___x_284_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_k_18_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_v_19_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_l_251_);
lean_ctor_set(v_reuseFailAlloc_292_, 4, v_l_251_);
v___x_288_ = v_reuseFailAlloc_292_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_290_; 
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 4, v_r_280_);
lean_ctor_set(v___x_23_, 3, v___x_288_);
lean_ctor_set(v___x_23_, 2, v_v_282_);
lean_ctor_set(v___x_23_, 1, v_k_281_);
lean_ctor_set(v___x_23_, 0, v___x_286_);
v___x_290_ = v___x_23_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_k_281_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_v_282_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_r_280_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
else
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_unsigned_to_nat(2u);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 4, v_impl_166_);
lean_ctor_set(v___x_23_, 3, v_r_280_);
lean_ctor_set(v___x_23_, 0, v___x_297_);
v___x_299_ = v___x_23_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_k_18_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v_v_19_);
lean_ctor_set(v_reuseFailAlloc_300_, 3, v_r_280_);
lean_ctor_set(v_reuseFailAlloc_300_, 4, v_impl_166_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v_k_14_);
lean_ctor_set(v___x_303_, 2, v_v_15_);
lean_ctor_set(v___x_303_, 3, v_t_16_);
lean_ctor_set(v___x_303_, 4, v_t_16_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_insert___redArg(lean_object* v_m_304_, lean_object* v_n_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_305_, v_a_306_, v_m_304_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_insert(lean_object* v_00_u03b1_308_, lean_object* v_m_309_, lean_object* v_n_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_310_, v_a_311_, v_m_309_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0(lean_object* v_00_u03b2_313_, lean_object* v_k_314_, lean_object* v_v_315_, lean_object* v_t_316_, lean_object* v_hl_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_314_, v_v_315_, v_t_316_);
return v___x_318_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object* v_k_319_, lean_object* v_t_320_){
_start:
{
if (lean_obj_tag(v_t_320_) == 0)
{
lean_object* v_k_321_; lean_object* v_l_322_; lean_object* v_r_323_; uint8_t v___x_324_; 
v_k_321_ = lean_ctor_get(v_t_320_, 1);
v_l_322_ = lean_ctor_get(v_t_320_, 3);
v_r_323_ = lean_ctor_get(v_t_320_, 4);
v___x_324_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_319_, v_k_321_);
switch(v___x_324_)
{
case 0:
{
v_t_320_ = v_l_322_;
goto _start;
}
case 1:
{
uint8_t v___x_326_; 
v___x_326_ = 1;
return v___x_326_;
}
default: 
{
v_t_320_ = v_r_323_;
goto _start;
}
}
}
else
{
uint8_t v___x_328_; 
v___x_328_ = 0;
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg___boxed(lean_object* v_k_329_, lean_object* v_t_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_k_329_, v_t_330_);
lean_dec(v_t_330_);
lean_dec(v_k_329_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameMap_contains___redArg(lean_object* v_m_333_, lean_object* v_n_334_){
_start:
{
uint8_t v___x_335_; 
v___x_335_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_334_, v_m_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___redArg___boxed(lean_object* v_m_336_, lean_object* v_n_337_){
_start:
{
uint8_t v_res_338_; lean_object* v_r_339_; 
v_res_338_ = l_Lean_NameMap_contains___redArg(v_m_336_, v_n_337_);
lean_dec(v_n_337_);
lean_dec(v_m_336_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameMap_contains(lean_object* v_00_u03b1_340_, lean_object* v_m_341_, lean_object* v_n_342_){
_start:
{
uint8_t v___x_343_; 
v___x_343_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_342_, v_m_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___boxed(lean_object* v_00_u03b1_344_, lean_object* v_m_345_, lean_object* v_n_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Lean_NameMap_contains(v_00_u03b1_344_, v_m_345_, v_n_346_);
lean_dec(v_n_346_);
lean_dec(v_m_345_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0(lean_object* v_00_u03b2_349_, lean_object* v_k_350_, lean_object* v_t_351_){
_start:
{
uint8_t v___x_352_; 
v___x_352_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_k_350_, v_t_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___boxed(lean_object* v_00_u03b2_353_, lean_object* v_k_354_, lean_object* v_t_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0(v_00_u03b2_353_, v_k_354_, v_t_355_);
lean_dec(v_t_355_);
lean_dec(v_k_354_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object* v_t_358_, lean_object* v_k_359_){
_start:
{
if (lean_obj_tag(v_t_358_) == 0)
{
lean_object* v_k_360_; lean_object* v_v_361_; lean_object* v_l_362_; lean_object* v_r_363_; uint8_t v___x_364_; 
v_k_360_ = lean_ctor_get(v_t_358_, 1);
v_v_361_ = lean_ctor_get(v_t_358_, 2);
v_l_362_ = lean_ctor_get(v_t_358_, 3);
v_r_363_ = lean_ctor_get(v_t_358_, 4);
v___x_364_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_359_, v_k_360_);
switch(v___x_364_)
{
case 0:
{
v_t_358_ = v_l_362_;
goto _start;
}
case 1:
{
lean_object* v___x_366_; 
lean_inc(v_v_361_);
v___x_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_366_, 0, v_v_361_);
return v___x_366_;
}
default: 
{
v_t_358_ = v_r_363_;
goto _start;
}
}
}
else
{
lean_object* v___x_368_; 
v___x_368_ = lean_box(0);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg___boxed(lean_object* v_t_369_, lean_object* v_k_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_t_369_, v_k_370_);
lean_dec(v_k_370_);
lean_dec(v_t_369_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg(lean_object* v_m_372_, lean_object* v_n_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_m_372_, v_n_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg___boxed(lean_object* v_m_375_, lean_object* v_n_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_NameMap_find_x3f___redArg(v_m_375_, v_n_376_);
lean_dec(v_n_376_);
lean_dec(v_m_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f(lean_object* v_00_u03b1_378_, lean_object* v_m_379_, lean_object* v_n_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_m_379_, v_n_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___boxed(lean_object* v_00_u03b1_382_, lean_object* v_m_383_, lean_object* v_n_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_NameMap_find_x3f(v_00_u03b1_382_, v_m_383_, v_n_384_);
lean_dec(v_n_384_);
lean_dec(v_m_383_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0(lean_object* v_00_u03b4_386_, lean_object* v_t_387_, lean_object* v_k_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_t_387_, v_k_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___boxed(lean_object* v_00_u03b4_390_, lean_object* v_t_391_, lean_object* v_k_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0(v_00_u03b4_390_, v_t_391_, v_k_392_);
lean_dec(v_k_392_);
lean_dec(v_t_391_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___redArg(lean_object* v_inst_394_){
_start:
{
lean_object* v___f_395_; 
v___f_395_ = lean_alloc_closure((void*)(l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_395_, 0, v_inst_394_);
return v___f_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad(lean_object* v_00_u03b1_396_, lean_object* v_m_397_, lean_object* v_inst_398_){
_start:
{
lean_object* v___f_399_; 
v___f_399_ = lean_alloc_closure((void*)(l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_399_, 0, v_inst_398_);
return v___f_399_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object* v_f_400_, lean_object* v_t_401_){
_start:
{
if (lean_obj_tag(v_t_401_) == 0)
{
lean_object* v_k_402_; lean_object* v_v_403_; lean_object* v_l_404_; lean_object* v_r_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v_k_402_ = lean_ctor_get(v_t_401_, 1);
lean_inc(v_k_402_);
v_v_403_ = lean_ctor_get(v_t_401_, 2);
lean_inc(v_v_403_);
v_l_404_ = lean_ctor_get(v_t_401_, 3);
lean_inc(v_l_404_);
v_r_405_ = lean_ctor_get(v_t_401_, 4);
lean_inc(v_r_405_);
lean_dec_ref(v_t_401_);
lean_inc_ref(v_f_400_);
lean_inc(v_v_403_);
lean_inc(v_k_402_);
v___x_406_ = lean_apply_2(v_f_400_, v_k_402_, v_v_403_);
v___x_407_ = lean_unbox(v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v_impl_408_; lean_object* v_impl_409_; lean_object* v___x_410_; 
lean_dec(v_v_403_);
lean_dec(v_k_402_);
lean_inc_ref(v_f_400_);
v_impl_408_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_400_, v_l_404_);
v_impl_409_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_400_, v_r_405_);
v___x_410_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_408_, v_impl_409_);
return v___x_410_;
}
else
{
lean_object* v_impl_411_; lean_object* v_impl_412_; lean_object* v___x_413_; 
lean_inc_ref(v_f_400_);
v_impl_411_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_400_, v_l_404_);
v_impl_412_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_400_, v_r_405_);
v___x_413_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_402_, v_v_403_, v_impl_411_, v_impl_412_);
return v___x_413_;
}
}
else
{
lean_dec_ref(v_f_400_);
return v_t_401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filter___redArg(lean_object* v_f_414_, lean_object* v_m_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_414_, v_m_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filter(lean_object* v_00_u03b1_417_, lean_object* v_f_418_, lean_object* v_m_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_418_, v_m_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0(lean_object* v_00_u03b1_421_, lean_object* v_f_422_, lean_object* v_t_423_, lean_object* v_hl_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_422_, v_t_423_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_NameSet_empty(void){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = lean_box(1);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_NameSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = lean_box(1);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_NameSet_instInhabited(void){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = lean_box(1);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_insert(lean_object* v_s_429_, lean_object* v_n_430_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_430_, v_s_429_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_box(0);
v___x_433_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_430_, v___x_432_, v_s_429_);
return v___x_433_;
}
else
{
lean_dec(v_n_430_);
return v_s_429_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_NameSet_contains(lean_object* v_s_434_, lean_object* v_n_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_435_, v_s_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_contains___boxed(lean_object* v_s_437_, lean_object* v_n_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_Lean_NameSet_contains(v_s_437_, v_n_438_);
lean_dec(v_n_438_);
lean_dec(v_s_437_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___redArg(lean_object* v_inst_441_){
_start:
{
lean_object* v___f_442_; 
v___f_442_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_442_, 0, v_inst_441_);
return v___f_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad(lean_object* v_m_443_, lean_object* v_inst_444_){
_start:
{
lean_object* v___f_445_; 
v___f_445_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_445_, 0, v_inst_444_);
return v___f_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_448_, lean_object* v_x_449_){
_start:
{
if (lean_obj_tag(v_x_449_) == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v_b_u2082_448_);
return v___x_450_;
}
else
{
lean_object* v___x_451_; 
v___x_451_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0));
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_452_, lean_object* v_x_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_452_, v_x_453_);
lean_dec(v_x_453_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(lean_object* v_b_u2082_455_, lean_object* v_k_456_, lean_object* v_t_457_){
_start:
{
if (lean_obj_tag(v_t_457_) == 0)
{
lean_object* v_size_458_; lean_object* v_k_459_; lean_object* v_v_460_; lean_object* v_l_461_; lean_object* v_r_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_477_; 
v_size_458_ = lean_ctor_get(v_t_457_, 0);
v_k_459_ = lean_ctor_get(v_t_457_, 1);
v_v_460_ = lean_ctor_get(v_t_457_, 2);
v_l_461_ = lean_ctor_get(v_t_457_, 3);
v_r_462_ = lean_ctor_get(v_t_457_, 4);
v_isSharedCheck_477_ = !lean_is_exclusive(v_t_457_);
if (v_isSharedCheck_477_ == 0)
{
v___x_464_ = v_t_457_;
v_isShared_465_ = v_isSharedCheck_477_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_r_462_);
lean_inc(v_l_461_);
lean_inc(v_v_460_);
lean_inc(v_k_459_);
lean_inc(v_size_458_);
lean_dec(v_t_457_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_477_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v___x_466_; 
v___x_466_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_456_, v_k_459_);
switch(v___x_466_)
{
case 0:
{
lean_object* v_impl_467_; lean_object* v___x_468_; 
lean_del_object(v___x_464_);
lean_dec(v_size_458_);
v_impl_467_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_455_, v_k_456_, v_l_461_);
v___x_468_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_459_, v_v_460_, v_impl_467_, v_r_462_);
return v___x_468_;
}
case 1:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v_val_471_; lean_object* v___x_473_; 
lean_dec(v_k_459_);
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v_v_460_);
v___x_470_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_455_, v___x_469_);
lean_dec_ref(v___x_469_);
v_val_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_val_471_);
lean_dec(v___x_470_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 2, v_val_471_);
lean_ctor_set(v___x_464_, 1, v_k_456_);
v___x_473_ = v___x_464_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_size_458_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_k_456_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_val_471_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_l_461_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v_r_462_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
default: 
{
lean_object* v_impl_475_; lean_object* v___x_476_; 
lean_del_object(v___x_464_);
lean_dec(v_size_458_);
v_impl_475_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_455_, v_k_456_, v_r_462_);
v___x_476_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_459_, v_v_460_, v_l_461_, v_impl_475_);
return v___x_476_;
}
}
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v_val_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_478_ = lean_box(0);
v___x_479_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_455_, v___x_478_);
v_val_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_val_480_);
lean_dec(v___x_479_);
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v_k_456_);
lean_ctor_set(v___x_482_, 2, v_val_480_);
lean_ctor_set(v___x_482_, 3, v_t_457_);
lean_ctor_set(v___x_482_, 4, v_t_457_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(lean_object* v_init_483_, lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
lean_object* v_k_485_; lean_object* v_v_486_; lean_object* v_l_487_; lean_object* v_r_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_k_485_ = lean_ctor_get(v_x_484_, 1);
lean_inc(v_k_485_);
v_v_486_ = lean_ctor_get(v_x_484_, 2);
lean_inc(v_v_486_);
v_l_487_ = lean_ctor_get(v_x_484_, 3);
lean_inc(v_l_487_);
v_r_488_ = lean_ctor_get(v_x_484_, 4);
lean_inc(v_r_488_);
lean_dec_ref(v_x_484_);
v___x_489_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_init_483_, v_l_487_);
v___x_490_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_v_486_, v_k_485_, v___x_489_);
v_init_483_ = v___x_490_;
v_x_484_ = v_r_488_;
goto _start;
}
else
{
return v_init_483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_append(lean_object* v_s_492_, lean_object* v_t_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_s_492_, v_t_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0(lean_object* v_b_u2082_495_, lean_object* v_k_496_, lean_object* v_t_497_, lean_object* v_hl_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_495_, v_k_496_, v_t_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1(lean_object* v_init_500_, lean_object* v_t_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_init_500_, v_t_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSingletonName___lam__0(lean_object* v_n_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_box(1);
v___x_507_ = l_Lean_NameSet_insert(v___x_506_, v_n_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__0(lean_object* v_t_511_, lean_object* v_c_512_, lean_object* v_a_513_, lean_object* v_x_514_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_a_513_, v_t_511_);
if (v___x_515_ == 0)
{
lean_dec(v_a_513_);
return v_c_512_;
}
else
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_NameSet_insert(v_c_512_, v_a_513_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__0___boxed(lean_object* v_t_517_, lean_object* v_c_518_, lean_object* v_a_519_, lean_object* v_x_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_NameSet_instInter___lam__0(v_t_517_, v_c_518_, v_a_519_, v_x_520_);
lean_dec(v_t_517_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__1(lean_object* v_s_522_, lean_object* v_t_523_){
_start:
{
lean_object* v___f_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___f_524_ = lean_alloc_closure((void*)(l_Lean_NameSet_instInter___lam__0___boxed), 4, 1);
lean_closure_set(v___f_524_, 0, v_t_523_);
v___x_525_ = lean_box(1);
v___x_526_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_524_, v___x_525_, v_s_522_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSDiff___lam__0(lean_object* v___x_529_, lean_object* v_c_530_, lean_object* v_a_531_, lean_object* v_x_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_529_, v_a_531_, v_c_530_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSDiff___lam__1(lean_object* v_s_537_, lean_object* v_t_538_){
_start:
{
lean_object* v___f_539_; lean_object* v___x_540_; 
v___f_539_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__1));
v___x_540_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_539_, v_s_537_, v_t_538_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(lean_object* v_f_543_, lean_object* v_t_544_){
_start:
{
if (lean_obj_tag(v_t_544_) == 0)
{
lean_object* v_k_545_; lean_object* v_v_546_; lean_object* v_l_547_; lean_object* v_r_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_k_545_ = lean_ctor_get(v_t_544_, 1);
lean_inc(v_k_545_);
v_v_546_ = lean_ctor_get(v_t_544_, 2);
lean_inc(v_v_546_);
v_l_547_ = lean_ctor_get(v_t_544_, 3);
lean_inc(v_l_547_);
v_r_548_ = lean_ctor_get(v_t_544_, 4);
lean_inc(v_r_548_);
lean_dec_ref(v_t_544_);
lean_inc_ref(v_f_543_);
lean_inc(v_k_545_);
v___x_549_ = lean_apply_1(v_f_543_, v_k_545_);
v___x_550_ = lean_unbox(v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v_impl_551_; lean_object* v_impl_552_; lean_object* v___x_553_; 
lean_dec(v_v_546_);
lean_dec(v_k_545_);
lean_inc_ref(v_f_543_);
v_impl_551_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_543_, v_l_547_);
v_impl_552_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_543_, v_r_548_);
v___x_553_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_551_, v_impl_552_);
return v___x_553_;
}
else
{
lean_object* v_impl_554_; lean_object* v_impl_555_; lean_object* v___x_556_; 
lean_inc_ref(v_f_543_);
v_impl_554_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_543_, v_l_547_);
v_impl_555_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_543_, v_r_548_);
v___x_556_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_545_, v_v_546_, v_impl_554_, v_impl_555_);
return v___x_556_;
}
}
else
{
lean_dec_ref(v_f_543_);
return v_t_544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_filter(lean_object* v_f_557_, lean_object* v_s_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_557_, v_s_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0(lean_object* v_f_560_, lean_object* v_t_561_, lean_object* v_hl_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_560_, v_t_561_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofList(lean_object* v_l_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__0));
v___x_566_ = l_Std_TreeSet_ofList___redArg(v_l_564_, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofArray(lean_object* v_l_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__0));
v___x_569_ = l_Std_TreeSet_ofArray___redArg(v_l_567_, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofArray___boxed(lean_object* v_l_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_NameSet_ofArray(v_l_570_);
lean_dec_ref(v_l_570_);
return v_res_571_;
}
}
static lean_object* _init_l_Lean_NameSSet_empty___closed__2(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__1));
v___x_575_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__0));
v___x_576_ = l_Lean_SMap_empty(lean_box(0), lean_box(0), v___x_575_, v___x_574_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_NameSSet_empty(void){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__2, &l_Lean_NameSSet_empty___closed__2_once, _init_l_Lean_NameSSet_empty___closed__2);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_NameSSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__2, &l_Lean_NameSSet_empty___closed__2_once, _init_l_Lean_NameSSet_empty___closed__2);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_NameSSet_instInhabited(void){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__2, &l_Lean_NameSSet_empty___closed__2_once, _init_l_Lean_NameSSet_empty___closed__2);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSSet_insert(lean_object* v_s_580_, lean_object* v_n_581_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_582_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__0));
v___x_583_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__1));
v___x_584_ = lean_box(0);
v___x_585_ = l_Lean_SMap_insert___redArg(v___x_582_, v___x_583_, v_s_580_, v_n_581_, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameSSet_contains(lean_object* v_s_586_, lean_object* v_n_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__0));
v___x_589_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__1));
v___x_590_ = l_Lean_SMap_contains___redArg(v___x_588_, v___x_589_, v_s_586_, v_n_587_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSSet_contains___boxed(lean_object* v_s_591_, lean_object* v_n_592_){
_start:
{
uint8_t v_res_593_; lean_object* v_r_594_; 
v_res_593_ = l_Lean_NameSSet_contains(v_s_591_, v_n_592_);
v_r_594_ = lean_box(v_res_593_);
return v_r_594_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__0(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_box(0);
v___x_596_ = lean_unsigned_to_nat(16u);
v___x_597_ = lean_mk_array(v___x_596_, v___x_595_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__1(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__0, &l_Lean_NameHashSet_empty___closed__0_once, _init_l_Lean_NameHashSet_empty___closed__0);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_598_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty(void){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_NameHashSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_NameHashSet_instInhabited(void){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_603_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(lean_object* v_a_604_, lean_object* v_x_605_){
_start:
{
if (lean_obj_tag(v_x_605_) == 0)
{
uint8_t v___x_606_; 
v___x_606_ = 0;
return v___x_606_;
}
else
{
lean_object* v_key_607_; lean_object* v_tail_608_; uint8_t v___x_609_; 
v_key_607_ = lean_ctor_get(v_x_605_, 0);
v_tail_608_ = lean_ctor_get(v_x_605_, 2);
v___x_609_ = lean_name_eq(v_key_607_, v_a_604_);
if (v___x_609_ == 0)
{
v_x_605_ = v_tail_608_;
goto _start;
}
else
{
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg___boxed(lean_object* v_a_611_, lean_object* v_x_612_){
_start:
{
uint8_t v_res_613_; lean_object* v_r_614_; 
v_res_613_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_611_, v_x_612_);
lean_dec(v_x_612_);
lean_dec(v_a_611_);
v_r_614_ = lean_box(v_res_613_);
return v_r_614_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_615_; uint64_t v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(1723u);
v___x_616_ = lean_uint64_of_nat(v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_618_) == 0)
{
return v_x_617_;
}
else
{
lean_object* v_key_619_; lean_object* v_value_620_; lean_object* v_tail_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_647_; 
v_key_619_ = lean_ctor_get(v_x_618_, 0);
v_value_620_ = lean_ctor_get(v_x_618_, 1);
v_tail_621_ = lean_ctor_get(v_x_618_, 2);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_647_ == 0)
{
v___x_623_ = v_x_618_;
v_isShared_624_ = v_isSharedCheck_647_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_tail_621_);
lean_inc(v_value_620_);
lean_inc(v_key_619_);
lean_dec(v_x_618_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_647_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; uint64_t v___y_627_; 
v___x_625_ = lean_array_get_size(v_x_617_);
if (lean_obj_tag(v_key_619_) == 0)
{
uint64_t v___x_645_; 
v___x_645_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_627_ = v___x_645_;
goto v___jp_626_;
}
else
{
uint64_t v_hash_646_; 
v_hash_646_ = lean_ctor_get_uint64(v_key_619_, sizeof(void*)*2);
v___y_627_ = v_hash_646_;
goto v___jp_626_;
}
v___jp_626_:
{
uint64_t v___x_628_; uint64_t v___x_629_; uint64_t v_fold_630_; uint64_t v___x_631_; uint64_t v___x_632_; uint64_t v___x_633_; size_t v___x_634_; size_t v___x_635_; size_t v___x_636_; size_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_628_ = 32ULL;
v___x_629_ = lean_uint64_shift_right(v___y_627_, v___x_628_);
v_fold_630_ = lean_uint64_xor(v___y_627_, v___x_629_);
v___x_631_ = 16ULL;
v___x_632_ = lean_uint64_shift_right(v_fold_630_, v___x_631_);
v___x_633_ = lean_uint64_xor(v_fold_630_, v___x_632_);
v___x_634_ = lean_uint64_to_usize(v___x_633_);
v___x_635_ = lean_usize_of_nat(v___x_625_);
v___x_636_ = ((size_t)1ULL);
v___x_637_ = lean_usize_sub(v___x_635_, v___x_636_);
v___x_638_ = lean_usize_land(v___x_634_, v___x_637_);
v___x_639_ = lean_array_uget_borrowed(v_x_617_, v___x_638_);
lean_inc(v___x_639_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 2, v___x_639_);
v___x_641_ = v___x_623_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_key_619_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_value_620_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v___x_639_);
v___x_641_ = v_reuseFailAlloc_644_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; 
v___x_642_ = lean_array_uset(v_x_617_, v___x_638_, v___x_641_);
v_x_617_ = v___x_642_;
v_x_618_ = v_tail_621_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(lean_object* v_i_648_, lean_object* v_source_649_, lean_object* v_target_650_){
_start:
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = lean_array_get_size(v_source_649_);
v___x_652_ = lean_nat_dec_lt(v_i_648_, v___x_651_);
if (v___x_652_ == 0)
{
lean_dec_ref(v_source_649_);
lean_dec(v_i_648_);
return v_target_650_;
}
else
{
lean_object* v_es_653_; lean_object* v___x_654_; lean_object* v_source_655_; lean_object* v_target_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_es_653_ = lean_array_fget(v_source_649_, v_i_648_);
v___x_654_ = lean_box(0);
v_source_655_ = lean_array_fset(v_source_649_, v_i_648_, v___x_654_);
v_target_656_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_target_650_, v_es_653_);
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_nat_add(v_i_648_, v___x_657_);
lean_dec(v_i_648_);
v_i_648_ = v___x_658_;
v_source_649_ = v_source_655_;
v_target_650_ = v_target_656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(lean_object* v_data_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v_nbuckets_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_661_ = lean_array_get_size(v_data_660_);
v___x_662_ = lean_unsigned_to_nat(2u);
v_nbuckets_663_ = lean_nat_mul(v___x_661_, v___x_662_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_box(0);
v___x_666_ = lean_mk_array(v_nbuckets_663_, v___x_665_);
v___x_667_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(v___x_664_, v_data_660_, v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(lean_object* v_m_668_, lean_object* v_a_669_, lean_object* v_b_670_){
_start:
{
lean_object* v_size_671_; lean_object* v_buckets_672_; lean_object* v___x_673_; uint64_t v___y_675_; 
v_size_671_ = lean_ctor_get(v_m_668_, 0);
v_buckets_672_ = lean_ctor_get(v_m_668_, 1);
v___x_673_ = lean_array_get_size(v_buckets_672_);
if (lean_obj_tag(v_a_669_) == 0)
{
uint64_t v___x_712_; 
v___x_712_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_675_ = v___x_712_;
goto v___jp_674_;
}
else
{
uint64_t v_hash_713_; 
v_hash_713_ = lean_ctor_get_uint64(v_a_669_, sizeof(void*)*2);
v___y_675_ = v_hash_713_;
goto v___jp_674_;
}
v___jp_674_:
{
uint64_t v___x_676_; uint64_t v___x_677_; uint64_t v_fold_678_; uint64_t v___x_679_; uint64_t v___x_680_; uint64_t v___x_681_; size_t v___x_682_; size_t v___x_683_; size_t v___x_684_; size_t v___x_685_; size_t v___x_686_; lean_object* v_bkt_687_; uint8_t v___x_688_; 
v___x_676_ = 32ULL;
v___x_677_ = lean_uint64_shift_right(v___y_675_, v___x_676_);
v_fold_678_ = lean_uint64_xor(v___y_675_, v___x_677_);
v___x_679_ = 16ULL;
v___x_680_ = lean_uint64_shift_right(v_fold_678_, v___x_679_);
v___x_681_ = lean_uint64_xor(v_fold_678_, v___x_680_);
v___x_682_ = lean_uint64_to_usize(v___x_681_);
v___x_683_ = lean_usize_of_nat(v___x_673_);
v___x_684_ = ((size_t)1ULL);
v___x_685_ = lean_usize_sub(v___x_683_, v___x_684_);
v___x_686_ = lean_usize_land(v___x_682_, v___x_685_);
v_bkt_687_ = lean_array_uget_borrowed(v_buckets_672_, v___x_686_);
v___x_688_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_669_, v_bkt_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_709_; 
lean_inc_ref(v_buckets_672_);
lean_inc(v_size_671_);
v_isSharedCheck_709_ = !lean_is_exclusive(v_m_668_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; lean_object* v_unused_711_; 
v_unused_710_ = lean_ctor_get(v_m_668_, 1);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_m_668_, 0);
lean_dec(v_unused_711_);
v___x_690_ = v_m_668_;
v_isShared_691_ = v_isSharedCheck_709_;
goto v_resetjp_689_;
}
else
{
lean_dec(v_m_668_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_709_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v_size_x27_693_; lean_object* v___x_694_; lean_object* v_buckets_x27_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_692_ = lean_unsigned_to_nat(1u);
v_size_x27_693_ = lean_nat_add(v_size_671_, v___x_692_);
lean_dec(v_size_671_);
lean_inc(v_bkt_687_);
v___x_694_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_694_, 0, v_a_669_);
lean_ctor_set(v___x_694_, 1, v_b_670_);
lean_ctor_set(v___x_694_, 2, v_bkt_687_);
v_buckets_x27_695_ = lean_array_uset(v_buckets_672_, v___x_686_, v___x_694_);
v___x_696_ = lean_unsigned_to_nat(4u);
v___x_697_ = lean_nat_mul(v_size_x27_693_, v___x_696_);
v___x_698_ = lean_unsigned_to_nat(3u);
v___x_699_ = lean_nat_div(v___x_697_, v___x_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_array_get_size(v_buckets_x27_695_);
v___x_701_ = lean_nat_dec_le(v___x_699_, v___x_700_);
lean_dec(v___x_699_);
if (v___x_701_ == 0)
{
lean_object* v_val_702_; lean_object* v___x_704_; 
v_val_702_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(v_buckets_x27_695_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v_val_702_);
lean_ctor_set(v___x_690_, 0, v_size_x27_693_);
v___x_704_ = v___x_690_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_size_x27_693_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_val_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
else
{
lean_object* v___x_707_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v_buckets_x27_695_);
lean_ctor_set(v___x_690_, 0, v_size_x27_693_);
v___x_707_ = v___x_690_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_size_x27_693_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_buckets_x27_695_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_dec(v_b_670_);
lean_dec(v_a_669_);
return v_m_668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_insert(lean_object* v_s_714_, lean_object* v_n_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_box(0);
v___x_717_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(v_s_714_, v_n_715_, v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0(lean_object* v_00_u03b2_718_, lean_object* v_m_719_, lean_object* v_a_720_, lean_object* v_b_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(v_m_719_, v_a_720_, v_b_721_);
return v___x_722_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(lean_object* v_00_u03b2_723_, lean_object* v_a_724_, lean_object* v_x_725_){
_start:
{
uint8_t v___x_726_; 
v___x_726_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_724_, v_x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_727_, lean_object* v_a_728_, lean_object* v_x_729_){
_start:
{
uint8_t v_res_730_; lean_object* v_r_731_; 
v_res_730_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(v_00_u03b2_727_, v_a_728_, v_x_729_);
lean_dec(v_x_729_);
lean_dec(v_a_728_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1(lean_object* v_00_u03b2_732_, lean_object* v_data_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(v_data_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_735_, lean_object* v_i_736_, lean_object* v_source_737_, lean_object* v_target_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(v_i_736_, v_source_737_, v_target_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_740_, lean_object* v_x_741_, lean_object* v_x_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_x_741_, v_x_742_);
return v___x_743_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(lean_object* v_m_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_buckets_746_; lean_object* v___x_747_; uint64_t v___y_749_; 
v_buckets_746_ = lean_ctor_get(v_m_744_, 1);
v___x_747_ = lean_array_get_size(v_buckets_746_);
if (lean_obj_tag(v_a_745_) == 0)
{
uint64_t v___x_763_; 
v___x_763_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_749_ = v___x_763_;
goto v___jp_748_;
}
else
{
uint64_t v_hash_764_; 
v_hash_764_ = lean_ctor_get_uint64(v_a_745_, sizeof(void*)*2);
v___y_749_ = v_hash_764_;
goto v___jp_748_;
}
v___jp_748_:
{
uint64_t v___x_750_; uint64_t v___x_751_; uint64_t v_fold_752_; uint64_t v___x_753_; uint64_t v___x_754_; uint64_t v___x_755_; size_t v___x_756_; size_t v___x_757_; size_t v___x_758_; size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_750_ = 32ULL;
v___x_751_ = lean_uint64_shift_right(v___y_749_, v___x_750_);
v_fold_752_ = lean_uint64_xor(v___y_749_, v___x_751_);
v___x_753_ = 16ULL;
v___x_754_ = lean_uint64_shift_right(v_fold_752_, v___x_753_);
v___x_755_ = lean_uint64_xor(v_fold_752_, v___x_754_);
v___x_756_ = lean_uint64_to_usize(v___x_755_);
v___x_757_ = lean_usize_of_nat(v___x_747_);
v___x_758_ = ((size_t)1ULL);
v___x_759_ = lean_usize_sub(v___x_757_, v___x_758_);
v___x_760_ = lean_usize_land(v___x_756_, v___x_759_);
v___x_761_ = lean_array_uget_borrowed(v_buckets_746_, v___x_760_);
v___x_762_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_745_, v___x_761_);
return v___x_762_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg___boxed(lean_object* v_m_765_, lean_object* v_a_766_){
_start:
{
uint8_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_m_765_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameHashSet_contains(lean_object* v_s_769_, lean_object* v_n_770_){
_start:
{
uint8_t v___x_771_; 
v___x_771_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_s_769_, v_n_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_contains___boxed(lean_object* v_s_772_, lean_object* v_n_773_){
_start:
{
uint8_t v_res_774_; lean_object* v_r_775_; 
v_res_774_ = l_Lean_NameHashSet_contains(v_s_772_, v_n_773_);
lean_dec(v_n_773_);
lean_dec_ref(v_s_772_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(lean_object* v_00_u03b2_776_, lean_object* v_m_777_, lean_object* v_a_778_){
_start:
{
uint8_t v___x_779_; 
v___x_779_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_777_, v_a_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___boxed(lean_object* v_00_u03b2_780_, lean_object* v_m_781_, lean_object* v_a_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(v_00_u03b2_780_, v_m_781_, v_a_782_);
lean_dec(v_a_782_);
lean_dec_ref(v_m_781_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(lean_object* v_f_785_, lean_object* v_acc_786_, lean_object* v_a_787_){
_start:
{
if (lean_obj_tag(v_a_787_) == 0)
{
lean_dec_ref(v_f_785_);
return v_acc_786_;
}
else
{
lean_object* v_key_788_; lean_object* v_value_789_; lean_object* v_tail_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_801_; 
v_key_788_ = lean_ctor_get(v_a_787_, 0);
v_value_789_ = lean_ctor_get(v_a_787_, 1);
v_tail_790_ = lean_ctor_get(v_a_787_, 2);
v_isSharedCheck_801_ = !lean_is_exclusive(v_a_787_);
if (v_isSharedCheck_801_ == 0)
{
v___x_792_ = v_a_787_;
v_isShared_793_ = v_isSharedCheck_801_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_tail_790_);
lean_inc(v_value_789_);
lean_inc(v_key_788_);
lean_dec(v_a_787_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_801_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; uint8_t v___x_795_; 
lean_inc_ref(v_f_785_);
lean_inc(v_key_788_);
v___x_794_ = lean_apply_1(v_f_785_, v_key_788_);
v___x_795_ = lean_unbox(v___x_794_);
if (v___x_795_ == 0)
{
lean_del_object(v___x_792_);
lean_dec(v_value_789_);
lean_dec(v_key_788_);
v_a_787_ = v_tail_790_;
goto _start;
}
else
{
lean_object* v___x_798_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 2, v_acc_786_);
v___x_798_ = v___x_792_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_key_788_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_value_789_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v_acc_786_);
v___x_798_ = v_reuseFailAlloc_800_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
v_acc_786_ = v___x_798_;
v_a_787_ = v_tail_790_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(lean_object* v_f_802_, size_t v_sz_803_, size_t v_i_804_, lean_object* v_bs_805_){
_start:
{
uint8_t v___x_806_; 
v___x_806_ = lean_usize_dec_lt(v_i_804_, v_sz_803_);
if (v___x_806_ == 0)
{
lean_dec_ref(v_f_802_);
return v_bs_805_;
}
else
{
lean_object* v_v_807_; lean_object* v___x_808_; lean_object* v_bs_x27_809_; lean_object* v___x_810_; lean_object* v___x_811_; size_t v___x_812_; size_t v___x_813_; lean_object* v___x_814_; 
v_v_807_ = lean_array_uget(v_bs_805_, v_i_804_);
v___x_808_ = lean_unsigned_to_nat(0u);
v_bs_x27_809_ = lean_array_uset(v_bs_805_, v_i_804_, v___x_808_);
v___x_810_ = lean_box(0);
lean_inc_ref(v_f_802_);
v___x_811_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(v_f_802_, v___x_810_, v_v_807_);
v___x_812_ = ((size_t)1ULL);
v___x_813_ = lean_usize_add(v_i_804_, v___x_812_);
v___x_814_ = lean_array_uset(v_bs_x27_809_, v_i_804_, v___x_811_);
v_i_804_ = v___x_813_;
v_bs_805_ = v___x_814_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1___boxed(lean_object* v_f_816_, lean_object* v_sz_817_, lean_object* v_i_818_, lean_object* v_bs_819_){
_start:
{
size_t v_sz_boxed_820_; size_t v_i_boxed_821_; lean_object* v_res_822_; 
v_sz_boxed_820_ = lean_unbox_usize(v_sz_817_);
lean_dec(v_sz_817_);
v_i_boxed_821_ = lean_unbox_usize(v_i_818_);
lean_dec(v_i_818_);
v_res_822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(v_f_816_, v_sz_boxed_820_, v_i_boxed_821_, v_bs_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(lean_object* v_as_823_, size_t v_i_824_, size_t v_stop_825_, lean_object* v_b_826_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = lean_usize_dec_eq(v_i_824_, v_stop_825_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; size_t v___x_831_; size_t v___x_832_; 
v___x_828_ = lean_array_uget_borrowed(v_as_823_, v_i_824_);
v___x_829_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v___x_828_);
v___x_830_ = lean_nat_add(v_b_826_, v___x_829_);
lean_dec(v___x_829_);
lean_dec(v_b_826_);
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_add(v_i_824_, v___x_831_);
v_i_824_ = v___x_832_;
v_b_826_ = v___x_830_;
goto _start;
}
else
{
return v_b_826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2___boxed(lean_object* v_as_834_, lean_object* v_i_835_, lean_object* v_stop_836_, lean_object* v_b_837_){
_start:
{
size_t v_i_boxed_838_; size_t v_stop_boxed_839_; lean_object* v_res_840_; 
v_i_boxed_838_ = lean_unbox_usize(v_i_835_);
lean_dec(v_i_835_);
v_stop_boxed_839_ = lean_unbox_usize(v_stop_836_);
lean_dec(v_stop_836_);
v_res_840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_as_834_, v_i_boxed_838_, v_stop_boxed_839_, v_b_837_);
lean_dec_ref(v_as_834_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(lean_object* v_f_841_, lean_object* v_m_842_){
_start:
{
lean_object* v_buckets_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_870_; 
v_buckets_843_ = lean_ctor_get(v_m_842_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_m_842_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v_m_842_, 0);
lean_dec(v_unused_871_);
v___x_845_ = v_m_842_;
v_isShared_846_ = v_isSharedCheck_870_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_buckets_843_);
lean_dec(v_m_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_870_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
size_t v_sz_847_; size_t v___x_848_; lean_object* v_newBuckets_849_; lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_sz_847_ = lean_array_size(v_buckets_843_);
v___x_848_ = ((size_t)0ULL);
v_newBuckets_849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(v_f_841_, v_sz_847_, v___x_848_, v_buckets_843_);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_array_get_size(v_newBuckets_849_);
v___x_852_ = lean_nat_dec_lt(v___x_850_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_854_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v_newBuckets_849_);
lean_ctor_set(v___x_845_, 0, v___x_850_);
v___x_854_ = v___x_845_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_newBuckets_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
else
{
uint8_t v___x_856_; 
v___x_856_ = lean_nat_dec_le(v___x_851_, v___x_851_);
if (v___x_856_ == 0)
{
if (v___x_852_ == 0)
{
lean_object* v___x_858_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v_newBuckets_849_);
lean_ctor_set(v___x_845_, 0, v___x_850_);
v___x_858_ = v___x_845_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_newBuckets_849_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
else
{
size_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_860_ = lean_usize_of_nat(v___x_851_);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_newBuckets_849_, v___x_848_, v___x_860_, v___x_850_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v_newBuckets_849_);
lean_ctor_set(v___x_845_, 0, v___x_861_);
v___x_863_ = v___x_845_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_newBuckets_849_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
else
{
size_t v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_865_ = lean_usize_of_nat(v___x_851_);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_newBuckets_849_, v___x_848_, v___x_865_, v___x_850_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v_newBuckets_849_);
lean_ctor_set(v___x_845_, 0, v___x_866_);
v___x_868_ = v___x_845_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_newBuckets_849_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_filter(lean_object* v_f_872_, lean_object* v_s_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(v_f_872_, v_s_873_);
return v___x_874_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
if (lean_obj_tag(v_x_875_) == 0)
{
if (lean_obj_tag(v_x_876_) == 0)
{
uint8_t v___x_877_; 
v___x_877_ = 1;
return v___x_877_;
}
else
{
uint8_t v___x_878_; 
v___x_878_ = 0;
return v___x_878_;
}
}
else
{
if (lean_obj_tag(v_x_876_) == 0)
{
uint8_t v___x_879_; 
v___x_879_ = 0;
return v___x_879_;
}
else
{
lean_object* v_head_880_; lean_object* v_tail_881_; lean_object* v_head_882_; lean_object* v_tail_883_; uint8_t v___x_884_; 
v_head_880_ = lean_ctor_get(v_x_875_, 0);
v_tail_881_ = lean_ctor_get(v_x_875_, 1);
v_head_882_ = lean_ctor_get(v_x_876_, 0);
v_tail_883_ = lean_ctor_get(v_x_876_, 1);
v___x_884_ = lean_nat_dec_eq(v_head_880_, v_head_882_);
if (v___x_884_ == 0)
{
return v___x_884_;
}
else
{
v_x_875_ = v_tail_881_;
v_x_876_ = v_tail_883_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0___boxed(lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
uint8_t v_res_888_; lean_object* v_r_889_; 
v_res_888_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_x_886_, v_x_887_);
lean_dec(v_x_887_);
lean_dec(v_x_886_);
v_r_889_ = lean_box(v_res_888_);
return v_r_889_;
}
}
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isPrefixOf(lean_object* v_v_u2081_890_, lean_object* v_v_u2082_891_){
_start:
{
lean_object* v_name_892_; lean_object* v_imported_893_; lean_object* v_ctx_894_; lean_object* v_scopes_895_; lean_object* v_name_896_; lean_object* v_imported_897_; lean_object* v_ctx_898_; lean_object* v_scopes_899_; uint8_t v___y_901_; uint8_t v___x_904_; 
v_name_892_ = lean_ctor_get(v_v_u2081_890_, 0);
v_imported_893_ = lean_ctor_get(v_v_u2081_890_, 1);
v_ctx_894_ = lean_ctor_get(v_v_u2081_890_, 2);
v_scopes_895_ = lean_ctor_get(v_v_u2081_890_, 3);
v_name_896_ = lean_ctor_get(v_v_u2082_891_, 0);
v_imported_897_ = lean_ctor_get(v_v_u2082_891_, 1);
v_ctx_898_ = lean_ctor_get(v_v_u2082_891_, 2);
v_scopes_899_ = lean_ctor_get(v_v_u2082_891_, 3);
v___x_904_ = l_Lean_Name_isPrefixOf(v_name_892_, v_name_896_);
if (v___x_904_ == 0)
{
v___y_901_ = v___x_904_;
goto v___jp_900_;
}
else
{
uint8_t v___x_905_; 
v___x_905_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_scopes_895_, v_scopes_899_);
v___y_901_ = v___x_905_;
goto v___jp_900_;
}
v___jp_900_:
{
if (v___y_901_ == 0)
{
return v___y_901_;
}
else
{
uint8_t v___x_902_; 
v___x_902_ = lean_name_eq(v_ctx_894_, v_ctx_898_);
if (v___x_902_ == 0)
{
return v___x_902_;
}
else
{
uint8_t v___x_903_; 
v___x_903_ = lean_name_eq(v_imported_893_, v_imported_897_);
return v___x_903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isPrefixOf___boxed(lean_object* v_v_u2081_906_, lean_object* v_v_u2082_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l_Lean_MacroScopesView_isPrefixOf(v_v_u2081_906_, v_v_u2082_907_);
lean_dec_ref(v_v_u2082_907_);
lean_dec_ref(v_v_u2081_906_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object* v_v_u2081_910_, lean_object* v_v_u2082_911_){
_start:
{
lean_object* v_name_912_; lean_object* v_imported_913_; lean_object* v_ctx_914_; lean_object* v_scopes_915_; lean_object* v_name_916_; lean_object* v_imported_917_; lean_object* v_ctx_918_; lean_object* v_scopes_919_; uint8_t v___y_921_; uint8_t v___x_924_; 
v_name_912_ = lean_ctor_get(v_v_u2081_910_, 0);
v_imported_913_ = lean_ctor_get(v_v_u2081_910_, 1);
v_ctx_914_ = lean_ctor_get(v_v_u2081_910_, 2);
v_scopes_915_ = lean_ctor_get(v_v_u2081_910_, 3);
v_name_916_ = lean_ctor_get(v_v_u2082_911_, 0);
v_imported_917_ = lean_ctor_get(v_v_u2082_911_, 1);
v_ctx_918_ = lean_ctor_get(v_v_u2082_911_, 2);
v_scopes_919_ = lean_ctor_get(v_v_u2082_911_, 3);
v___x_924_ = l_Lean_Name_isSuffixOf(v_name_912_, v_name_916_);
if (v___x_924_ == 0)
{
v___y_921_ = v___x_924_;
goto v___jp_920_;
}
else
{
uint8_t v___x_925_; 
v___x_925_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_scopes_915_, v_scopes_919_);
v___y_921_ = v___x_925_;
goto v___jp_920_;
}
v___jp_920_:
{
if (v___y_921_ == 0)
{
return v___y_921_;
}
else
{
uint8_t v___x_922_; 
v___x_922_ = lean_name_eq(v_ctx_914_, v_ctx_918_);
if (v___x_922_ == 0)
{
return v___x_922_;
}
else
{
uint8_t v___x_923_; 
v___x_923_ = lean_name_eq(v_imported_913_, v_imported_917_);
return v___x_923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isSuffixOf___boxed(lean_object* v_v_u2081_926_, lean_object* v_v_u2082_927_){
_start:
{
uint8_t v_res_928_; lean_object* v_r_929_; 
v_res_928_ = l_Lean_MacroScopesView_isSuffixOf(v_v_u2081_926_, v_v_u2082_927_);
lean_dec_ref(v_v_u2082_927_);
lean_dec_ref(v_v_u2081_926_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_SSet(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Name(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_NameMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_SSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_NameSet_empty = _init_l_Lean_NameSet_empty();
lean_mark_persistent(l_Lean_NameSet_empty);
l_Lean_NameSet_instEmptyCollection = _init_l_Lean_NameSet_instEmptyCollection();
lean_mark_persistent(l_Lean_NameSet_instEmptyCollection);
l_Lean_NameSet_instInhabited = _init_l_Lean_NameSet_instInhabited();
lean_mark_persistent(l_Lean_NameSet_instInhabited);
l_Lean_NameSSet_empty = _init_l_Lean_NameSSet_empty();
lean_mark_persistent(l_Lean_NameSSet_empty);
l_Lean_NameSSet_instEmptyCollection = _init_l_Lean_NameSSet_instEmptyCollection();
lean_mark_persistent(l_Lean_NameSSet_instEmptyCollection);
l_Lean_NameSSet_instInhabited = _init_l_Lean_NameSSet_instInhabited();
lean_mark_persistent(l_Lean_NameSSet_instInhabited);
l_Lean_NameHashSet_empty = _init_l_Lean_NameHashSet_empty();
lean_mark_persistent(l_Lean_NameHashSet_empty);
l_Lean_NameHashSet_instEmptyCollection = _init_l_Lean_NameHashSet_instEmptyCollection();
lean_mark_persistent(l_Lean_NameHashSet_instEmptyCollection);
l_Lean_NameHashSet_instInhabited = _init_l_Lean_NameHashSet_instInhabited();
lean_mark_persistent(l_Lean_NameHashSet_instInhabited);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_NameMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_SSet(uint8_t builtin);
lean_object* initialize_Lean_Data_Name(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_NameMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_SSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_NameMap_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
