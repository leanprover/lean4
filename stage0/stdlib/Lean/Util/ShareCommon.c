// Lean compiler output
// Module: Lean.Util.ShareCommon
// Imports: public import Init.ShareCommon public import Std.Data.HashSet.Basic public import Lean.Data.PersistentHashSet
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
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_ShareCommon_StateFactory_mkImpl(lean_object*);
lean_object* lean_state_sharecommon(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_ShareCommon_mkStateImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_ShareCommon_objectFactory___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_objectFactory___elam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_objectFactory___closed__0 = (const lean_object*)&l_Lean_ShareCommon_objectFactory___closed__0_value;
static const lean_closure_object l_Lean_ShareCommon_objectFactory___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_objectFactory___elam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_objectFactory___closed__1 = (const lean_object*)&l_Lean_ShareCommon_objectFactory___closed__1_value;
static const lean_closure_object l_Lean_ShareCommon_objectFactory___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_objectFactory___elam__2, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_objectFactory___closed__2 = (const lean_object*)&l_Lean_ShareCommon_objectFactory___closed__2_value;
static const lean_closure_object l_Lean_ShareCommon_objectFactory___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_objectFactory___elam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_objectFactory___closed__3 = (const lean_object*)&l_Lean_ShareCommon_objectFactory___closed__3_value;
static const lean_closure_object l_Lean_ShareCommon_objectFactory___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_objectFactory___elam__4___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_objectFactory___closed__4 = (const lean_object*)&l_Lean_ShareCommon_objectFactory___closed__4_value;
static const lean_closure_object l_Lean_ShareCommon_objectFactory___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_objectFactory___elam__5, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_objectFactory___closed__5 = (const lean_object*)&l_Lean_ShareCommon_objectFactory___closed__5_value;
static const lean_ctor_object l_Lean_ShareCommon_objectFactory___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ShareCommon_objectFactory___closed__0_value),((lean_object*)&l_Lean_ShareCommon_objectFactory___closed__1_value),((lean_object*)&l_Lean_ShareCommon_objectFactory___closed__2_value),((lean_object*)&l_Lean_ShareCommon_objectFactory___closed__3_value),((lean_object*)&l_Lean_ShareCommon_objectFactory___closed__4_value),((lean_object*)&l_Lean_ShareCommon_objectFactory___closed__5_value)}};
static const lean_object* l_Lean_ShareCommon_objectFactory___closed__6 = (const lean_object*)&l_Lean_ShareCommon_objectFactory___closed__6_value;
static lean_once_cell_t l_Lean_ShareCommon_objectFactory___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ShareCommon_objectFactory___closed__7;
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory;
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_ShareCommon_persistentObjectFactory___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_persistentObjectFactory___elam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_persistentObjectFactory___closed__0 = (const lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__0_value;
static const lean_closure_object l_Lean_ShareCommon_persistentObjectFactory___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_persistentObjectFactory___elam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_persistentObjectFactory___closed__1 = (const lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__1_value;
static const lean_closure_object l_Lean_ShareCommon_persistentObjectFactory___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_persistentObjectFactory___elam__2, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_persistentObjectFactory___closed__2 = (const lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__2_value;
static const lean_closure_object l_Lean_ShareCommon_persistentObjectFactory___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_persistentObjectFactory___elam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_persistentObjectFactory___closed__3 = (const lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__3_value;
static const lean_closure_object l_Lean_ShareCommon_persistentObjectFactory___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_persistentObjectFactory___elam__4___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_persistentObjectFactory___closed__4 = (const lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__4_value;
static const lean_closure_object l_Lean_ShareCommon_persistentObjectFactory___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_persistentObjectFactory___elam__5, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_persistentObjectFactory___closed__5 = (const lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__5_value;
static const lean_ctor_object l_Lean_ShareCommon_persistentObjectFactory___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__0_value),((lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__1_value),((lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__2_value),((lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__3_value),((lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__4_value),((lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__5_value)}};
static const lean_object* l_Lean_ShareCommon_persistentObjectFactory___closed__6 = (const lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__6_value;
static lean_once_cell_t l_Lean_ShareCommon_persistentObjectFactory___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ShareCommon_persistentObjectFactory___closed__7;
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory;
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_withShareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0 = (const lean_object*)&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0_value;
static lean_once_cell_t l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonM_run___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonM_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonM_run___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonM_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_shareCommon___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_shareCommon(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__0___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = lean_unsigned_to_nat(4u);
v___x_4_ = lean_nat_mul(v_x_1_, v___x_3_);
v___x_5_ = lean_unsigned_to_nat(3u);
v___x_6_ = lean_nat_div(v___x_4_, v___x_5_);
lean_dec(v___x_4_);
v___x_7_ = l_Nat_nextPowerOfTwo(v___x_6_);
lean_dec(v___x_6_);
v___x_8_ = lean_box(0);
v___x_9_ = lean_mk_array(v___x_7_, v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_2_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__0___redArg___boxed(lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_ShareCommon_objectFactory___elam__0___redArg(v_x_11_);
lean_dec(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__0(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_x_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_ShareCommon_objectFactory___elam__0___redArg(v_x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__0___boxed(lean_object* v_00_u03b1_19_, lean_object* v_00_u03b2_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_x_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_ShareCommon_objectFactory___elam__0(v_00_u03b1_19_, v_00_u03b2_20_, v_inst_21_, v_inst_22_, v_x_23_);
lean_dec(v_x_23_);
lean_dec_ref(v_inst_22_);
lean_dec_ref(v_inst_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__3___redArg(lean_object* v_x_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = lean_unsigned_to_nat(4u);
v___x_28_ = lean_nat_mul(v_x_25_, v___x_27_);
v___x_29_ = lean_unsigned_to_nat(3u);
v___x_30_ = lean_nat_div(v___x_28_, v___x_29_);
lean_dec(v___x_28_);
v___x_31_ = l_Nat_nextPowerOfTwo(v___x_30_);
lean_dec(v___x_30_);
v___x_32_ = lean_box(0);
v___x_33_ = lean_mk_array(v___x_31_, v___x_32_);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_26_);
lean_ctor_set(v___x_34_, 1, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__3___redArg___boxed(lean_object* v_x_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_ShareCommon_objectFactory___elam__3___redArg(v_x_35_);
lean_dec(v_x_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__3(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_x_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_ShareCommon_objectFactory___elam__3___redArg(v_x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__3___boxed(lean_object* v_00_u03b1_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_x_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_ShareCommon_objectFactory___elam__3(v_00_u03b1_42_, v_inst_43_, v_inst_44_, v_x_45_);
lean_dec(v_x_45_);
lean_dec_ref(v_inst_44_);
lean_dec_ref(v_inst_43_);
return v_res_46_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(lean_object* v_inst_47_, lean_object* v_a_48_, lean_object* v_x_49_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
uint8_t v___x_50_; 
lean_dec(v_a_48_);
lean_dec_ref(v_inst_47_);
v___x_50_ = 0;
return v___x_50_;
}
else
{
lean_object* v_key_51_; lean_object* v_tail_52_; lean_object* v___x_53_; uint8_t v___x_54_; 
v_key_51_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_key_51_);
v_tail_52_ = lean_ctor_get(v_x_49_, 2);
lean_inc(v_tail_52_);
lean_dec_ref(v_x_49_);
lean_inc_ref(v_inst_47_);
lean_inc(v_a_48_);
v___x_53_ = lean_apply_2(v_inst_47_, v_key_51_, v_a_48_);
v___x_54_ = lean_unbox(v___x_53_);
if (v___x_54_ == 0)
{
v_x_49_ = v_tail_52_;
goto _start;
}
else
{
uint8_t v___x_56_; 
lean_dec(v_tail_52_);
lean_dec(v_a_48_);
lean_dec_ref(v_inst_47_);
v___x_56_ = lean_unbox(v___x_53_);
return v___x_56_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg___boxed(lean_object* v_inst_57_, lean_object* v_a_58_, lean_object* v_x_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_57_, v_a_58_, v_x_59_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13___redArg(lean_object* v_inst_62_, lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
if (lean_obj_tag(v_x_64_) == 0)
{
lean_dec_ref(v_inst_62_);
return v_x_63_;
}
else
{
lean_object* v_key_65_; lean_object* v_value_66_; lean_object* v_tail_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_92_; 
v_key_65_ = lean_ctor_get(v_x_64_, 0);
v_value_66_ = lean_ctor_get(v_x_64_, 1);
v_tail_67_ = lean_ctor_get(v_x_64_, 2);
v_isSharedCheck_92_ = !lean_is_exclusive(v_x_64_);
if (v_isSharedCheck_92_ == 0)
{
v___x_69_ = v_x_64_;
v_isShared_70_ = v_isSharedCheck_92_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_tail_67_);
lean_inc(v_value_66_);
lean_inc(v_key_65_);
lean_dec(v_x_64_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_92_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; lean_object* v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v_fold_77_; uint64_t v___x_78_; uint64_t v___x_79_; uint64_t v___x_80_; size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_71_ = lean_array_get_size(v_x_63_);
lean_inc_ref(v_inst_62_);
lean_inc(v_key_65_);
v___x_72_ = lean_apply_1(v_inst_62_, v_key_65_);
v___x_73_ = 32ULL;
v___x_74_ = lean_unbox_uint64(v___x_72_);
v___x_75_ = lean_uint64_shift_right(v___x_74_, v___x_73_);
v___x_76_ = lean_unbox_uint64(v___x_72_);
lean_dec_ref(v___x_72_);
v_fold_77_ = lean_uint64_xor(v___x_76_, v___x_75_);
v___x_78_ = 16ULL;
v___x_79_ = lean_uint64_shift_right(v_fold_77_, v___x_78_);
v___x_80_ = lean_uint64_xor(v_fold_77_, v___x_79_);
v___x_81_ = lean_uint64_to_usize(v___x_80_);
v___x_82_ = lean_usize_of_nat(v___x_71_);
v___x_83_ = ((size_t)1ULL);
v___x_84_ = lean_usize_sub(v___x_82_, v___x_83_);
v___x_85_ = lean_usize_land(v___x_81_, v___x_84_);
v___x_86_ = lean_array_uget_borrowed(v_x_63_, v___x_85_);
lean_inc(v___x_86_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 2, v___x_86_);
v___x_88_ = v___x_69_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_key_65_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_value_66_);
lean_ctor_set(v_reuseFailAlloc_91_, 2, v___x_86_);
v___x_88_ = v_reuseFailAlloc_91_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; 
v___x_89_ = lean_array_uset(v_x_63_, v___x_85_, v___x_88_);
v_x_63_ = v___x_89_;
v_x_64_ = v_tail_67_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10___redArg(lean_object* v_inst_93_, lean_object* v_i_94_, lean_object* v_source_95_, lean_object* v_target_96_){
_start:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_array_get_size(v_source_95_);
v___x_98_ = lean_nat_dec_lt(v_i_94_, v___x_97_);
if (v___x_98_ == 0)
{
lean_dec_ref(v_source_95_);
lean_dec(v_i_94_);
lean_dec_ref(v_inst_93_);
return v_target_96_;
}
else
{
lean_object* v_es_99_; lean_object* v___x_100_; lean_object* v_source_101_; lean_object* v_target_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_es_99_ = lean_array_fget(v_source_95_, v_i_94_);
v___x_100_ = lean_box(0);
v_source_101_ = lean_array_fset(v_source_95_, v_i_94_, v___x_100_);
lean_inc_ref(v_inst_93_);
v_target_102_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13___redArg(v_inst_93_, v_target_96_, v_es_99_);
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_add(v_i_94_, v___x_103_);
lean_dec(v_i_94_);
v_i_94_ = v___x_104_;
v_source_95_ = v_source_101_;
v_target_96_ = v_target_102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(lean_object* v_inst_106_, lean_object* v_data_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v_nbuckets_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_108_ = lean_array_get_size(v_data_107_);
v___x_109_ = lean_unsigned_to_nat(2u);
v_nbuckets_110_ = lean_nat_mul(v___x_108_, v___x_109_);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_box(0);
v___x_113_ = lean_mk_array(v_nbuckets_110_, v___x_112_);
v___x_114_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10___redArg(v_inst_106_, v___x_111_, v_data_107_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_m_117_, lean_object* v_a_118_, lean_object* v_b_119_){
_start:
{
lean_object* v_size_120_; lean_object* v_buckets_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; uint64_t v_fold_128_; uint64_t v___x_129_; uint64_t v___x_130_; uint64_t v___x_131_; size_t v___x_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; lean_object* v_bkt_137_; uint8_t v___x_138_; 
v_size_120_ = lean_ctor_get(v_m_117_, 0);
v_buckets_121_ = lean_ctor_get(v_m_117_, 1);
v___x_122_ = lean_array_get_size(v_buckets_121_);
lean_inc_ref(v_inst_116_);
lean_inc_n(v_a_118_, 2);
v___x_123_ = lean_apply_1(v_inst_116_, v_a_118_);
v___x_124_ = 32ULL;
v___x_125_ = lean_unbox_uint64(v___x_123_);
v___x_126_ = lean_uint64_shift_right(v___x_125_, v___x_124_);
v___x_127_ = lean_unbox_uint64(v___x_123_);
lean_dec_ref(v___x_123_);
v_fold_128_ = lean_uint64_xor(v___x_127_, v___x_126_);
v___x_129_ = 16ULL;
v___x_130_ = lean_uint64_shift_right(v_fold_128_, v___x_129_);
v___x_131_ = lean_uint64_xor(v_fold_128_, v___x_130_);
v___x_132_ = lean_uint64_to_usize(v___x_131_);
v___x_133_ = lean_usize_of_nat(v___x_122_);
v___x_134_ = ((size_t)1ULL);
v___x_135_ = lean_usize_sub(v___x_133_, v___x_134_);
v___x_136_ = lean_usize_land(v___x_132_, v___x_135_);
v_bkt_137_ = lean_array_uget_borrowed(v_buckets_121_, v___x_136_);
lean_inc(v_bkt_137_);
v___x_138_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_115_, v_a_118_, v_bkt_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_159_; 
lean_inc_ref(v_buckets_121_);
lean_inc(v_size_120_);
v_isSharedCheck_159_ = !lean_is_exclusive(v_m_117_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; lean_object* v_unused_161_; 
v_unused_160_ = lean_ctor_get(v_m_117_, 1);
lean_dec(v_unused_160_);
v_unused_161_ = lean_ctor_get(v_m_117_, 0);
lean_dec(v_unused_161_);
v___x_140_ = v_m_117_;
v_isShared_141_ = v_isSharedCheck_159_;
goto v_resetjp_139_;
}
else
{
lean_dec(v_m_117_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_159_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v_size_x27_143_; lean_object* v___x_144_; lean_object* v_buckets_x27_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_142_ = lean_unsigned_to_nat(1u);
v_size_x27_143_ = lean_nat_add(v_size_120_, v___x_142_);
lean_dec(v_size_120_);
lean_inc(v_bkt_137_);
v___x_144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_144_, 0, v_a_118_);
lean_ctor_set(v___x_144_, 1, v_b_119_);
lean_ctor_set(v___x_144_, 2, v_bkt_137_);
v_buckets_x27_145_ = lean_array_uset(v_buckets_121_, v___x_136_, v___x_144_);
v___x_146_ = lean_unsigned_to_nat(4u);
v___x_147_ = lean_nat_mul(v_size_x27_143_, v___x_146_);
v___x_148_ = lean_unsigned_to_nat(3u);
v___x_149_ = lean_nat_div(v___x_147_, v___x_148_);
lean_dec(v___x_147_);
v___x_150_ = lean_array_get_size(v_buckets_x27_145_);
v___x_151_ = lean_nat_dec_le(v___x_149_, v___x_150_);
lean_dec(v___x_149_);
if (v___x_151_ == 0)
{
lean_object* v_val_152_; lean_object* v___x_154_; 
v_val_152_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_116_, v_buckets_x27_145_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v_val_152_);
lean_ctor_set(v___x_140_, 0, v_size_x27_143_);
v___x_154_ = v___x_140_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_size_x27_143_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_val_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
else
{
lean_object* v___x_157_; 
lean_dec_ref(v_inst_116_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v_buckets_x27_145_);
lean_ctor_set(v___x_140_, 0, v_size_x27_143_);
v___x_157_ = v___x_140_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_size_x27_143_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_buckets_x27_145_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
else
{
lean_dec(v_b_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_inst_116_);
return v_m_117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__5___redArg(lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_x_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_box(0);
v___x_167_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(v_inst_162_, v_inst_163_, v_x_164_, v___y_165_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__5(lean_object* v_00_u03b1_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_x_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_ShareCommon_objectFactory___elam__5___redArg(v_inst_169_, v_inst_170_, v_x_171_, v___y_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(lean_object* v_inst_174_, lean_object* v_a_175_, lean_object* v_b_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_dec(v_b_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_inst_174_);
return v_x_177_;
}
else
{
lean_object* v_key_178_; lean_object* v_value_179_; lean_object* v_tail_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_193_; 
v_key_178_ = lean_ctor_get(v_x_177_, 0);
v_value_179_ = lean_ctor_get(v_x_177_, 1);
v_tail_180_ = lean_ctor_get(v_x_177_, 2);
v_isSharedCheck_193_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_193_ == 0)
{
v___x_182_ = v_x_177_;
v_isShared_183_ = v_isSharedCheck_193_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_tail_180_);
lean_inc(v_value_179_);
lean_inc(v_key_178_);
lean_dec(v_x_177_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_193_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
lean_inc_ref(v_inst_174_);
lean_inc(v_a_175_);
lean_inc(v_key_178_);
v___x_184_ = lean_apply_2(v_inst_174_, v_key_178_, v_a_175_);
v___x_185_ = lean_unbox(v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_174_, v_a_175_, v_b_176_, v_tail_180_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 2, v___x_186_);
v___x_188_ = v___x_182_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_key_178_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_value_179_);
lean_ctor_set(v_reuseFailAlloc_189_, 2, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
else
{
lean_object* v___x_191_; 
lean_dec(v_value_179_);
lean_dec(v_key_178_);
lean_dec_ref(v_inst_174_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 1, v_b_176_);
lean_ctor_set(v___x_182_, 0, v_a_175_);
v___x_191_ = v___x_182_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_175_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_b_176_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_tail_180_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_m_196_, lean_object* v_a_197_, lean_object* v_b_198_){
_start:
{
lean_object* v_size_199_; lean_object* v_buckets_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_245_; 
v_size_199_ = lean_ctor_get(v_m_196_, 0);
v_buckets_200_ = lean_ctor_get(v_m_196_, 1);
v_isSharedCheck_245_ = !lean_is_exclusive(v_m_196_);
if (v_isSharedCheck_245_ == 0)
{
v___x_202_ = v_m_196_;
v_isShared_203_ = v_isSharedCheck_245_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_buckets_200_);
lean_inc(v_size_199_);
lean_dec(v_m_196_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_245_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_205_; uint64_t v___x_206_; uint64_t v___x_207_; uint64_t v___x_208_; uint64_t v___x_209_; uint64_t v_fold_210_; uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v___x_213_; size_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; lean_object* v_bkt_219_; uint8_t v___x_220_; 
v___x_204_ = lean_array_get_size(v_buckets_200_);
lean_inc_ref(v_inst_195_);
lean_inc_n(v_a_197_, 2);
v___x_205_ = lean_apply_1(v_inst_195_, v_a_197_);
v___x_206_ = 32ULL;
v___x_207_ = lean_unbox_uint64(v___x_205_);
v___x_208_ = lean_uint64_shift_right(v___x_207_, v___x_206_);
v___x_209_ = lean_unbox_uint64(v___x_205_);
lean_dec_ref(v___x_205_);
v_fold_210_ = lean_uint64_xor(v___x_209_, v___x_208_);
v___x_211_ = 16ULL;
v___x_212_ = lean_uint64_shift_right(v_fold_210_, v___x_211_);
v___x_213_ = lean_uint64_xor(v_fold_210_, v___x_212_);
v___x_214_ = lean_uint64_to_usize(v___x_213_);
v___x_215_ = lean_usize_of_nat(v___x_204_);
v___x_216_ = ((size_t)1ULL);
v___x_217_ = lean_usize_sub(v___x_215_, v___x_216_);
v___x_218_ = lean_usize_land(v___x_214_, v___x_217_);
v_bkt_219_ = lean_array_uget_borrowed(v_buckets_200_, v___x_218_);
lean_inc(v_bkt_219_);
lean_inc_ref(v_inst_194_);
v___x_220_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_194_, v_a_197_, v_bkt_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v_size_x27_222_; lean_object* v___x_223_; lean_object* v_buckets_x27_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
lean_dec_ref(v_inst_194_);
v___x_221_ = lean_unsigned_to_nat(1u);
v_size_x27_222_ = lean_nat_add(v_size_199_, v___x_221_);
lean_dec(v_size_199_);
lean_inc(v_bkt_219_);
v___x_223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_223_, 0, v_a_197_);
lean_ctor_set(v___x_223_, 1, v_b_198_);
lean_ctor_set(v___x_223_, 2, v_bkt_219_);
v_buckets_x27_224_ = lean_array_uset(v_buckets_200_, v___x_218_, v___x_223_);
v___x_225_ = lean_unsigned_to_nat(4u);
v___x_226_ = lean_nat_mul(v_size_x27_222_, v___x_225_);
v___x_227_ = lean_unsigned_to_nat(3u);
v___x_228_ = lean_nat_div(v___x_226_, v___x_227_);
lean_dec(v___x_226_);
v___x_229_ = lean_array_get_size(v_buckets_x27_224_);
v___x_230_ = lean_nat_dec_le(v___x_228_, v___x_229_);
lean_dec(v___x_228_);
if (v___x_230_ == 0)
{
lean_object* v_val_231_; lean_object* v___x_233_; 
v_val_231_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_195_, v_buckets_x27_224_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v_val_231_);
lean_ctor_set(v___x_202_, 0, v_size_x27_222_);
v___x_233_ = v___x_202_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_size_x27_222_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_val_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
else
{
lean_object* v___x_236_; 
lean_dec_ref(v_inst_195_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v_buckets_x27_224_);
lean_ctor_set(v___x_202_, 0, v_size_x27_222_);
v___x_236_ = v___x_202_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_size_x27_222_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_buckets_x27_224_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
else
{
lean_object* v___x_238_; lean_object* v_buckets_x27_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
lean_inc(v_bkt_219_);
lean_dec_ref(v_inst_195_);
v___x_238_ = lean_box(0);
v_buckets_x27_239_ = lean_array_uset(v_buckets_200_, v___x_218_, v___x_238_);
v___x_240_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_194_, v_a_197_, v_b_198_, v_bkt_219_);
v___x_241_ = lean_array_uset(v_buckets_x27_239_, v___x_218_, v___x_240_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v___x_241_);
v___x_243_ = v___x_202_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_size_199_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__2(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_x_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_248_, v_inst_249_, v_x_250_, v___y_251_, v___y_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(lean_object* v_inst_254_, lean_object* v_a_255_, lean_object* v_x_256_){
_start:
{
if (lean_obj_tag(v_x_256_) == 0)
{
lean_object* v___x_257_; 
lean_dec(v_a_255_);
lean_dec_ref(v_inst_254_);
v___x_257_ = lean_box(0);
return v___x_257_;
}
else
{
lean_object* v_key_258_; lean_object* v_tail_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v_key_258_ = lean_ctor_get(v_x_256_, 0);
lean_inc_n(v_key_258_, 2);
v_tail_259_ = lean_ctor_get(v_x_256_, 2);
lean_inc(v_tail_259_);
lean_dec_ref(v_x_256_);
lean_inc_ref(v_inst_254_);
lean_inc(v_a_255_);
v___x_260_ = lean_apply_2(v_inst_254_, v_key_258_, v_a_255_);
v___x_261_ = lean_unbox(v___x_260_);
if (v___x_261_ == 0)
{
lean_dec(v_key_258_);
v_x_256_ = v_tail_259_;
goto _start;
}
else
{
lean_object* v___x_263_; 
lean_dec(v_tail_259_);
lean_dec(v_a_255_);
lean_dec_ref(v_inst_254_);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v_key_258_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_m_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_buckets_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint64_t v___x_271_; uint64_t v___x_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v_fold_275_; uint64_t v___x_276_; uint64_t v___x_277_; uint64_t v___x_278_; size_t v___x_279_; size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_buckets_268_ = lean_ctor_get(v_m_266_, 1);
v___x_269_ = lean_array_get_size(v_buckets_268_);
lean_inc(v_a_267_);
v___x_270_ = lean_apply_1(v_inst_265_, v_a_267_);
v___x_271_ = 32ULL;
v___x_272_ = lean_unbox_uint64(v___x_270_);
v___x_273_ = lean_uint64_shift_right(v___x_272_, v___x_271_);
v___x_274_ = lean_unbox_uint64(v___x_270_);
lean_dec_ref(v___x_270_);
v_fold_275_ = lean_uint64_xor(v___x_274_, v___x_273_);
v___x_276_ = 16ULL;
v___x_277_ = lean_uint64_shift_right(v_fold_275_, v___x_276_);
v___x_278_ = lean_uint64_xor(v_fold_275_, v___x_277_);
v___x_279_ = lean_uint64_to_usize(v___x_278_);
v___x_280_ = lean_usize_of_nat(v___x_269_);
v___x_281_ = ((size_t)1ULL);
v___x_282_ = lean_usize_sub(v___x_280_, v___x_281_);
v___x_283_ = lean_usize_land(v___x_279_, v___x_282_);
v___x_284_ = lean_array_uget_borrowed(v_buckets_268_, v___x_283_);
lean_inc(v___x_284_);
v___x_285_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(v_inst_264_, v_a_267_, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg___boxed(lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_m_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_286_, v_inst_287_, v_m_288_, v_a_289_);
lean_dec_ref(v_m_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4(lean_object* v_00_u03b1_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_x_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_292_, v_inst_293_, v_x_294_, v___y_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___boxed(lean_object* v_00_u03b1_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_x_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_ShareCommon_objectFactory___elam__4(v_00_u03b1_297_, v_inst_298_, v_inst_299_, v_x_300_, v___y_301_);
lean_dec_ref(v_x_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(lean_object* v_inst_303_, lean_object* v_a_304_, lean_object* v_x_305_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
lean_object* v___x_306_; 
lean_dec(v_a_304_);
lean_dec_ref(v_inst_303_);
v___x_306_ = lean_box(0);
return v___x_306_;
}
else
{
lean_object* v_key_307_; lean_object* v_value_308_; lean_object* v_tail_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v_key_307_ = lean_ctor_get(v_x_305_, 0);
lean_inc(v_key_307_);
v_value_308_ = lean_ctor_get(v_x_305_, 1);
lean_inc(v_value_308_);
v_tail_309_ = lean_ctor_get(v_x_305_, 2);
lean_inc(v_tail_309_);
lean_dec_ref(v_x_305_);
lean_inc_ref(v_inst_303_);
lean_inc(v_a_304_);
v___x_310_ = lean_apply_2(v_inst_303_, v_key_307_, v_a_304_);
v___x_311_ = lean_unbox(v___x_310_);
if (v___x_311_ == 0)
{
lean_dec(v_value_308_);
v_x_305_ = v_tail_309_;
goto _start;
}
else
{
lean_object* v___x_313_; 
lean_dec(v_tail_309_);
lean_dec(v_a_304_);
lean_dec_ref(v_inst_303_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v_value_308_);
return v___x_313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_m_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_buckets_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v_fold_325_; uint64_t v___x_326_; uint64_t v___x_327_; uint64_t v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_buckets_318_ = lean_ctor_get(v_m_316_, 1);
v___x_319_ = lean_array_get_size(v_buckets_318_);
lean_inc(v_a_317_);
v___x_320_ = lean_apply_1(v_inst_315_, v_a_317_);
v___x_321_ = 32ULL;
v___x_322_ = lean_unbox_uint64(v___x_320_);
v___x_323_ = lean_uint64_shift_right(v___x_322_, v___x_321_);
v___x_324_ = lean_unbox_uint64(v___x_320_);
lean_dec_ref(v___x_320_);
v_fold_325_ = lean_uint64_xor(v___x_324_, v___x_323_);
v___x_326_ = 16ULL;
v___x_327_ = lean_uint64_shift_right(v_fold_325_, v___x_326_);
v___x_328_ = lean_uint64_xor(v_fold_325_, v___x_327_);
v___x_329_ = lean_uint64_to_usize(v___x_328_);
v___x_330_ = lean_usize_of_nat(v___x_319_);
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_sub(v___x_330_, v___x_331_);
v___x_333_ = lean_usize_land(v___x_329_, v___x_332_);
v___x_334_ = lean_array_uget_borrowed(v_buckets_318_, v___x_333_);
lean_inc(v___x_334_);
v___x_335_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(v_inst_314_, v_a_317_, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg___boxed(lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_m_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_336_, v_inst_337_, v_m_338_, v_a_339_);
lean_dec_ref(v_m_338_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1(lean_object* v_00_u03b1_341_, lean_object* v_00_u03b2_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_x_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_343_, v_inst_344_, v_x_345_, v___y_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___boxed(lean_object* v_00_u03b1_348_, lean_object* v_00_u03b2_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_x_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_ShareCommon_objectFactory___elam__1(v_00_u03b1_348_, v_00_u03b2_349_, v_inst_350_, v_inst_351_, v_x_352_, v___y_353_);
lean_dec_ref(v_x_352_);
return v_res_354_;
}
}
static lean_object* _init_l_Lean_ShareCommon_objectFactory___closed__7(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_ShareCommon_objectFactory___closed__6));
v___x_369_ = l_ShareCommon_StateFactory_mkImpl(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_ShareCommon_objectFactory(void){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = lean_obj_once(&l_Lean_ShareCommon_objectFactory___closed__7, &l_Lean_ShareCommon_objectFactory___closed__7_once, _init_l_Lean_ShareCommon_objectFactory___closed__7);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___redArg(lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_x_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_371_, v_inst_372_, v_x_373_, v___y_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___redArg___boxed(lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_x_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_ShareCommon_objectFactory___elam__1___redArg(v_inst_376_, v_inst_377_, v_x_378_, v___y_379_);
lean_dec_ref(v_x_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__2___redArg(lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_x_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_381_, v_inst_382_, v_x_383_, v___y_384_, v___y_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___redArg(lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_x_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_387_, v_inst_388_, v_x_389_, v___y_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___redArg___boxed(lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_x_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_ShareCommon_objectFactory___elam__4___redArg(v_inst_392_, v_inst_393_, v_x_394_, v___y_395_);
lean_dec_ref(v_x_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1(lean_object* v_00_u03b1_397_, lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_00_u03b2_400_, lean_object* v_m_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_398_, v_inst_399_, v_m_401_, v_a_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___boxed(lean_object* v_00_u03b1_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_00_u03b2_407_, lean_object* v_m_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1(v_00_u03b1_404_, v_inst_405_, v_inst_406_, v_00_u03b2_407_, v_m_408_, v_a_409_);
lean_dec_ref(v_m_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3(lean_object* v_00_u03b1_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_00_u03b2_414_, lean_object* v_m_415_, lean_object* v_a_416_, lean_object* v_b_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_412_, v_inst_413_, v_m_415_, v_a_416_, v_b_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6(lean_object* v_00_u03b1_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_00_u03b2_422_, lean_object* v_m_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_420_, v_inst_421_, v_m_423_, v_a_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___boxed(lean_object* v_00_u03b1_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_00_u03b2_429_, lean_object* v_m_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6(v_00_u03b1_426_, v_inst_427_, v_inst_428_, v_00_u03b2_429_, v_m_430_, v_a_431_);
lean_dec_ref(v_m_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8(lean_object* v_00_u03b1_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_00_u03b2_436_, lean_object* v_m_437_, lean_object* v_a_438_, lean_object* v_b_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(v_inst_434_, v_inst_435_, v_m_437_, v_a_438_, v_b_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3(lean_object* v_00_u03b1_441_, lean_object* v_inst_442_, lean_object* v_00_u03b2_443_, lean_object* v_a_444_, lean_object* v_x_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(v_inst_442_, v_a_444_, v_x_445_);
return v___x_446_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(lean_object* v_00_u03b1_447_, lean_object* v_inst_448_, lean_object* v_00_u03b2_449_, lean_object* v_a_450_, lean_object* v_x_451_){
_start:
{
uint8_t v___x_452_; 
v___x_452_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_448_, v_a_450_, v_x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_453_, lean_object* v_inst_454_, lean_object* v_00_u03b2_455_, lean_object* v_a_456_, lean_object* v_x_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(v_00_u03b1_453_, v_inst_454_, v_00_u03b2_455_, v_a_456_, v_x_457_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7(lean_object* v_00_u03b1_460_, lean_object* v_inst_461_, lean_object* v_00_u03b2_462_, lean_object* v_data_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_461_, v_data_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8(lean_object* v_00_u03b1_465_, lean_object* v_inst_466_, lean_object* v_00_u03b2_467_, lean_object* v_a_468_, lean_object* v_b_469_, lean_object* v_x_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_466_, v_a_468_, v_b_469_, v_x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11(lean_object* v_00_u03b1_472_, lean_object* v_inst_473_, lean_object* v_00_u03b2_474_, lean_object* v_a_475_, lean_object* v_x_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(v_inst_473_, v_a_475_, v_x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10(lean_object* v_00_u03b1_478_, lean_object* v_inst_479_, lean_object* v_00_u03b2_480_, lean_object* v_i_481_, lean_object* v_source_482_, lean_object* v_target_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10___redArg(v_inst_479_, v_i_481_, v_source_482_, v_target_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13(lean_object* v_00_u03b1_485_, lean_object* v_00_u03b2_486_, lean_object* v_inst_487_, lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13___redArg(v_inst_487_, v_x_488_, v_x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(lean_object* v_inst_491_, lean_object* v_keys_492_, lean_object* v_vals_493_, lean_object* v_i_494_, lean_object* v_k_495_){
_start:
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_array_get_size(v_keys_492_);
v___x_497_ = lean_nat_dec_lt(v_i_494_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
lean_dec(v_k_495_);
lean_dec(v_i_494_);
lean_dec_ref(v_inst_491_);
v___x_498_ = lean_box(0);
return v___x_498_;
}
else
{
lean_object* v_k_x27_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_k_x27_499_ = lean_array_fget_borrowed(v_keys_492_, v_i_494_);
lean_inc_ref(v_inst_491_);
lean_inc(v_k_x27_499_);
lean_inc(v_k_495_);
v___x_500_ = lean_apply_2(v_inst_491_, v_k_495_, v_k_x27_499_);
v___x_501_ = lean_unbox(v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_unsigned_to_nat(1u);
v___x_503_ = lean_nat_add(v_i_494_, v___x_502_);
lean_dec(v_i_494_);
v_i_494_ = v___x_503_;
goto _start;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v_k_495_);
lean_dec_ref(v_inst_491_);
v___x_505_ = lean_array_fget_borrowed(v_vals_493_, v_i_494_);
lean_dec(v_i_494_);
lean_inc(v___x_505_);
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg___boxed(lean_object* v_inst_507_, lean_object* v_keys_508_, lean_object* v_vals_509_, lean_object* v_i_510_, lean_object* v_k_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_507_, v_keys_508_, v_vals_509_, v_i_510_, v_k_511_);
lean_dec_ref(v_vals_509_);
lean_dec_ref(v_keys_508_);
return v_res_512_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_513_; size_t v___x_514_; size_t v___x_515_; 
v___x_513_ = ((size_t)5ULL);
v___x_514_ = ((size_t)1ULL);
v___x_515_ = lean_usize_shift_left(v___x_514_, v___x_513_);
return v___x_515_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_516_; size_t v___x_517_; size_t v___x_518_; 
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0);
v___x_518_ = lean_usize_sub(v___x_517_, v___x_516_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(lean_object* v_inst_519_, lean_object* v_x_520_, size_t v_x_521_, lean_object* v_x_522_){
_start:
{
if (lean_obj_tag(v_x_520_) == 0)
{
lean_object* v_es_523_; lean_object* v___x_524_; size_t v___x_525_; size_t v___x_526_; size_t v___x_527_; lean_object* v_j_528_; lean_object* v___x_529_; 
v_es_523_ = lean_ctor_get(v_x_520_, 0);
lean_inc_ref(v_es_523_);
lean_dec_ref(v_x_520_);
v___x_524_ = lean_box(2);
v___x_525_ = ((size_t)5ULL);
v___x_526_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1);
v___x_527_ = lean_usize_land(v_x_521_, v___x_526_);
v_j_528_ = lean_usize_to_nat(v___x_527_);
v___x_529_ = lean_array_get(v___x_524_, v_es_523_, v_j_528_);
lean_dec(v_j_528_);
lean_dec_ref(v_es_523_);
switch(lean_obj_tag(v___x_529_))
{
case 0:
{
lean_object* v_key_530_; lean_object* v_val_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_key_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_key_530_);
v_val_531_ = lean_ctor_get(v___x_529_, 1);
lean_inc(v_val_531_);
lean_dec_ref(v___x_529_);
v___x_532_ = lean_apply_2(v_inst_519_, v_x_522_, v_key_530_);
v___x_533_ = lean_unbox(v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
lean_dec(v_val_531_);
v___x_534_ = lean_box(0);
return v___x_534_;
}
else
{
lean_object* v___x_535_; 
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v_val_531_);
return v___x_535_;
}
}
case 1:
{
lean_object* v_node_536_; size_t v___x_537_; 
v_node_536_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_node_536_);
lean_dec_ref(v___x_529_);
v___x_537_ = lean_usize_shift_right(v_x_521_, v___x_525_);
v_x_520_ = v_node_536_;
v_x_521_ = v___x_537_;
goto _start;
}
default: 
{
lean_object* v___x_539_; 
lean_dec(v_x_522_);
lean_dec_ref(v_inst_519_);
v___x_539_ = lean_box(0);
return v___x_539_;
}
}
}
else
{
lean_object* v_ks_540_; lean_object* v_vs_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_ks_540_ = lean_ctor_get(v_x_520_, 0);
lean_inc_ref(v_ks_540_);
v_vs_541_ = lean_ctor_get(v_x_520_, 1);
lean_inc_ref(v_vs_541_);
lean_dec_ref(v_x_520_);
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_519_, v_ks_540_, v_vs_541_, v___x_542_, v_x_522_);
lean_dec_ref(v_vs_541_);
lean_dec_ref(v_ks_540_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___boxed(lean_object* v_inst_544_, lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
size_t v_x_710__boxed_548_; lean_object* v_res_549_; 
v_x_710__boxed_548_ = lean_unbox_usize(v_x_546_);
lean_dec(v_x_546_);
v_res_549_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_544_, v_x_545_, v_x_710__boxed_548_, v_x_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; uint64_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; 
lean_inc(v_x_553_);
v___x_554_ = lean_apply_1(v_inst_551_, v_x_553_);
v___x_555_ = lean_unbox_uint64(v___x_554_);
lean_dec_ref(v___x_554_);
v___x_556_ = lean_uint64_to_usize(v___x_555_);
lean_inc_ref(v_x_552_);
v___x_557_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_550_, v_x_552_, v___x_556_, v_x_553_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg___boxed(lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_558_, v_inst_559_, v_x_560_, v_x_561_);
lean_dec_ref(v_x_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1(lean_object* v_00_u03b1_563_, lean_object* v_00_u03b2_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_x_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_565_, v_inst_566_, v_x_567_, v___y_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___boxed(lean_object* v_00_u03b1_570_, lean_object* v_00_u03b2_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_x_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_ShareCommon_persistentObjectFactory___elam__1(v_00_u03b1_570_, v_00_u03b2_571_, v_inst_572_, v_inst_573_, v_x_574_, v___y_575_);
lean_dec_ref(v_x_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(lean_object* v_inst_577_, lean_object* v_keys_578_, lean_object* v_vals_579_, lean_object* v_i_580_, lean_object* v_k_581_){
_start:
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_array_get_size(v_keys_578_);
v___x_583_ = lean_nat_dec_lt(v_i_580_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
lean_dec(v_k_581_);
lean_dec(v_i_580_);
lean_dec_ref(v_inst_577_);
v___x_584_ = lean_box(0);
return v___x_584_;
}
else
{
lean_object* v_k_x27_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v_k_x27_585_ = lean_array_fget_borrowed(v_keys_578_, v_i_580_);
lean_inc_ref(v_inst_577_);
lean_inc(v_k_x27_585_);
lean_inc(v_k_581_);
v___x_586_ = lean_apply_2(v_inst_577_, v_k_581_, v_k_x27_585_);
v___x_587_ = lean_unbox(v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_nat_add(v_i_580_, v___x_588_);
lean_dec(v_i_580_);
v_i_580_ = v___x_589_;
goto _start;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec(v_k_581_);
lean_dec_ref(v_inst_577_);
v___x_591_ = lean_array_fget_borrowed(v_vals_579_, v_i_580_);
lean_dec(v_i_580_);
lean_inc(v___x_591_);
lean_inc(v_k_x27_585_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v_k_x27_585_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object* v_inst_594_, lean_object* v_keys_595_, lean_object* v_vals_596_, lean_object* v_i_597_, lean_object* v_k_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_594_, v_keys_595_, v_vals_596_, v_i_597_, v_k_598_);
lean_dec_ref(v_vals_596_);
lean_dec_ref(v_keys_595_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(lean_object* v_inst_600_, lean_object* v_x_601_, size_t v_x_602_, lean_object* v_x_603_){
_start:
{
if (lean_obj_tag(v_x_601_) == 0)
{
lean_object* v_es_604_; lean_object* v___x_605_; size_t v___x_606_; size_t v___x_607_; size_t v___x_608_; lean_object* v_j_609_; lean_object* v___x_610_; 
v_es_604_ = lean_ctor_get(v_x_601_, 0);
lean_inc_ref(v_es_604_);
lean_dec_ref(v_x_601_);
v___x_605_ = lean_box(2);
v___x_606_ = ((size_t)5ULL);
v___x_607_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1);
v___x_608_ = lean_usize_land(v_x_602_, v___x_607_);
v_j_609_ = lean_usize_to_nat(v___x_608_);
v___x_610_ = lean_array_get(v___x_605_, v_es_604_, v_j_609_);
lean_dec(v_j_609_);
lean_dec_ref(v_es_604_);
switch(lean_obj_tag(v___x_610_))
{
case 0:
{
lean_object* v_key_611_; lean_object* v_val_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_key_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc_n(v_key_611_, 2);
v_val_612_ = lean_ctor_get(v___x_610_, 1);
lean_inc(v_val_612_);
lean_dec_ref(v___x_610_);
v___x_613_ = lean_apply_2(v_inst_600_, v_x_603_, v_key_611_);
v___x_614_ = lean_unbox(v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
lean_dec(v_val_612_);
lean_dec(v_key_611_);
v___x_615_ = lean_box(0);
return v___x_615_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v_key_611_);
lean_ctor_set(v___x_616_, 1, v_val_612_);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
case 1:
{
lean_object* v_node_618_; size_t v___x_619_; 
v_node_618_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_node_618_);
lean_dec_ref(v___x_610_);
v___x_619_ = lean_usize_shift_right(v_x_602_, v___x_606_);
v_x_601_ = v_node_618_;
v_x_602_ = v___x_619_;
goto _start;
}
default: 
{
lean_object* v___x_621_; 
lean_dec(v_x_603_);
lean_dec_ref(v_inst_600_);
v___x_621_ = lean_box(0);
return v___x_621_;
}
}
}
else
{
lean_object* v_ks_622_; lean_object* v_vs_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_ks_622_ = lean_ctor_get(v_x_601_, 0);
lean_inc_ref(v_ks_622_);
v_vs_623_ = lean_ctor_get(v_x_601_, 1);
lean_inc_ref(v_vs_623_);
lean_dec_ref(v_x_601_);
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_600_, v_ks_622_, v_vs_623_, v___x_624_, v_x_603_);
lean_dec_ref(v_vs_623_);
lean_dec_ref(v_ks_622_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg___boxed(lean_object* v_inst_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
size_t v_x_839__boxed_630_; lean_object* v_res_631_; 
v_x_839__boxed_630_ = lean_unbox_usize(v_x_628_);
lean_dec(v_x_628_);
v_res_631_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_626_, v_x_627_, v_x_839__boxed_630_, v_x_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
lean_object* v___x_636_; uint64_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; 
lean_inc(v_x_635_);
v___x_636_ = lean_apply_1(v_inst_633_, v_x_635_);
v___x_637_ = lean_unbox_uint64(v___x_636_);
lean_dec_ref(v___x_636_);
v___x_638_ = lean_uint64_to_usize(v___x_637_);
lean_inc_ref(v_x_634_);
v___x_639_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_632_, v_x_634_, v___x_638_, v_x_635_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg___boxed(lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_640_, v_inst_641_, v_x_642_, v_x_643_);
lean_dec_ref(v_x_642_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_x_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_645_, v_inst_646_, v_x_647_, v___y_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v___x_650_; 
v___x_650_ = lean_box(0);
return v___x_650_;
}
else
{
lean_object* v_val_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_659_; 
v_val_651_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_659_ == 0)
{
v___x_653_ = v___x_649_;
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_val_651_);
lean_dec(v___x_649_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_fst_655_; lean_object* v___x_657_; 
v_fst_655_ = lean_ctor_get(v_val_651_, 0);
lean_inc(v_fst_655_);
lean_dec(v_val_651_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v_fst_655_);
v___x_657_ = v___x_653_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_fst_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg___boxed(lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_x_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(v_inst_660_, v_inst_661_, v_x_662_, v___y_663_);
lean_dec_ref(v_x_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4(lean_object* v_00_u03b1_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_x_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(v_inst_666_, v_inst_667_, v_x_668_, v___y_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___boxed(lean_object* v_00_u03b1_671_, lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_x_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4(v_00_u03b1_671_, v_inst_672_, v_inst_673_, v_x_674_, v___y_675_);
lean_dec_ref(v_x_674_);
return v_res_676_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_677_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_object* v_00_u03b1_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_00_u03b2_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___boxed(lean_object* v_00_u03b1_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_00_u03b2_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(v_00_u03b1_685_, v_inst_686_, v_inst_687_, v_00_u03b2_688_);
lean_dec_ref(v_inst_687_);
lean_dec_ref(v_inst_686_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0(lean_object* v_00_u03b1_690_, lean_object* v_00_u03b2_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_x_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_box(0), v_inst_692_, v_inst_693_, lean_box(0));
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___boxed(lean_object* v_00_u03b1_696_, lean_object* v_00_u03b2_697_, lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_x_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_ShareCommon_persistentObjectFactory___elam__0(v_00_u03b1_696_, v_00_u03b2_697_, v_inst_698_, v_inst_699_, v_x_700_);
lean_dec(v_x_700_);
lean_dec_ref(v_inst_699_);
lean_dec_ref(v_inst_698_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3(lean_object* v_00_u03b1_702_, lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_x_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_box(0), v_inst_703_, v_inst_704_, lean_box(0));
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___boxed(lean_object* v_00_u03b1_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_x_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_ShareCommon_persistentObjectFactory___elam__3(v_00_u03b1_707_, v_inst_708_, v_inst_709_, v_x_710_);
lean_dec(v_x_710_);
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_708_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(lean_object* v_inst_712_, lean_object* v_x_713_, lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_x_716_){
_start:
{
lean_object* v_ks_717_; lean_object* v_vs_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_743_; 
v_ks_717_ = lean_ctor_get(v_x_713_, 0);
v_vs_718_ = lean_ctor_get(v_x_713_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_x_713_);
if (v_isSharedCheck_743_ == 0)
{
v___x_720_ = v_x_713_;
v_isShared_721_ = v_isSharedCheck_743_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_vs_718_);
lean_inc(v_ks_717_);
lean_dec(v_x_713_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_743_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = lean_array_get_size(v_ks_717_);
v___x_723_ = lean_nat_dec_lt(v_x_714_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
lean_dec(v_x_714_);
lean_dec_ref(v_inst_712_);
v___x_724_ = lean_array_push(v_ks_717_, v_x_715_);
v___x_725_ = lean_array_push(v_vs_718_, v_x_716_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v___x_725_);
lean_ctor_set(v___x_720_, 0, v___x_724_);
v___x_727_ = v___x_720_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
else
{
lean_object* v_k_x27_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v_k_x27_729_ = lean_array_fget_borrowed(v_ks_717_, v_x_714_);
lean_inc_ref(v_inst_712_);
lean_inc(v_k_x27_729_);
lean_inc(v_x_715_);
v___x_730_ = lean_apply_2(v_inst_712_, v_x_715_, v_k_x27_729_);
v___x_731_ = lean_unbox(v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_733_; 
if (v_isShared_721_ == 0)
{
v___x_733_ = v___x_720_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_ks_717_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_vs_718_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_unsigned_to_nat(1u);
v___x_735_ = lean_nat_add(v_x_714_, v___x_734_);
lean_dec(v_x_714_);
v_x_713_ = v___x_733_;
v_x_714_ = v___x_735_;
goto _start;
}
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
lean_dec_ref(v_inst_712_);
v___x_738_ = lean_array_fset(v_ks_717_, v_x_714_, v_x_715_);
v___x_739_ = lean_array_fset(v_vs_718_, v_x_714_, v_x_716_);
lean_dec(v_x_714_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v___x_739_);
lean_ctor_set(v___x_720_, 0, v___x_738_);
v___x_741_ = v___x_720_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(lean_object* v_inst_744_, lean_object* v_n_745_, lean_object* v_k_746_, lean_object* v_v_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(v_inst_744_, v_n_745_, v___x_748_, v_k_746_, v_v_747_);
return v___x_749_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_x_753_, size_t v_x_754_, size_t v_x_755_, lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
if (lean_obj_tag(v_x_753_) == 0)
{
lean_object* v_es_758_; size_t v___x_759_; size_t v___x_760_; size_t v___x_761_; size_t v___x_762_; lean_object* v_j_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v_es_758_ = lean_ctor_get(v_x_753_, 0);
v___x_759_ = ((size_t)5ULL);
v___x_760_ = ((size_t)1ULL);
v___x_761_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1);
v___x_762_ = lean_usize_land(v_x_754_, v___x_761_);
v_j_763_ = lean_usize_to_nat(v___x_762_);
v___x_764_ = lean_array_get_size(v_es_758_);
v___x_765_ = lean_nat_dec_lt(v_j_763_, v___x_764_);
if (v___x_765_ == 0)
{
lean_dec(v_j_763_);
lean_dec(v_x_757_);
lean_dec(v_x_756_);
lean_dec_ref(v_inst_752_);
lean_dec_ref(v_inst_751_);
return v_x_753_;
}
else
{
lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_803_; 
lean_inc_ref(v_es_758_);
v_isSharedCheck_803_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_804_);
v___x_767_ = v_x_753_;
v_isShared_768_ = v_isSharedCheck_803_;
goto v_resetjp_766_;
}
else
{
lean_dec(v_x_753_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_803_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_v_769_; lean_object* v___x_770_; lean_object* v_xs_x27_771_; lean_object* v___y_773_; 
v_v_769_ = lean_array_fget(v_es_758_, v_j_763_);
v___x_770_ = lean_box(0);
v_xs_x27_771_ = lean_array_fset(v_es_758_, v_j_763_, v___x_770_);
switch(lean_obj_tag(v_v_769_))
{
case 0:
{
lean_object* v_key_778_; lean_object* v_val_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v_inst_752_);
v_key_778_ = lean_ctor_get(v_v_769_, 0);
v_val_779_ = lean_ctor_get(v_v_769_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_v_769_);
if (v_isSharedCheck_790_ == 0)
{
v___x_781_ = v_v_769_;
v_isShared_782_ = v_isSharedCheck_790_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_val_779_);
lean_inc(v_key_778_);
lean_dec(v_v_769_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_790_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; uint8_t v___x_784_; 
lean_inc(v_key_778_);
lean_inc(v_x_756_);
v___x_783_ = lean_apply_2(v_inst_751_, v_x_756_, v_key_778_);
v___x_784_ = lean_unbox(v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; 
lean_del_object(v___x_781_);
v___x_785_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_778_, v_val_779_, v_x_756_, v_x_757_);
v___x_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
v___y_773_ = v___x_786_;
goto v___jp_772_;
}
else
{
lean_object* v___x_788_; 
lean_dec(v_val_779_);
lean_dec(v_key_778_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v_x_757_);
lean_ctor_set(v___x_781_, 0, v_x_756_);
v___x_788_ = v___x_781_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_x_756_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_x_757_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
v___y_773_ = v___x_788_;
goto v___jp_772_;
}
}
}
}
case 1:
{
lean_object* v_node_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_801_; 
v_node_791_ = lean_ctor_get(v_v_769_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v_v_769_);
if (v_isSharedCheck_801_ == 0)
{
v___x_793_ = v_v_769_;
v_isShared_794_ = v_isSharedCheck_801_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_node_791_);
lean_dec(v_v_769_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_801_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_795_ = lean_usize_shift_right(v_x_754_, v___x_759_);
v___x_796_ = lean_usize_add(v_x_755_, v___x_760_);
v___x_797_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_751_, v_inst_752_, v_node_791_, v___x_795_, v___x_796_, v_x_756_, v_x_757_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_797_);
v___x_799_ = v___x_793_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
v___y_773_ = v___x_799_;
goto v___jp_772_;
}
}
}
default: 
{
lean_object* v___x_802_; 
lean_dec_ref(v_inst_752_);
lean_dec_ref(v_inst_751_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v_x_756_);
lean_ctor_set(v___x_802_, 1, v_x_757_);
v___y_773_ = v___x_802_;
goto v___jp_772_;
}
}
v___jp_772_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = lean_array_fset(v_xs_x27_771_, v_j_763_, v___y_773_);
lean_dec(v_j_763_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_774_);
v___x_776_ = v___x_767_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
else
{
lean_object* v_ks_805_; lean_object* v_vs_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_826_; 
v_ks_805_ = lean_ctor_get(v_x_753_, 0);
v_vs_806_ = lean_ctor_get(v_x_753_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_826_ == 0)
{
v___x_808_ = v_x_753_;
v_isShared_809_ = v_isSharedCheck_826_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_vs_806_);
lean_inc(v_ks_805_);
lean_dec(v_x_753_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_826_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_ks_805_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_vs_806_);
v___x_811_ = v_reuseFailAlloc_825_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v_newNode_812_; uint8_t v___y_814_; size_t v___x_820_; uint8_t v___x_821_; 
lean_inc_ref(v_inst_751_);
v_newNode_812_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(v_inst_751_, v___x_811_, v_x_756_, v_x_757_);
v___x_820_ = ((size_t)7ULL);
v___x_821_ = lean_usize_dec_le(v___x_820_, v_x_755_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_822_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_812_);
v___x_823_ = lean_unsigned_to_nat(4u);
v___x_824_ = lean_nat_dec_lt(v___x_822_, v___x_823_);
lean_dec(v___x_822_);
v___y_814_ = v___x_824_;
goto v___jp_813_;
}
else
{
v___y_814_ = v___x_821_;
goto v___jp_813_;
}
v___jp_813_:
{
if (v___y_814_ == 0)
{
lean_object* v_ks_815_; lean_object* v_vs_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_ks_815_ = lean_ctor_get(v_newNode_812_, 0);
lean_inc_ref(v_ks_815_);
v_vs_816_ = lean_ctor_get(v_newNode_812_, 1);
lean_inc_ref(v_vs_816_);
lean_dec_ref(v_newNode_812_);
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0);
v___x_819_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_751_, v_inst_752_, v_x_755_, v_ks_815_, v_vs_816_, v___x_817_, v___x_818_);
lean_dec_ref(v_vs_816_);
lean_dec_ref(v_ks_815_);
return v___x_819_;
}
else
{
lean_dec_ref(v_inst_752_);
lean_dec_ref(v_inst_751_);
return v_newNode_812_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(lean_object* v_inst_827_, lean_object* v_inst_828_, size_t v_depth_829_, lean_object* v_keys_830_, lean_object* v_vals_831_, lean_object* v_i_832_, lean_object* v_entries_833_){
_start:
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_array_get_size(v_keys_830_);
v___x_835_ = lean_nat_dec_lt(v_i_832_, v___x_834_);
if (v___x_835_ == 0)
{
lean_dec(v_i_832_);
lean_dec_ref(v_inst_828_);
lean_dec_ref(v_inst_827_);
return v_entries_833_;
}
else
{
lean_object* v_k_836_; lean_object* v_v_837_; lean_object* v___x_838_; uint64_t v___x_839_; size_t v_h_840_; size_t v___x_841_; lean_object* v___x_842_; size_t v___x_843_; size_t v___x_844_; size_t v___x_845_; size_t v_h_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_k_836_ = lean_array_fget_borrowed(v_keys_830_, v_i_832_);
v_v_837_ = lean_array_fget_borrowed(v_vals_831_, v_i_832_);
lean_inc_ref_n(v_inst_828_, 2);
lean_inc_n(v_k_836_, 2);
v___x_838_ = lean_apply_1(v_inst_828_, v_k_836_);
v___x_839_ = lean_unbox_uint64(v___x_838_);
lean_dec_ref(v___x_838_);
v_h_840_ = lean_uint64_to_usize(v___x_839_);
v___x_841_ = ((size_t)5ULL);
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = ((size_t)1ULL);
v___x_844_ = lean_usize_sub(v_depth_829_, v___x_843_);
v___x_845_ = lean_usize_mul(v___x_841_, v___x_844_);
v_h_846_ = lean_usize_shift_right(v_h_840_, v___x_845_);
v___x_847_ = lean_nat_add(v_i_832_, v___x_842_);
lean_dec(v_i_832_);
lean_inc(v_v_837_);
lean_inc_ref(v_inst_827_);
v___x_848_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_827_, v_inst_828_, v_entries_833_, v_h_846_, v_depth_829_, v_k_836_, v_v_837_);
v_i_832_ = v___x_847_;
v_entries_833_ = v___x_848_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg___boxed(lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_depth_852_, lean_object* v_keys_853_, lean_object* v_vals_854_, lean_object* v_i_855_, lean_object* v_entries_856_){
_start:
{
size_t v_depth_boxed_857_; lean_object* v_res_858_; 
v_depth_boxed_857_ = lean_unbox_usize(v_depth_852_);
lean_dec(v_depth_852_);
v_res_858_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_850_, v_inst_851_, v_depth_boxed_857_, v_keys_853_, v_vals_854_, v_i_855_, v_entries_856_);
lean_dec_ref(v_vals_854_);
lean_dec_ref(v_keys_853_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___boxed(lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
size_t v_x_1109__boxed_866_; size_t v_x_1110__boxed_867_; lean_object* v_res_868_; 
v_x_1109__boxed_866_ = lean_unbox_usize(v_x_862_);
lean_dec(v_x_862_);
v_x_1110__boxed_867_ = lean_unbox_usize(v_x_863_);
lean_dec(v_x_863_);
v_res_868_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_859_, v_inst_860_, v_x_861_, v_x_1109__boxed_866_, v_x_1110__boxed_867_, v_x_864_, v_x_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
lean_object* v___x_874_; uint64_t v___x_875_; size_t v___x_876_; size_t v___x_877_; lean_object* v___x_878_; 
lean_inc_ref(v_inst_870_);
lean_inc(v_x_872_);
v___x_874_ = lean_apply_1(v_inst_870_, v_x_872_);
v___x_875_ = lean_unbox_uint64(v___x_874_);
lean_dec_ref(v___x_874_);
v___x_876_ = lean_uint64_to_usize(v___x_875_);
v___x_877_ = ((size_t)1ULL);
v___x_878_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_869_, v_inst_870_, v_x_871_, v___x_876_, v___x_877_, v_x_872_, v_x_873_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__2(lean_object* v_00_u03b1_879_, lean_object* v_00_u03b2_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_x_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_881_, v_inst_882_, v_x_883_, v___y_884_, v___y_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(lean_object* v_inst_887_, lean_object* v_inst_888_, lean_object* v_x_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_box(0);
v___x_892_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_887_, v_inst_888_, v_x_889_, v___y_890_, v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__5(lean_object* v_00_u03b1_893_, lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_x_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(v_inst_894_, v_inst_895_, v_x_896_, v___y_897_);
return v___x_898_;
}
}
static lean_object* _init_l_Lean_ShareCommon_persistentObjectFactory___closed__7(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_ShareCommon_persistentObjectFactory___closed__6));
v___x_913_ = l_ShareCommon_StateFactory_mkImpl(v___x_912_);
return v___x_913_;
}
}
static lean_object* _init_l_Lean_ShareCommon_persistentObjectFactory(void){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___closed__7, &l_Lean_ShareCommon_persistentObjectFactory___closed__7_once, _init_l_Lean_ShareCommon_persistentObjectFactory___closed__7);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(lean_object* v_inst_915_, lean_object* v_inst_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_box(0), v_inst_915_, v_inst_916_, lean_box(0));
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg___boxed(lean_object* v_inst_918_, lean_object* v_inst_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(v_inst_918_, v_inst_919_);
lean_dec_ref(v_inst_919_);
lean_dec_ref(v_inst_918_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg(lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_x_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_921_, v_inst_922_, v_x_923_, v___y_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg___boxed(lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_x_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg(v_inst_926_, v_inst_927_, v_x_928_, v___y_929_);
lean_dec_ref(v_x_928_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__2___redArg(lean_object* v_inst_931_, lean_object* v_inst_932_, lean_object* v_x_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_931_, v_inst_932_, v_x_933_, v___y_934_, v___y_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(lean_object* v_inst_937_, lean_object* v_inst_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_box(0), v_inst_937_, v_inst_938_, lean_box(0));
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg___boxed(lean_object* v_inst_940_, lean_object* v_inst_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(v_inst_940_, v_inst_941_);
lean_dec_ref(v_inst_941_);
lean_dec_ref(v_inst_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(lean_object* v_00_u03b1_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_00_u03b2_946_, lean_object* v_x_947_, lean_object* v_x_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_944_, v_inst_945_, v_x_947_, v_x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___boxed(lean_object* v_00_u03b1_950_, lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_00_u03b2_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(v_00_u03b1_950_, v_inst_951_, v_inst_952_, v_00_u03b2_953_, v_x_954_, v_x_955_);
lean_dec_ref(v_x_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4(lean_object* v_00_u03b1_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_00_u03b2_960_, lean_object* v_x_961_, lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_958_, v_inst_959_, v_x_961_, v_x_962_, v_x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(lean_object* v_00_u03b1_965_, lean_object* v_inst_966_, lean_object* v_inst_967_, lean_object* v_00_u03b2_968_, lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_966_, v_inst_967_, v_x_969_, v_x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___boxed(lean_object* v_00_u03b1_972_, lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_00_u03b2_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(v_00_u03b1_972_, v_inst_973_, v_inst_974_, v_00_u03b2_975_, v_x_976_, v_x_977_);
lean_dec_ref(v_x_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(lean_object* v_00_u03b1_979_, lean_object* v_inst_980_, lean_object* v_00_u03b2_981_, lean_object* v_x_982_, size_t v_x_983_, lean_object* v_x_984_){
_start:
{
lean_object* v___x_985_; 
lean_inc_ref(v_x_982_);
v___x_985_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_980_, v_x_982_, v_x_983_, v_x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_986_, lean_object* v_inst_987_, lean_object* v_00_u03b2_988_, lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
size_t v_x_1476__boxed_992_; lean_object* v_res_993_; 
v_x_1476__boxed_992_ = lean_unbox_usize(v_x_990_);
lean_dec(v_x_990_);
v_res_993_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(v_00_u03b1_986_, v_inst_987_, v_00_u03b2_988_, v_x_989_, v_x_1476__boxed_992_, v_x_991_);
lean_dec_ref(v_x_989_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(lean_object* v_00_u03b1_994_, lean_object* v_inst_995_, lean_object* v_inst_996_, lean_object* v_00_u03b2_997_, lean_object* v_x_998_, size_t v_x_999_, size_t v_x_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_995_, v_inst_996_, v_x_998_, v_x_999_, v_x_1000_, v_x_1001_, v_x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1004_, lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_00_u03b2_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
size_t v_x_1494__boxed_1013_; size_t v_x_1495__boxed_1014_; lean_object* v_res_1015_; 
v_x_1494__boxed_1013_ = lean_unbox_usize(v_x_1009_);
lean_dec(v_x_1009_);
v_x_1495__boxed_1014_ = lean_unbox_usize(v_x_1010_);
lean_dec(v_x_1010_);
v_res_1015_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(v_00_u03b1_1004_, v_inst_1005_, v_inst_1006_, v_00_u03b2_1007_, v_x_1008_, v_x_1494__boxed_1013_, v_x_1495__boxed_1014_, v_x_1011_, v_x_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(lean_object* v_00_u03b1_1016_, lean_object* v_inst_1017_, lean_object* v_00_u03b2_1018_, lean_object* v_x_1019_, size_t v_x_1020_, lean_object* v_x_1021_){
_start:
{
lean_object* v___x_1022_; 
lean_inc_ref(v_x_1019_);
v___x_1022_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_1017_, v_x_1019_, v_x_1020_, v_x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1023_, lean_object* v_inst_1024_, lean_object* v_00_u03b2_1025_, lean_object* v_x_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_){
_start:
{
size_t v_x_1519__boxed_1029_; lean_object* v_res_1030_; 
v_x_1519__boxed_1029_ = lean_unbox_usize(v_x_1027_);
lean_dec(v_x_1027_);
v_res_1030_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(v_00_u03b1_1023_, v_inst_1024_, v_00_u03b2_1025_, v_x_1026_, v_x_1519__boxed_1029_, v_x_1028_);
lean_dec_ref(v_x_1026_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(lean_object* v_00_u03b1_1031_, lean_object* v_inst_1032_, lean_object* v_00_u03b2_1033_, lean_object* v_keys_1034_, lean_object* v_vals_1035_, lean_object* v_heq_1036_, lean_object* v_i_1037_, lean_object* v_k_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_1032_, v_keys_1034_, v_vals_1035_, v_i_1037_, v_k_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___boxed(lean_object* v_00_u03b1_1040_, lean_object* v_inst_1041_, lean_object* v_00_u03b2_1042_, lean_object* v_keys_1043_, lean_object* v_vals_1044_, lean_object* v_heq_1045_, lean_object* v_i_1046_, lean_object* v_k_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(v_00_u03b1_1040_, v_inst_1041_, v_00_u03b2_1042_, v_keys_1043_, v_vals_1044_, v_heq_1045_, v_i_1046_, v_k_1047_);
lean_dec_ref(v_vals_1044_);
lean_dec_ref(v_keys_1043_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11(lean_object* v_00_u03b1_1049_, lean_object* v_inst_1050_, lean_object* v_00_u03b2_1051_, lean_object* v_n_1052_, lean_object* v_k_1053_, lean_object* v_v_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(v_inst_1050_, v_n_1052_, v_k_1053_, v_v_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(lean_object* v_00_u03b1_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_, lean_object* v_00_u03b2_1059_, size_t v_depth_1060_, lean_object* v_keys_1061_, lean_object* v_vals_1062_, lean_object* v_heq_1063_, lean_object* v_i_1064_, lean_object* v_entries_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_1057_, v_inst_1058_, v_depth_1060_, v_keys_1061_, v_vals_1062_, v_i_1064_, v_entries_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___boxed(lean_object* v_00_u03b1_1067_, lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_00_u03b2_1070_, lean_object* v_depth_1071_, lean_object* v_keys_1072_, lean_object* v_vals_1073_, lean_object* v_heq_1074_, lean_object* v_i_1075_, lean_object* v_entries_1076_){
_start:
{
size_t v_depth_boxed_1077_; lean_object* v_res_1078_; 
v_depth_boxed_1077_ = lean_unbox_usize(v_depth_1071_);
lean_dec(v_depth_1071_);
v_res_1078_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(v_00_u03b1_1067_, v_inst_1068_, v_inst_1069_, v_00_u03b2_1070_, v_depth_boxed_1077_, v_keys_1072_, v_vals_1073_, v_heq_1074_, v_i_1075_, v_entries_1076_);
lean_dec_ref(v_vals_1073_);
lean_dec_ref(v_keys_1072_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(lean_object* v_00_u03b1_1079_, lean_object* v_inst_1080_, lean_object* v_00_u03b2_1081_, lean_object* v_keys_1082_, lean_object* v_vals_1083_, lean_object* v_heq_1084_, lean_object* v_i_1085_, lean_object* v_k_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_1080_, v_keys_1082_, v_vals_1083_, v_i_1085_, v_k_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___boxed(lean_object* v_00_u03b1_1088_, lean_object* v_inst_1089_, lean_object* v_00_u03b2_1090_, lean_object* v_keys_1091_, lean_object* v_vals_1092_, lean_object* v_heq_1093_, lean_object* v_i_1094_, lean_object* v_k_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(v_00_u03b1_1088_, v_inst_1089_, v_00_u03b2_1090_, v_keys_1091_, v_vals_1092_, v_heq_1093_, v_i_1094_, v_k_1095_);
lean_dec_ref(v_vals_1092_);
lean_dec_ref(v_keys_1091_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13(lean_object* v_00_u03b1_1097_, lean_object* v_inst_1098_, lean_object* v_00_u03b2_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(v_inst_1098_, v_x_1100_, v_x_1101_, v_x_1102_, v_x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(lean_object* v_inst_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_toApplicative_1108_; lean_object* v_toPure_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_toApplicative_1108_ = lean_ctor_get(v_inst_1105_, 0);
lean_inc_ref(v_toApplicative_1108_);
lean_dec_ref(v_inst_1105_);
v_toPure_1109_ = lean_ctor_get(v_toApplicative_1108_, 1);
lean_inc(v_toPure_1109_);
lean_dec_ref(v_toApplicative_1108_);
v___x_1110_ = l_Lean_ShareCommon_objectFactory;
v___x_1111_ = lean_state_sharecommon(v___x_1110_, v_a_1107_, v_a_1106_);
v___x_1112_ = lean_apply_2(v_toPure_1109_, lean_box(0), v___x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon(lean_object* v_m_1113_, lean_object* v_00_u03b1_1114_, lean_object* v_inst_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(v_inst_1115_, v_a_1116_, v_a_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(lean_object* v_inst_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_toApplicative_1122_; lean_object* v_toPure_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_toApplicative_1122_ = lean_ctor_get(v_inst_1119_, 0);
lean_inc_ref(v_toApplicative_1122_);
lean_dec_ref(v_inst_1119_);
v_toPure_1123_ = lean_ctor_get(v_toApplicative_1122_, 1);
lean_inc(v_toPure_1123_);
lean_dec_ref(v_toApplicative_1122_);
v___x_1124_ = l_Lean_ShareCommon_persistentObjectFactory;
v___x_1125_ = lean_state_sharecommon(v___x_1124_, v_a_1121_, v_a_1120_);
v___x_1126_ = lean_apply_2(v_toPure_1123_, lean_box(0), v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_withShareCommon(lean_object* v_m_1127_, lean_object* v_00_u03b1_1128_, lean_object* v_inst_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(v_inst_1129_, v_a_1130_, v_a_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0(lean_object* v_inst_1133_, lean_object* v_00_u03b1_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(v_inst_1133_, v___y_1135_, v___y_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg(lean_object* v_inst_1138_){
_start:
{
lean_object* v___f_1139_; 
v___f_1139_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1139_, 0, v_inst_1138_);
return v___f_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon(lean_object* v_m_1140_, lean_object* v_inst_1141_){
_start:
{
lean_object* v___f_1142_; 
v___f_1142_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1142_, 0, v_inst_1141_);
return v___f_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0(lean_object* v_inst_1143_, lean_object* v_00_u03b1_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(v_inst_1143_, v___y_1145_, v___y_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg(lean_object* v_inst_1148_){
_start:
{
lean_object* v___f_1149_; 
v___f_1149_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1149_, 0, v_inst_1148_);
return v___f_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon(lean_object* v_m_1150_, lean_object* v_inst_1151_){
_start:
{
lean_object* v___f_1152_; 
v___f_1152_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1152_, 0, v_inst_1151_);
return v___f_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(lean_object* v_x_1153_){
_start:
{
lean_object* v_fst_1154_; 
v_fst_1154_ = lean_ctor_get(v_x_1153_, 0);
lean_inc(v_fst_1154_);
return v_fst_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0___boxed(lean_object* v_x_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(v_x_1155_);
lean_dec_ref(v_x_1155_);
return v_res_1156_;
}
}
static lean_object* _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = l_Lean_ShareCommon_objectFactory;
v___x_1159_ = l_ShareCommon_mkStateImpl(v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg(lean_object* v_inst_1160_, lean_object* v_x_1161_){
_start:
{
lean_object* v_toApplicative_1162_; lean_object* v_toFunctor_1163_; lean_object* v_map_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_toApplicative_1162_ = lean_ctor_get(v_inst_1160_, 0);
lean_inc_ref(v_toApplicative_1162_);
lean_dec_ref(v_inst_1160_);
v_toFunctor_1163_ = lean_ctor_get(v_toApplicative_1162_, 0);
lean_inc_ref(v_toFunctor_1163_);
lean_dec_ref(v_toApplicative_1162_);
v_map_1164_ = lean_ctor_get(v_toFunctor_1163_, 0);
lean_inc(v_map_1164_);
lean_dec_ref(v_toFunctor_1163_);
v___f_1165_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1166_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1167_ = lean_apply_1(v_x_1161_, v___x_1166_);
v___x_1168_ = lean_apply_4(v_map_1164_, lean_box(0), lean_box(0), v___f_1165_, v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run(lean_object* v_m_1169_, lean_object* v_00_u03b1_1170_, lean_object* v_inst_1171_, lean_object* v_x_1172_){
_start:
{
lean_object* v_toApplicative_1173_; lean_object* v_toFunctor_1174_; lean_object* v_map_1175_; lean_object* v___f_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_toApplicative_1173_ = lean_ctor_get(v_inst_1171_, 0);
lean_inc_ref(v_toApplicative_1173_);
lean_dec_ref(v_inst_1171_);
v_toFunctor_1174_ = lean_ctor_get(v_toApplicative_1173_, 0);
lean_inc_ref(v_toFunctor_1174_);
lean_dec_ref(v_toApplicative_1173_);
v_map_1175_ = lean_ctor_get(v_toFunctor_1174_, 0);
lean_inc(v_map_1175_);
lean_dec_ref(v_toFunctor_1174_);
v___f_1176_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1177_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1178_ = lean_apply_1(v_x_1172_, v___x_1177_);
v___x_1179_ = lean_apply_4(v_map_1175_, lean_box(0), lean_box(0), v___f_1176_, v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = l_Lean_ShareCommon_persistentObjectFactory;
v___x_1181_ = l_ShareCommon_mkStateImpl(v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_run___redArg(lean_object* v_inst_1182_, lean_object* v_x_1183_){
_start:
{
lean_object* v_toApplicative_1184_; lean_object* v_toFunctor_1185_; lean_object* v_map_1186_; lean_object* v___f_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v_toApplicative_1184_ = lean_ctor_get(v_inst_1182_, 0);
lean_inc_ref(v_toApplicative_1184_);
lean_dec_ref(v_inst_1182_);
v_toFunctor_1185_ = lean_ctor_get(v_toApplicative_1184_, 0);
lean_inc_ref(v_toFunctor_1185_);
lean_dec_ref(v_toApplicative_1184_);
v_map_1186_ = lean_ctor_get(v_toFunctor_1185_, 0);
lean_inc(v_map_1186_);
lean_dec_ref(v_toFunctor_1185_);
v___f_1187_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1188_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1189_ = lean_apply_1(v_x_1183_, v___x_1188_);
v___x_1190_ = lean_apply_4(v_map_1186_, lean_box(0), lean_box(0), v___f_1187_, v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_run(lean_object* v_m_1191_, lean_object* v_00_u03b1_1192_, lean_object* v_inst_1193_, lean_object* v_x_1194_){
_start:
{
lean_object* v_toApplicative_1195_; lean_object* v_toFunctor_1196_; lean_object* v_map_1197_; lean_object* v___f_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v_toApplicative_1195_ = lean_ctor_get(v_inst_1193_, 0);
lean_inc_ref(v_toApplicative_1195_);
lean_dec_ref(v_inst_1193_);
v_toFunctor_1196_ = lean_ctor_get(v_toApplicative_1195_, 0);
lean_inc_ref(v_toFunctor_1196_);
lean_dec_ref(v_toApplicative_1195_);
v_map_1197_ = lean_ctor_get(v_toFunctor_1196_, 0);
lean_inc(v_map_1197_);
lean_dec_ref(v_toFunctor_1196_);
v___f_1198_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1199_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1200_ = lean_apply_1(v_x_1194_, v___x_1199_);
v___x_1201_ = lean_apply_4(v_map_1197_, lean_box(0), lean_box(0), v___f_1198_, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonM_run___redArg(lean_object* v_a_1202_){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_fst_1205_; 
v___x_1203_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1204_ = lean_apply_1(v_a_1202_, v___x_1203_);
v_fst_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_fst_1205_);
lean_dec_ref(v___x_1204_);
return v_fst_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonM_run(lean_object* v_00_u03b1_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_fst_1210_; 
v___x_1208_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1209_ = lean_apply_1(v_a_1207_, v___x_1208_);
v_fst_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_fst_1210_);
lean_dec_ref(v___x_1209_);
return v_fst_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonM_run___redArg(lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_fst_1214_; 
v___x_1212_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1213_ = lean_apply_1(v_a_1211_, v___x_1212_);
v_fst_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_fst_1214_);
lean_dec_ref(v___x_1213_);
return v_fst_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonM_run(lean_object* v_00_u03b1_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_fst_1219_; 
v___x_1217_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1218_ = lean_apply_1(v_a_1216_, v___x_1217_);
v_fst_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_fst_1219_);
lean_dec_ref(v___x_1218_);
return v_fst_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = l_Lean_ShareCommon_objectFactory;
v___x_1223_ = lean_state_sharecommon(v___x_1222_, v_a_1221_, v_a_1220_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0(lean_object* v_00_u03b1_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(v_a_1225_, v_a_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_shareCommon___redArg(lean_object* v_a_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v_fst_1231_; 
v___x_1229_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1230_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(v_a_1228_, v___x_1229_);
v_fst_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_fst_1231_);
lean_dec_ref(v___x_1230_);
return v_fst_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_shareCommon(lean_object* v_00_u03b1_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_ShareCommon_shareCommon___redArg(v_a_1233_);
return v___x_1234_;
}
}
lean_object* runtime_initialize_Init_ShareCommon(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentHashSet(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_ShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PersistentHashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_ShareCommon_objectFactory = _init_l_Lean_ShareCommon_objectFactory();
lean_mark_persistent(l_Lean_ShareCommon_objectFactory);
l_Lean_ShareCommon_persistentObjectFactory = _init_l_Lean_ShareCommon_persistentObjectFactory();
lean_mark_persistent(l_Lean_ShareCommon_persistentObjectFactory);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_ShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_ShareCommon(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_PersistentHashSet(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentHashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_ShareCommon(builtin);
}
#ifdef __cplusplus
}
#endif
