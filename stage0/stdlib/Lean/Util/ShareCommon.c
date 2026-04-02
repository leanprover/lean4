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
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_ShareCommon_persistentObjectFactory___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_persistentObjectFactory___elam__1, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_persistentObjectFactory___closed__1 = (const lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__1_value;
static const lean_closure_object l_Lean_ShareCommon_persistentObjectFactory___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_persistentObjectFactory___elam__2, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_persistentObjectFactory___closed__2 = (const lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__2_value;
static const lean_closure_object l_Lean_ShareCommon_persistentObjectFactory___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_persistentObjectFactory___elam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ShareCommon_persistentObjectFactory___closed__3 = (const lean_object*)&l_Lean_ShareCommon_persistentObjectFactory___closed__3_value;
static const lean_closure_object l_Lean_ShareCommon_persistentObjectFactory___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ShareCommon_persistentObjectFactory___elam__4, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_es_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_545_; 
v_es_523_ = lean_ctor_get(v_x_520_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_545_ == 0)
{
v___x_525_ = v_x_520_;
v_isShared_526_ = v_isSharedCheck_545_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_es_523_);
lean_dec(v_x_520_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_545_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; size_t v___x_528_; size_t v___x_529_; size_t v___x_530_; lean_object* v_j_531_; lean_object* v___x_532_; 
v___x_527_ = lean_box(2);
v___x_528_ = ((size_t)5ULL);
v___x_529_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1);
v___x_530_ = lean_usize_land(v_x_521_, v___x_529_);
v_j_531_ = lean_usize_to_nat(v___x_530_);
v___x_532_ = lean_array_get(v___x_527_, v_es_523_, v_j_531_);
lean_dec(v_j_531_);
lean_dec_ref(v_es_523_);
switch(lean_obj_tag(v___x_532_))
{
case 0:
{
lean_object* v_key_533_; lean_object* v_val_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v_key_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_key_533_);
v_val_534_ = lean_ctor_get(v___x_532_, 1);
lean_inc(v_val_534_);
lean_dec_ref(v___x_532_);
v___x_535_ = lean_apply_2(v_inst_519_, v_x_522_, v_key_533_);
v___x_536_ = lean_unbox(v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
lean_dec(v_val_534_);
lean_del_object(v___x_525_);
v___x_537_ = lean_box(0);
return v___x_537_;
}
else
{
lean_object* v___x_539_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set_tag(v___x_525_, 1);
lean_ctor_set(v___x_525_, 0, v_val_534_);
v___x_539_ = v___x_525_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_val_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
case 1:
{
lean_object* v_node_541_; size_t v___x_542_; 
lean_del_object(v___x_525_);
v_node_541_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_node_541_);
lean_dec_ref(v___x_532_);
v___x_542_ = lean_usize_shift_right(v_x_521_, v___x_528_);
v_x_520_ = v_node_541_;
v_x_521_ = v___x_542_;
goto _start;
}
default: 
{
lean_object* v___x_544_; 
lean_del_object(v___x_525_);
lean_dec(v_x_522_);
lean_dec_ref(v_inst_519_);
v___x_544_ = lean_box(0);
return v___x_544_;
}
}
}
}
else
{
lean_object* v_ks_546_; lean_object* v_vs_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_ks_546_ = lean_ctor_get(v_x_520_, 0);
lean_inc_ref(v_ks_546_);
v_vs_547_ = lean_ctor_get(v_x_520_, 1);
lean_inc_ref(v_vs_547_);
lean_dec_ref(v_x_520_);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_519_, v_ks_546_, v_vs_547_, v___x_548_, v_x_522_);
lean_dec_ref(v_vs_547_);
lean_dec_ref(v_ks_546_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___boxed(lean_object* v_inst_550_, lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
size_t v_x_710__boxed_554_; lean_object* v_res_555_; 
v_x_710__boxed_554_ = lean_unbox_usize(v_x_552_);
lean_dec(v_x_552_);
v_res_555_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_550_, v_x_551_, v_x_710__boxed_554_, v_x_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(lean_object* v_inst_556_, lean_object* v_inst_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v___x_560_; uint64_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; 
lean_inc(v_x_559_);
v___x_560_ = lean_apply_1(v_inst_557_, v_x_559_);
v___x_561_ = lean_unbox_uint64(v___x_560_);
lean_dec_ref(v___x_560_);
v___x_562_ = lean_uint64_to_usize(v___x_561_);
v___x_563_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_556_, v_x_558_, v___x_562_, v_x_559_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1(lean_object* v_00_u03b1_564_, lean_object* v_00_u03b2_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_x_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_566_, v_inst_567_, v_x_568_, v___y_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(lean_object* v_inst_571_, lean_object* v_keys_572_, lean_object* v_vals_573_, lean_object* v_i_574_, lean_object* v_k_575_){
_start:
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_array_get_size(v_keys_572_);
v___x_577_ = lean_nat_dec_lt(v_i_574_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec(v_k_575_);
lean_dec(v_i_574_);
lean_dec_ref(v_inst_571_);
v___x_578_ = lean_box(0);
return v___x_578_;
}
else
{
lean_object* v_k_x27_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v_k_x27_579_ = lean_array_fget_borrowed(v_keys_572_, v_i_574_);
lean_inc_ref(v_inst_571_);
lean_inc(v_k_x27_579_);
lean_inc(v_k_575_);
v___x_580_ = lean_apply_2(v_inst_571_, v_k_575_, v_k_x27_579_);
v___x_581_ = lean_unbox(v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_nat_add(v_i_574_, v___x_582_);
lean_dec(v_i_574_);
v_i_574_ = v___x_583_;
goto _start;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_k_575_);
lean_dec_ref(v_inst_571_);
v___x_585_ = lean_array_fget_borrowed(v_vals_573_, v_i_574_);
lean_dec(v_i_574_);
lean_inc(v___x_585_);
lean_inc(v_k_x27_579_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_k_x27_579_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object* v_inst_588_, lean_object* v_keys_589_, lean_object* v_vals_590_, lean_object* v_i_591_, lean_object* v_k_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_588_, v_keys_589_, v_vals_590_, v_i_591_, v_k_592_);
lean_dec_ref(v_vals_590_);
lean_dec_ref(v_keys_589_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(lean_object* v_inst_594_, lean_object* v_x_595_, size_t v_x_596_, lean_object* v_x_597_){
_start:
{
if (lean_obj_tag(v_x_595_) == 0)
{
lean_object* v_es_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_627_; 
v_es_598_ = lean_ctor_get(v_x_595_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v_x_595_);
if (v_isSharedCheck_627_ == 0)
{
v___x_600_ = v_x_595_;
v_isShared_601_ = v_isSharedCheck_627_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_es_598_);
lean_dec(v_x_595_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_627_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; lean_object* v_j_606_; lean_object* v___x_607_; 
v___x_602_ = lean_box(2);
v___x_603_ = ((size_t)5ULL);
v___x_604_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1);
v___x_605_ = lean_usize_land(v_x_596_, v___x_604_);
v_j_606_ = lean_usize_to_nat(v___x_605_);
v___x_607_ = lean_array_get(v___x_602_, v_es_598_, v_j_606_);
lean_dec(v_j_606_);
lean_dec_ref(v_es_598_);
switch(lean_obj_tag(v___x_607_))
{
case 0:
{
lean_object* v_key_608_; lean_object* v_val_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_622_; 
v_key_608_ = lean_ctor_get(v___x_607_, 0);
v_val_609_ = lean_ctor_get(v___x_607_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_622_ == 0)
{
v___x_611_ = v___x_607_;
v_isShared_612_ = v_isSharedCheck_622_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_val_609_);
lean_inc(v_key_608_);
lean_dec(v___x_607_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_622_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; uint8_t v___x_614_; 
lean_inc(v_key_608_);
v___x_613_ = lean_apply_2(v_inst_594_, v_x_597_, v_key_608_);
v___x_614_ = lean_unbox(v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
lean_del_object(v___x_611_);
lean_dec(v_val_609_);
lean_dec(v_key_608_);
lean_del_object(v___x_600_);
v___x_615_ = lean_box(0);
return v___x_615_;
}
else
{
lean_object* v___x_617_; 
if (v_isShared_612_ == 0)
{
v___x_617_ = v___x_611_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_key_608_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_val_609_);
v___x_617_ = v_reuseFailAlloc_621_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set_tag(v___x_600_, 1);
lean_ctor_set(v___x_600_, 0, v___x_617_);
v___x_619_ = v___x_600_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
case 1:
{
lean_object* v_node_623_; size_t v___x_624_; 
lean_del_object(v___x_600_);
v_node_623_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_node_623_);
lean_dec_ref(v___x_607_);
v___x_624_ = lean_usize_shift_right(v_x_596_, v___x_603_);
v_x_595_ = v_node_623_;
v_x_596_ = v___x_624_;
goto _start;
}
default: 
{
lean_object* v___x_626_; 
lean_del_object(v___x_600_);
lean_dec(v_x_597_);
lean_dec_ref(v_inst_594_);
v___x_626_ = lean_box(0);
return v___x_626_;
}
}
}
}
else
{
lean_object* v_ks_628_; lean_object* v_vs_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_ks_628_ = lean_ctor_get(v_x_595_, 0);
lean_inc_ref(v_ks_628_);
v_vs_629_ = lean_ctor_get(v_x_595_, 1);
lean_inc_ref(v_vs_629_);
lean_dec_ref(v_x_595_);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_594_, v_ks_628_, v_vs_629_, v___x_630_, v_x_597_);
lean_dec_ref(v_vs_629_);
lean_dec_ref(v_ks_628_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg___boxed(lean_object* v_inst_632_, lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
size_t v_x_841__boxed_636_; lean_object* v_res_637_; 
v_x_841__boxed_636_ = lean_unbox_usize(v_x_634_);
lean_dec(v_x_634_);
v_res_637_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_632_, v_x_633_, v_x_841__boxed_636_, v_x_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_x_640_, lean_object* v_x_641_){
_start:
{
lean_object* v___x_642_; uint64_t v___x_643_; size_t v___x_644_; lean_object* v___x_645_; 
lean_inc(v_x_641_);
v___x_642_ = lean_apply_1(v_inst_639_, v_x_641_);
v___x_643_ = lean_unbox_uint64(v___x_642_);
lean_dec_ref(v___x_642_);
v___x_644_ = lean_uint64_to_usize(v___x_643_);
v___x_645_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_638_, v_x_640_, v___x_644_, v_x_641_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_x_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_646_, v_inst_647_, v_x_648_, v___y_649_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_651_; 
v___x_651_ = lean_box(0);
return v___x_651_;
}
else
{
lean_object* v_val_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
v_val_652_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_660_ == 0)
{
v___x_654_ = v___x_650_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_val_652_);
lean_dec(v___x_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_fst_656_; lean_object* v___x_658_; 
v_fst_656_ = lean_ctor_get(v_val_652_, 0);
lean_inc(v_fst_656_);
lean_dec(v_val_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v_fst_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_fst_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4(lean_object* v_00_u03b1_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_x_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(v_inst_662_, v_inst_663_, v_x_664_, v___y_665_);
return v___x_666_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_667_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_object* v_00_u03b1_670_, lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_00_u03b2_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___boxed(lean_object* v_00_u03b1_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_00_u03b2_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(v_00_u03b1_675_, v_inst_676_, v_inst_677_, v_00_u03b2_678_);
lean_dec_ref(v_inst_677_);
lean_dec_ref(v_inst_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0(lean_object* v_00_u03b1_680_, lean_object* v_00_u03b2_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_x_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_box(0), v_inst_682_, v_inst_683_, lean_box(0));
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___boxed(lean_object* v_00_u03b1_686_, lean_object* v_00_u03b2_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_x_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_ShareCommon_persistentObjectFactory___elam__0(v_00_u03b1_686_, v_00_u03b2_687_, v_inst_688_, v_inst_689_, v_x_690_);
lean_dec(v_x_690_);
lean_dec_ref(v_inst_689_);
lean_dec_ref(v_inst_688_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3(lean_object* v_00_u03b1_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_x_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_box(0), v_inst_693_, v_inst_694_, lean_box(0));
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___boxed(lean_object* v_00_u03b1_697_, lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_x_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_ShareCommon_persistentObjectFactory___elam__3(v_00_u03b1_697_, v_inst_698_, v_inst_699_, v_x_700_);
lean_dec(v_x_700_);
lean_dec_ref(v_inst_699_);
lean_dec_ref(v_inst_698_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(lean_object* v_inst_702_, lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
lean_object* v_ks_707_; lean_object* v_vs_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_733_; 
v_ks_707_ = lean_ctor_get(v_x_703_, 0);
v_vs_708_ = lean_ctor_get(v_x_703_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_x_703_);
if (v_isSharedCheck_733_ == 0)
{
v___x_710_ = v_x_703_;
v_isShared_711_ = v_isSharedCheck_733_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_vs_708_);
lean_inc(v_ks_707_);
lean_dec(v_x_703_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_733_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_array_get_size(v_ks_707_);
v___x_713_ = lean_nat_dec_lt(v_x_704_, v___x_712_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
lean_dec(v_x_704_);
lean_dec_ref(v_inst_702_);
v___x_714_ = lean_array_push(v_ks_707_, v_x_705_);
v___x_715_ = lean_array_push(v_vs_708_, v_x_706_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_715_);
lean_ctor_set(v___x_710_, 0, v___x_714_);
v___x_717_ = v___x_710_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
else
{
lean_object* v_k_x27_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_k_x27_719_ = lean_array_fget_borrowed(v_ks_707_, v_x_704_);
lean_inc_ref(v_inst_702_);
lean_inc(v_k_x27_719_);
lean_inc(v_x_705_);
v___x_720_ = lean_apply_2(v_inst_702_, v_x_705_, v_k_x27_719_);
v___x_721_ = lean_unbox(v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_723_; 
if (v_isShared_711_ == 0)
{
v___x_723_ = v___x_710_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_ks_707_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_vs_708_);
v___x_723_ = v_reuseFailAlloc_727_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_add(v_x_704_, v___x_724_);
lean_dec(v_x_704_);
v_x_703_ = v___x_723_;
v_x_704_ = v___x_725_;
goto _start;
}
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
lean_dec_ref(v_inst_702_);
v___x_728_ = lean_array_fset(v_ks_707_, v_x_704_, v_x_705_);
v___x_729_ = lean_array_fset(v_vs_708_, v_x_704_, v_x_706_);
lean_dec(v_x_704_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_729_);
lean_ctor_set(v___x_710_, 0, v___x_728_);
v___x_731_ = v___x_710_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(lean_object* v_inst_734_, lean_object* v_n_735_, lean_object* v_k_736_, lean_object* v_v_737_){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(v_inst_734_, v_n_735_, v___x_738_, v_k_736_, v_v_737_);
return v___x_739_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_x_743_, size_t v_x_744_, size_t v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
if (lean_obj_tag(v_x_743_) == 0)
{
lean_object* v_es_748_; size_t v___x_749_; size_t v___x_750_; size_t v___x_751_; size_t v___x_752_; lean_object* v_j_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_es_748_ = lean_ctor_get(v_x_743_, 0);
v___x_749_ = ((size_t)5ULL);
v___x_750_ = ((size_t)1ULL);
v___x_751_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1);
v___x_752_ = lean_usize_land(v_x_744_, v___x_751_);
v_j_753_ = lean_usize_to_nat(v___x_752_);
v___x_754_ = lean_array_get_size(v_es_748_);
v___x_755_ = lean_nat_dec_lt(v_j_753_, v___x_754_);
if (v___x_755_ == 0)
{
lean_dec(v_j_753_);
lean_dec(v_x_747_);
lean_dec(v_x_746_);
lean_dec_ref(v_inst_742_);
lean_dec_ref(v_inst_741_);
return v_x_743_;
}
else
{
lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_793_; 
lean_inc_ref(v_es_748_);
v_isSharedCheck_793_ = !lean_is_exclusive(v_x_743_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_x_743_, 0);
lean_dec(v_unused_794_);
v___x_757_ = v_x_743_;
v_isShared_758_ = v_isSharedCheck_793_;
goto v_resetjp_756_;
}
else
{
lean_dec(v_x_743_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_793_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v_v_759_; lean_object* v___x_760_; lean_object* v_xs_x27_761_; lean_object* v___y_763_; 
v_v_759_ = lean_array_fget(v_es_748_, v_j_753_);
v___x_760_ = lean_box(0);
v_xs_x27_761_ = lean_array_fset(v_es_748_, v_j_753_, v___x_760_);
switch(lean_obj_tag(v_v_759_))
{
case 0:
{
lean_object* v_key_768_; lean_object* v_val_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v_inst_742_);
v_key_768_ = lean_ctor_get(v_v_759_, 0);
v_val_769_ = lean_ctor_get(v_v_759_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v_v_759_);
if (v_isSharedCheck_780_ == 0)
{
v___x_771_ = v_v_759_;
v_isShared_772_ = v_isSharedCheck_780_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_val_769_);
lean_inc(v_key_768_);
lean_dec(v_v_759_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_780_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; uint8_t v___x_774_; 
lean_inc(v_key_768_);
lean_inc(v_x_746_);
v___x_773_ = lean_apply_2(v_inst_741_, v_x_746_, v_key_768_);
v___x_774_ = lean_unbox(v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; 
lean_del_object(v___x_771_);
v___x_775_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_768_, v_val_769_, v_x_746_, v_x_747_);
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
v___y_763_ = v___x_776_;
goto v___jp_762_;
}
else
{
lean_object* v___x_778_; 
lean_dec(v_val_769_);
lean_dec(v_key_768_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v_x_747_);
lean_ctor_set(v___x_771_, 0, v_x_746_);
v___x_778_ = v___x_771_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_x_746_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_x_747_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
v___y_763_ = v___x_778_;
goto v___jp_762_;
}
}
}
}
case 1:
{
lean_object* v_node_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_791_; 
v_node_781_ = lean_ctor_get(v_v_759_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v_v_759_);
if (v_isSharedCheck_791_ == 0)
{
v___x_783_ = v_v_759_;
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_node_781_);
lean_dec(v_v_759_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_785_ = lean_usize_shift_right(v_x_744_, v___x_749_);
v___x_786_ = lean_usize_add(v_x_745_, v___x_750_);
v___x_787_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_741_, v_inst_742_, v_node_781_, v___x_785_, v___x_786_, v_x_746_, v_x_747_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_787_);
v___x_789_ = v___x_783_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
v___y_763_ = v___x_789_;
goto v___jp_762_;
}
}
}
default: 
{
lean_object* v___x_792_; 
lean_dec_ref(v_inst_742_);
lean_dec_ref(v_inst_741_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v_x_746_);
lean_ctor_set(v___x_792_, 1, v_x_747_);
v___y_763_ = v___x_792_;
goto v___jp_762_;
}
}
v___jp_762_:
{
lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_764_ = lean_array_fset(v_xs_x27_761_, v_j_753_, v___y_763_);
lean_dec(v_j_753_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_764_);
v___x_766_ = v___x_757_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
else
{
lean_object* v_ks_795_; lean_object* v_vs_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_816_; 
v_ks_795_ = lean_ctor_get(v_x_743_, 0);
v_vs_796_ = lean_ctor_get(v_x_743_, 1);
v_isSharedCheck_816_ = !lean_is_exclusive(v_x_743_);
if (v_isSharedCheck_816_ == 0)
{
v___x_798_ = v_x_743_;
v_isShared_799_ = v_isSharedCheck_816_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_vs_796_);
lean_inc(v_ks_795_);
lean_dec(v_x_743_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_816_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_ks_795_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_vs_796_);
v___x_801_ = v_reuseFailAlloc_815_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v_newNode_802_; uint8_t v___y_804_; size_t v___x_810_; uint8_t v___x_811_; 
lean_inc_ref(v_inst_741_);
v_newNode_802_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(v_inst_741_, v___x_801_, v_x_746_, v_x_747_);
v___x_810_ = ((size_t)7ULL);
v___x_811_ = lean_usize_dec_le(v___x_810_, v_x_745_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_812_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_802_);
v___x_813_ = lean_unsigned_to_nat(4u);
v___x_814_ = lean_nat_dec_lt(v___x_812_, v___x_813_);
lean_dec(v___x_812_);
v___y_804_ = v___x_814_;
goto v___jp_803_;
}
else
{
v___y_804_ = v___x_811_;
goto v___jp_803_;
}
v___jp_803_:
{
if (v___y_804_ == 0)
{
lean_object* v_ks_805_; lean_object* v_vs_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_ks_805_ = lean_ctor_get(v_newNode_802_, 0);
lean_inc_ref(v_ks_805_);
v_vs_806_ = lean_ctor_get(v_newNode_802_, 1);
lean_inc_ref(v_vs_806_);
lean_dec_ref(v_newNode_802_);
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0);
v___x_809_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_741_, v_inst_742_, v_x_745_, v_ks_805_, v_vs_806_, v___x_807_, v___x_808_);
lean_dec_ref(v_vs_806_);
lean_dec_ref(v_ks_805_);
return v___x_809_;
}
else
{
lean_dec_ref(v_inst_742_);
lean_dec_ref(v_inst_741_);
return v_newNode_802_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(lean_object* v_inst_817_, lean_object* v_inst_818_, size_t v_depth_819_, lean_object* v_keys_820_, lean_object* v_vals_821_, lean_object* v_i_822_, lean_object* v_entries_823_){
_start:
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = lean_array_get_size(v_keys_820_);
v___x_825_ = lean_nat_dec_lt(v_i_822_, v___x_824_);
if (v___x_825_ == 0)
{
lean_dec(v_i_822_);
lean_dec_ref(v_inst_818_);
lean_dec_ref(v_inst_817_);
return v_entries_823_;
}
else
{
lean_object* v_k_826_; lean_object* v_v_827_; lean_object* v___x_828_; uint64_t v___x_829_; size_t v_h_830_; size_t v___x_831_; lean_object* v___x_832_; size_t v___x_833_; size_t v___x_834_; size_t v___x_835_; size_t v_h_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_k_826_ = lean_array_fget_borrowed(v_keys_820_, v_i_822_);
v_v_827_ = lean_array_fget_borrowed(v_vals_821_, v_i_822_);
lean_inc_ref_n(v_inst_818_, 2);
lean_inc_n(v_k_826_, 2);
v___x_828_ = lean_apply_1(v_inst_818_, v_k_826_);
v___x_829_ = lean_unbox_uint64(v___x_828_);
lean_dec_ref(v___x_828_);
v_h_830_ = lean_uint64_to_usize(v___x_829_);
v___x_831_ = ((size_t)5ULL);
v___x_832_ = lean_unsigned_to_nat(1u);
v___x_833_ = ((size_t)1ULL);
v___x_834_ = lean_usize_sub(v_depth_819_, v___x_833_);
v___x_835_ = lean_usize_mul(v___x_831_, v___x_834_);
v_h_836_ = lean_usize_shift_right(v_h_830_, v___x_835_);
v___x_837_ = lean_nat_add(v_i_822_, v___x_832_);
lean_dec(v_i_822_);
lean_inc(v_v_827_);
lean_inc_ref(v_inst_817_);
v___x_838_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_817_, v_inst_818_, v_entries_823_, v_h_836_, v_depth_819_, v_k_826_, v_v_827_);
v_i_822_ = v___x_837_;
v_entries_823_ = v___x_838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg___boxed(lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_depth_842_, lean_object* v_keys_843_, lean_object* v_vals_844_, lean_object* v_i_845_, lean_object* v_entries_846_){
_start:
{
size_t v_depth_boxed_847_; lean_object* v_res_848_; 
v_depth_boxed_847_ = lean_unbox_usize(v_depth_842_);
lean_dec(v_depth_842_);
v_res_848_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_840_, v_inst_841_, v_depth_boxed_847_, v_keys_843_, v_vals_844_, v_i_845_, v_entries_846_);
lean_dec_ref(v_vals_844_);
lean_dec_ref(v_keys_843_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___boxed(lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_x_854_, lean_object* v_x_855_){
_start:
{
size_t v_x_1122__boxed_856_; size_t v_x_1123__boxed_857_; lean_object* v_res_858_; 
v_x_1122__boxed_856_ = lean_unbox_usize(v_x_852_);
lean_dec(v_x_852_);
v_x_1123__boxed_857_ = lean_unbox_usize(v_x_853_);
lean_dec(v_x_853_);
v_res_858_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_849_, v_inst_850_, v_x_851_, v_x_1122__boxed_856_, v_x_1123__boxed_857_, v_x_854_, v_x_855_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
lean_object* v___x_864_; uint64_t v___x_865_; size_t v___x_866_; size_t v___x_867_; lean_object* v___x_868_; 
lean_inc_ref(v_inst_860_);
lean_inc(v_x_862_);
v___x_864_ = lean_apply_1(v_inst_860_, v_x_862_);
v___x_865_ = lean_unbox_uint64(v___x_864_);
lean_dec_ref(v___x_864_);
v___x_866_ = lean_uint64_to_usize(v___x_865_);
v___x_867_ = ((size_t)1ULL);
v___x_868_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_859_, v_inst_860_, v_x_861_, v___x_866_, v___x_867_, v_x_862_, v_x_863_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__2(lean_object* v_00_u03b1_869_, lean_object* v_00_u03b2_870_, lean_object* v_inst_871_, lean_object* v_inst_872_, lean_object* v_x_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_871_, v_inst_872_, v_x_873_, v___y_874_, v___y_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_x_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_box(0);
v___x_882_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_877_, v_inst_878_, v_x_879_, v___y_880_, v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__5(lean_object* v_00_u03b1_883_, lean_object* v_inst_884_, lean_object* v_inst_885_, lean_object* v_x_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(v_inst_884_, v_inst_885_, v_x_886_, v___y_887_);
return v___x_888_;
}
}
static lean_object* _init_l_Lean_ShareCommon_persistentObjectFactory___closed__7(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean_ShareCommon_persistentObjectFactory___closed__6));
v___x_903_ = l_ShareCommon_StateFactory_mkImpl(v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_ShareCommon_persistentObjectFactory(void){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___closed__7, &l_Lean_ShareCommon_persistentObjectFactory___closed__7_once, _init_l_Lean_ShareCommon_persistentObjectFactory___closed__7);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(lean_object* v_inst_905_, lean_object* v_inst_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_box(0), v_inst_905_, v_inst_906_, lean_box(0));
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg___boxed(lean_object* v_inst_908_, lean_object* v_inst_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(v_inst_908_, v_inst_909_);
lean_dec_ref(v_inst_909_);
lean_dec_ref(v_inst_908_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg(lean_object* v_inst_911_, lean_object* v_inst_912_, lean_object* v_x_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_911_, v_inst_912_, v_x_913_, v___y_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__2___redArg(lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_x_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_916_, v_inst_917_, v_x_918_, v___y_919_, v___y_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(lean_object* v_inst_922_, lean_object* v_inst_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_box(0), v_inst_922_, v_inst_923_, lean_box(0));
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg___boxed(lean_object* v_inst_925_, lean_object* v_inst_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(v_inst_925_, v_inst_926_);
lean_dec_ref(v_inst_926_);
lean_dec_ref(v_inst_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(lean_object* v_00_u03b1_928_, lean_object* v_inst_929_, lean_object* v_inst_930_, lean_object* v_00_u03b2_931_, lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_929_, v_inst_930_, v_x_932_, v_x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4(lean_object* v_00_u03b1_935_, lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_00_u03b2_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_936_, v_inst_937_, v_x_939_, v_x_940_, v_x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(lean_object* v_00_u03b1_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_00_u03b2_946_, lean_object* v_x_947_, lean_object* v_x_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_944_, v_inst_945_, v_x_947_, v_x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(lean_object* v_00_u03b1_950_, lean_object* v_inst_951_, lean_object* v_00_u03b2_952_, lean_object* v_x_953_, size_t v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_951_, v_x_953_, v_x_954_, v_x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_957_, lean_object* v_inst_958_, lean_object* v_00_u03b2_959_, lean_object* v_x_960_, lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
size_t v_x_1475__boxed_963_; lean_object* v_res_964_; 
v_x_1475__boxed_963_ = lean_unbox_usize(v_x_961_);
lean_dec(v_x_961_);
v_res_964_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(v_00_u03b1_957_, v_inst_958_, v_00_u03b2_959_, v_x_960_, v_x_1475__boxed_963_, v_x_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(lean_object* v_00_u03b1_965_, lean_object* v_inst_966_, lean_object* v_inst_967_, lean_object* v_00_u03b2_968_, lean_object* v_x_969_, size_t v_x_970_, size_t v_x_971_, lean_object* v_x_972_, lean_object* v_x_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_966_, v_inst_967_, v_x_969_, v_x_970_, v_x_971_, v_x_972_, v_x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_975_, lean_object* v_inst_976_, lean_object* v_inst_977_, lean_object* v_00_u03b2_978_, lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
size_t v_x_1493__boxed_984_; size_t v_x_1494__boxed_985_; lean_object* v_res_986_; 
v_x_1493__boxed_984_ = lean_unbox_usize(v_x_980_);
lean_dec(v_x_980_);
v_x_1494__boxed_985_ = lean_unbox_usize(v_x_981_);
lean_dec(v_x_981_);
v_res_986_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(v_00_u03b1_975_, v_inst_976_, v_inst_977_, v_00_u03b2_978_, v_x_979_, v_x_1493__boxed_984_, v_x_1494__boxed_985_, v_x_982_, v_x_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(lean_object* v_00_u03b1_987_, lean_object* v_inst_988_, lean_object* v_00_u03b2_989_, lean_object* v_x_990_, size_t v_x_991_, lean_object* v_x_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_988_, v_x_990_, v_x_991_, v_x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_994_, lean_object* v_inst_995_, lean_object* v_00_u03b2_996_, lean_object* v_x_997_, lean_object* v_x_998_, lean_object* v_x_999_){
_start:
{
size_t v_x_1518__boxed_1000_; lean_object* v_res_1001_; 
v_x_1518__boxed_1000_ = lean_unbox_usize(v_x_998_);
lean_dec(v_x_998_);
v_res_1001_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(v_00_u03b1_994_, v_inst_995_, v_00_u03b2_996_, v_x_997_, v_x_1518__boxed_1000_, v_x_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(lean_object* v_00_u03b1_1002_, lean_object* v_inst_1003_, lean_object* v_00_u03b2_1004_, lean_object* v_keys_1005_, lean_object* v_vals_1006_, lean_object* v_heq_1007_, lean_object* v_i_1008_, lean_object* v_k_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_1003_, v_keys_1005_, v_vals_1006_, v_i_1008_, v_k_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___boxed(lean_object* v_00_u03b1_1011_, lean_object* v_inst_1012_, lean_object* v_00_u03b2_1013_, lean_object* v_keys_1014_, lean_object* v_vals_1015_, lean_object* v_heq_1016_, lean_object* v_i_1017_, lean_object* v_k_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(v_00_u03b1_1011_, v_inst_1012_, v_00_u03b2_1013_, v_keys_1014_, v_vals_1015_, v_heq_1016_, v_i_1017_, v_k_1018_);
lean_dec_ref(v_vals_1015_);
lean_dec_ref(v_keys_1014_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11(lean_object* v_00_u03b1_1020_, lean_object* v_inst_1021_, lean_object* v_00_u03b2_1022_, lean_object* v_n_1023_, lean_object* v_k_1024_, lean_object* v_v_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(v_inst_1021_, v_n_1023_, v_k_1024_, v_v_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(lean_object* v_00_u03b1_1027_, lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_00_u03b2_1030_, size_t v_depth_1031_, lean_object* v_keys_1032_, lean_object* v_vals_1033_, lean_object* v_heq_1034_, lean_object* v_i_1035_, lean_object* v_entries_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_1028_, v_inst_1029_, v_depth_1031_, v_keys_1032_, v_vals_1033_, v_i_1035_, v_entries_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___boxed(lean_object* v_00_u03b1_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_00_u03b2_1041_, lean_object* v_depth_1042_, lean_object* v_keys_1043_, lean_object* v_vals_1044_, lean_object* v_heq_1045_, lean_object* v_i_1046_, lean_object* v_entries_1047_){
_start:
{
size_t v_depth_boxed_1048_; lean_object* v_res_1049_; 
v_depth_boxed_1048_ = lean_unbox_usize(v_depth_1042_);
lean_dec(v_depth_1042_);
v_res_1049_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(v_00_u03b1_1038_, v_inst_1039_, v_inst_1040_, v_00_u03b2_1041_, v_depth_boxed_1048_, v_keys_1043_, v_vals_1044_, v_heq_1045_, v_i_1046_, v_entries_1047_);
lean_dec_ref(v_vals_1044_);
lean_dec_ref(v_keys_1043_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(lean_object* v_00_u03b1_1050_, lean_object* v_inst_1051_, lean_object* v_00_u03b2_1052_, lean_object* v_keys_1053_, lean_object* v_vals_1054_, lean_object* v_heq_1055_, lean_object* v_i_1056_, lean_object* v_k_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_1051_, v_keys_1053_, v_vals_1054_, v_i_1056_, v_k_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___boxed(lean_object* v_00_u03b1_1059_, lean_object* v_inst_1060_, lean_object* v_00_u03b2_1061_, lean_object* v_keys_1062_, lean_object* v_vals_1063_, lean_object* v_heq_1064_, lean_object* v_i_1065_, lean_object* v_k_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(v_00_u03b1_1059_, v_inst_1060_, v_00_u03b2_1061_, v_keys_1062_, v_vals_1063_, v_heq_1064_, v_i_1065_, v_k_1066_);
lean_dec_ref(v_vals_1063_);
lean_dec_ref(v_keys_1062_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13(lean_object* v_00_u03b1_1068_, lean_object* v_inst_1069_, lean_object* v_00_u03b2_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(v_inst_1069_, v_x_1071_, v_x_1072_, v_x_1073_, v_x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(lean_object* v_inst_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_toApplicative_1079_; lean_object* v_toPure_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v_toApplicative_1079_ = lean_ctor_get(v_inst_1076_, 0);
lean_inc_ref(v_toApplicative_1079_);
lean_dec_ref(v_inst_1076_);
v_toPure_1080_ = lean_ctor_get(v_toApplicative_1079_, 1);
lean_inc(v_toPure_1080_);
lean_dec_ref(v_toApplicative_1079_);
v___x_1081_ = l_Lean_ShareCommon_objectFactory;
v___x_1082_ = lean_state_sharecommon(v___x_1081_, v_a_1078_, v_a_1077_);
v___x_1083_ = lean_apply_2(v_toPure_1080_, lean_box(0), v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon(lean_object* v_m_1084_, lean_object* v_00_u03b1_1085_, lean_object* v_inst_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(v_inst_1086_, v_a_1087_, v_a_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(lean_object* v_inst_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_toApplicative_1093_; lean_object* v_toPure_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_toApplicative_1093_ = lean_ctor_get(v_inst_1090_, 0);
lean_inc_ref(v_toApplicative_1093_);
lean_dec_ref(v_inst_1090_);
v_toPure_1094_ = lean_ctor_get(v_toApplicative_1093_, 1);
lean_inc(v_toPure_1094_);
lean_dec_ref(v_toApplicative_1093_);
v___x_1095_ = l_Lean_ShareCommon_persistentObjectFactory;
v___x_1096_ = lean_state_sharecommon(v___x_1095_, v_a_1092_, v_a_1091_);
v___x_1097_ = lean_apply_2(v_toPure_1094_, lean_box(0), v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_withShareCommon(lean_object* v_m_1098_, lean_object* v_00_u03b1_1099_, lean_object* v_inst_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(v_inst_1100_, v_a_1101_, v_a_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0(lean_object* v_inst_1104_, lean_object* v_00_u03b1_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(v_inst_1104_, v___y_1106_, v___y_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg(lean_object* v_inst_1109_){
_start:
{
lean_object* v___f_1110_; 
v___f_1110_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1110_, 0, v_inst_1109_);
return v___f_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon(lean_object* v_m_1111_, lean_object* v_inst_1112_){
_start:
{
lean_object* v___f_1113_; 
v___f_1113_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1113_, 0, v_inst_1112_);
return v___f_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0(lean_object* v_inst_1114_, lean_object* v_00_u03b1_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(v_inst_1114_, v___y_1116_, v___y_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg(lean_object* v_inst_1119_){
_start:
{
lean_object* v___f_1120_; 
v___f_1120_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1120_, 0, v_inst_1119_);
return v___f_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon(lean_object* v_m_1121_, lean_object* v_inst_1122_){
_start:
{
lean_object* v___f_1123_; 
v___f_1123_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1123_, 0, v_inst_1122_);
return v___f_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(lean_object* v_x_1124_){
_start:
{
lean_object* v_fst_1125_; 
v_fst_1125_ = lean_ctor_get(v_x_1124_, 0);
lean_inc(v_fst_1125_);
return v_fst_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0___boxed(lean_object* v_x_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(v_x_1126_);
lean_dec_ref(v_x_1126_);
return v_res_1127_;
}
}
static lean_object* _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = l_Lean_ShareCommon_objectFactory;
v___x_1130_ = l_ShareCommon_mkStateImpl(v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg(lean_object* v_inst_1131_, lean_object* v_x_1132_){
_start:
{
lean_object* v_toApplicative_1133_; lean_object* v_toFunctor_1134_; lean_object* v_map_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_toApplicative_1133_ = lean_ctor_get(v_inst_1131_, 0);
lean_inc_ref(v_toApplicative_1133_);
lean_dec_ref(v_inst_1131_);
v_toFunctor_1134_ = lean_ctor_get(v_toApplicative_1133_, 0);
lean_inc_ref(v_toFunctor_1134_);
lean_dec_ref(v_toApplicative_1133_);
v_map_1135_ = lean_ctor_get(v_toFunctor_1134_, 0);
lean_inc(v_map_1135_);
lean_dec_ref(v_toFunctor_1134_);
v___f_1136_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1137_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1138_ = lean_apply_1(v_x_1132_, v___x_1137_);
v___x_1139_ = lean_apply_4(v_map_1135_, lean_box(0), lean_box(0), v___f_1136_, v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run(lean_object* v_m_1140_, lean_object* v_00_u03b1_1141_, lean_object* v_inst_1142_, lean_object* v_x_1143_){
_start:
{
lean_object* v_toApplicative_1144_; lean_object* v_toFunctor_1145_; lean_object* v_map_1146_; lean_object* v___f_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v_toApplicative_1144_ = lean_ctor_get(v_inst_1142_, 0);
lean_inc_ref(v_toApplicative_1144_);
lean_dec_ref(v_inst_1142_);
v_toFunctor_1145_ = lean_ctor_get(v_toApplicative_1144_, 0);
lean_inc_ref(v_toFunctor_1145_);
lean_dec_ref(v_toApplicative_1144_);
v_map_1146_ = lean_ctor_get(v_toFunctor_1145_, 0);
lean_inc(v_map_1146_);
lean_dec_ref(v_toFunctor_1145_);
v___f_1147_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1148_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1149_ = lean_apply_1(v_x_1143_, v___x_1148_);
v___x_1150_ = lean_apply_4(v_map_1146_, lean_box(0), lean_box(0), v___f_1147_, v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = l_Lean_ShareCommon_persistentObjectFactory;
v___x_1152_ = l_ShareCommon_mkStateImpl(v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_run___redArg(lean_object* v_inst_1153_, lean_object* v_x_1154_){
_start:
{
lean_object* v_toApplicative_1155_; lean_object* v_toFunctor_1156_; lean_object* v_map_1157_; lean_object* v___f_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v_toApplicative_1155_ = lean_ctor_get(v_inst_1153_, 0);
lean_inc_ref(v_toApplicative_1155_);
lean_dec_ref(v_inst_1153_);
v_toFunctor_1156_ = lean_ctor_get(v_toApplicative_1155_, 0);
lean_inc_ref(v_toFunctor_1156_);
lean_dec_ref(v_toApplicative_1155_);
v_map_1157_ = lean_ctor_get(v_toFunctor_1156_, 0);
lean_inc(v_map_1157_);
lean_dec_ref(v_toFunctor_1156_);
v___f_1158_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1159_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1160_ = lean_apply_1(v_x_1154_, v___x_1159_);
v___x_1161_ = lean_apply_4(v_map_1157_, lean_box(0), lean_box(0), v___f_1158_, v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_run(lean_object* v_m_1162_, lean_object* v_00_u03b1_1163_, lean_object* v_inst_1164_, lean_object* v_x_1165_){
_start:
{
lean_object* v_toApplicative_1166_; lean_object* v_toFunctor_1167_; lean_object* v_map_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_toApplicative_1166_ = lean_ctor_get(v_inst_1164_, 0);
lean_inc_ref(v_toApplicative_1166_);
lean_dec_ref(v_inst_1164_);
v_toFunctor_1167_ = lean_ctor_get(v_toApplicative_1166_, 0);
lean_inc_ref(v_toFunctor_1167_);
lean_dec_ref(v_toApplicative_1166_);
v_map_1168_ = lean_ctor_get(v_toFunctor_1167_, 0);
lean_inc(v_map_1168_);
lean_dec_ref(v_toFunctor_1167_);
v___f_1169_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1170_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1171_ = lean_apply_1(v_x_1165_, v___x_1170_);
v___x_1172_ = lean_apply_4(v_map_1168_, lean_box(0), lean_box(0), v___f_1169_, v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonM_run___redArg(lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v_fst_1176_; 
v___x_1174_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1175_ = lean_apply_1(v_a_1173_, v___x_1174_);
v_fst_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_fst_1176_);
lean_dec_ref(v___x_1175_);
return v_fst_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonM_run(lean_object* v_00_u03b1_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v_fst_1181_; 
v___x_1179_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1180_ = lean_apply_1(v_a_1178_, v___x_1179_);
v_fst_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_fst_1181_);
lean_dec_ref(v___x_1180_);
return v_fst_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonM_run___redArg(lean_object* v_a_1182_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v_fst_1185_; 
v___x_1183_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1184_ = lean_apply_1(v_a_1182_, v___x_1183_);
v_fst_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_fst_1185_);
lean_dec_ref(v___x_1184_);
return v_fst_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonM_run(lean_object* v_00_u03b1_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v_fst_1190_; 
v___x_1188_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1189_ = lean_apply_1(v_a_1187_, v___x_1188_);
v_fst_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_fst_1190_);
lean_dec_ref(v___x_1189_);
return v_fst_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = l_Lean_ShareCommon_objectFactory;
v___x_1194_ = lean_state_sharecommon(v___x_1193_, v_a_1192_, v_a_1191_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0(lean_object* v_00_u03b1_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(v_a_1196_, v_a_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_shareCommon___redArg(lean_object* v_a_1199_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v_fst_1202_; 
v___x_1200_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1201_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(v_a_1199_, v___x_1200_);
v_fst_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_fst_1202_);
lean_dec_ref(v___x_1201_);
return v_fst_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_shareCommon(lean_object* v_00_u03b1_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_ShareCommon_shareCommon___redArg(v_a_1204_);
return v___x_1205_;
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
