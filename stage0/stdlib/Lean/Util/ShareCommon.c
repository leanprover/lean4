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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(lean_object* v_inst_47_, lean_object* v_a_48_, lean_object* v_x_49_){
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
lean_dec_ref_known(v_x_49_, 3);
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_47_ = stack[0].m_obj;
lean_object* v_a_48_ = stack[1].m_obj;
lean_object* v_x_49_ = stack[2].m_obj;
uint8_t v_res_57_;
v_res_57_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_47_, v_a_48_, v_x_49_);
stack->m_num = v_res_57_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg___boxed(lean_object* v_inst_58_, lean_object* v_a_59_, lean_object* v_x_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_58_, v_a_59_, v_x_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13___redArg(lean_object* v_inst_63_, lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
lean_dec_ref(v_inst_63_);
return v_x_64_;
}
else
{
lean_object* v_key_66_; lean_object* v_value_67_; lean_object* v_tail_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_93_; 
v_key_66_ = lean_ctor_get(v_x_65_, 0);
v_value_67_ = lean_ctor_get(v_x_65_, 1);
v_tail_68_ = lean_ctor_get(v_x_65_, 2);
v_isSharedCheck_93_ = !lean_is_exclusive(v_x_65_);
if (v_isSharedCheck_93_ == 0)
{
v___x_70_ = v_x_65_;
v_isShared_71_ = v_isSharedCheck_93_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_tail_68_);
lean_inc(v_value_67_);
lean_inc(v_key_66_);
lean_dec(v_x_65_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_93_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_72_; lean_object* v___x_73_; uint64_t v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; uint64_t v_fold_78_; uint64_t v___x_79_; uint64_t v___x_80_; uint64_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; size_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_72_ = lean_array_get_size(v_x_64_);
lean_inc_ref(v_inst_63_);
lean_inc(v_key_66_);
v___x_73_ = lean_apply_1(v_inst_63_, v_key_66_);
v___x_74_ = 32ULL;
v___x_75_ = lean_unbox_uint64(v___x_73_);
v___x_76_ = lean_uint64_shift_right(v___x_75_, v___x_74_);
v___x_77_ = lean_unbox_uint64(v___x_73_);
lean_dec_ref(v___x_73_);
v_fold_78_ = lean_uint64_xor(v___x_77_, v___x_76_);
v___x_79_ = 16ULL;
v___x_80_ = lean_uint64_shift_right(v_fold_78_, v___x_79_);
v___x_81_ = lean_uint64_xor(v_fold_78_, v___x_80_);
v___x_82_ = lean_uint64_to_usize(v___x_81_);
v___x_83_ = lean_usize_of_nat(v___x_72_);
v___x_84_ = ((size_t)1ULL);
v___x_85_ = lean_usize_sub(v___x_83_, v___x_84_);
v___x_86_ = lean_usize_land(v___x_82_, v___x_85_);
v___x_87_ = lean_array_uget_borrowed(v_x_64_, v___x_86_);
lean_inc(v___x_87_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 2, v___x_87_);
v___x_89_ = v___x_70_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_key_66_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_value_67_);
lean_ctor_set(v_reuseFailAlloc_92_, 2, v___x_87_);
v___x_89_ = v_reuseFailAlloc_92_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_90_; 
v___x_90_ = lean_array_uset(v_x_64_, v___x_86_, v___x_89_);
v_x_64_ = v___x_90_;
v_x_65_ = v_tail_68_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10___redArg(lean_object* v_inst_94_, lean_object* v_i_95_, lean_object* v_source_96_, lean_object* v_target_97_){
_start:
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_array_get_size(v_source_96_);
v___x_99_ = lean_nat_dec_lt(v_i_95_, v___x_98_);
if (v___x_99_ == 0)
{
lean_dec_ref(v_source_96_);
lean_dec(v_i_95_);
lean_dec_ref(v_inst_94_);
return v_target_97_;
}
else
{
lean_object* v_es_100_; lean_object* v___x_101_; lean_object* v_source_102_; lean_object* v_target_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_es_100_ = lean_array_fget(v_source_96_, v_i_95_);
v___x_101_ = lean_box(0);
v_source_102_ = lean_array_fset(v_source_96_, v_i_95_, v___x_101_);
lean_inc_ref(v_inst_94_);
v_target_103_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13___redArg(v_inst_94_, v_target_97_, v_es_100_);
v___x_104_ = lean_unsigned_to_nat(1u);
v___x_105_ = lean_nat_add(v_i_95_, v___x_104_);
lean_dec(v_i_95_);
v_i_95_ = v___x_105_;
v_source_96_ = v_source_102_;
v_target_97_ = v_target_103_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(lean_object* v_inst_107_, lean_object* v_data_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v_nbuckets_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_109_ = lean_array_get_size(v_data_108_);
v___x_110_ = lean_unsigned_to_nat(2u);
v_nbuckets_111_ = lean_nat_mul(v___x_109_, v___x_110_);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_box(0);
v___x_114_ = lean_mk_array(v_nbuckets_111_, v___x_113_);
v___x_115_ = lean_array_propagate_mark(v_data_108_, v___x_114_);
v___x_116_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10___redArg(v_inst_107_, v___x_112_, v_data_108_, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_m_119_, lean_object* v_a_120_, lean_object* v_b_121_){
_start:
{
lean_object* v_size_122_; lean_object* v_buckets_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v___x_129_; uint64_t v_fold_130_; uint64_t v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; size_t v___x_138_; lean_object* v_bkt_139_; uint8_t v___x_140_; 
v_size_122_ = lean_ctor_get(v_m_119_, 0);
v_buckets_123_ = lean_ctor_get(v_m_119_, 1);
v___x_124_ = lean_array_get_size(v_buckets_123_);
lean_inc_ref(v_inst_118_);
lean_inc_n(v_a_120_, 2);
v___x_125_ = lean_apply_1(v_inst_118_, v_a_120_);
v___x_126_ = 32ULL;
v___x_127_ = lean_unbox_uint64(v___x_125_);
v___x_128_ = lean_uint64_shift_right(v___x_127_, v___x_126_);
v___x_129_ = lean_unbox_uint64(v___x_125_);
lean_dec_ref(v___x_125_);
v_fold_130_ = lean_uint64_xor(v___x_129_, v___x_128_);
v___x_131_ = 16ULL;
v___x_132_ = lean_uint64_shift_right(v_fold_130_, v___x_131_);
v___x_133_ = lean_uint64_xor(v_fold_130_, v___x_132_);
v___x_134_ = lean_uint64_to_usize(v___x_133_);
v___x_135_ = lean_usize_of_nat(v___x_124_);
v___x_136_ = ((size_t)1ULL);
v___x_137_ = lean_usize_sub(v___x_135_, v___x_136_);
v___x_138_ = lean_usize_land(v___x_134_, v___x_137_);
v_bkt_139_ = lean_array_uget_borrowed(v_buckets_123_, v___x_138_);
lean_inc(v_bkt_139_);
v___x_140_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_117_, v_a_120_, v_bkt_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_161_; 
lean_inc_ref(v_buckets_123_);
lean_inc(v_size_122_);
v_isSharedCheck_161_ = !lean_is_exclusive(v_m_119_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; lean_object* v_unused_163_; 
v_unused_162_ = lean_ctor_get(v_m_119_, 1);
lean_dec(v_unused_162_);
v_unused_163_ = lean_ctor_get(v_m_119_, 0);
lean_dec(v_unused_163_);
v___x_142_ = v_m_119_;
v_isShared_143_ = v_isSharedCheck_161_;
goto v_resetjp_141_;
}
else
{
lean_dec(v_m_119_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_161_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v_size_x27_145_; lean_object* v___x_146_; lean_object* v_buckets_x27_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v_size_x27_145_ = lean_nat_add(v_size_122_, v___x_144_);
lean_dec(v_size_122_);
lean_inc(v_bkt_139_);
v___x_146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_146_, 0, v_a_120_);
lean_ctor_set(v___x_146_, 1, v_b_121_);
lean_ctor_set(v___x_146_, 2, v_bkt_139_);
v_buckets_x27_147_ = lean_array_uset(v_buckets_123_, v___x_138_, v___x_146_);
v___x_148_ = lean_unsigned_to_nat(4u);
v___x_149_ = lean_nat_mul(v_size_x27_145_, v___x_148_);
v___x_150_ = lean_unsigned_to_nat(3u);
v___x_151_ = lean_nat_div(v___x_149_, v___x_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_array_get_size(v_buckets_x27_147_);
v___x_153_ = lean_nat_dec_le(v___x_151_, v___x_152_);
lean_dec(v___x_151_);
if (v___x_153_ == 0)
{
lean_object* v_val_154_; lean_object* v___x_156_; 
v_val_154_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_118_, v_buckets_x27_147_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v_val_154_);
lean_ctor_set(v___x_142_, 0, v_size_x27_145_);
v___x_156_ = v___x_142_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_size_x27_145_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_val_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
else
{
lean_object* v___x_159_; 
lean_dec_ref(v_inst_118_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v_buckets_x27_147_);
lean_ctor_set(v___x_142_, 0, v_size_x27_145_);
v___x_159_ = v___x_142_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_size_x27_145_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_buckets_x27_147_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_dec(v_b_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_inst_118_);
return v_m_119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__5___redArg(lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_x_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_box(0);
v___x_169_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(v_inst_164_, v_inst_165_, v_x_166_, v___y_167_, v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__5(lean_object* v_00_u03b1_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_x_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_ShareCommon_objectFactory___elam__5___redArg(v_inst_171_, v_inst_172_, v_x_173_, v___y_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(lean_object* v_inst_176_, lean_object* v_a_177_, lean_object* v_b_178_, lean_object* v_x_179_){
_start:
{
if (lean_obj_tag(v_x_179_) == 0)
{
lean_dec(v_b_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_inst_176_);
return v_x_179_;
}
else
{
lean_object* v_key_180_; lean_object* v_value_181_; lean_object* v_tail_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_195_; 
v_key_180_ = lean_ctor_get(v_x_179_, 0);
v_value_181_ = lean_ctor_get(v_x_179_, 1);
v_tail_182_ = lean_ctor_get(v_x_179_, 2);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_195_ == 0)
{
v___x_184_ = v_x_179_;
v_isShared_185_ = v_isSharedCheck_195_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_tail_182_);
lean_inc(v_value_181_);
lean_inc(v_key_180_);
lean_dec(v_x_179_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_195_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; uint8_t v___x_187_; 
lean_inc_ref(v_inst_176_);
lean_inc(v_a_177_);
lean_inc(v_key_180_);
v___x_186_ = lean_apply_2(v_inst_176_, v_key_180_, v_a_177_);
v___x_187_ = lean_unbox(v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_176_, v_a_177_, v_b_178_, v_tail_182_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 2, v___x_188_);
v___x_190_ = v___x_184_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_key_180_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_value_181_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
else
{
lean_object* v___x_193_; 
lean_dec(v_value_181_);
lean_dec(v_key_180_);
lean_dec_ref(v_inst_176_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v_b_178_);
lean_ctor_set(v___x_184_, 0, v_a_177_);
v___x_193_ = v___x_184_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_177_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_b_178_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_tail_182_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_m_198_, lean_object* v_a_199_, lean_object* v_b_200_){
_start:
{
lean_object* v_size_201_; lean_object* v_buckets_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_247_; 
v_size_201_ = lean_ctor_get(v_m_198_, 0);
v_buckets_202_ = lean_ctor_get(v_m_198_, 1);
v_isSharedCheck_247_ = !lean_is_exclusive(v_m_198_);
if (v_isSharedCheck_247_ == 0)
{
v___x_204_ = v_m_198_;
v_isShared_205_ = v_isSharedCheck_247_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_buckets_202_);
lean_inc(v_size_201_);
lean_dec(v_m_198_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_247_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; uint64_t v___x_208_; uint64_t v___x_209_; uint64_t v___x_210_; uint64_t v___x_211_; uint64_t v_fold_212_; uint64_t v___x_213_; uint64_t v___x_214_; uint64_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; lean_object* v_bkt_221_; uint8_t v___x_222_; 
v___x_206_ = lean_array_get_size(v_buckets_202_);
lean_inc_ref(v_inst_197_);
lean_inc_n(v_a_199_, 2);
v___x_207_ = lean_apply_1(v_inst_197_, v_a_199_);
v___x_208_ = 32ULL;
v___x_209_ = lean_unbox_uint64(v___x_207_);
v___x_210_ = lean_uint64_shift_right(v___x_209_, v___x_208_);
v___x_211_ = lean_unbox_uint64(v___x_207_);
lean_dec_ref(v___x_207_);
v_fold_212_ = lean_uint64_xor(v___x_211_, v___x_210_);
v___x_213_ = 16ULL;
v___x_214_ = lean_uint64_shift_right(v_fold_212_, v___x_213_);
v___x_215_ = lean_uint64_xor(v_fold_212_, v___x_214_);
v___x_216_ = lean_uint64_to_usize(v___x_215_);
v___x_217_ = lean_usize_of_nat(v___x_206_);
v___x_218_ = ((size_t)1ULL);
v___x_219_ = lean_usize_sub(v___x_217_, v___x_218_);
v___x_220_ = lean_usize_land(v___x_216_, v___x_219_);
v_bkt_221_ = lean_array_uget_borrowed(v_buckets_202_, v___x_220_);
lean_inc(v_bkt_221_);
lean_inc_ref(v_inst_196_);
v___x_222_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_196_, v_a_199_, v_bkt_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; lean_object* v_size_x27_224_; lean_object* v___x_225_; lean_object* v_buckets_x27_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
lean_dec_ref(v_inst_196_);
v___x_223_ = lean_unsigned_to_nat(1u);
v_size_x27_224_ = lean_nat_add(v_size_201_, v___x_223_);
lean_dec(v_size_201_);
lean_inc(v_bkt_221_);
v___x_225_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_225_, 0, v_a_199_);
lean_ctor_set(v___x_225_, 1, v_b_200_);
lean_ctor_set(v___x_225_, 2, v_bkt_221_);
v_buckets_x27_226_ = lean_array_uset(v_buckets_202_, v___x_220_, v___x_225_);
v___x_227_ = lean_unsigned_to_nat(4u);
v___x_228_ = lean_nat_mul(v_size_x27_224_, v___x_227_);
v___x_229_ = lean_unsigned_to_nat(3u);
v___x_230_ = lean_nat_div(v___x_228_, v___x_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_array_get_size(v_buckets_x27_226_);
v___x_232_ = lean_nat_dec_le(v___x_230_, v___x_231_);
lean_dec(v___x_230_);
if (v___x_232_ == 0)
{
lean_object* v_val_233_; lean_object* v___x_235_; 
v_val_233_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_197_, v_buckets_x27_226_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v_val_233_);
lean_ctor_set(v___x_204_, 0, v_size_x27_224_);
v___x_235_ = v___x_204_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_size_x27_224_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_val_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
else
{
lean_object* v___x_238_; 
lean_dec_ref(v_inst_197_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v_buckets_x27_226_);
lean_ctor_set(v___x_204_, 0, v_size_x27_224_);
v___x_238_ = v___x_204_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_size_x27_224_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_buckets_x27_226_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
else
{
lean_object* v___x_240_; lean_object* v_buckets_x27_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
lean_inc(v_bkt_221_);
lean_dec_ref(v_inst_197_);
v___x_240_ = lean_box(0);
v_buckets_x27_241_ = lean_array_uset(v_buckets_202_, v___x_220_, v___x_240_);
v___x_242_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_196_, v_a_199_, v_b_200_, v_bkt_221_);
v___x_243_ = lean_array_uset(v_buckets_x27_241_, v___x_220_, v___x_242_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_243_);
v___x_245_ = v___x_204_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_size_201_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__2(lean_object* v_00_u03b1_248_, lean_object* v_00_u03b2_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_x_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_250_, v_inst_251_, v_x_252_, v___y_253_, v___y_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(lean_object* v_inst_256_, lean_object* v_a_257_, lean_object* v_x_258_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
lean_object* v___x_259_; 
lean_dec(v_a_257_);
lean_dec_ref(v_inst_256_);
v___x_259_ = lean_box(0);
return v___x_259_;
}
else
{
lean_object* v_key_260_; lean_object* v_tail_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_key_260_ = lean_ctor_get(v_x_258_, 0);
lean_inc_n(v_key_260_, 2);
v_tail_261_ = lean_ctor_get(v_x_258_, 2);
lean_inc(v_tail_261_);
lean_dec_ref_known(v_x_258_, 3);
lean_inc_ref(v_inst_256_);
lean_inc(v_a_257_);
v___x_262_ = lean_apply_2(v_inst_256_, v_key_260_, v_a_257_);
v___x_263_ = lean_unbox(v___x_262_);
if (v___x_263_ == 0)
{
lean_dec(v_key_260_);
v_x_258_ = v_tail_261_;
goto _start;
}
else
{
lean_object* v___x_265_; 
lean_dec(v_tail_261_);
lean_dec(v_a_257_);
lean_dec_ref(v_inst_256_);
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v_key_260_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_m_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_buckets_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v___x_275_; uint64_t v___x_276_; uint64_t v_fold_277_; uint64_t v___x_278_; uint64_t v___x_279_; uint64_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_buckets_270_ = lean_ctor_get(v_m_268_, 1);
v___x_271_ = lean_array_get_size(v_buckets_270_);
lean_inc(v_a_269_);
v___x_272_ = lean_apply_1(v_inst_267_, v_a_269_);
v___x_273_ = 32ULL;
v___x_274_ = lean_unbox_uint64(v___x_272_);
v___x_275_ = lean_uint64_shift_right(v___x_274_, v___x_273_);
v___x_276_ = lean_unbox_uint64(v___x_272_);
lean_dec_ref(v___x_272_);
v_fold_277_ = lean_uint64_xor(v___x_276_, v___x_275_);
v___x_278_ = 16ULL;
v___x_279_ = lean_uint64_shift_right(v_fold_277_, v___x_278_);
v___x_280_ = lean_uint64_xor(v_fold_277_, v___x_279_);
v___x_281_ = lean_uint64_to_usize(v___x_280_);
v___x_282_ = lean_usize_of_nat(v___x_271_);
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_sub(v___x_282_, v___x_283_);
v___x_285_ = lean_usize_land(v___x_281_, v___x_284_);
v___x_286_ = lean_array_uget_borrowed(v_buckets_270_, v___x_285_);
lean_inc(v___x_286_);
v___x_287_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(v_inst_266_, v_a_269_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg___boxed(lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_m_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_288_, v_inst_289_, v_m_290_, v_a_291_);
lean_dec_ref(v_m_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4(lean_object* v_00_u03b1_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_x_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_294_, v_inst_295_, v_x_296_, v___y_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___boxed(lean_object* v_00_u03b1_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_x_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_ShareCommon_objectFactory___elam__4(v_00_u03b1_299_, v_inst_300_, v_inst_301_, v_x_302_, v___y_303_);
lean_dec_ref(v_x_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(lean_object* v_inst_305_, lean_object* v_a_306_, lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_object* v___x_308_; 
lean_dec(v_a_306_);
lean_dec_ref(v_inst_305_);
v___x_308_ = lean_box(0);
return v___x_308_;
}
else
{
lean_object* v_key_309_; lean_object* v_value_310_; lean_object* v_tail_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_key_309_ = lean_ctor_get(v_x_307_, 0);
lean_inc(v_key_309_);
v_value_310_ = lean_ctor_get(v_x_307_, 1);
lean_inc(v_value_310_);
v_tail_311_ = lean_ctor_get(v_x_307_, 2);
lean_inc(v_tail_311_);
lean_dec_ref_known(v_x_307_, 3);
lean_inc_ref(v_inst_305_);
lean_inc(v_a_306_);
v___x_312_ = lean_apply_2(v_inst_305_, v_key_309_, v_a_306_);
v___x_313_ = lean_unbox(v___x_312_);
if (v___x_313_ == 0)
{
lean_dec(v_value_310_);
v_x_307_ = v_tail_311_;
goto _start;
}
else
{
lean_object* v___x_315_; 
lean_dec(v_tail_311_);
lean_dec(v_a_306_);
lean_dec_ref(v_inst_305_);
v___x_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_315_, 0, v_value_310_);
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_m_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_buckets_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v___x_325_; uint64_t v___x_326_; uint64_t v_fold_327_; uint64_t v___x_328_; uint64_t v___x_329_; uint64_t v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_buckets_320_ = lean_ctor_get(v_m_318_, 1);
v___x_321_ = lean_array_get_size(v_buckets_320_);
lean_inc(v_a_319_);
v___x_322_ = lean_apply_1(v_inst_317_, v_a_319_);
v___x_323_ = 32ULL;
v___x_324_ = lean_unbox_uint64(v___x_322_);
v___x_325_ = lean_uint64_shift_right(v___x_324_, v___x_323_);
v___x_326_ = lean_unbox_uint64(v___x_322_);
lean_dec_ref(v___x_322_);
v_fold_327_ = lean_uint64_xor(v___x_326_, v___x_325_);
v___x_328_ = 16ULL;
v___x_329_ = lean_uint64_shift_right(v_fold_327_, v___x_328_);
v___x_330_ = lean_uint64_xor(v_fold_327_, v___x_329_);
v___x_331_ = lean_uint64_to_usize(v___x_330_);
v___x_332_ = lean_usize_of_nat(v___x_321_);
v___x_333_ = ((size_t)1ULL);
v___x_334_ = lean_usize_sub(v___x_332_, v___x_333_);
v___x_335_ = lean_usize_land(v___x_331_, v___x_334_);
v___x_336_ = lean_array_uget_borrowed(v_buckets_320_, v___x_335_);
lean_inc(v___x_336_);
v___x_337_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(v_inst_316_, v_a_319_, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg___boxed(lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_m_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_338_, v_inst_339_, v_m_340_, v_a_341_);
lean_dec_ref(v_m_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_x_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_345_, v_inst_346_, v_x_347_, v___y_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___boxed(lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_x_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_ShareCommon_objectFactory___elam__1(v_00_u03b1_350_, v_00_u03b2_351_, v_inst_352_, v_inst_353_, v_x_354_, v___y_355_);
lean_dec_ref(v_x_354_);
return v_res_356_;
}
}
static lean_object* _init_l_Lean_ShareCommon_objectFactory___closed__7(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_ShareCommon_objectFactory___closed__6));
v___x_371_ = l_ShareCommon_StateFactory_mkImpl(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_ShareCommon_objectFactory(void){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_obj_once(&l_Lean_ShareCommon_objectFactory___closed__7, &l_Lean_ShareCommon_objectFactory___closed__7_once, _init_l_Lean_ShareCommon_objectFactory___closed__7);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___redArg(lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_x_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_373_, v_inst_374_, v_x_375_, v___y_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___redArg___boxed(lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_x_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_ShareCommon_objectFactory___elam__1___redArg(v_inst_378_, v_inst_379_, v_x_380_, v___y_381_);
lean_dec_ref(v_x_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__2___redArg(lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_x_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_383_, v_inst_384_, v_x_385_, v___y_386_, v___y_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___redArg(lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_x_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_389_, v_inst_390_, v_x_391_, v___y_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___redArg___boxed(lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_x_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_ShareCommon_objectFactory___elam__4___redArg(v_inst_394_, v_inst_395_, v_x_396_, v___y_397_);
lean_dec_ref(v_x_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1(lean_object* v_00_u03b1_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_00_u03b2_402_, lean_object* v_m_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_400_, v_inst_401_, v_m_403_, v_a_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___boxed(lean_object* v_00_u03b1_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_00_u03b2_409_, lean_object* v_m_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1(v_00_u03b1_406_, v_inst_407_, v_inst_408_, v_00_u03b2_409_, v_m_410_, v_a_411_);
lean_dec_ref(v_m_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3(lean_object* v_00_u03b1_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_00_u03b2_416_, lean_object* v_m_417_, lean_object* v_a_418_, lean_object* v_b_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_414_, v_inst_415_, v_m_417_, v_a_418_, v_b_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6(lean_object* v_00_u03b1_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_00_u03b2_424_, lean_object* v_m_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_422_, v_inst_423_, v_m_425_, v_a_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___boxed(lean_object* v_00_u03b1_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_00_u03b2_431_, lean_object* v_m_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6(v_00_u03b1_428_, v_inst_429_, v_inst_430_, v_00_u03b2_431_, v_m_432_, v_a_433_);
lean_dec_ref(v_m_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8(lean_object* v_00_u03b1_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_00_u03b2_438_, lean_object* v_m_439_, lean_object* v_a_440_, lean_object* v_b_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(v_inst_436_, v_inst_437_, v_m_439_, v_a_440_, v_b_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3(lean_object* v_00_u03b1_443_, lean_object* v_inst_444_, lean_object* v_00_u03b2_445_, lean_object* v_a_446_, lean_object* v_x_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(v_inst_444_, v_a_446_, v_x_447_);
return v___x_448_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(lean_object* v_00_u03b1_449_, lean_object* v_inst_450_, lean_object* v_00_u03b2_451_, lean_object* v_a_452_, lean_object* v_x_453_){
_start:
{
uint8_t v___x_454_; 
v___x_454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_450_, v_a_452_, v_x_453_);
return v___x_454_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_450_ = stack[1].m_obj;
lean_object* v_a_452_ = stack[3].m_obj;
lean_object* v_x_453_ = stack[4].m_obj;
uint8_t v_res_455_;
v_res_455_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(lean_box(0), v_inst_450_, lean_box(0), v_a_452_, v_x_453_);
stack->m_num = v_res_455_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_456_, lean_object* v_inst_457_, lean_object* v_00_u03b2_458_, lean_object* v_a_459_, lean_object* v_x_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(v_00_u03b1_456_, v_inst_457_, v_00_u03b2_458_, v_a_459_, v_x_460_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7(lean_object* v_00_u03b1_463_, lean_object* v_inst_464_, lean_object* v_00_u03b2_465_, lean_object* v_data_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_464_, v_data_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8(lean_object* v_00_u03b1_468_, lean_object* v_inst_469_, lean_object* v_00_u03b2_470_, lean_object* v_a_471_, lean_object* v_b_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_469_, v_a_471_, v_b_472_, v_x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11(lean_object* v_00_u03b1_475_, lean_object* v_inst_476_, lean_object* v_00_u03b2_477_, lean_object* v_a_478_, lean_object* v_x_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(v_inst_476_, v_a_478_, v_x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10(lean_object* v_00_u03b1_481_, lean_object* v_inst_482_, lean_object* v_00_u03b2_483_, lean_object* v_i_484_, lean_object* v_source_485_, lean_object* v_target_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10___redArg(v_inst_482_, v_i_484_, v_source_485_, v_target_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13(lean_object* v_00_u03b1_488_, lean_object* v_00_u03b2_489_, lean_object* v_inst_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13___redArg(v_inst_490_, v_x_491_, v_x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(lean_object* v_inst_494_, lean_object* v_keys_495_, lean_object* v_vals_496_, lean_object* v_i_497_, lean_object* v_k_498_){
_start:
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_array_get_size(v_keys_495_);
v___x_500_ = lean_nat_dec_lt(v_i_497_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
lean_dec(v_k_498_);
lean_dec(v_i_497_);
lean_dec_ref(v_inst_494_);
v___x_501_ = lean_box(0);
return v___x_501_;
}
else
{
lean_object* v_k_x27_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v_k_x27_502_ = lean_array_fget_borrowed(v_keys_495_, v_i_497_);
lean_inc_ref(v_inst_494_);
lean_inc(v_k_x27_502_);
lean_inc(v_k_498_);
v___x_503_ = lean_apply_2(v_inst_494_, v_k_498_, v_k_x27_502_);
v___x_504_ = lean_unbox(v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(1u);
v___x_506_ = lean_nat_add(v_i_497_, v___x_505_);
lean_dec(v_i_497_);
v_i_497_ = v___x_506_;
goto _start;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v_k_498_);
lean_dec_ref(v_inst_494_);
v___x_508_ = lean_array_fget_borrowed(v_vals_496_, v_i_497_);
lean_dec(v_i_497_);
lean_inc(v___x_508_);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg___boxed(lean_object* v_inst_510_, lean_object* v_keys_511_, lean_object* v_vals_512_, lean_object* v_i_513_, lean_object* v_k_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_510_, v_keys_511_, v_vals_512_, v_i_513_, v_k_514_);
lean_dec_ref(v_vals_512_);
lean_dec_ref(v_keys_511_);
return v_res_515_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(lean_object* v_inst_516_, lean_object* v_x_517_, size_t v_x_518_, lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v_es_520_; lean_object* v___x_521_; size_t v___x_522_; size_t v___x_523_; lean_object* v_j_524_; lean_object* v___x_525_; 
v_es_520_ = lean_ctor_get(v_x_517_, 0);
lean_inc_ref(v_es_520_);
lean_dec_ref_known(v_x_517_, 1);
v___x_521_ = lean_box(2);
v___x_522_ = ((size_t)31ULL);
v___x_523_ = lean_usize_land(v_x_518_, v___x_522_);
v_j_524_ = lean_usize_to_nat(v___x_523_);
v___x_525_ = lean_array_get(v___x_521_, v_es_520_, v_j_524_);
lean_dec(v_j_524_);
lean_dec_ref(v_es_520_);
switch(lean_obj_tag(v___x_525_))
{
case 0:
{
lean_object* v_key_526_; lean_object* v_val_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v_key_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_key_526_);
v_val_527_ = lean_ctor_get(v___x_525_, 1);
lean_inc(v_val_527_);
lean_dec_ref_known(v___x_525_, 2);
v___x_528_ = lean_apply_2(v_inst_516_, v_x_519_, v_key_526_);
v___x_529_ = lean_unbox(v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; 
lean_dec(v_val_527_);
v___x_530_ = lean_box(0);
return v___x_530_;
}
else
{
lean_object* v___x_531_; 
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v_val_527_);
return v___x_531_;
}
}
case 1:
{
lean_object* v_node_532_; size_t v___x_533_; size_t v___x_534_; 
v_node_532_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_node_532_);
lean_dec_ref_known(v___x_525_, 1);
v___x_533_ = ((size_t)5ULL);
v___x_534_ = lean_usize_shift_right(v_x_518_, v___x_533_);
v_x_517_ = v_node_532_;
v_x_518_ = v___x_534_;
goto _start;
}
default: 
{
lean_object* v___x_536_; 
lean_dec(v_x_519_);
lean_dec_ref(v_inst_516_);
v___x_536_ = lean_box(0);
return v___x_536_;
}
}
}
else
{
lean_object* v_ks_537_; lean_object* v_vs_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_ks_537_ = lean_ctor_get(v_x_517_, 0);
lean_inc_ref(v_ks_537_);
v_vs_538_ = lean_ctor_get(v_x_517_, 1);
lean_inc_ref(v_vs_538_);
lean_dec_ref_known(v_x_517_, 2);
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_516_, v_ks_537_, v_vs_538_, v___x_539_, v_x_519_);
lean_dec_ref(v_vs_538_);
lean_dec_ref(v_ks_537_);
return v___x_540_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_516_ = stack[0].m_obj;
lean_object* v_x_517_ = stack[1].m_obj;
size_t v_x_518_ = stack[2].m_num;
lean_object* v_x_519_ = stack[3].m_obj;
lean_object* v_res_541_;
v_res_541_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_516_, v_x_517_, v_x_518_, v_x_519_);
stack->m_obj
 = v_res_541_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___boxed(lean_object* v_inst_542_, lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
size_t v_x_720__boxed_546_; lean_object* v_res_547_; 
v_x_720__boxed_546_ = lean_unbox_usize(v_x_544_);
lean_dec(v_x_544_);
v_res_547_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_542_, v_x_543_, v_x_720__boxed_546_, v_x_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
lean_object* v___x_552_; uint64_t v___x_553_; size_t v___x_554_; lean_object* v___x_555_; 
lean_inc(v_x_551_);
v___x_552_ = lean_apply_1(v_inst_549_, v_x_551_);
v___x_553_ = lean_unbox_uint64(v___x_552_);
lean_dec_ref(v___x_552_);
v___x_554_ = lean_uint64_to_usize(v___x_553_);
lean_inc_ref(v_x_550_);
v___x_555_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_548_, v_x_550_, v___x_554_, v_x_551_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg___boxed(lean_object* v_inst_556_, lean_object* v_inst_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_556_, v_inst_557_, v_x_558_, v_x_559_);
lean_dec_ref(v_x_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1(lean_object* v_00_u03b1_561_, lean_object* v_00_u03b2_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_x_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_563_, v_inst_564_, v_x_565_, v___y_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___boxed(lean_object* v_00_u03b1_568_, lean_object* v_00_u03b2_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_x_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_ShareCommon_persistentObjectFactory___elam__1(v_00_u03b1_568_, v_00_u03b2_569_, v_inst_570_, v_inst_571_, v_x_572_, v___y_573_);
lean_dec_ref(v_x_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(lean_object* v_inst_575_, lean_object* v_keys_576_, lean_object* v_vals_577_, lean_object* v_i_578_, lean_object* v_k_579_){
_start:
{
lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_580_ = lean_array_get_size(v_keys_576_);
v___x_581_ = lean_nat_dec_lt(v_i_578_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec(v_k_579_);
lean_dec(v_i_578_);
lean_dec_ref(v_inst_575_);
v___x_582_ = lean_box(0);
return v___x_582_;
}
else
{
lean_object* v_k_x27_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v_k_x27_583_ = lean_array_fget_borrowed(v_keys_576_, v_i_578_);
lean_inc_ref(v_inst_575_);
lean_inc(v_k_x27_583_);
lean_inc(v_k_579_);
v___x_584_ = lean_apply_2(v_inst_575_, v_k_579_, v_k_x27_583_);
v___x_585_ = lean_unbox(v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = lean_nat_add(v_i_578_, v___x_586_);
lean_dec(v_i_578_);
v_i_578_ = v___x_587_;
goto _start;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
lean_dec(v_k_579_);
lean_dec_ref(v_inst_575_);
v___x_589_ = lean_array_fget_borrowed(v_vals_577_, v_i_578_);
lean_dec(v_i_578_);
lean_inc(v___x_589_);
lean_inc(v_k_x27_583_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v_k_x27_583_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object* v_inst_592_, lean_object* v_keys_593_, lean_object* v_vals_594_, lean_object* v_i_595_, lean_object* v_k_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_592_, v_keys_593_, v_vals_594_, v_i_595_, v_k_596_);
lean_dec_ref(v_vals_594_);
lean_dec_ref(v_keys_593_);
return v_res_597_;
}
}
lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(lean_object* v_inst_598_, lean_object* v_x_599_, size_t v_x_600_, lean_object* v_x_601_){
_start:
{
if (lean_obj_tag(v_x_599_) == 0)
{
lean_object* v_es_602_; lean_object* v___x_603_; size_t v___x_604_; size_t v___x_605_; lean_object* v_j_606_; lean_object* v___x_607_; 
v_es_602_ = lean_ctor_get(v_x_599_, 0);
lean_inc_ref(v_es_602_);
lean_dec_ref_known(v_x_599_, 1);
v___x_603_ = lean_box(2);
v___x_604_ = ((size_t)31ULL);
v___x_605_ = lean_usize_land(v_x_600_, v___x_604_);
v_j_606_ = lean_usize_to_nat(v___x_605_);
v___x_607_ = lean_array_get(v___x_603_, v_es_602_, v_j_606_);
lean_dec(v_j_606_);
lean_dec_ref(v_es_602_);
switch(lean_obj_tag(v___x_607_))
{
case 0:
{
lean_object* v_key_608_; lean_object* v_val_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_key_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc_n(v_key_608_, 2);
v_val_609_ = lean_ctor_get(v___x_607_, 1);
lean_inc(v_val_609_);
lean_dec_ref_known(v___x_607_, 2);
v___x_610_ = lean_apply_2(v_inst_598_, v_x_601_, v_key_608_);
v___x_611_ = lean_unbox(v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
lean_dec(v_val_609_);
lean_dec(v_key_608_);
v___x_612_ = lean_box(0);
return v___x_612_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v_key_608_);
lean_ctor_set(v___x_613_, 1, v_val_609_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
return v___x_614_;
}
}
case 1:
{
lean_object* v_node_615_; size_t v___x_616_; size_t v___x_617_; 
v_node_615_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_node_615_);
lean_dec_ref_known(v___x_607_, 1);
v___x_616_ = ((size_t)5ULL);
v___x_617_ = lean_usize_shift_right(v_x_600_, v___x_616_);
v_x_599_ = v_node_615_;
v_x_600_ = v___x_617_;
goto _start;
}
default: 
{
lean_object* v___x_619_; 
lean_dec(v_x_601_);
lean_dec_ref(v_inst_598_);
v___x_619_ = lean_box(0);
return v___x_619_;
}
}
}
else
{
lean_object* v_ks_620_; lean_object* v_vs_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_ks_620_ = lean_ctor_get(v_x_599_, 0);
lean_inc_ref(v_ks_620_);
v_vs_621_ = lean_ctor_get(v_x_599_, 1);
lean_inc_ref(v_vs_621_);
lean_dec_ref_known(v_x_599_, 2);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_598_, v_ks_620_, v_vs_621_, v___x_622_, v_x_601_);
lean_dec_ref(v_vs_621_);
lean_dec_ref(v_ks_620_);
return v___x_623_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_598_ = stack[0].m_obj;
lean_object* v_x_599_ = stack[1].m_obj;
size_t v_x_600_ = stack[2].m_num;
lean_object* v_x_601_ = stack[3].m_obj;
lean_object* v_res_624_;
v_res_624_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_598_, v_x_599_, v_x_600_, v_x_601_);
stack->m_obj
 = v_res_624_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg___boxed(lean_object* v_inst_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
size_t v_x_903__boxed_629_; lean_object* v_res_630_; 
v_x_903__boxed_629_ = lean_unbox_usize(v_x_627_);
lean_dec(v_x_627_);
v_res_630_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_625_, v_x_626_, v_x_903__boxed_629_, v_x_628_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
lean_object* v___x_635_; uint64_t v___x_636_; size_t v___x_637_; lean_object* v___x_638_; 
lean_inc(v_x_634_);
v___x_635_ = lean_apply_1(v_inst_632_, v_x_634_);
v___x_636_ = lean_unbox_uint64(v___x_635_);
lean_dec_ref(v___x_635_);
v___x_637_ = lean_uint64_to_usize(v___x_636_);
lean_inc_ref(v_x_633_);
v___x_638_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_631_, v_x_633_, v___x_637_, v_x_634_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg___boxed(lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_639_, v_inst_640_, v_x_641_, v_x_642_);
lean_dec_ref(v_x_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_x_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_644_, v_inst_645_, v_x_646_, v___y_647_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v___x_649_; 
v___x_649_ = lean_box(0);
return v___x_649_;
}
else
{
lean_object* v_val_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_658_; 
v_val_650_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_658_ == 0)
{
v___x_652_ = v___x_648_;
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_val_650_);
lean_dec(v___x_648_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_fst_654_; lean_object* v___x_656_; 
v_fst_654_ = lean_ctor_get(v_val_650_, 0);
lean_inc(v_fst_654_);
lean_dec(v_val_650_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v_fst_654_);
v___x_656_ = v___x_652_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_fst_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg___boxed(lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_x_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(v_inst_659_, v_inst_660_, v_x_661_, v___y_662_);
lean_dec_ref(v_x_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4(lean_object* v_00_u03b1_664_, lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_x_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(v_inst_665_, v_inst_666_, v_x_667_, v___y_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___boxed(lean_object* v_00_u03b1_670_, lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_x_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4(v_00_u03b1_670_, v_inst_671_, v_inst_672_, v_x_673_, v___y_674_);
lean_dec_ref(v_x_673_);
return v_res_675_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_676_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__0);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg(){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__1);
return v___x_680_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_681_;
v_res_681_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg();
stack->m_obj
 = v_res_681_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___boxed(lean_object* v___dummy_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg();
return v_res_683_;
}
}
static lean_object* _init_l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0(void){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg();
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0(lean_object* v_00_u03b1_685_, lean_object* v_00_u03b2_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_x_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0, &l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0_once, _init_l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___boxed(lean_object* v_00_u03b1_691_, lean_object* v_00_u03b2_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_x_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_ShareCommon_persistentObjectFactory___elam__0(v_00_u03b1_691_, v_00_u03b2_692_, v_inst_693_, v_inst_694_, v_x_695_);
lean_dec(v_x_695_);
lean_dec_ref(v_inst_694_);
lean_dec_ref(v_inst_693_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3(lean_object* v_00_u03b1_697_, lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_x_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0, &l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0_once, _init_l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___boxed(lean_object* v_00_u03b1_702_, lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_x_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_ShareCommon_persistentObjectFactory___elam__3(v_00_u03b1_702_, v_inst_703_, v_inst_704_, v_x_705_);
lean_dec(v_x_705_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(lean_object* v_inst_707_, lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
lean_object* v_ks_712_; lean_object* v_vs_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_738_; 
v_ks_712_ = lean_ctor_get(v_x_708_, 0);
v_vs_713_ = lean_ctor_get(v_x_708_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_x_708_);
if (v_isSharedCheck_738_ == 0)
{
v___x_715_ = v_x_708_;
v_isShared_716_ = v_isSharedCheck_738_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_vs_713_);
lean_inc(v_ks_712_);
lean_dec(v_x_708_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_738_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = lean_array_get_size(v_ks_712_);
v___x_718_ = lean_nat_dec_lt(v_x_709_, v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
lean_dec(v_x_709_);
lean_dec_ref(v_inst_707_);
v___x_719_ = lean_array_push(v_ks_712_, v_x_710_);
v___x_720_ = lean_array_push(v_vs_713_, v_x_711_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v___x_720_);
lean_ctor_set(v___x_715_, 0, v___x_719_);
v___x_722_ = v___x_715_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
else
{
lean_object* v_k_x27_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_k_x27_724_ = lean_array_fget_borrowed(v_ks_712_, v_x_709_);
lean_inc_ref(v_inst_707_);
lean_inc(v_k_x27_724_);
lean_inc(v_x_710_);
v___x_725_ = lean_apply_2(v_inst_707_, v_x_710_, v_k_x27_724_);
v___x_726_ = lean_unbox(v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_728_; 
if (v_isShared_716_ == 0)
{
v___x_728_ = v___x_715_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_ks_712_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_vs_713_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = lean_nat_add(v_x_709_, v___x_729_);
lean_dec(v_x_709_);
v_x_708_ = v___x_728_;
v_x_709_ = v___x_730_;
goto _start;
}
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
lean_dec_ref(v_inst_707_);
v___x_733_ = lean_array_fset(v_ks_712_, v_x_709_, v_x_710_);
v___x_734_ = lean_array_fset(v_vs_713_, v_x_709_, v_x_711_);
lean_dec(v_x_709_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v___x_734_);
lean_ctor_set(v___x_715_, 0, v___x_733_);
v___x_736_ = v___x_715_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(lean_object* v_inst_739_, lean_object* v_n_740_, lean_object* v_k_741_, lean_object* v_v_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(v_inst_739_, v_n_740_, v___x_743_, v_k_741_, v_v_742_);
return v___x_744_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_745_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_x_748_, size_t v_x_749_, size_t v_x_750_, lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v_es_753_; size_t v___x_754_; size_t v___x_755_; lean_object* v_j_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v_es_753_ = lean_ctor_get(v_x_748_, 0);
v___x_754_ = ((size_t)31ULL);
v___x_755_ = lean_usize_land(v_x_749_, v___x_754_);
v_j_756_ = lean_usize_to_nat(v___x_755_);
v___x_757_ = lean_array_get_size(v_es_753_);
v___x_758_ = lean_nat_dec_lt(v_j_756_, v___x_757_);
if (v___x_758_ == 0)
{
lean_dec(v_j_756_);
lean_dec(v_x_752_);
lean_dec(v_x_751_);
lean_dec_ref(v_inst_747_);
lean_dec_ref(v_inst_746_);
return v_x_748_;
}
else
{
lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_798_; 
lean_inc_ref(v_es_753_);
v_isSharedCheck_798_ = !lean_is_exclusive(v_x_748_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v_x_748_, 0);
lean_dec(v_unused_799_);
v___x_760_ = v_x_748_;
v_isShared_761_ = v_isSharedCheck_798_;
goto v_resetjp_759_;
}
else
{
lean_dec(v_x_748_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_798_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_v_762_; lean_object* v___x_763_; lean_object* v_xs_x27_764_; lean_object* v___y_766_; 
v_v_762_ = lean_array_fget(v_es_753_, v_j_756_);
v___x_763_ = lean_box(0);
v_xs_x27_764_ = lean_array_fset(v_es_753_, v_j_756_, v___x_763_);
switch(lean_obj_tag(v_v_762_))
{
case 0:
{
lean_object* v_key_771_; lean_object* v_val_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v_inst_747_);
v_key_771_ = lean_ctor_get(v_v_762_, 0);
v_val_772_ = lean_ctor_get(v_v_762_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_v_762_);
if (v_isSharedCheck_783_ == 0)
{
v___x_774_ = v_v_762_;
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_val_772_);
lean_inc(v_key_771_);
lean_dec(v_v_762_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; uint8_t v___x_777_; 
lean_inc(v_key_771_);
lean_inc(v_x_751_);
v___x_776_ = lean_apply_2(v_inst_746_, v_x_751_, v_key_771_);
v___x_777_ = lean_unbox(v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; 
lean_del_object(v___x_774_);
v___x_778_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_771_, v_val_772_, v_x_751_, v_x_752_);
v___x_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
v___y_766_ = v___x_779_;
goto v___jp_765_;
}
else
{
lean_object* v___x_781_; 
lean_dec(v_val_772_);
lean_dec(v_key_771_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v_x_752_);
lean_ctor_set(v___x_774_, 0, v_x_751_);
v___x_781_ = v___x_774_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_x_751_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_x_752_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
v___y_766_ = v___x_781_;
goto v___jp_765_;
}
}
}
}
case 1:
{
lean_object* v_node_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_796_; 
v_node_784_ = lean_ctor_get(v_v_762_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_v_762_);
if (v_isSharedCheck_796_ == 0)
{
v___x_786_ = v_v_762_;
v_isShared_787_ = v_isSharedCheck_796_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_node_784_);
lean_dec(v_v_762_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_796_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
size_t v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_788_ = ((size_t)5ULL);
v___x_789_ = lean_usize_shift_right(v_x_749_, v___x_788_);
v___x_790_ = ((size_t)1ULL);
v___x_791_ = lean_usize_add(v_x_750_, v___x_790_);
v___x_792_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_746_, v_inst_747_, v_node_784_, v___x_789_, v___x_791_, v_x_751_, v_x_752_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_792_);
v___x_794_ = v___x_786_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
v___y_766_ = v___x_794_;
goto v___jp_765_;
}
}
}
default: 
{
lean_object* v___x_797_; 
lean_dec_ref(v_inst_747_);
lean_dec_ref(v_inst_746_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_x_751_);
lean_ctor_set(v___x_797_, 1, v_x_752_);
v___y_766_ = v___x_797_;
goto v___jp_765_;
}
}
v___jp_765_:
{
lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_767_ = lean_array_fset(v_xs_x27_764_, v_j_756_, v___y_766_);
lean_dec(v_j_756_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_767_);
v___x_769_ = v___x_760_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
else
{
lean_object* v_ks_800_; lean_object* v_vs_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_819_; 
v_ks_800_ = lean_ctor_get(v_x_748_, 0);
v_vs_801_ = lean_ctor_get(v_x_748_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v_x_748_);
if (v_isSharedCheck_819_ == 0)
{
v___x_803_ = v_x_748_;
v_isShared_804_ = v_isSharedCheck_819_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_vs_801_);
lean_inc(v_ks_800_);
lean_dec(v_x_748_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_819_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_ks_800_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_vs_801_);
v___x_806_ = v_reuseFailAlloc_818_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v_newNode_807_; size_t v___x_808_; uint8_t v___x_809_; 
lean_inc_ref(v_inst_746_);
v_newNode_807_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(v_inst_746_, v___x_806_, v_x_751_, v_x_752_);
v___x_808_ = ((size_t)7ULL);
v___x_809_ = lean_usize_dec_le(v___x_808_, v_x_750_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_810_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_807_);
v___x_811_ = lean_unsigned_to_nat(4u);
v___x_812_ = lean_nat_dec_lt(v___x_810_, v___x_811_);
lean_dec(v___x_810_);
if (v___x_812_ == 0)
{
lean_object* v_ks_813_; lean_object* v_vs_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v_ks_813_ = lean_ctor_get(v_newNode_807_, 0);
lean_inc_ref(v_ks_813_);
v_vs_814_ = lean_ctor_get(v_newNode_807_, 1);
lean_inc_ref(v_vs_814_);
lean_dec_ref(v_newNode_807_);
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0);
v___x_817_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_746_, v_inst_747_, v_x_750_, v_ks_813_, v_vs_814_, v___x_815_, v___x_816_);
lean_dec_ref(v_vs_814_);
lean_dec_ref(v_ks_813_);
return v___x_817_;
}
else
{
lean_dec_ref(v_inst_747_);
lean_dec_ref(v_inst_746_);
return v_newNode_807_;
}
}
else
{
lean_dec_ref(v_inst_747_);
lean_dec_ref(v_inst_746_);
return v_newNode_807_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_746_ = stack[0].m_obj;
lean_object* v_inst_747_ = stack[1].m_obj;
lean_object* v_x_748_ = stack[2].m_obj;
size_t v_x_749_ = stack[3].m_num;
size_t v_x_750_ = stack[4].m_num;
lean_object* v_x_751_ = stack[5].m_obj;
lean_object* v_x_752_ = stack[6].m_obj;
lean_object* v_res_820_;
v_res_820_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_746_, v_inst_747_, v_x_748_, v_x_749_, v_x_750_, v_x_751_, v_x_752_);
stack->m_obj
 = v_res_820_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(lean_object* v_inst_821_, lean_object* v_inst_822_, size_t v_depth_823_, lean_object* v_keys_824_, lean_object* v_vals_825_, lean_object* v_i_826_, lean_object* v_entries_827_){
_start:
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = lean_array_get_size(v_keys_824_);
v___x_829_ = lean_nat_dec_lt(v_i_826_, v___x_828_);
if (v___x_829_ == 0)
{
lean_dec(v_i_826_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
return v_entries_827_;
}
else
{
lean_object* v_k_830_; lean_object* v_v_831_; lean_object* v___x_832_; uint64_t v___x_833_; size_t v_h_834_; size_t v___x_835_; lean_object* v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; size_t v_h_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_k_830_ = lean_array_fget_borrowed(v_keys_824_, v_i_826_);
v_v_831_ = lean_array_fget_borrowed(v_vals_825_, v_i_826_);
lean_inc_ref_n(v_inst_822_, 2);
lean_inc_n(v_k_830_, 2);
v___x_832_ = lean_apply_1(v_inst_822_, v_k_830_);
v___x_833_ = lean_unbox_uint64(v___x_832_);
lean_dec_ref(v___x_832_);
v_h_834_ = lean_uint64_to_usize(v___x_833_);
v___x_835_ = ((size_t)5ULL);
v___x_836_ = lean_unsigned_to_nat(1u);
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_sub(v_depth_823_, v___x_837_);
v___x_839_ = lean_usize_mul(v___x_835_, v___x_838_);
v_h_840_ = lean_usize_shift_right(v_h_834_, v___x_839_);
v___x_841_ = lean_nat_add(v_i_826_, v___x_836_);
lean_dec(v_i_826_);
lean_inc(v_v_831_);
lean_inc_ref(v_inst_821_);
v___x_842_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_821_, v_inst_822_, v_entries_827_, v_h_840_, v_depth_823_, v_k_830_, v_v_831_);
v_i_826_ = v___x_841_;
v_entries_827_ = v___x_842_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_821_ = stack[0].m_obj;
lean_object* v_inst_822_ = stack[1].m_obj;
size_t v_depth_823_ = stack[2].m_num;
lean_object* v_keys_824_ = stack[3].m_obj;
lean_object* v_vals_825_ = stack[4].m_obj;
lean_object* v_i_826_ = stack[5].m_obj;
lean_object* v_entries_827_ = stack[6].m_obj;
lean_object* v_res_844_;
v_res_844_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_821_, v_inst_822_, v_depth_823_, v_keys_824_, v_vals_825_, v_i_826_, v_entries_827_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg___boxed(lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_depth_847_, lean_object* v_keys_848_, lean_object* v_vals_849_, lean_object* v_i_850_, lean_object* v_entries_851_){
_start:
{
size_t v_depth_boxed_852_; lean_object* v_res_853_; 
v_depth_boxed_852_ = lean_unbox_usize(v_depth_847_);
lean_dec(v_depth_847_);
v_res_853_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_845_, v_inst_846_, v_depth_boxed_852_, v_keys_848_, v_vals_849_, v_i_850_, v_entries_851_);
lean_dec_ref(v_vals_849_);
lean_dec_ref(v_keys_848_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___boxed(lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
size_t v_x_1290__boxed_861_; size_t v_x_1291__boxed_862_; lean_object* v_res_863_; 
v_x_1290__boxed_861_ = lean_unbox_usize(v_x_857_);
lean_dec(v_x_857_);
v_x_1291__boxed_862_ = lean_unbox_usize(v_x_858_);
lean_dec(v_x_858_);
v_res_863_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_854_, v_inst_855_, v_x_856_, v_x_1290__boxed_861_, v_x_1291__boxed_862_, v_x_859_, v_x_860_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
lean_object* v___x_869_; uint64_t v___x_870_; size_t v___x_871_; size_t v___x_872_; lean_object* v___x_873_; 
lean_inc_ref(v_inst_865_);
lean_inc(v_x_867_);
v___x_869_ = lean_apply_1(v_inst_865_, v_x_867_);
v___x_870_ = lean_unbox_uint64(v___x_869_);
lean_dec_ref(v___x_869_);
v___x_871_ = lean_uint64_to_usize(v___x_870_);
v___x_872_ = ((size_t)1ULL);
v___x_873_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_864_, v_inst_865_, v_x_866_, v___x_871_, v___x_872_, v_x_867_, v_x_868_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__2(lean_object* v_00_u03b1_874_, lean_object* v_00_u03b2_875_, lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_x_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_876_, v_inst_877_, v_x_878_, v___y_879_, v___y_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(lean_object* v_inst_882_, lean_object* v_inst_883_, lean_object* v_x_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_box(0);
v___x_887_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_882_, v_inst_883_, v_x_884_, v___y_885_, v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__5(lean_object* v_00_u03b1_888_, lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_x_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(v_inst_889_, v_inst_890_, v_x_891_, v___y_892_);
return v___x_893_;
}
}
static lean_object* _init_l_Lean_ShareCommon_persistentObjectFactory___closed__7(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l_Lean_ShareCommon_persistentObjectFactory___closed__6));
v___x_908_ = l_ShareCommon_StateFactory_mkImpl(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_ShareCommon_persistentObjectFactory(void){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___closed__7, &l_Lean_ShareCommon_persistentObjectFactory___closed__7_once, _init_l_Lean_ShareCommon_persistentObjectFactory___closed__7);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_object* v_00_u03b1_910_, lean_object* v_inst_911_, lean_object* v_inst_912_, lean_object* v_00_u03b2_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0, &l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0_once, _init_l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___boxed(lean_object* v_00_u03b1_915_, lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_00_u03b2_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(v_00_u03b1_915_, v_inst_916_, v_inst_917_, v_00_u03b2_918_);
lean_dec_ref(v_inst_917_);
lean_dec_ref(v_inst_916_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(lean_object* v_inst_920_, lean_object* v_inst_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0, &l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0_once, _init_l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg___boxed(lean_object* v_inst_923_, lean_object* v_inst_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(v_inst_923_, v_inst_924_);
lean_dec_ref(v_inst_924_);
lean_dec_ref(v_inst_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg(lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_x_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_926_, v_inst_927_, v_x_928_, v___y_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg___boxed(lean_object* v_inst_931_, lean_object* v_inst_932_, lean_object* v_x_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg(v_inst_931_, v_inst_932_, v_x_933_, v___y_934_);
lean_dec_ref(v_x_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__2___redArg(lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_x_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_936_, v_inst_937_, v_x_938_, v___y_939_, v___y_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(lean_object* v_inst_942_, lean_object* v_inst_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0, &l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0_once, _init_l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg___boxed(lean_object* v_inst_945_, lean_object* v_inst_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(v_inst_945_, v_inst_946_);
lean_dec_ref(v_inst_946_);
lean_dec_ref(v_inst_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(lean_object* v_00_u03b1_948_, lean_object* v_inst_949_, lean_object* v_inst_950_, lean_object* v_00_u03b2_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_949_, v_inst_950_, v_x_952_, v_x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___boxed(lean_object* v_00_u03b1_955_, lean_object* v_inst_956_, lean_object* v_inst_957_, lean_object* v_00_u03b2_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(v_00_u03b1_955_, v_inst_956_, v_inst_957_, v_00_u03b2_958_, v_x_959_, v_x_960_);
lean_dec_ref(v_x_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4(lean_object* v_00_u03b1_962_, lean_object* v_inst_963_, lean_object* v_inst_964_, lean_object* v_00_u03b2_965_, lean_object* v_x_966_, lean_object* v_x_967_, lean_object* v_x_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_963_, v_inst_964_, v_x_966_, v_x_967_, v_x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(lean_object* v_00_u03b1_970_, lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_00_u03b2_973_, lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_971_, v_inst_972_, v_x_974_, v_x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___boxed(lean_object* v_00_u03b1_977_, lean_object* v_inst_978_, lean_object* v_inst_979_, lean_object* v_00_u03b2_980_, lean_object* v_x_981_, lean_object* v_x_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(v_00_u03b1_977_, v_inst_978_, v_inst_979_, v_00_u03b2_980_, v_x_981_, v_x_982_);
lean_dec_ref(v_x_981_);
return v_res_983_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(lean_object* v_00_u03b1_984_, lean_object* v_inst_985_, lean_object* v_00_u03b2_986_, lean_object* v_x_987_, size_t v_x_988_, lean_object* v_x_989_){
_start:
{
lean_object* v___x_990_; 
lean_inc_ref(v_x_987_);
v___x_990_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_985_, v_x_987_, v_x_988_, v_x_989_);
return v___x_990_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_985_ = stack[1].m_obj;
lean_object* v_x_987_ = stack[3].m_obj;
size_t v_x_988_ = stack[4].m_num;
lean_object* v_x_989_ = stack[5].m_obj;
lean_object* v_res_991_;
v_res_991_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(lean_box(0), v_inst_985_, lean_box(0), v_x_987_, v_x_988_, v_x_989_);
stack->m_obj
 = v_res_991_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_992_, lean_object* v_inst_993_, lean_object* v_00_u03b2_994_, lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
size_t v_x_1868__boxed_998_; lean_object* v_res_999_; 
v_x_1868__boxed_998_ = lean_unbox_usize(v_x_996_);
lean_dec(v_x_996_);
v_res_999_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(v_00_u03b1_992_, v_inst_993_, v_00_u03b2_994_, v_x_995_, v_x_1868__boxed_998_, v_x_997_);
lean_dec_ref(v_x_995_);
return v_res_999_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(lean_object* v_00_u03b1_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_00_u03b2_1003_, lean_object* v_x_1004_, size_t v_x_1005_, size_t v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_1001_, v_inst_1002_, v_x_1004_, v_x_1005_, v_x_1006_, v_x_1007_, v_x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1001_ = stack[1].m_obj;
lean_object* v_inst_1002_ = stack[2].m_obj;
lean_object* v_x_1004_ = stack[4].m_obj;
size_t v_x_1005_ = stack[5].m_num;
size_t v_x_1006_ = stack[6].m_num;
lean_object* v_x_1007_ = stack[7].m_obj;
lean_object* v_x_1008_ = stack[8].m_obj;
lean_object* v_res_1010_;
v_res_1010_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(lean_box(0), v_inst_1001_, v_inst_1002_, lean_box(0), v_x_1004_, v_x_1005_, v_x_1006_, v_x_1007_, v_x_1008_);
stack->m_obj
 = v_res_1010_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1011_, lean_object* v_inst_1012_, lean_object* v_inst_1013_, lean_object* v_00_u03b2_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
size_t v_x_1897__boxed_1020_; size_t v_x_1898__boxed_1021_; lean_object* v_res_1022_; 
v_x_1897__boxed_1020_ = lean_unbox_usize(v_x_1016_);
lean_dec(v_x_1016_);
v_x_1898__boxed_1021_ = lean_unbox_usize(v_x_1017_);
lean_dec(v_x_1017_);
v_res_1022_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(v_00_u03b1_1011_, v_inst_1012_, v_inst_1013_, v_00_u03b2_1014_, v_x_1015_, v_x_1897__boxed_1020_, v_x_1898__boxed_1021_, v_x_1018_, v_x_1019_);
return v_res_1022_;
}
}
lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(lean_object* v_00_u03b1_1023_, lean_object* v_inst_1024_, lean_object* v_00_u03b2_1025_, lean_object* v_x_1026_, size_t v_x_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v___x_1029_; 
lean_inc_ref(v_x_1026_);
v___x_1029_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_1024_, v_x_1026_, v_x_1027_, v_x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1024_ = stack[1].m_obj;
lean_object* v_x_1026_ = stack[3].m_obj;
size_t v_x_1027_ = stack[4].m_num;
lean_object* v_x_1028_ = stack[5].m_obj;
lean_object* v_res_1030_;
v_res_1030_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(lean_box(0), v_inst_1024_, lean_box(0), v_x_1026_, v_x_1027_, v_x_1028_);
stack->m_obj
 = v_res_1030_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1031_, lean_object* v_inst_1032_, lean_object* v_00_u03b2_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_){
_start:
{
size_t v_x_1939__boxed_1037_; lean_object* v_res_1038_; 
v_x_1939__boxed_1037_ = lean_unbox_usize(v_x_1035_);
lean_dec(v_x_1035_);
v_res_1038_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(v_00_u03b1_1031_, v_inst_1032_, v_00_u03b2_1033_, v_x_1034_, v_x_1939__boxed_1037_, v_x_1036_);
lean_dec_ref(v_x_1034_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(lean_object* v_00_u03b1_1039_, lean_object* v_inst_1040_, lean_object* v_00_u03b2_1041_, lean_object* v_keys_1042_, lean_object* v_vals_1043_, lean_object* v_heq_1044_, lean_object* v_i_1045_, lean_object* v_k_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_1040_, v_keys_1042_, v_vals_1043_, v_i_1045_, v_k_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___boxed(lean_object* v_00_u03b1_1048_, lean_object* v_inst_1049_, lean_object* v_00_u03b2_1050_, lean_object* v_keys_1051_, lean_object* v_vals_1052_, lean_object* v_heq_1053_, lean_object* v_i_1054_, lean_object* v_k_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(v_00_u03b1_1048_, v_inst_1049_, v_00_u03b2_1050_, v_keys_1051_, v_vals_1052_, v_heq_1053_, v_i_1054_, v_k_1055_);
lean_dec_ref(v_vals_1052_);
lean_dec_ref(v_keys_1051_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11(lean_object* v_00_u03b1_1057_, lean_object* v_inst_1058_, lean_object* v_00_u03b2_1059_, lean_object* v_n_1060_, lean_object* v_k_1061_, lean_object* v_v_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(v_inst_1058_, v_n_1060_, v_k_1061_, v_v_1062_);
return v___x_1063_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(lean_object* v_00_u03b1_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_00_u03b2_1067_, size_t v_depth_1068_, lean_object* v_keys_1069_, lean_object* v_vals_1070_, lean_object* v_heq_1071_, lean_object* v_i_1072_, lean_object* v_entries_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_1065_, v_inst_1066_, v_depth_1068_, v_keys_1069_, v_vals_1070_, v_i_1072_, v_entries_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1065_ = stack[1].m_obj;
lean_object* v_inst_1066_ = stack[2].m_obj;
size_t v_depth_1068_ = stack[4].m_num;
lean_object* v_keys_1069_ = stack[5].m_obj;
lean_object* v_vals_1070_ = stack[6].m_obj;
lean_object* v_i_1072_ = stack[8].m_obj;
lean_object* v_entries_1073_ = stack[9].m_obj;
lean_object* v_res_1075_;
v_res_1075_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(lean_box(0), v_inst_1065_, v_inst_1066_, lean_box(0), v_depth_1068_, v_keys_1069_, v_vals_1070_, lean_box(0), v_i_1072_, v_entries_1073_);
stack->m_obj
 = v_res_1075_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___boxed(lean_object* v_00_u03b1_1076_, lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_depth_1080_, lean_object* v_keys_1081_, lean_object* v_vals_1082_, lean_object* v_heq_1083_, lean_object* v_i_1084_, lean_object* v_entries_1085_){
_start:
{
size_t v_depth_boxed_1086_; lean_object* v_res_1087_; 
v_depth_boxed_1086_ = lean_unbox_usize(v_depth_1080_);
lean_dec(v_depth_1080_);
v_res_1087_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(v_00_u03b1_1076_, v_inst_1077_, v_inst_1078_, v_00_u03b2_1079_, v_depth_boxed_1086_, v_keys_1081_, v_vals_1082_, v_heq_1083_, v_i_1084_, v_entries_1085_);
lean_dec_ref(v_vals_1082_);
lean_dec_ref(v_keys_1081_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(lean_object* v_00_u03b1_1088_, lean_object* v_inst_1089_, lean_object* v_00_u03b2_1090_, lean_object* v_keys_1091_, lean_object* v_vals_1092_, lean_object* v_heq_1093_, lean_object* v_i_1094_, lean_object* v_k_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_1089_, v_keys_1091_, v_vals_1092_, v_i_1094_, v_k_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___boxed(lean_object* v_00_u03b1_1097_, lean_object* v_inst_1098_, lean_object* v_00_u03b2_1099_, lean_object* v_keys_1100_, lean_object* v_vals_1101_, lean_object* v_heq_1102_, lean_object* v_i_1103_, lean_object* v_k_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(v_00_u03b1_1097_, v_inst_1098_, v_00_u03b2_1099_, v_keys_1100_, v_vals_1101_, v_heq_1102_, v_i_1103_, v_k_1104_);
lean_dec_ref(v_vals_1101_);
lean_dec_ref(v_keys_1100_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13(lean_object* v_00_u03b1_1106_, lean_object* v_inst_1107_, lean_object* v_00_u03b2_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_, lean_object* v_x_1111_, lean_object* v_x_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(v_inst_1107_, v_x_1109_, v_x_1110_, v_x_1111_, v_x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(lean_object* v_inst_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_toApplicative_1117_; lean_object* v_toPure_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_toApplicative_1117_ = lean_ctor_get(v_inst_1114_, 0);
lean_inc_ref(v_toApplicative_1117_);
lean_dec_ref(v_inst_1114_);
v_toPure_1118_ = lean_ctor_get(v_toApplicative_1117_, 1);
lean_inc(v_toPure_1118_);
lean_dec_ref(v_toApplicative_1117_);
v___x_1119_ = l_Lean_ShareCommon_objectFactory;
v___x_1120_ = lean_state_sharecommon(v___x_1119_, v_a_1116_, v_a_1115_);
v___x_1121_ = lean_apply_2(v_toPure_1118_, lean_box(0), v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon(lean_object* v_m_1122_, lean_object* v_00_u03b1_1123_, lean_object* v_inst_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(v_inst_1124_, v_a_1125_, v_a_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(lean_object* v_inst_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_toApplicative_1131_; lean_object* v_toPure_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_toApplicative_1131_ = lean_ctor_get(v_inst_1128_, 0);
lean_inc_ref(v_toApplicative_1131_);
lean_dec_ref(v_inst_1128_);
v_toPure_1132_ = lean_ctor_get(v_toApplicative_1131_, 1);
lean_inc(v_toPure_1132_);
lean_dec_ref(v_toApplicative_1131_);
v___x_1133_ = l_Lean_ShareCommon_persistentObjectFactory;
v___x_1134_ = lean_state_sharecommon(v___x_1133_, v_a_1130_, v_a_1129_);
v___x_1135_ = lean_apply_2(v_toPure_1132_, lean_box(0), v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_withShareCommon(lean_object* v_m_1136_, lean_object* v_00_u03b1_1137_, lean_object* v_inst_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(v_inst_1138_, v_a_1139_, v_a_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0(lean_object* v_inst_1142_, lean_object* v_00_u03b1_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(v_inst_1142_, v___y_1144_, v___y_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg(lean_object* v_inst_1147_){
_start:
{
lean_object* v___f_1148_; 
v___f_1148_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1148_, 0, v_inst_1147_);
return v___f_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon(lean_object* v_m_1149_, lean_object* v_inst_1150_){
_start:
{
lean_object* v___f_1151_; 
v___f_1151_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1151_, 0, v_inst_1150_);
return v___f_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0(lean_object* v_inst_1152_, lean_object* v_00_u03b1_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(v_inst_1152_, v___y_1154_, v___y_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg(lean_object* v_inst_1157_){
_start:
{
lean_object* v___f_1158_; 
v___f_1158_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1158_, 0, v_inst_1157_);
return v___f_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon(lean_object* v_m_1159_, lean_object* v_inst_1160_){
_start:
{
lean_object* v___f_1161_; 
v___f_1161_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1161_, 0, v_inst_1160_);
return v___f_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(lean_object* v_x_1162_){
_start:
{
lean_object* v_fst_1163_; 
v_fst_1163_ = lean_ctor_get(v_x_1162_, 0);
lean_inc(v_fst_1163_);
return v_fst_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0___boxed(lean_object* v_x_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(v_x_1164_);
lean_dec_ref(v_x_1164_);
return v_res_1165_;
}
}
static lean_object* _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = l_Lean_ShareCommon_objectFactory;
v___x_1168_ = l_ShareCommon_mkStateImpl(v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg(lean_object* v_inst_1169_, lean_object* v_x_1170_){
_start:
{
lean_object* v_toApplicative_1171_; lean_object* v_toFunctor_1172_; lean_object* v_map_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_toApplicative_1171_ = lean_ctor_get(v_inst_1169_, 0);
lean_inc_ref(v_toApplicative_1171_);
lean_dec_ref(v_inst_1169_);
v_toFunctor_1172_ = lean_ctor_get(v_toApplicative_1171_, 0);
lean_inc_ref(v_toFunctor_1172_);
lean_dec_ref(v_toApplicative_1171_);
v_map_1173_ = lean_ctor_get(v_toFunctor_1172_, 0);
lean_inc(v_map_1173_);
lean_dec_ref(v_toFunctor_1172_);
v___f_1174_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1175_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1176_ = lean_apply_1(v_x_1170_, v___x_1175_);
v___x_1177_ = lean_apply_4(v_map_1173_, lean_box(0), lean_box(0), v___f_1174_, v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run(lean_object* v_m_1178_, lean_object* v_00_u03b1_1179_, lean_object* v_inst_1180_, lean_object* v_x_1181_){
_start:
{
lean_object* v_toApplicative_1182_; lean_object* v_toFunctor_1183_; lean_object* v_map_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_toApplicative_1182_ = lean_ctor_get(v_inst_1180_, 0);
lean_inc_ref(v_toApplicative_1182_);
lean_dec_ref(v_inst_1180_);
v_toFunctor_1183_ = lean_ctor_get(v_toApplicative_1182_, 0);
lean_inc_ref(v_toFunctor_1183_);
lean_dec_ref(v_toApplicative_1182_);
v_map_1184_ = lean_ctor_get(v_toFunctor_1183_, 0);
lean_inc(v_map_1184_);
lean_dec_ref(v_toFunctor_1183_);
v___f_1185_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1186_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1187_ = lean_apply_1(v_x_1181_, v___x_1186_);
v___x_1188_ = lean_apply_4(v_map_1184_, lean_box(0), lean_box(0), v___f_1185_, v___x_1187_);
return v___x_1188_;
}
}
static lean_object* _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = l_Lean_ShareCommon_persistentObjectFactory;
v___x_1190_ = l_ShareCommon_mkStateImpl(v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_run___redArg(lean_object* v_inst_1191_, lean_object* v_x_1192_){
_start:
{
lean_object* v_toApplicative_1193_; lean_object* v_toFunctor_1194_; lean_object* v_map_1195_; lean_object* v___f_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v_toApplicative_1193_ = lean_ctor_get(v_inst_1191_, 0);
lean_inc_ref(v_toApplicative_1193_);
lean_dec_ref(v_inst_1191_);
v_toFunctor_1194_ = lean_ctor_get(v_toApplicative_1193_, 0);
lean_inc_ref(v_toFunctor_1194_);
lean_dec_ref(v_toApplicative_1193_);
v_map_1195_ = lean_ctor_get(v_toFunctor_1194_, 0);
lean_inc(v_map_1195_);
lean_dec_ref(v_toFunctor_1194_);
v___f_1196_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1197_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1198_ = lean_apply_1(v_x_1192_, v___x_1197_);
v___x_1199_ = lean_apply_4(v_map_1195_, lean_box(0), lean_box(0), v___f_1196_, v___x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_run(lean_object* v_m_1200_, lean_object* v_00_u03b1_1201_, lean_object* v_inst_1202_, lean_object* v_x_1203_){
_start:
{
lean_object* v_toApplicative_1204_; lean_object* v_toFunctor_1205_; lean_object* v_map_1206_; lean_object* v___f_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_toApplicative_1204_ = lean_ctor_get(v_inst_1202_, 0);
lean_inc_ref(v_toApplicative_1204_);
lean_dec_ref(v_inst_1202_);
v_toFunctor_1205_ = lean_ctor_get(v_toApplicative_1204_, 0);
lean_inc_ref(v_toFunctor_1205_);
lean_dec_ref(v_toApplicative_1204_);
v_map_1206_ = lean_ctor_get(v_toFunctor_1205_, 0);
lean_inc(v_map_1206_);
lean_dec_ref(v_toFunctor_1205_);
v___f_1207_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1208_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1209_ = lean_apply_1(v_x_1203_, v___x_1208_);
v___x_1210_ = lean_apply_4(v_map_1206_, lean_box(0), lean_box(0), v___f_1207_, v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonM_run___redArg(lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_fst_1214_; 
v___x_1212_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1213_ = lean_apply_1(v_a_1211_, v___x_1212_);
v_fst_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_fst_1214_);
lean_dec_ref(v___x_1213_);
return v_fst_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonM_run(lean_object* v_00_u03b1_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_fst_1219_; 
v___x_1217_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1218_ = lean_apply_1(v_a_1216_, v___x_1217_);
v_fst_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_fst_1219_);
lean_dec_ref(v___x_1218_);
return v_fst_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonM_run___redArg(lean_object* v_a_1220_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_fst_1223_; 
v___x_1221_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1222_ = lean_apply_1(v_a_1220_, v___x_1221_);
v_fst_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_fst_1223_);
lean_dec_ref(v___x_1222_);
return v_fst_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonM_run(lean_object* v_00_u03b1_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v_fst_1228_; 
v___x_1226_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1227_ = lean_apply_1(v_a_1225_, v___x_1226_);
v_fst_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_fst_1228_);
lean_dec_ref(v___x_1227_);
return v_fst_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = l_Lean_ShareCommon_objectFactory;
v___x_1232_ = lean_state_sharecommon(v___x_1231_, v_a_1230_, v_a_1229_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0(lean_object* v_00_u03b1_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(v_a_1234_, v_a_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_shareCommon___redArg(lean_object* v_a_1237_){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_fst_1240_; 
v___x_1238_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1239_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(v_a_1237_, v___x_1238_);
v_fst_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_fst_1240_);
lean_dec_ref(v___x_1239_);
return v_fst_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_shareCommon(lean_object* v_00_u03b1_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_ShareCommon_shareCommon___redArg(v_a_1242_);
return v___x_1243_;
}
}
lean_object* runtime_initialize_Init_ShareCommon(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentHashSet(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_ShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
