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
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v_nbuckets_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_108_ = lean_array_get_size(v_data_107_);
v___x_109_ = lean_unsigned_to_nat(2u);
v_nbuckets_110_ = lean_nat_mul(v___x_108_, v___x_109_);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_box(0);
v___x_113_ = lean_mk_array(v_nbuckets_110_, v___x_112_);
v___x_114_ = lean_array_propagate_mark(v_data_107_, v___x_113_);
v___x_115_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10___redArg(v_inst_106_, v___x_111_, v_data_107_, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_m_118_, lean_object* v_a_119_, lean_object* v_b_120_){
_start:
{
lean_object* v_size_121_; lean_object* v_buckets_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v_fold_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; lean_object* v_bkt_138_; uint8_t v___x_139_; 
v_size_121_ = lean_ctor_get(v_m_118_, 0);
v_buckets_122_ = lean_ctor_get(v_m_118_, 1);
v___x_123_ = lean_array_get_size(v_buckets_122_);
lean_inc_ref(v_inst_117_);
lean_inc_n(v_a_119_, 2);
v___x_124_ = lean_apply_1(v_inst_117_, v_a_119_);
v___x_125_ = 32ULL;
v___x_126_ = lean_unbox_uint64(v___x_124_);
v___x_127_ = lean_uint64_shift_right(v___x_126_, v___x_125_);
v___x_128_ = lean_unbox_uint64(v___x_124_);
lean_dec_ref(v___x_124_);
v_fold_129_ = lean_uint64_xor(v___x_128_, v___x_127_);
v___x_130_ = 16ULL;
v___x_131_ = lean_uint64_shift_right(v_fold_129_, v___x_130_);
v___x_132_ = lean_uint64_xor(v_fold_129_, v___x_131_);
v___x_133_ = lean_uint64_to_usize(v___x_132_);
v___x_134_ = lean_usize_of_nat(v___x_123_);
v___x_135_ = ((size_t)1ULL);
v___x_136_ = lean_usize_sub(v___x_134_, v___x_135_);
v___x_137_ = lean_usize_land(v___x_133_, v___x_136_);
v_bkt_138_ = lean_array_uget_borrowed(v_buckets_122_, v___x_137_);
lean_inc(v_bkt_138_);
v___x_139_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_116_, v_a_119_, v_bkt_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_160_; 
lean_inc_ref(v_buckets_122_);
lean_inc(v_size_121_);
v_isSharedCheck_160_ = !lean_is_exclusive(v_m_118_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; lean_object* v_unused_162_; 
v_unused_161_ = lean_ctor_get(v_m_118_, 1);
lean_dec(v_unused_161_);
v_unused_162_ = lean_ctor_get(v_m_118_, 0);
lean_dec(v_unused_162_);
v___x_141_ = v_m_118_;
v_isShared_142_ = v_isSharedCheck_160_;
goto v_resetjp_140_;
}
else
{
lean_dec(v_m_118_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_160_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v_size_x27_144_; lean_object* v___x_145_; lean_object* v_buckets_x27_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_143_ = lean_unsigned_to_nat(1u);
v_size_x27_144_ = lean_nat_add(v_size_121_, v___x_143_);
lean_dec(v_size_121_);
lean_inc(v_bkt_138_);
v___x_145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_145_, 0, v_a_119_);
lean_ctor_set(v___x_145_, 1, v_b_120_);
lean_ctor_set(v___x_145_, 2, v_bkt_138_);
v_buckets_x27_146_ = lean_array_uset(v_buckets_122_, v___x_137_, v___x_145_);
v___x_147_ = lean_unsigned_to_nat(4u);
v___x_148_ = lean_nat_mul(v_size_x27_144_, v___x_147_);
v___x_149_ = lean_unsigned_to_nat(3u);
v___x_150_ = lean_nat_div(v___x_148_, v___x_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_array_get_size(v_buckets_x27_146_);
v___x_152_ = lean_nat_dec_le(v___x_150_, v___x_151_);
lean_dec(v___x_150_);
if (v___x_152_ == 0)
{
lean_object* v_val_153_; lean_object* v___x_155_; 
v_val_153_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_117_, v_buckets_x27_146_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v_val_153_);
lean_ctor_set(v___x_141_, 0, v_size_x27_144_);
v___x_155_ = v___x_141_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_size_x27_144_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_val_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
else
{
lean_object* v___x_158_; 
lean_dec_ref(v_inst_117_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v_buckets_x27_146_);
lean_ctor_set(v___x_141_, 0, v_size_x27_144_);
v___x_158_ = v___x_141_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_size_x27_144_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_buckets_x27_146_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
else
{
lean_dec(v_b_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_inst_117_);
return v_m_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__5___redArg(lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_x_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_box(0);
v___x_168_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(v_inst_163_, v_inst_164_, v_x_165_, v___y_166_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__5(lean_object* v_00_u03b1_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_x_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_ShareCommon_objectFactory___elam__5___redArg(v_inst_170_, v_inst_171_, v_x_172_, v___y_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(lean_object* v_inst_175_, lean_object* v_a_176_, lean_object* v_b_177_, lean_object* v_x_178_){
_start:
{
if (lean_obj_tag(v_x_178_) == 0)
{
lean_dec(v_b_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_inst_175_);
return v_x_178_;
}
else
{
lean_object* v_key_179_; lean_object* v_value_180_; lean_object* v_tail_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_194_; 
v_key_179_ = lean_ctor_get(v_x_178_, 0);
v_value_180_ = lean_ctor_get(v_x_178_, 1);
v_tail_181_ = lean_ctor_get(v_x_178_, 2);
v_isSharedCheck_194_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_194_ == 0)
{
v___x_183_ = v_x_178_;
v_isShared_184_ = v_isSharedCheck_194_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_tail_181_);
lean_inc(v_value_180_);
lean_inc(v_key_179_);
lean_dec(v_x_178_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_194_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; uint8_t v___x_186_; 
lean_inc_ref(v_inst_175_);
lean_inc(v_a_176_);
lean_inc(v_key_179_);
v___x_185_ = lean_apply_2(v_inst_175_, v_key_179_, v_a_176_);
v___x_186_ = lean_unbox(v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_175_, v_a_176_, v_b_177_, v_tail_181_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 2, v___x_187_);
v___x_189_ = v___x_183_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_key_179_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_value_180_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
else
{
lean_object* v___x_192_; 
lean_dec(v_value_180_);
lean_dec(v_key_179_);
lean_dec_ref(v_inst_175_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v_b_177_);
lean_ctor_set(v___x_183_, 0, v_a_176_);
v___x_192_ = v___x_183_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_176_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_b_177_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v_tail_181_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_m_197_, lean_object* v_a_198_, lean_object* v_b_199_){
_start:
{
lean_object* v_size_200_; lean_object* v_buckets_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_246_; 
v_size_200_ = lean_ctor_get(v_m_197_, 0);
v_buckets_201_ = lean_ctor_get(v_m_197_, 1);
v_isSharedCheck_246_ = !lean_is_exclusive(v_m_197_);
if (v_isSharedCheck_246_ == 0)
{
v___x_203_ = v_m_197_;
v_isShared_204_ = v_isSharedCheck_246_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_buckets_201_);
lean_inc(v_size_200_);
lean_dec(v_m_197_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_246_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_206_; uint64_t v___x_207_; uint64_t v___x_208_; uint64_t v___x_209_; uint64_t v___x_210_; uint64_t v_fold_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; lean_object* v_bkt_220_; uint8_t v___x_221_; 
v___x_205_ = lean_array_get_size(v_buckets_201_);
lean_inc_ref(v_inst_196_);
lean_inc_n(v_a_198_, 2);
v___x_206_ = lean_apply_1(v_inst_196_, v_a_198_);
v___x_207_ = 32ULL;
v___x_208_ = lean_unbox_uint64(v___x_206_);
v___x_209_ = lean_uint64_shift_right(v___x_208_, v___x_207_);
v___x_210_ = lean_unbox_uint64(v___x_206_);
lean_dec_ref(v___x_206_);
v_fold_211_ = lean_uint64_xor(v___x_210_, v___x_209_);
v___x_212_ = 16ULL;
v___x_213_ = lean_uint64_shift_right(v_fold_211_, v___x_212_);
v___x_214_ = lean_uint64_xor(v_fold_211_, v___x_213_);
v___x_215_ = lean_uint64_to_usize(v___x_214_);
v___x_216_ = lean_usize_of_nat(v___x_205_);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_sub(v___x_216_, v___x_217_);
v___x_219_ = lean_usize_land(v___x_215_, v___x_218_);
v_bkt_220_ = lean_array_uget_borrowed(v_buckets_201_, v___x_219_);
lean_inc(v_bkt_220_);
lean_inc_ref(v_inst_195_);
v___x_221_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_195_, v_a_198_, v_bkt_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; lean_object* v_size_x27_223_; lean_object* v___x_224_; lean_object* v_buckets_x27_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
lean_dec_ref(v_inst_195_);
v___x_222_ = lean_unsigned_to_nat(1u);
v_size_x27_223_ = lean_nat_add(v_size_200_, v___x_222_);
lean_dec(v_size_200_);
lean_inc(v_bkt_220_);
v___x_224_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_224_, 0, v_a_198_);
lean_ctor_set(v___x_224_, 1, v_b_199_);
lean_ctor_set(v___x_224_, 2, v_bkt_220_);
v_buckets_x27_225_ = lean_array_uset(v_buckets_201_, v___x_219_, v___x_224_);
v___x_226_ = lean_unsigned_to_nat(4u);
v___x_227_ = lean_nat_mul(v_size_x27_223_, v___x_226_);
v___x_228_ = lean_unsigned_to_nat(3u);
v___x_229_ = lean_nat_div(v___x_227_, v___x_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_array_get_size(v_buckets_x27_225_);
v___x_231_ = lean_nat_dec_le(v___x_229_, v___x_230_);
lean_dec(v___x_229_);
if (v___x_231_ == 0)
{
lean_object* v_val_232_; lean_object* v___x_234_; 
v_val_232_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_196_, v_buckets_x27_225_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v_val_232_);
lean_ctor_set(v___x_203_, 0, v_size_x27_223_);
v___x_234_ = v___x_203_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_size_x27_223_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_val_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
else
{
lean_object* v___x_237_; 
lean_dec_ref(v_inst_196_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v_buckets_x27_225_);
lean_ctor_set(v___x_203_, 0, v_size_x27_223_);
v___x_237_ = v___x_203_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_size_x27_223_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_buckets_x27_225_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
else
{
lean_object* v___x_239_; lean_object* v_buckets_x27_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
lean_inc(v_bkt_220_);
lean_dec_ref(v_inst_196_);
v___x_239_ = lean_box(0);
v_buckets_x27_240_ = lean_array_uset(v_buckets_201_, v___x_219_, v___x_239_);
v___x_241_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_195_, v_a_198_, v_b_199_, v_bkt_220_);
v___x_242_ = lean_array_uset(v_buckets_x27_240_, v___x_219_, v___x_241_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v___x_242_);
v___x_244_ = v___x_203_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_size_200_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__2(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_x_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_249_, v_inst_250_, v_x_251_, v___y_252_, v___y_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(lean_object* v_inst_255_, lean_object* v_a_256_, lean_object* v_x_257_){
_start:
{
if (lean_obj_tag(v_x_257_) == 0)
{
lean_object* v___x_258_; 
lean_dec(v_a_256_);
lean_dec_ref(v_inst_255_);
v___x_258_ = lean_box(0);
return v___x_258_;
}
else
{
lean_object* v_key_259_; lean_object* v_tail_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_key_259_ = lean_ctor_get(v_x_257_, 0);
lean_inc_n(v_key_259_, 2);
v_tail_260_ = lean_ctor_get(v_x_257_, 2);
lean_inc(v_tail_260_);
lean_dec_ref_known(v_x_257_, 3);
lean_inc_ref(v_inst_255_);
lean_inc(v_a_256_);
v___x_261_ = lean_apply_2(v_inst_255_, v_key_259_, v_a_256_);
v___x_262_ = lean_unbox(v___x_261_);
if (v___x_262_ == 0)
{
lean_dec(v_key_259_);
v_x_257_ = v_tail_260_;
goto _start;
}
else
{
lean_object* v___x_264_; 
lean_dec(v_tail_260_);
lean_dec(v_a_256_);
lean_dec_ref(v_inst_255_);
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v_key_259_);
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_m_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_buckets_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint64_t v___x_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v___x_275_; uint64_t v_fold_276_; uint64_t v___x_277_; uint64_t v___x_278_; uint64_t v___x_279_; size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_buckets_269_ = lean_ctor_get(v_m_267_, 1);
v___x_270_ = lean_array_get_size(v_buckets_269_);
lean_inc(v_a_268_);
v___x_271_ = lean_apply_1(v_inst_266_, v_a_268_);
v___x_272_ = 32ULL;
v___x_273_ = lean_unbox_uint64(v___x_271_);
v___x_274_ = lean_uint64_shift_right(v___x_273_, v___x_272_);
v___x_275_ = lean_unbox_uint64(v___x_271_);
lean_dec_ref(v___x_271_);
v_fold_276_ = lean_uint64_xor(v___x_275_, v___x_274_);
v___x_277_ = 16ULL;
v___x_278_ = lean_uint64_shift_right(v_fold_276_, v___x_277_);
v___x_279_ = lean_uint64_xor(v_fold_276_, v___x_278_);
v___x_280_ = lean_uint64_to_usize(v___x_279_);
v___x_281_ = lean_usize_of_nat(v___x_270_);
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_sub(v___x_281_, v___x_282_);
v___x_284_ = lean_usize_land(v___x_280_, v___x_283_);
v___x_285_ = lean_array_uget_borrowed(v_buckets_269_, v___x_284_);
lean_inc(v___x_285_);
v___x_286_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(v_inst_265_, v_a_268_, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg___boxed(lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_m_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_287_, v_inst_288_, v_m_289_, v_a_290_);
lean_dec_ref(v_m_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4(lean_object* v_00_u03b1_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_x_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_293_, v_inst_294_, v_x_295_, v___y_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___boxed(lean_object* v_00_u03b1_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_x_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_ShareCommon_objectFactory___elam__4(v_00_u03b1_298_, v_inst_299_, v_inst_300_, v_x_301_, v___y_302_);
lean_dec_ref(v_x_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(lean_object* v_inst_304_, lean_object* v_a_305_, lean_object* v_x_306_){
_start:
{
if (lean_obj_tag(v_x_306_) == 0)
{
lean_object* v___x_307_; 
lean_dec(v_a_305_);
lean_dec_ref(v_inst_304_);
v___x_307_ = lean_box(0);
return v___x_307_;
}
else
{
lean_object* v_key_308_; lean_object* v_value_309_; lean_object* v_tail_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_key_308_ = lean_ctor_get(v_x_306_, 0);
lean_inc(v_key_308_);
v_value_309_ = lean_ctor_get(v_x_306_, 1);
lean_inc(v_value_309_);
v_tail_310_ = lean_ctor_get(v_x_306_, 2);
lean_inc(v_tail_310_);
lean_dec_ref_known(v_x_306_, 3);
lean_inc_ref(v_inst_304_);
lean_inc(v_a_305_);
v___x_311_ = lean_apply_2(v_inst_304_, v_key_308_, v_a_305_);
v___x_312_ = lean_unbox(v___x_311_);
if (v___x_312_ == 0)
{
lean_dec(v_value_309_);
v_x_306_ = v_tail_310_;
goto _start;
}
else
{
lean_object* v___x_314_; 
lean_dec(v_tail_310_);
lean_dec(v_a_305_);
lean_dec_ref(v_inst_304_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v_value_309_);
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_m_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_buckets_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v___x_325_; uint64_t v_fold_326_; uint64_t v___x_327_; uint64_t v___x_328_; uint64_t v___x_329_; size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_buckets_319_ = lean_ctor_get(v_m_317_, 1);
v___x_320_ = lean_array_get_size(v_buckets_319_);
lean_inc(v_a_318_);
v___x_321_ = lean_apply_1(v_inst_316_, v_a_318_);
v___x_322_ = 32ULL;
v___x_323_ = lean_unbox_uint64(v___x_321_);
v___x_324_ = lean_uint64_shift_right(v___x_323_, v___x_322_);
v___x_325_ = lean_unbox_uint64(v___x_321_);
lean_dec_ref(v___x_321_);
v_fold_326_ = lean_uint64_xor(v___x_325_, v___x_324_);
v___x_327_ = 16ULL;
v___x_328_ = lean_uint64_shift_right(v_fold_326_, v___x_327_);
v___x_329_ = lean_uint64_xor(v_fold_326_, v___x_328_);
v___x_330_ = lean_uint64_to_usize(v___x_329_);
v___x_331_ = lean_usize_of_nat(v___x_320_);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_sub(v___x_331_, v___x_332_);
v___x_334_ = lean_usize_land(v___x_330_, v___x_333_);
v___x_335_ = lean_array_uget_borrowed(v_buckets_319_, v___x_334_);
lean_inc(v___x_335_);
v___x_336_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(v_inst_315_, v_a_318_, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg___boxed(lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_m_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_337_, v_inst_338_, v_m_339_, v_a_340_);
lean_dec_ref(v_m_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1(lean_object* v_00_u03b1_342_, lean_object* v_00_u03b2_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_x_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_344_, v_inst_345_, v_x_346_, v___y_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___boxed(lean_object* v_00_u03b1_349_, lean_object* v_00_u03b2_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_x_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_ShareCommon_objectFactory___elam__1(v_00_u03b1_349_, v_00_u03b2_350_, v_inst_351_, v_inst_352_, v_x_353_, v___y_354_);
lean_dec_ref(v_x_353_);
return v_res_355_;
}
}
static lean_object* _init_l_Lean_ShareCommon_objectFactory___closed__7(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_ShareCommon_objectFactory___closed__6));
v___x_370_ = l_ShareCommon_StateFactory_mkImpl(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_ShareCommon_objectFactory(void){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_obj_once(&l_Lean_ShareCommon_objectFactory___closed__7, &l_Lean_ShareCommon_objectFactory___closed__7_once, _init_l_Lean_ShareCommon_objectFactory___closed__7);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___redArg(lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_x_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_372_, v_inst_373_, v_x_374_, v___y_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___redArg___boxed(lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_x_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_ShareCommon_objectFactory___elam__1___redArg(v_inst_377_, v_inst_378_, v_x_379_, v___y_380_);
lean_dec_ref(v_x_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__2___redArg(lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_x_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_382_, v_inst_383_, v_x_384_, v___y_385_, v___y_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___redArg(lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_x_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_388_, v_inst_389_, v_x_390_, v___y_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___redArg___boxed(lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_x_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_ShareCommon_objectFactory___elam__4___redArg(v_inst_393_, v_inst_394_, v_x_395_, v___y_396_);
lean_dec_ref(v_x_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1(lean_object* v_00_u03b1_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_00_u03b2_401_, lean_object* v_m_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_399_, v_inst_400_, v_m_402_, v_a_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___boxed(lean_object* v_00_u03b1_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_00_u03b2_408_, lean_object* v_m_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1(v_00_u03b1_405_, v_inst_406_, v_inst_407_, v_00_u03b2_408_, v_m_409_, v_a_410_);
lean_dec_ref(v_m_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3(lean_object* v_00_u03b1_412_, lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_00_u03b2_415_, lean_object* v_m_416_, lean_object* v_a_417_, lean_object* v_b_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_413_, v_inst_414_, v_m_416_, v_a_417_, v_b_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6(lean_object* v_00_u03b1_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_00_u03b2_423_, lean_object* v_m_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_421_, v_inst_422_, v_m_424_, v_a_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___boxed(lean_object* v_00_u03b1_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_00_u03b2_430_, lean_object* v_m_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6(v_00_u03b1_427_, v_inst_428_, v_inst_429_, v_00_u03b2_430_, v_m_431_, v_a_432_);
lean_dec_ref(v_m_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8(lean_object* v_00_u03b1_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_00_u03b2_437_, lean_object* v_m_438_, lean_object* v_a_439_, lean_object* v_b_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(v_inst_435_, v_inst_436_, v_m_438_, v_a_439_, v_b_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3(lean_object* v_00_u03b1_442_, lean_object* v_inst_443_, lean_object* v_00_u03b2_444_, lean_object* v_a_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(v_inst_443_, v_a_445_, v_x_446_);
return v___x_447_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(lean_object* v_00_u03b1_448_, lean_object* v_inst_449_, lean_object* v_00_u03b2_450_, lean_object* v_a_451_, lean_object* v_x_452_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_449_, v_a_451_, v_x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_454_, lean_object* v_inst_455_, lean_object* v_00_u03b2_456_, lean_object* v_a_457_, lean_object* v_x_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(v_00_u03b1_454_, v_inst_455_, v_00_u03b2_456_, v_a_457_, v_x_458_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7(lean_object* v_00_u03b1_461_, lean_object* v_inst_462_, lean_object* v_00_u03b2_463_, lean_object* v_data_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_462_, v_data_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8(lean_object* v_00_u03b1_466_, lean_object* v_inst_467_, lean_object* v_00_u03b2_468_, lean_object* v_a_469_, lean_object* v_b_470_, lean_object* v_x_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_467_, v_a_469_, v_b_470_, v_x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11(lean_object* v_00_u03b1_473_, lean_object* v_inst_474_, lean_object* v_00_u03b2_475_, lean_object* v_a_476_, lean_object* v_x_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(v_inst_474_, v_a_476_, v_x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10(lean_object* v_00_u03b1_479_, lean_object* v_inst_480_, lean_object* v_00_u03b2_481_, lean_object* v_i_482_, lean_object* v_source_483_, lean_object* v_target_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10___redArg(v_inst_480_, v_i_482_, v_source_483_, v_target_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13(lean_object* v_00_u03b1_486_, lean_object* v_00_u03b2_487_, lean_object* v_inst_488_, lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13___redArg(v_inst_488_, v_x_489_, v_x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(lean_object* v_inst_492_, lean_object* v_keys_493_, lean_object* v_vals_494_, lean_object* v_i_495_, lean_object* v_k_496_){
_start:
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = lean_array_get_size(v_keys_493_);
v___x_498_ = lean_nat_dec_lt(v_i_495_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_dec(v_k_496_);
lean_dec(v_i_495_);
lean_dec_ref(v_inst_492_);
v___x_499_ = lean_box(0);
return v___x_499_;
}
else
{
lean_object* v_k_x27_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_k_x27_500_ = lean_array_fget_borrowed(v_keys_493_, v_i_495_);
lean_inc_ref(v_inst_492_);
lean_inc(v_k_x27_500_);
lean_inc(v_k_496_);
v___x_501_ = lean_apply_2(v_inst_492_, v_k_496_, v_k_x27_500_);
v___x_502_ = lean_unbox(v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_unsigned_to_nat(1u);
v___x_504_ = lean_nat_add(v_i_495_, v___x_503_);
lean_dec(v_i_495_);
v_i_495_ = v___x_504_;
goto _start;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v_k_496_);
lean_dec_ref(v_inst_492_);
v___x_506_ = lean_array_fget_borrowed(v_vals_494_, v_i_495_);
lean_dec(v_i_495_);
lean_inc(v___x_506_);
v___x_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg___boxed(lean_object* v_inst_508_, lean_object* v_keys_509_, lean_object* v_vals_510_, lean_object* v_i_511_, lean_object* v_k_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_508_, v_keys_509_, v_vals_510_, v_i_511_, v_k_512_);
lean_dec_ref(v_vals_510_);
lean_dec_ref(v_keys_509_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(lean_object* v_inst_514_, lean_object* v_x_515_, size_t v_x_516_, lean_object* v_x_517_){
_start:
{
if (lean_obj_tag(v_x_515_) == 0)
{
lean_object* v_es_518_; lean_object* v___x_519_; size_t v___x_520_; size_t v___x_521_; lean_object* v_j_522_; lean_object* v___x_523_; 
v_es_518_ = lean_ctor_get(v_x_515_, 0);
lean_inc_ref(v_es_518_);
lean_dec_ref_known(v_x_515_, 1);
v___x_519_ = lean_box(2);
v___x_520_ = ((size_t)31ULL);
v___x_521_ = lean_usize_land(v_x_516_, v___x_520_);
v_j_522_ = lean_usize_to_nat(v___x_521_);
v___x_523_ = lean_array_get(v___x_519_, v_es_518_, v_j_522_);
lean_dec(v_j_522_);
lean_dec_ref(v_es_518_);
switch(lean_obj_tag(v___x_523_))
{
case 0:
{
lean_object* v_key_524_; lean_object* v_val_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v_key_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_key_524_);
v_val_525_ = lean_ctor_get(v___x_523_, 1);
lean_inc(v_val_525_);
lean_dec_ref_known(v___x_523_, 2);
v___x_526_ = lean_apply_2(v_inst_514_, v_x_517_, v_key_524_);
v___x_527_ = lean_unbox(v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_dec(v_val_525_);
v___x_528_ = lean_box(0);
return v___x_528_;
}
else
{
lean_object* v___x_529_; 
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_val_525_);
return v___x_529_;
}
}
case 1:
{
lean_object* v_node_530_; size_t v___x_531_; size_t v___x_532_; 
v_node_530_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_node_530_);
lean_dec_ref_known(v___x_523_, 1);
v___x_531_ = ((size_t)5ULL);
v___x_532_ = lean_usize_shift_right(v_x_516_, v___x_531_);
v_x_515_ = v_node_530_;
v_x_516_ = v___x_532_;
goto _start;
}
default: 
{
lean_object* v___x_534_; 
lean_dec(v_x_517_);
lean_dec_ref(v_inst_514_);
v___x_534_ = lean_box(0);
return v___x_534_;
}
}
}
else
{
lean_object* v_ks_535_; lean_object* v_vs_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_ks_535_ = lean_ctor_get(v_x_515_, 0);
lean_inc_ref(v_ks_535_);
v_vs_536_ = lean_ctor_get(v_x_515_, 1);
lean_inc_ref(v_vs_536_);
lean_dec_ref_known(v_x_515_, 2);
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_514_, v_ks_535_, v_vs_536_, v___x_537_, v_x_517_);
lean_dec_ref(v_vs_536_);
lean_dec_ref(v_ks_535_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___boxed(lean_object* v_inst_539_, lean_object* v_x_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
size_t v_x_708__boxed_543_; lean_object* v_res_544_; 
v_x_708__boxed_543_ = lean_unbox_usize(v_x_541_);
lean_dec(v_x_541_);
v_res_544_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_539_, v_x_540_, v_x_708__boxed_543_, v_x_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v___x_549_; uint64_t v___x_550_; size_t v___x_551_; lean_object* v___x_552_; 
lean_inc(v_x_548_);
v___x_549_ = lean_apply_1(v_inst_546_, v_x_548_);
v___x_550_ = lean_unbox_uint64(v___x_549_);
lean_dec_ref(v___x_549_);
v___x_551_ = lean_uint64_to_usize(v___x_550_);
lean_inc_ref(v_x_547_);
v___x_552_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_545_, v_x_547_, v___x_551_, v_x_548_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg___boxed(lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_553_, v_inst_554_, v_x_555_, v_x_556_);
lean_dec_ref(v_x_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1(lean_object* v_00_u03b1_558_, lean_object* v_00_u03b2_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_x_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_560_, v_inst_561_, v_x_562_, v___y_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___boxed(lean_object* v_00_u03b1_565_, lean_object* v_00_u03b2_566_, lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_x_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_ShareCommon_persistentObjectFactory___elam__1(v_00_u03b1_565_, v_00_u03b2_566_, v_inst_567_, v_inst_568_, v_x_569_, v___y_570_);
lean_dec_ref(v_x_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(lean_object* v_inst_572_, lean_object* v_keys_573_, lean_object* v_vals_574_, lean_object* v_i_575_, lean_object* v_k_576_){
_start:
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_array_get_size(v_keys_573_);
v___x_578_ = lean_nat_dec_lt(v_i_575_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
lean_dec(v_k_576_);
lean_dec(v_i_575_);
lean_dec_ref(v_inst_572_);
v___x_579_ = lean_box(0);
return v___x_579_;
}
else
{
lean_object* v_k_x27_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v_k_x27_580_ = lean_array_fget_borrowed(v_keys_573_, v_i_575_);
lean_inc_ref(v_inst_572_);
lean_inc(v_k_x27_580_);
lean_inc(v_k_576_);
v___x_581_ = lean_apply_2(v_inst_572_, v_k_576_, v_k_x27_580_);
v___x_582_ = lean_unbox(v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_nat_add(v_i_575_, v___x_583_);
lean_dec(v_i_575_);
v_i_575_ = v___x_584_;
goto _start;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_k_576_);
lean_dec_ref(v_inst_572_);
v___x_586_ = lean_array_fget_borrowed(v_vals_574_, v_i_575_);
lean_dec(v_i_575_);
lean_inc(v___x_586_);
lean_inc(v_k_x27_580_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v_k_x27_580_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object* v_inst_589_, lean_object* v_keys_590_, lean_object* v_vals_591_, lean_object* v_i_592_, lean_object* v_k_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_589_, v_keys_590_, v_vals_591_, v_i_592_, v_k_593_);
lean_dec_ref(v_vals_591_);
lean_dec_ref(v_keys_590_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(lean_object* v_inst_595_, lean_object* v_x_596_, size_t v_x_597_, lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_596_) == 0)
{
lean_object* v_es_599_; lean_object* v___x_600_; size_t v___x_601_; size_t v___x_602_; lean_object* v_j_603_; lean_object* v___x_604_; 
v_es_599_ = lean_ctor_get(v_x_596_, 0);
lean_inc_ref(v_es_599_);
lean_dec_ref_known(v_x_596_, 1);
v___x_600_ = lean_box(2);
v___x_601_ = ((size_t)31ULL);
v___x_602_ = lean_usize_land(v_x_597_, v___x_601_);
v_j_603_ = lean_usize_to_nat(v___x_602_);
v___x_604_ = lean_array_get(v___x_600_, v_es_599_, v_j_603_);
lean_dec(v_j_603_);
lean_dec_ref(v_es_599_);
switch(lean_obj_tag(v___x_604_))
{
case 0:
{
lean_object* v_key_605_; lean_object* v_val_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_key_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc_n(v_key_605_, 2);
v_val_606_ = lean_ctor_get(v___x_604_, 1);
lean_inc(v_val_606_);
lean_dec_ref_known(v___x_604_, 2);
v___x_607_ = lean_apply_2(v_inst_595_, v_x_598_, v_key_605_);
v___x_608_ = lean_unbox(v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
lean_dec(v_val_606_);
lean_dec(v_key_605_);
v___x_609_ = lean_box(0);
return v___x_609_;
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v_key_605_);
lean_ctor_set(v___x_610_, 1, v_val_606_);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
}
case 1:
{
lean_object* v_node_612_; size_t v___x_613_; size_t v___x_614_; 
v_node_612_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_node_612_);
lean_dec_ref_known(v___x_604_, 1);
v___x_613_ = ((size_t)5ULL);
v___x_614_ = lean_usize_shift_right(v_x_597_, v___x_613_);
v_x_596_ = v_node_612_;
v_x_597_ = v___x_614_;
goto _start;
}
default: 
{
lean_object* v___x_616_; 
lean_dec(v_x_598_);
lean_dec_ref(v_inst_595_);
v___x_616_ = lean_box(0);
return v___x_616_;
}
}
}
else
{
lean_object* v_ks_617_; lean_object* v_vs_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_ks_617_ = lean_ctor_get(v_x_596_, 0);
lean_inc_ref(v_ks_617_);
v_vs_618_ = lean_ctor_get(v_x_596_, 1);
lean_inc_ref(v_vs_618_);
lean_dec_ref_known(v_x_596_, 2);
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_595_, v_ks_617_, v_vs_618_, v___x_619_, v_x_598_);
lean_dec_ref(v_vs_618_);
lean_dec_ref(v_ks_617_);
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg___boxed(lean_object* v_inst_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
size_t v_x_825__boxed_625_; lean_object* v_res_626_; 
v_x_825__boxed_625_ = lean_unbox_usize(v_x_623_);
lean_dec(v_x_623_);
v_res_626_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_621_, v_x_622_, v_x_825__boxed_625_, v_x_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
lean_object* v___x_631_; uint64_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; 
lean_inc(v_x_630_);
v___x_631_ = lean_apply_1(v_inst_628_, v_x_630_);
v___x_632_ = lean_unbox_uint64(v___x_631_);
lean_dec_ref(v___x_631_);
v___x_633_ = lean_uint64_to_usize(v___x_632_);
lean_inc_ref(v_x_629_);
v___x_634_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_627_, v_x_629_, v___x_633_, v_x_630_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg___boxed(lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_635_, v_inst_636_, v_x_637_, v_x_638_);
lean_dec_ref(v_x_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_x_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_640_, v_inst_641_, v_x_642_, v___y_643_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v___x_645_; 
v___x_645_ = lean_box(0);
return v___x_645_;
}
else
{
lean_object* v_val_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
v_val_646_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_654_ == 0)
{
v___x_648_ = v___x_644_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_val_646_);
lean_dec(v___x_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_fst_650_; lean_object* v___x_652_; 
v_fst_650_ = lean_ctor_get(v_val_646_, 0);
lean_inc(v_fst_650_);
lean_dec(v_val_646_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v_fst_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fst_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg___boxed(lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_x_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(v_inst_655_, v_inst_656_, v_x_657_, v___y_658_);
lean_dec_ref(v_x_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4(lean_object* v_00_u03b1_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_x_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(v_inst_661_, v_inst_662_, v_x_663_, v___y_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___boxed(lean_object* v_00_u03b1_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_x_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4(v_00_u03b1_666_, v_inst_667_, v_inst_668_, v_x_669_, v___y_670_);
lean_dec_ref(v_x_669_);
return v_res_671_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_672_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__0);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg(){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___closed__1);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg___boxed(lean_object* v___dummy_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg();
return v_res_678_;
}
}
static lean_object* _init_l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0(void){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___redArg();
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0(lean_object* v_00_u03b1_680_, lean_object* v_00_u03b2_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_x_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0, &l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0_once, _init_l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0);
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
v___x_696_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0, &l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0_once, _init_l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0);
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
v___x_740_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_x_743_, size_t v_x_744_, size_t v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
if (lean_obj_tag(v_x_743_) == 0)
{
lean_object* v_es_748_; size_t v___x_749_; size_t v___x_750_; lean_object* v_j_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v_es_748_ = lean_ctor_get(v_x_743_, 0);
v___x_749_ = ((size_t)31ULL);
v___x_750_ = lean_usize_land(v_x_744_, v___x_749_);
v_j_751_ = lean_usize_to_nat(v___x_750_);
v___x_752_ = lean_array_get_size(v_es_748_);
v___x_753_ = lean_nat_dec_lt(v_j_751_, v___x_752_);
if (v___x_753_ == 0)
{
lean_dec(v_j_751_);
lean_dec(v_x_747_);
lean_dec(v_x_746_);
lean_dec_ref(v_inst_742_);
lean_dec_ref(v_inst_741_);
return v_x_743_;
}
else
{
lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_793_; 
lean_inc_ref(v_es_748_);
v_isSharedCheck_793_ = !lean_is_exclusive(v_x_743_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_x_743_, 0);
lean_dec(v_unused_794_);
v___x_755_ = v_x_743_;
v_isShared_756_ = v_isSharedCheck_793_;
goto v_resetjp_754_;
}
else
{
lean_dec(v_x_743_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_793_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_v_757_; lean_object* v___x_758_; lean_object* v_xs_x27_759_; lean_object* v___y_761_; 
v_v_757_ = lean_array_fget(v_es_748_, v_j_751_);
v___x_758_ = lean_box(0);
v_xs_x27_759_ = lean_array_fset(v_es_748_, v_j_751_, v___x_758_);
switch(lean_obj_tag(v_v_757_))
{
case 0:
{
lean_object* v_key_766_; lean_object* v_val_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_inst_742_);
v_key_766_ = lean_ctor_get(v_v_757_, 0);
v_val_767_ = lean_ctor_get(v_v_757_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_v_757_);
if (v_isSharedCheck_778_ == 0)
{
v___x_769_ = v_v_757_;
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_val_767_);
lean_inc(v_key_766_);
lean_dec(v_v_757_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; uint8_t v___x_772_; 
lean_inc(v_key_766_);
lean_inc(v_x_746_);
v___x_771_ = lean_apply_2(v_inst_741_, v_x_746_, v_key_766_);
v___x_772_ = lean_unbox(v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
lean_del_object(v___x_769_);
v___x_773_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_766_, v_val_767_, v_x_746_, v_x_747_);
v___x_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
v___y_761_ = v___x_774_;
goto v___jp_760_;
}
else
{
lean_object* v___x_776_; 
lean_dec(v_val_767_);
lean_dec(v_key_766_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 1, v_x_747_);
lean_ctor_set(v___x_769_, 0, v_x_746_);
v___x_776_ = v___x_769_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_x_746_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_x_747_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
v___y_761_ = v___x_776_;
goto v___jp_760_;
}
}
}
}
case 1:
{
lean_object* v_node_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_791_; 
v_node_779_ = lean_ctor_get(v_v_757_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v_v_757_);
if (v_isSharedCheck_791_ == 0)
{
v___x_781_ = v_v_757_;
v_isShared_782_ = v_isSharedCheck_791_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_node_779_);
lean_dec(v_v_757_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_791_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
size_t v___x_783_; size_t v___x_784_; size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_783_ = ((size_t)5ULL);
v___x_784_ = lean_usize_shift_right(v_x_744_, v___x_783_);
v___x_785_ = ((size_t)1ULL);
v___x_786_ = lean_usize_add(v_x_745_, v___x_785_);
v___x_787_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_741_, v_inst_742_, v_node_779_, v___x_784_, v___x_786_, v_x_746_, v_x_747_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_787_);
v___x_789_ = v___x_781_;
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
v___y_761_ = v___x_789_;
goto v___jp_760_;
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
v___y_761_ = v___x_792_;
goto v___jp_760_;
}
}
v___jp_760_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_array_fset(v_xs_x27_759_, v_j_751_, v___y_761_);
lean_dec(v_j_751_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_762_);
v___x_764_ = v___x_755_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
else
{
lean_object* v_ks_795_; lean_object* v_vs_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_814_; 
v_ks_795_ = lean_ctor_get(v_x_743_, 0);
v_vs_796_ = lean_ctor_get(v_x_743_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v_x_743_);
if (v_isSharedCheck_814_ == 0)
{
v___x_798_ = v_x_743_;
v_isShared_799_ = v_isSharedCheck_814_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_vs_796_);
lean_inc(v_ks_795_);
lean_dec(v_x_743_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_814_;
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
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_ks_795_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_vs_796_);
v___x_801_ = v_reuseFailAlloc_813_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v_newNode_802_; size_t v___x_803_; uint8_t v___x_804_; 
lean_inc_ref(v_inst_741_);
v_newNode_802_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(v_inst_741_, v___x_801_, v_x_746_, v_x_747_);
v___x_803_ = ((size_t)7ULL);
v___x_804_ = lean_usize_dec_le(v___x_803_, v_x_745_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_805_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_802_);
v___x_806_ = lean_unsigned_to_nat(4u);
v___x_807_ = lean_nat_dec_lt(v___x_805_, v___x_806_);
lean_dec(v___x_805_);
if (v___x_807_ == 0)
{
lean_object* v_ks_808_; lean_object* v_vs_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_ks_808_ = lean_ctor_get(v_newNode_802_, 0);
lean_inc_ref(v_ks_808_);
v_vs_809_ = lean_ctor_get(v_newNode_802_, 1);
lean_inc_ref(v_vs_809_);
lean_dec_ref(v_newNode_802_);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0);
v___x_812_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_741_, v_inst_742_, v_x_745_, v_ks_808_, v_vs_809_, v___x_810_, v___x_811_);
lean_dec_ref(v_vs_809_);
lean_dec_ref(v_ks_808_);
return v___x_812_;
}
else
{
lean_dec_ref(v_inst_742_);
lean_dec_ref(v_inst_741_);
return v_newNode_802_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(lean_object* v_inst_815_, lean_object* v_inst_816_, size_t v_depth_817_, lean_object* v_keys_818_, lean_object* v_vals_819_, lean_object* v_i_820_, lean_object* v_entries_821_){
_start:
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = lean_array_get_size(v_keys_818_);
v___x_823_ = lean_nat_dec_lt(v_i_820_, v___x_822_);
if (v___x_823_ == 0)
{
lean_dec(v_i_820_);
lean_dec_ref(v_inst_816_);
lean_dec_ref(v_inst_815_);
return v_entries_821_;
}
else
{
lean_object* v_k_824_; lean_object* v_v_825_; lean_object* v___x_826_; uint64_t v___x_827_; size_t v_h_828_; size_t v___x_829_; lean_object* v___x_830_; size_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v_h_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v_k_824_ = lean_array_fget_borrowed(v_keys_818_, v_i_820_);
v_v_825_ = lean_array_fget_borrowed(v_vals_819_, v_i_820_);
lean_inc_ref_n(v_inst_816_, 2);
lean_inc_n(v_k_824_, 2);
v___x_826_ = lean_apply_1(v_inst_816_, v_k_824_);
v___x_827_ = lean_unbox_uint64(v___x_826_);
lean_dec_ref(v___x_826_);
v_h_828_ = lean_uint64_to_usize(v___x_827_);
v___x_829_ = ((size_t)5ULL);
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_sub(v_depth_817_, v___x_831_);
v___x_833_ = lean_usize_mul(v___x_829_, v___x_832_);
v_h_834_ = lean_usize_shift_right(v_h_828_, v___x_833_);
v___x_835_ = lean_nat_add(v_i_820_, v___x_830_);
lean_dec(v_i_820_);
lean_inc(v_v_825_);
lean_inc_ref(v_inst_815_);
v___x_836_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_815_, v_inst_816_, v_entries_821_, v_h_834_, v_depth_817_, v_k_824_, v_v_825_);
v_i_820_ = v___x_835_;
v_entries_821_ = v___x_836_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg___boxed(lean_object* v_inst_838_, lean_object* v_inst_839_, lean_object* v_depth_840_, lean_object* v_keys_841_, lean_object* v_vals_842_, lean_object* v_i_843_, lean_object* v_entries_844_){
_start:
{
size_t v_depth_boxed_845_; lean_object* v_res_846_; 
v_depth_boxed_845_ = lean_unbox_usize(v_depth_840_);
lean_dec(v_depth_840_);
v_res_846_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_838_, v_inst_839_, v_depth_boxed_845_, v_keys_841_, v_vals_842_, v_i_843_, v_entries_844_);
lean_dec_ref(v_vals_842_);
lean_dec_ref(v_keys_841_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___boxed(lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
size_t v_x_1082__boxed_854_; size_t v_x_1083__boxed_855_; lean_object* v_res_856_; 
v_x_1082__boxed_854_ = lean_unbox_usize(v_x_850_);
lean_dec(v_x_850_);
v_x_1083__boxed_855_ = lean_unbox_usize(v_x_851_);
lean_dec(v_x_851_);
v_res_856_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_847_, v_inst_848_, v_x_849_, v_x_1082__boxed_854_, v_x_1083__boxed_855_, v_x_852_, v_x_853_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v___x_862_; uint64_t v___x_863_; size_t v___x_864_; size_t v___x_865_; lean_object* v___x_866_; 
lean_inc_ref(v_inst_858_);
lean_inc(v_x_860_);
v___x_862_ = lean_apply_1(v_inst_858_, v_x_860_);
v___x_863_ = lean_unbox_uint64(v___x_862_);
lean_dec_ref(v___x_862_);
v___x_864_ = lean_uint64_to_usize(v___x_863_);
v___x_865_ = ((size_t)1ULL);
v___x_866_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_857_, v_inst_858_, v_x_859_, v___x_864_, v___x_865_, v_x_860_, v_x_861_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__2(lean_object* v_00_u03b1_867_, lean_object* v_00_u03b2_868_, lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_x_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_869_, v_inst_870_, v_x_871_, v___y_872_, v___y_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(lean_object* v_inst_875_, lean_object* v_inst_876_, lean_object* v_x_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_box(0);
v___x_880_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_875_, v_inst_876_, v_x_877_, v___y_878_, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__5(lean_object* v_00_u03b1_881_, lean_object* v_inst_882_, lean_object* v_inst_883_, lean_object* v_x_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(v_inst_882_, v_inst_883_, v_x_884_, v___y_885_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_ShareCommon_persistentObjectFactory___closed__7(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = ((lean_object*)(l_Lean_ShareCommon_persistentObjectFactory___closed__6));
v___x_901_ = l_ShareCommon_StateFactory_mkImpl(v___x_900_);
return v___x_901_;
}
}
static lean_object* _init_l_Lean_ShareCommon_persistentObjectFactory(void){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___closed__7, &l_Lean_ShareCommon_persistentObjectFactory___closed__7_once, _init_l_Lean_ShareCommon_persistentObjectFactory___closed__7);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_object* v_00_u03b1_903_, lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_00_u03b2_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0, &l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0_once, _init_l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___boxed(lean_object* v_00_u03b1_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_00_u03b2_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(v_00_u03b1_908_, v_inst_909_, v_inst_910_, v_00_u03b2_911_);
lean_dec_ref(v_inst_910_);
lean_dec_ref(v_inst_909_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(lean_object* v_inst_913_, lean_object* v_inst_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0, &l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0_once, _init_l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg___boxed(lean_object* v_inst_916_, lean_object* v_inst_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(v_inst_916_, v_inst_917_);
lean_dec_ref(v_inst_917_);
lean_dec_ref(v_inst_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg(lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_x_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_919_, v_inst_920_, v_x_921_, v___y_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg___boxed(lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_x_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg(v_inst_924_, v_inst_925_, v_x_926_, v___y_927_);
lean_dec_ref(v_x_926_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__2___redArg(lean_object* v_inst_929_, lean_object* v_inst_930_, lean_object* v_x_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_929_, v_inst_930_, v_x_931_, v___y_932_, v___y_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(lean_object* v_inst_935_, lean_object* v_inst_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0, &l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0_once, _init_l_Lean_ShareCommon_persistentObjectFactory___elam__0___closed__0);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg___boxed(lean_object* v_inst_938_, lean_object* v_inst_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(v_inst_938_, v_inst_939_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_inst_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(lean_object* v_00_u03b1_941_, lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_00_u03b2_944_, lean_object* v_x_945_, lean_object* v_x_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_942_, v_inst_943_, v_x_945_, v_x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___boxed(lean_object* v_00_u03b1_948_, lean_object* v_inst_949_, lean_object* v_inst_950_, lean_object* v_00_u03b2_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(v_00_u03b1_948_, v_inst_949_, v_inst_950_, v_00_u03b2_951_, v_x_952_, v_x_953_);
lean_dec_ref(v_x_952_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4(lean_object* v_00_u03b1_955_, lean_object* v_inst_956_, lean_object* v_inst_957_, lean_object* v_00_u03b2_958_, lean_object* v_x_959_, lean_object* v_x_960_, lean_object* v_x_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_956_, v_inst_957_, v_x_959_, v_x_960_, v_x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(lean_object* v_00_u03b1_963_, lean_object* v_inst_964_, lean_object* v_inst_965_, lean_object* v_00_u03b2_966_, lean_object* v_x_967_, lean_object* v_x_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_964_, v_inst_965_, v_x_967_, v_x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___boxed(lean_object* v_00_u03b1_970_, lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_00_u03b2_973_, lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(v_00_u03b1_970_, v_inst_971_, v_inst_972_, v_00_u03b2_973_, v_x_974_, v_x_975_);
lean_dec_ref(v_x_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(lean_object* v_00_u03b1_977_, lean_object* v_inst_978_, lean_object* v_00_u03b2_979_, lean_object* v_x_980_, size_t v_x_981_, lean_object* v_x_982_){
_start:
{
lean_object* v___x_983_; 
lean_inc_ref(v_x_980_);
v___x_983_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_978_, v_x_980_, v_x_981_, v_x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_984_, lean_object* v_inst_985_, lean_object* v_00_u03b2_986_, lean_object* v_x_987_, lean_object* v_x_988_, lean_object* v_x_989_){
_start:
{
size_t v_x_1459__boxed_990_; lean_object* v_res_991_; 
v_x_1459__boxed_990_ = lean_unbox_usize(v_x_988_);
lean_dec(v_x_988_);
v_res_991_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(v_00_u03b1_984_, v_inst_985_, v_00_u03b2_986_, v_x_987_, v_x_1459__boxed_990_, v_x_989_);
lean_dec_ref(v_x_987_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(lean_object* v_00_u03b1_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_00_u03b2_995_, lean_object* v_x_996_, size_t v_x_997_, size_t v_x_998_, lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_993_, v_inst_994_, v_x_996_, v_x_997_, v_x_998_, v_x_999_, v_x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1002_, lean_object* v_inst_1003_, lean_object* v_inst_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_){
_start:
{
size_t v_x_1477__boxed_1011_; size_t v_x_1478__boxed_1012_; lean_object* v_res_1013_; 
v_x_1477__boxed_1011_ = lean_unbox_usize(v_x_1007_);
lean_dec(v_x_1007_);
v_x_1478__boxed_1012_ = lean_unbox_usize(v_x_1008_);
lean_dec(v_x_1008_);
v_res_1013_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(v_00_u03b1_1002_, v_inst_1003_, v_inst_1004_, v_00_u03b2_1005_, v_x_1006_, v_x_1477__boxed_1011_, v_x_1478__boxed_1012_, v_x_1009_, v_x_1010_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(lean_object* v_00_u03b1_1014_, lean_object* v_inst_1015_, lean_object* v_00_u03b2_1016_, lean_object* v_x_1017_, size_t v_x_1018_, lean_object* v_x_1019_){
_start:
{
lean_object* v___x_1020_; 
lean_inc_ref(v_x_1017_);
v___x_1020_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_1015_, v_x_1017_, v_x_1018_, v_x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1021_, lean_object* v_inst_1022_, lean_object* v_00_u03b2_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
size_t v_x_1502__boxed_1027_; lean_object* v_res_1028_; 
v_x_1502__boxed_1027_ = lean_unbox_usize(v_x_1025_);
lean_dec(v_x_1025_);
v_res_1028_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(v_00_u03b1_1021_, v_inst_1022_, v_00_u03b2_1023_, v_x_1024_, v_x_1502__boxed_1027_, v_x_1026_);
lean_dec_ref(v_x_1024_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(lean_object* v_00_u03b1_1029_, lean_object* v_inst_1030_, lean_object* v_00_u03b2_1031_, lean_object* v_keys_1032_, lean_object* v_vals_1033_, lean_object* v_heq_1034_, lean_object* v_i_1035_, lean_object* v_k_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_1030_, v_keys_1032_, v_vals_1033_, v_i_1035_, v_k_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___boxed(lean_object* v_00_u03b1_1038_, lean_object* v_inst_1039_, lean_object* v_00_u03b2_1040_, lean_object* v_keys_1041_, lean_object* v_vals_1042_, lean_object* v_heq_1043_, lean_object* v_i_1044_, lean_object* v_k_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(v_00_u03b1_1038_, v_inst_1039_, v_00_u03b2_1040_, v_keys_1041_, v_vals_1042_, v_heq_1043_, v_i_1044_, v_k_1045_);
lean_dec_ref(v_vals_1042_);
lean_dec_ref(v_keys_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11(lean_object* v_00_u03b1_1047_, lean_object* v_inst_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_n_1050_, lean_object* v_k_1051_, lean_object* v_v_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(v_inst_1048_, v_n_1050_, v_k_1051_, v_v_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(lean_object* v_00_u03b1_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_00_u03b2_1057_, size_t v_depth_1058_, lean_object* v_keys_1059_, lean_object* v_vals_1060_, lean_object* v_heq_1061_, lean_object* v_i_1062_, lean_object* v_entries_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_1055_, v_inst_1056_, v_depth_1058_, v_keys_1059_, v_vals_1060_, v_i_1062_, v_entries_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___boxed(lean_object* v_00_u03b1_1065_, lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_00_u03b2_1068_, lean_object* v_depth_1069_, lean_object* v_keys_1070_, lean_object* v_vals_1071_, lean_object* v_heq_1072_, lean_object* v_i_1073_, lean_object* v_entries_1074_){
_start:
{
size_t v_depth_boxed_1075_; lean_object* v_res_1076_; 
v_depth_boxed_1075_ = lean_unbox_usize(v_depth_1069_);
lean_dec(v_depth_1069_);
v_res_1076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(v_00_u03b1_1065_, v_inst_1066_, v_inst_1067_, v_00_u03b2_1068_, v_depth_boxed_1075_, v_keys_1070_, v_vals_1071_, v_heq_1072_, v_i_1073_, v_entries_1074_);
lean_dec_ref(v_vals_1071_);
lean_dec_ref(v_keys_1070_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(lean_object* v_00_u03b1_1077_, lean_object* v_inst_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_keys_1080_, lean_object* v_vals_1081_, lean_object* v_heq_1082_, lean_object* v_i_1083_, lean_object* v_k_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_1078_, v_keys_1080_, v_vals_1081_, v_i_1083_, v_k_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___boxed(lean_object* v_00_u03b1_1086_, lean_object* v_inst_1087_, lean_object* v_00_u03b2_1088_, lean_object* v_keys_1089_, lean_object* v_vals_1090_, lean_object* v_heq_1091_, lean_object* v_i_1092_, lean_object* v_k_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(v_00_u03b1_1086_, v_inst_1087_, v_00_u03b2_1088_, v_keys_1089_, v_vals_1090_, v_heq_1091_, v_i_1092_, v_k_1093_);
lean_dec_ref(v_vals_1090_);
lean_dec_ref(v_keys_1089_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13(lean_object* v_00_u03b1_1095_, lean_object* v_inst_1096_, lean_object* v_00_u03b2_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(v_inst_1096_, v_x_1098_, v_x_1099_, v_x_1100_, v_x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(lean_object* v_inst_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_toApplicative_1106_; lean_object* v_toPure_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_toApplicative_1106_ = lean_ctor_get(v_inst_1103_, 0);
lean_inc_ref(v_toApplicative_1106_);
lean_dec_ref(v_inst_1103_);
v_toPure_1107_ = lean_ctor_get(v_toApplicative_1106_, 1);
lean_inc(v_toPure_1107_);
lean_dec_ref(v_toApplicative_1106_);
v___x_1108_ = l_Lean_ShareCommon_objectFactory;
v___x_1109_ = lean_state_sharecommon(v___x_1108_, v_a_1105_, v_a_1104_);
v___x_1110_ = lean_apply_2(v_toPure_1107_, lean_box(0), v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon(lean_object* v_m_1111_, lean_object* v_00_u03b1_1112_, lean_object* v_inst_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(v_inst_1113_, v_a_1114_, v_a_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(lean_object* v_inst_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_toApplicative_1120_; lean_object* v_toPure_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_toApplicative_1120_ = lean_ctor_get(v_inst_1117_, 0);
lean_inc_ref(v_toApplicative_1120_);
lean_dec_ref(v_inst_1117_);
v_toPure_1121_ = lean_ctor_get(v_toApplicative_1120_, 1);
lean_inc(v_toPure_1121_);
lean_dec_ref(v_toApplicative_1120_);
v___x_1122_ = l_Lean_ShareCommon_persistentObjectFactory;
v___x_1123_ = lean_state_sharecommon(v___x_1122_, v_a_1119_, v_a_1118_);
v___x_1124_ = lean_apply_2(v_toPure_1121_, lean_box(0), v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_withShareCommon(lean_object* v_m_1125_, lean_object* v_00_u03b1_1126_, lean_object* v_inst_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(v_inst_1127_, v_a_1128_, v_a_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0(lean_object* v_inst_1131_, lean_object* v_00_u03b1_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(v_inst_1131_, v___y_1133_, v___y_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg(lean_object* v_inst_1136_){
_start:
{
lean_object* v___f_1137_; 
v___f_1137_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1137_, 0, v_inst_1136_);
return v___f_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon(lean_object* v_m_1138_, lean_object* v_inst_1139_){
_start:
{
lean_object* v___f_1140_; 
v___f_1140_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1140_, 0, v_inst_1139_);
return v___f_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0(lean_object* v_inst_1141_, lean_object* v_00_u03b1_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(v_inst_1141_, v___y_1143_, v___y_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg(lean_object* v_inst_1146_){
_start:
{
lean_object* v___f_1147_; 
v___f_1147_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1147_, 0, v_inst_1146_);
return v___f_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon(lean_object* v_m_1148_, lean_object* v_inst_1149_){
_start:
{
lean_object* v___f_1150_; 
v___f_1150_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1150_, 0, v_inst_1149_);
return v___f_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(lean_object* v_x_1151_){
_start:
{
lean_object* v_fst_1152_; 
v_fst_1152_ = lean_ctor_get(v_x_1151_, 0);
lean_inc(v_fst_1152_);
return v_fst_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0___boxed(lean_object* v_x_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(v_x_1153_);
lean_dec_ref(v_x_1153_);
return v_res_1154_;
}
}
static lean_object* _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = l_Lean_ShareCommon_objectFactory;
v___x_1157_ = l_ShareCommon_mkStateImpl(v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg(lean_object* v_inst_1158_, lean_object* v_x_1159_){
_start:
{
lean_object* v_toApplicative_1160_; lean_object* v_toFunctor_1161_; lean_object* v_map_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_toApplicative_1160_ = lean_ctor_get(v_inst_1158_, 0);
lean_inc_ref(v_toApplicative_1160_);
lean_dec_ref(v_inst_1158_);
v_toFunctor_1161_ = lean_ctor_get(v_toApplicative_1160_, 0);
lean_inc_ref(v_toFunctor_1161_);
lean_dec_ref(v_toApplicative_1160_);
v_map_1162_ = lean_ctor_get(v_toFunctor_1161_, 0);
lean_inc(v_map_1162_);
lean_dec_ref(v_toFunctor_1161_);
v___f_1163_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1164_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1165_ = lean_apply_1(v_x_1159_, v___x_1164_);
v___x_1166_ = lean_apply_4(v_map_1162_, lean_box(0), lean_box(0), v___f_1163_, v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run(lean_object* v_m_1167_, lean_object* v_00_u03b1_1168_, lean_object* v_inst_1169_, lean_object* v_x_1170_){
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
static lean_object* _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = l_Lean_ShareCommon_persistentObjectFactory;
v___x_1179_ = l_ShareCommon_mkStateImpl(v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_run___redArg(lean_object* v_inst_1180_, lean_object* v_x_1181_){
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
v___x_1186_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1187_ = lean_apply_1(v_x_1181_, v___x_1186_);
v___x_1188_ = lean_apply_4(v_map_1184_, lean_box(0), lean_box(0), v___f_1185_, v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_run(lean_object* v_m_1189_, lean_object* v_00_u03b1_1190_, lean_object* v_inst_1191_, lean_object* v_x_1192_){
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
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonM_run___redArg(lean_object* v_a_1200_){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v_fst_1203_; 
v___x_1201_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1202_ = lean_apply_1(v_a_1200_, v___x_1201_);
v_fst_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_fst_1203_);
lean_dec_ref(v___x_1202_);
return v_fst_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonM_run(lean_object* v_00_u03b1_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v_fst_1208_; 
v___x_1206_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1207_ = lean_apply_1(v_a_1205_, v___x_1206_);
v_fst_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_fst_1208_);
lean_dec_ref(v___x_1207_);
return v_fst_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonM_run___redArg(lean_object* v_a_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_fst_1212_; 
v___x_1210_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1211_ = lean_apply_1(v_a_1209_, v___x_1210_);
v_fst_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_fst_1212_);
lean_dec_ref(v___x_1211_);
return v_fst_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonM_run(lean_object* v_00_u03b1_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v_fst_1217_; 
v___x_1215_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1216_ = lean_apply_1(v_a_1214_, v___x_1215_);
v_fst_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_fst_1217_);
lean_dec_ref(v___x_1216_);
return v_fst_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = l_Lean_ShareCommon_objectFactory;
v___x_1221_ = lean_state_sharecommon(v___x_1220_, v_a_1219_, v_a_1218_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0(lean_object* v_00_u03b1_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(v_a_1223_, v_a_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_shareCommon___redArg(lean_object* v_a_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v_fst_1229_; 
v___x_1227_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1228_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(v_a_1226_, v___x_1227_);
v_fst_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_fst_1229_);
lean_dec_ref(v___x_1228_);
return v_fst_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_shareCommon(lean_object* v_00_u03b1_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_ShareCommon_shareCommon___redArg(v_a_1231_);
return v___x_1232_;
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
