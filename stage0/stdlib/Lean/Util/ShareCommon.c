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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_cellCount_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_2_ = lean_unsigned_to_nat(4u);
v___x_3_ = lean_nat_mul(v_x_1_, v___x_2_);
v___x_4_ = lean_unsigned_to_nat(2u);
v___x_5_ = lean_nat_add(v___x_3_, v___x_4_);
lean_dec(v___x_3_);
v___x_6_ = lean_unsigned_to_nat(3u);
v___x_7_ = lean_nat_div(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
v_cellCount_8_ = l_Nat_nextPowerOfTwo(v___x_7_);
lean_dec(v___x_7_);
v___x_9_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_8_);
v___x_10_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_8_);
v___x_11_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_8_);
v___x_12_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_12_, 0, v___x_9_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
lean_ctor_set(v___x_12_, 2, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__0___redArg___boxed(lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_ShareCommon_objectFactory___elam__0___redArg(v_x_13_);
lean_dec(v_x_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__0(lean_object* v_00_u03b1_15_, lean_object* v_00_u03b2_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_x_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_ShareCommon_objectFactory___elam__0___redArg(v_x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__0___boxed(lean_object* v_00_u03b1_21_, lean_object* v_00_u03b2_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_x_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_ShareCommon_objectFactory___elam__0(v_00_u03b1_21_, v_00_u03b2_22_, v_inst_23_, v_inst_24_, v_x_25_);
lean_dec(v_x_25_);
lean_dec_ref(v_inst_24_);
lean_dec_ref(v_inst_23_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__3___redArg(lean_object* v_x_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v_cellCount_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_28_ = lean_unsigned_to_nat(4u);
v___x_29_ = lean_nat_mul(v_x_27_, v___x_28_);
v___x_30_ = lean_unsigned_to_nat(2u);
v___x_31_ = lean_nat_add(v___x_29_, v___x_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_unsigned_to_nat(3u);
v___x_33_ = lean_nat_div(v___x_31_, v___x_32_);
lean_dec(v___x_31_);
v_cellCount_34_ = l_Nat_nextPowerOfTwo(v___x_33_);
lean_dec(v___x_33_);
v___x_35_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_34_);
v___x_36_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_34_);
v___x_37_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_34_);
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v___x_35_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__3___redArg___boxed(lean_object* v_x_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_ShareCommon_objectFactory___elam__3___redArg(v_x_39_);
lean_dec(v_x_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__3(lean_object* v_00_u03b1_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_x_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_ShareCommon_objectFactory___elam__3___redArg(v_x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__3___boxed(lean_object* v_00_u03b1_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_ShareCommon_objectFactory___elam__3(v_00_u03b1_46_, v_inst_47_, v_inst_48_, v_x_49_);
lean_dec(v_x_49_);
lean_dec_ref(v_inst_48_);
lean_dec_ref(v_inst_47_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(lean_object* v_inst_51_, lean_object* v_m_52_, lean_object* v_query_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_zero_57_; uint8_t v_isZero_58_; 
v_zero_57_ = lean_unsigned_to_nat(0u);
v_isZero_58_ = lean_nat_dec_eq(v_x_55_, v_zero_57_);
if (v_isZero_58_ == 1)
{
lean_dec(v_x_56_);
lean_dec(v_x_55_);
lean_dec(v_query_53_);
lean_dec_ref(v_inst_51_);
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_59_; 
v___x_59_ = lean_box(2);
return v___x_59_;
}
else
{
lean_object* v_val_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
v_val_60_ = lean_ctor_get(v_x_54_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v_x_54_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v_x_54_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_val_60_);
lean_dec(v_x_54_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_val_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
else
{
lean_object* v_keyArray_68_; lean_object* v_valueArray_69_; lean_object* v___x_70_; uint8_t v_isSome_71_; 
v_keyArray_68_ = lean_ctor_get(v_m_52_, 1);
v_valueArray_69_ = lean_ctor_get(v_m_52_, 2);
v___x_70_ = lean_array_fget_borrowed(v_keyArray_68_, v_x_56_);
v_isSome_71_ = lean_noption_is_some(v___x_70_);
if (v_isSome_71_ == 0)
{
lean_dec(v_x_55_);
lean_dec(v_query_53_);
lean_dec_ref(v_inst_51_);
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_72_; 
v___x_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_72_, 0, v_x_56_);
return v___x_72_;
}
else
{
lean_object* v_val_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
lean_dec(v_x_56_);
v_val_73_ = lean_ctor_get(v_x_54_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v_x_54_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v_x_54_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_val_73_);
lean_dec(v_x_54_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_val_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
else
{
lean_object* v_one_81_; lean_object* v_n_82_; lean_object* v___y_84_; 
v_one_81_ = lean_unsigned_to_nat(1u);
v_n_82_ = lean_nat_sub(v_x_55_, v_one_81_);
lean_dec(v_x_55_);
if (v_isSome_71_ == 0)
{
goto v___jp_90_;
}
else
{
lean_object* v___x_92_; uint8_t v_isSome_93_; 
v___x_92_ = lean_array_fget_borrowed(v_valueArray_69_, v_x_56_);
v_isSome_93_ = lean_noption_is_some(v___x_92_);
if (v_isSome_93_ == 0)
{
goto v___jp_90_;
}
else
{
lean_object* v_val_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
lean_inc(v___x_70_);
v_val_94_ = lean_noption_get(v___x_70_);
lean_inc_ref(v_inst_51_);
lean_inc(v_query_53_);
lean_inc(v_val_94_);
v___x_95_ = lean_apply_2(v_inst_51_, v_val_94_, v_query_53_);
v___x_96_ = lean_unbox(v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
lean_dec(v_val_94_);
v___x_97_ = lean_array_get_size(v_keyArray_68_);
v___x_98_ = lean_nat_add(v_x_56_, v_one_81_);
lean_dec(v_x_56_);
v___x_99_ = lean_nat_dec_lt(v___x_98_, v___x_97_);
if (v___x_99_ == 0)
{
lean_dec(v___x_98_);
v_x_55_ = v_n_82_;
v_x_56_ = v_zero_57_;
goto _start;
}
else
{
v_x_55_ = v_n_82_;
v_x_56_ = v___x_98_;
goto _start;
}
}
else
{
lean_object* v_val_102_; lean_object* v___x_103_; 
lean_dec(v_n_82_);
lean_dec(v_x_54_);
lean_dec(v_query_53_);
lean_dec_ref(v_inst_51_);
lean_inc(v___x_92_);
v_val_102_ = lean_noption_get(v___x_92_);
v___x_103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_103_, 0, v_x_56_);
lean_ctor_set(v___x_103_, 1, v_val_94_);
lean_ctor_set(v___x_103_, 2, v_val_102_);
return v___x_103_;
}
}
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_85_ = lean_array_get_size(v_keyArray_68_);
v___x_86_ = lean_nat_add(v_x_56_, v_one_81_);
lean_dec(v_x_56_);
v___x_87_ = lean_nat_dec_lt(v___x_86_, v___x_85_);
if (v___x_87_ == 0)
{
lean_dec(v___x_86_);
v_x_54_ = v___y_84_;
v_x_55_ = v_n_82_;
v_x_56_ = v_zero_57_;
goto _start;
}
else
{
v_x_54_ = v___y_84_;
v_x_55_ = v_n_82_;
v_x_56_ = v___x_86_;
goto _start;
}
}
v___jp_90_:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_91_; 
lean_inc(v_x_56_);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v_x_56_);
v___y_84_ = v___x_91_;
goto v___jp_83_;
}
else
{
v___y_84_ = v_x_54_;
goto v___jp_83_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg___boxed(lean_object* v_inst_104_, lean_object* v_m_105_, lean_object* v_query_106_, lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_104_, v_m_105_, v_query_106_, v_x_107_, v_x_108_, v_x_109_);
lean_dec_ref(v_m_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_m_113_, lean_object* v_query_114_){
_start:
{
lean_object* v_keyArray_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint64_t v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v_fold_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_keyArray_115_ = lean_ctor_get(v_m_113_, 1);
v___x_116_ = lean_array_get_size(v_keyArray_115_);
lean_inc(v_query_114_);
v___x_117_ = lean_apply_1(v_inst_112_, v_query_114_);
v___x_118_ = 32ULL;
v___x_119_ = lean_unbox_uint64(v___x_117_);
v___x_120_ = lean_uint64_shift_right(v___x_119_, v___x_118_);
v___x_121_ = lean_unbox_uint64(v___x_117_);
lean_dec_ref(v___x_117_);
v_fold_122_ = lean_uint64_xor(v___x_121_, v___x_120_);
v___x_123_ = 16ULL;
v___x_124_ = lean_uint64_shift_right(v_fold_122_, v___x_123_);
v___x_125_ = lean_uint64_xor(v_fold_122_, v___x_124_);
v___x_126_ = lean_uint64_to_usize(v___x_125_);
v___x_127_ = lean_usize_of_nat(v___x_116_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_sub(v___x_127_, v___x_128_);
v___x_130_ = lean_usize_land(v___x_126_, v___x_129_);
v___x_131_ = lean_usize_to_nat(v___x_130_);
v___x_132_ = lean_box(0);
v___x_133_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_111_, v_m_113_, v_query_114_, v___x_132_, v___x_116_, v___x_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg___boxed(lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_m_136_, lean_object* v_query_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_134_, v_inst_135_, v_m_136_, v_query_137_);
lean_dec_ref(v_m_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8_spec__11___redArg(lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_b_141_, lean_object* v_acc_142_, lean_object* v_i_143_){
_start:
{
lean_object* v___y_145_; lean_object* v_keyArray_153_; lean_object* v_valueArray_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v_keyArray_153_ = lean_ctor_get(v_b_141_, 1);
v_valueArray_154_ = lean_ctor_get(v_b_141_, 2);
v___x_155_ = lean_array_get_size(v_keyArray_153_);
v___x_156_ = lean_nat_dec_lt(v_i_143_, v___x_155_);
if (v___x_156_ == 0)
{
lean_dec(v_i_143_);
lean_dec_ref(v_inst_140_);
lean_dec_ref(v_inst_139_);
return v_acc_142_;
}
else
{
lean_object* v___x_157_; uint8_t v_isSome_158_; 
v___x_157_ = lean_array_fget_borrowed(v_keyArray_153_, v_i_143_);
v_isSome_158_ = lean_noption_is_some(v___x_157_);
if (v_isSome_158_ == 0)
{
goto v___jp_149_;
}
else
{
lean_object* v___x_159_; uint8_t v_isSome_160_; 
v___x_159_ = lean_array_fget_borrowed(v_valueArray_154_, v_i_143_);
v_isSome_160_ = lean_noption_is_some(v___x_159_);
if (v_isSome_160_ == 0)
{
goto v___jp_149_;
}
else
{
lean_object* v_val_161_; lean_object* v_val_162_; lean_object* v_i_164_; lean_object* v___x_169_; 
lean_inc(v___x_157_);
v_val_161_ = lean_noption_get(v___x_157_);
lean_inc(v___x_159_);
v_val_162_ = lean_noption_get(v___x_159_);
lean_inc(v_val_161_);
lean_inc_ref(v_inst_140_);
lean_inc_ref(v_inst_139_);
v___x_169_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_139_, v_inst_140_, v_acc_142_, v_val_161_);
switch(lean_obj_tag(v___x_169_))
{
case 0:
{
lean_object* v_index_170_; lean_object* v_size_171_; lean_object* v___x_172_; 
v_index_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_index_170_);
lean_dec_ref_known(v___x_169_, 3);
v_size_171_ = lean_ctor_get(v_acc_142_, 0);
lean_inc(v_size_171_);
v___x_172_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_142_, v_size_171_, v_index_170_, v_val_161_, v_val_162_);
lean_dec(v_index_170_);
v___y_145_ = v___x_172_;
goto v___jp_144_;
}
case 1:
{
lean_object* v_index_173_; 
v_index_173_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_index_173_);
lean_dec_ref_known(v___x_169_, 1);
v_i_164_ = v_index_173_;
goto v___jp_163_;
}
default: 
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_142_, v___x_174_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_index_176_; 
v_index_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_index_176_);
lean_dec_ref_known(v___x_175_, 1);
v_i_164_ = v_index_176_;
goto v___jp_163_;
}
else
{
lean_dec(v_val_162_);
lean_dec(v_val_161_);
v___y_145_ = v_acc_142_;
goto v___jp_144_;
}
}
}
v___jp_163_:
{
lean_object* v_size_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_size_165_ = lean_ctor_get(v_acc_142_, 0);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_add(v_size_165_, v___x_166_);
v___x_168_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_142_, v___x_167_, v_i_164_, v_val_161_, v_val_162_);
lean_dec(v_i_164_);
v___y_145_ = v___x_168_;
goto v___jp_144_;
}
}
}
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = lean_nat_add(v_i_143_, v___x_146_);
lean_dec(v_i_143_);
v_acc_142_ = v___y_145_;
v_i_143_ = v___x_147_;
goto _start;
}
v___jp_149_:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(1u);
v___x_151_ = lean_nat_add(v_i_143_, v___x_150_);
lean_dec(v_i_143_);
v_i_143_ = v___x_151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8_spec__11___redArg___boxed(lean_object* v_inst_177_, lean_object* v_inst_178_, lean_object* v_b_179_, lean_object* v_acc_180_, lean_object* v_i_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8_spec__11___redArg(v_inst_177_, v_inst_178_, v_b_179_, v_acc_180_, v_i_181_);
lean_dec_ref(v_b_179_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8___redArg(lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_init_185_, lean_object* v_b_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8_spec__11___redArg(v_inst_183_, v_inst_184_, v_b_186_, v_init_185_, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8___redArg___boxed(lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_init_191_, lean_object* v_b_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8___redArg(v_inst_189_, v_inst_190_, v_init_191_, v_b_192_);
lean_dec_ref(v_b_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4___redArg(lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_m_196_){
_start:
{
lean_object* v_keyArray_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v_cellCount_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v_target_204_; lean_object* v___x_205_; 
v_keyArray_197_ = lean_ctor_get(v_m_196_, 1);
v___x_198_ = lean_array_get_size(v_keyArray_197_);
v___x_199_ = lean_unsigned_to_nat(2u);
v_cellCount_200_ = lean_nat_mul(v___x_198_, v___x_199_);
v___x_201_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_200_);
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_200_);
v___x_203_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_200_);
v_target_204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_204_, 0, v___x_201_);
lean_ctor_set(v_target_204_, 1, v___x_202_);
lean_ctor_set(v_target_204_, 2, v___x_203_);
v___x_205_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8___redArg(v_inst_194_, v_inst_195_, v_target_204_, v_m_196_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4___redArg___boxed(lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_m_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4___redArg(v_inst_206_, v_inst_207_, v_m_208_);
lean_dec_ref(v_m_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__5___redArg(lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_x_212_, lean_object* v___y_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___y_216_; lean_object* v_i_217_; lean_object* v___y_223_; lean_object* v___y_233_; lean_object* v_i_234_; lean_object* v___x_249_; 
v___x_214_ = lean_box(0);
lean_inc(v___y_213_);
lean_inc_ref(v_inst_211_);
lean_inc_ref(v_inst_210_);
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_210_, v_inst_211_, v_x_212_, v___y_213_);
switch(lean_obj_tag(v___x_249_))
{
case 0:
{
lean_dec_ref_known(v___x_249_, 3);
lean_dec(v___y_213_);
lean_dec_ref(v_inst_211_);
lean_dec_ref(v_inst_210_);
return v_x_212_;
}
case 1:
{
lean_object* v_index_250_; lean_object* v_size_251_; lean_object* v_keyArray_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_index_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_index_250_);
lean_dec_ref_known(v___x_249_, 1);
v_size_251_ = lean_ctor_get(v_x_212_, 0);
v_keyArray_252_ = lean_ctor_get(v_x_212_, 1);
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_add(v_size_251_, v___x_253_);
v___x_255_ = lean_array_get_size(v_keyArray_252_);
v___x_256_ = lean_nat_dec_lt(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
lean_dec(v___x_254_);
lean_dec(v_index_250_);
goto v___jp_239_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_257_ = lean_unsigned_to_nat(4u);
v___x_258_ = lean_nat_mul(v___x_254_, v___x_257_);
v___x_259_ = lean_unsigned_to_nat(3u);
v___x_260_ = lean_nat_mul(v___x_255_, v___x_259_);
v___x_261_ = lean_nat_dec_le(v___x_258_, v___x_260_);
lean_dec(v___x_260_);
lean_dec(v___x_258_);
if (v___x_261_ == 0)
{
lean_dec(v___x_254_);
lean_dec(v_index_250_);
goto v___jp_239_;
}
else
{
lean_object* v___x_262_; 
lean_dec_ref(v_inst_211_);
lean_dec_ref(v_inst_210_);
v___x_262_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x_212_, v___x_254_, v_index_250_, v___y_213_, v___x_214_);
lean_dec(v_index_250_);
return v___x_262_;
}
}
}
default: 
{
lean_object* v_size_263_; lean_object* v_keyArray_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_size_263_ = lean_ctor_get(v_x_212_, 0);
v_keyArray_264_ = lean_ctor_get(v_x_212_, 1);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_size_263_, v___x_265_);
v___x_267_ = lean_array_get_size(v_keyArray_264_);
v___x_268_ = lean_nat_dec_lt(v___x_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
lean_dec(v___x_266_);
lean_inc_ref(v_inst_211_);
lean_inc_ref(v_inst_210_);
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4___redArg(v_inst_210_, v_inst_211_, v_x_212_);
lean_dec_ref(v_x_212_);
v___y_223_ = v___x_269_;
goto v___jp_222_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_270_ = lean_unsigned_to_nat(4u);
v___x_271_ = lean_nat_mul(v___x_266_, v___x_270_);
lean_dec(v___x_266_);
v___x_272_ = lean_unsigned_to_nat(3u);
v___x_273_ = lean_nat_mul(v___x_267_, v___x_272_);
v___x_274_ = lean_nat_dec_le(v___x_271_, v___x_273_);
lean_dec(v___x_273_);
lean_dec(v___x_271_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
lean_inc_ref(v_inst_211_);
lean_inc_ref(v_inst_210_);
v___x_275_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4___redArg(v_inst_210_, v_inst_211_, v_x_212_);
lean_dec_ref(v_x_212_);
v___y_223_ = v___x_275_;
goto v___jp_222_;
}
else
{
v___y_223_ = v_x_212_;
goto v___jp_222_;
}
}
}
}
v___jp_215_:
{
lean_object* v_size_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_size_218_ = lean_ctor_get(v___y_216_, 0);
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_add(v_size_218_, v___x_219_);
v___x_221_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_216_, v___x_220_, v_i_217_, v___y_213_, v___x_214_);
lean_dec(v_i_217_);
return v___x_221_;
}
v___jp_222_:
{
lean_object* v___x_224_; 
lean_inc(v___y_213_);
v___x_224_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_210_, v_inst_211_, v___y_223_, v___y_213_);
switch(lean_obj_tag(v___x_224_))
{
case 0:
{
lean_object* v_index_225_; lean_object* v_size_226_; lean_object* v___x_227_; 
v_index_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_index_225_);
lean_dec_ref_known(v___x_224_, 3);
v_size_226_ = lean_ctor_get(v___y_223_, 0);
lean_inc(v_size_226_);
v___x_227_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_223_, v_size_226_, v_index_225_, v___y_213_, v___x_214_);
lean_dec(v_index_225_);
return v___x_227_;
}
case 1:
{
lean_object* v_index_228_; 
v_index_228_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_index_228_);
lean_dec_ref_known(v___x_224_, 1);
v___y_216_ = v___y_223_;
v_i_217_ = v_index_228_;
goto v___jp_215_;
}
default: 
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_223_, v___x_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_index_231_; 
v_index_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_index_231_);
lean_dec_ref_known(v___x_230_, 1);
v___y_216_ = v___y_223_;
v_i_217_ = v_index_231_;
goto v___jp_215_;
}
else
{
lean_dec(v___y_213_);
return v___y_223_;
}
}
}
}
v___jp_232_:
{
lean_object* v_size_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_size_235_ = lean_ctor_get(v___y_233_, 0);
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_add(v_size_235_, v___x_236_);
v___x_238_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_233_, v___x_237_, v_i_234_, v___y_213_, v___x_214_);
lean_dec(v_i_234_);
return v___x_238_;
}
v___jp_239_:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_inc_ref(v_inst_211_);
lean_inc_ref(v_inst_210_);
v___x_240_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4___redArg(v_inst_210_, v_inst_211_, v_x_212_);
lean_dec_ref(v_x_212_);
lean_inc(v___y_213_);
v___x_241_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_210_, v_inst_211_, v___x_240_, v___y_213_);
switch(lean_obj_tag(v___x_241_))
{
case 0:
{
lean_object* v_index_242_; lean_object* v_size_243_; lean_object* v___x_244_; 
v_index_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_index_242_);
lean_dec_ref_known(v___x_241_, 3);
v_size_243_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_size_243_);
v___x_244_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_240_, v_size_243_, v_index_242_, v___y_213_, v___x_214_);
lean_dec(v_index_242_);
return v___x_244_;
}
case 1:
{
lean_object* v_index_245_; 
v_index_245_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_index_245_);
lean_dec_ref_known(v___x_241_, 1);
v___y_233_ = v___x_240_;
v_i_234_ = v_index_245_;
goto v___jp_232_;
}
default: 
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_240_, v___x_246_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_index_248_; 
v_index_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_index_248_);
lean_dec_ref_known(v___x_247_, 1);
v___y_233_ = v___x_240_;
v_i_234_ = v_index_248_;
goto v___jp_232_;
}
else
{
lean_dec(v___y_213_);
return v___x_240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__5(lean_object* v_00_u03b1_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_x_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_ShareCommon_objectFactory___elam__5___redArg(v_inst_277_, v_inst_278_, v_x_279_, v___y_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__2___redArg(lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_x_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___y_288_; lean_object* v_i_289_; lean_object* v___y_305_; lean_object* v_i_306_; lean_object* v___y_312_; lean_object* v___x_321_; 
lean_inc(v___y_285_);
lean_inc_ref(v_inst_283_);
lean_inc_ref(v_inst_282_);
v___x_321_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_282_, v_inst_283_, v_x_284_, v___y_285_);
switch(lean_obj_tag(v___x_321_))
{
case 0:
{
lean_object* v_index_322_; lean_object* v_size_323_; lean_object* v___x_324_; 
lean_dec_ref(v_inst_283_);
lean_dec_ref(v_inst_282_);
v_index_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_index_322_);
lean_dec_ref_known(v___x_321_, 3);
v_size_323_ = lean_ctor_get(v_x_284_, 0);
lean_inc(v_size_323_);
v___x_324_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x_284_, v_size_323_, v_index_322_, v___y_285_, v___y_286_);
lean_dec(v_index_322_);
return v___x_324_;
}
case 1:
{
lean_object* v_index_325_; lean_object* v_size_326_; lean_object* v_keyArray_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_index_325_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_index_325_);
lean_dec_ref_known(v___x_321_, 1);
v_size_326_ = lean_ctor_get(v_x_284_, 0);
v_keyArray_327_ = lean_ctor_get(v_x_284_, 1);
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_nat_add(v_size_326_, v___x_328_);
v___x_330_ = lean_array_get_size(v_keyArray_327_);
v___x_331_ = lean_nat_dec_lt(v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
lean_dec(v___x_329_);
lean_dec(v_index_325_);
goto v___jp_294_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_332_ = lean_unsigned_to_nat(4u);
v___x_333_ = lean_nat_mul(v___x_329_, v___x_332_);
v___x_334_ = lean_unsigned_to_nat(3u);
v___x_335_ = lean_nat_mul(v___x_330_, v___x_334_);
v___x_336_ = lean_nat_dec_le(v___x_333_, v___x_335_);
lean_dec(v___x_335_);
lean_dec(v___x_333_);
if (v___x_336_ == 0)
{
lean_dec(v___x_329_);
lean_dec(v_index_325_);
goto v___jp_294_;
}
else
{
lean_object* v___x_337_; 
lean_dec_ref(v_inst_283_);
lean_dec_ref(v_inst_282_);
v___x_337_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x_284_, v___x_329_, v_index_325_, v___y_285_, v___y_286_);
lean_dec(v_index_325_);
return v___x_337_;
}
}
}
default: 
{
lean_object* v_size_338_; lean_object* v_keyArray_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_size_338_ = lean_ctor_get(v_x_284_, 0);
v_keyArray_339_ = lean_ctor_get(v_x_284_, 1);
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = lean_nat_add(v_size_338_, v___x_340_);
v___x_342_ = lean_array_get_size(v_keyArray_339_);
v___x_343_ = lean_nat_dec_lt(v___x_341_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
lean_dec(v___x_341_);
lean_inc_ref(v_inst_283_);
lean_inc_ref(v_inst_282_);
v___x_344_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4___redArg(v_inst_282_, v_inst_283_, v_x_284_);
lean_dec_ref(v_x_284_);
v___y_312_ = v___x_344_;
goto v___jp_311_;
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_345_ = lean_unsigned_to_nat(4u);
v___x_346_ = lean_nat_mul(v___x_341_, v___x_345_);
lean_dec(v___x_341_);
v___x_347_ = lean_unsigned_to_nat(3u);
v___x_348_ = lean_nat_mul(v___x_342_, v___x_347_);
v___x_349_ = lean_nat_dec_le(v___x_346_, v___x_348_);
lean_dec(v___x_348_);
lean_dec(v___x_346_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
lean_inc_ref(v_inst_283_);
lean_inc_ref(v_inst_282_);
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4___redArg(v_inst_282_, v_inst_283_, v_x_284_);
lean_dec_ref(v_x_284_);
v___y_312_ = v___x_350_;
goto v___jp_311_;
}
else
{
v___y_312_ = v_x_284_;
goto v___jp_311_;
}
}
}
}
v___jp_287_:
{
lean_object* v_size_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_size_290_ = lean_ctor_get(v___y_288_, 0);
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_size_290_, v___x_291_);
v___x_293_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_288_, v___x_292_, v_i_289_, v___y_285_, v___y_286_);
lean_dec(v_i_289_);
return v___x_293_;
}
v___jp_294_:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_inc_ref(v_inst_283_);
lean_inc_ref(v_inst_282_);
v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4___redArg(v_inst_282_, v_inst_283_, v_x_284_);
lean_dec_ref(v_x_284_);
lean_inc(v___y_285_);
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_282_, v_inst_283_, v___x_295_, v___y_285_);
switch(lean_obj_tag(v___x_296_))
{
case 0:
{
lean_object* v_index_297_; lean_object* v_size_298_; lean_object* v___x_299_; 
v_index_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_index_297_);
lean_dec_ref_known(v___x_296_, 3);
v_size_298_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_size_298_);
v___x_299_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_295_, v_size_298_, v_index_297_, v___y_285_, v___y_286_);
lean_dec(v_index_297_);
return v___x_299_;
}
case 1:
{
lean_object* v_index_300_; 
v_index_300_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_index_300_);
lean_dec_ref_known(v___x_296_, 1);
v___y_288_ = v___x_295_;
v_i_289_ = v_index_300_;
goto v___jp_287_;
}
default: 
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_295_, v___x_301_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_index_303_; 
v_index_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_index_303_);
lean_dec_ref_known(v___x_302_, 1);
v___y_288_ = v___x_295_;
v_i_289_ = v_index_303_;
goto v___jp_287_;
}
else
{
lean_dec(v___y_286_);
lean_dec(v___y_285_);
return v___x_295_;
}
}
}
}
v___jp_304_:
{
lean_object* v_size_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_size_307_ = lean_ctor_get(v___y_305_, 0);
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_size_307_, v___x_308_);
v___x_310_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_305_, v___x_309_, v_i_306_, v___y_285_, v___y_286_);
lean_dec(v_i_306_);
return v___x_310_;
}
v___jp_311_:
{
lean_object* v___x_313_; 
lean_inc(v___y_285_);
v___x_313_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_282_, v_inst_283_, v___y_312_, v___y_285_);
switch(lean_obj_tag(v___x_313_))
{
case 0:
{
lean_object* v_index_314_; lean_object* v_size_315_; lean_object* v___x_316_; 
v_index_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_index_314_);
lean_dec_ref_known(v___x_313_, 3);
v_size_315_ = lean_ctor_get(v___y_312_, 0);
lean_inc(v_size_315_);
v___x_316_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_312_, v_size_315_, v_index_314_, v___y_285_, v___y_286_);
lean_dec(v_index_314_);
return v___x_316_;
}
case 1:
{
lean_object* v_index_317_; 
v_index_317_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_index_317_);
lean_dec_ref_known(v___x_313_, 1);
v___y_305_ = v___y_312_;
v_i_306_ = v_index_317_;
goto v___jp_304_;
}
default: 
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_312_, v___x_318_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_index_320_; 
v_index_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_index_320_);
lean_dec_ref_known(v___x_319_, 1);
v___y_305_ = v___y_312_;
v_i_306_ = v_index_320_;
goto v___jp_304_;
}
else
{
lean_dec(v___y_286_);
lean_dec(v___y_285_);
return v___y_312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__2(lean_object* v_00_u03b1_351_, lean_object* v_00_u03b2_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_x_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_ShareCommon_objectFactory___elam__2___redArg(v_inst_353_, v_inst_354_, v_x_355_, v___y_356_, v___y_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_m_361_, lean_object* v_query_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_359_, v_inst_360_, v_m_361_, v_query_362_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_index_364_; lean_object* v_key_365_; lean_object* v_value_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
v_index_364_ = lean_ctor_get(v___x_363_, 0);
v_key_365_ = lean_ctor_get(v___x_363_, 1);
v_value_366_ = lean_ctor_get(v___x_363_, 2);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_363_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_value_366_);
lean_inc(v_key_365_);
lean_inc(v_index_364_);
lean_dec(v___x_363_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_index_364_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_key_365_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_value_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v___x_374_; 
lean_dec(v___x_363_);
v___x_374_ = lean_box(1);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg___boxed(lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_m_377_, lean_object* v_query_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(v_inst_375_, v_inst_376_, v_m_377_, v_query_378_);
lean_dec_ref(v_m_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__7___redArg(lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_m_382_, lean_object* v_a_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(v_inst_380_, v_inst_381_, v_m_382_, v_a_383_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_key_385_; lean_object* v___x_386_; 
v_key_385_ = lean_ctor_get(v___x_384_, 1);
lean_inc(v_key_385_);
lean_dec_ref_known(v___x_384_, 3);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v_key_385_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; 
v___x_387_ = lean_box(0);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__7___redArg___boxed(lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_m_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__7___redArg(v_inst_388_, v_inst_389_, v_m_390_, v_a_391_);
lean_dec_ref(v_m_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4(lean_object* v_00_u03b1_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_x_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__7___redArg(v_inst_394_, v_inst_395_, v_x_396_, v___y_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___boxed(lean_object* v_00_u03b1_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_x_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_ShareCommon_objectFactory___elam__4(v_00_u03b1_399_, v_inst_400_, v_inst_401_, v_x_402_, v___y_403_);
lean_dec_ref(v_x_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_m_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(v_inst_405_, v_inst_406_, v_m_407_, v_a_408_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_value_410_; lean_object* v___x_411_; 
v_value_410_ = lean_ctor_get(v___x_409_, 2);
lean_inc(v_value_410_);
lean_dec_ref_known(v___x_409_, 3);
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v_value_410_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; 
v___x_412_ = lean_box(0);
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg___boxed(lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_m_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_413_, v_inst_414_, v_m_415_, v_a_416_);
lean_dec_ref(v_m_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1(lean_object* v_00_u03b1_418_, lean_object* v_00_u03b2_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_x_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_420_, v_inst_421_, v_x_422_, v___y_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___boxed(lean_object* v_00_u03b1_425_, lean_object* v_00_u03b2_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_x_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_ShareCommon_objectFactory___elam__1(v_00_u03b1_425_, v_00_u03b2_426_, v_inst_427_, v_inst_428_, v_x_429_, v___y_430_);
lean_dec_ref(v_x_429_);
return v_res_431_;
}
}
static lean_object* _init_l_Lean_ShareCommon_objectFactory___closed__7(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = ((lean_object*)(l_Lean_ShareCommon_objectFactory___closed__6));
v___x_446_ = l_ShareCommon_StateFactory_mkImpl(v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_ShareCommon_objectFactory(void){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = lean_obj_once(&l_Lean_ShareCommon_objectFactory___closed__7, &l_Lean_ShareCommon_objectFactory___closed__7_once, _init_l_Lean_ShareCommon_objectFactory___closed__7);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___redArg(lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_x_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_448_, v_inst_449_, v_x_450_, v___y_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__1___redArg___boxed(lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_x_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_ShareCommon_objectFactory___elam__1___redArg(v_inst_453_, v_inst_454_, v_x_455_, v___y_456_);
lean_dec_ref(v_x_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___redArg(lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_x_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__7___redArg(v_inst_458_, v_inst_459_, v_x_460_, v___y_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_objectFactory___elam__4___redArg___boxed(lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_x_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_ShareCommon_objectFactory___elam__4___redArg(v_inst_463_, v_inst_464_, v_x_465_, v___y_466_);
lean_dec_ref(v_x_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1(lean_object* v_00_u03b1_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_00_u03b2_471_, lean_object* v_m_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_469_, v_inst_470_, v_m_472_, v_a_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___boxed(lean_object* v_00_u03b1_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_00_u03b2_478_, lean_object* v_m_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1(v_00_u03b1_475_, v_inst_476_, v_inst_477_, v_00_u03b2_478_, v_m_479_, v_a_480_);
lean_dec_ref(v_m_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3(lean_object* v_00_u03b1_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_00_u03b2_485_, lean_object* v_m_486_, lean_object* v_query_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_483_, v_inst_484_, v_m_486_, v_query_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___boxed(lean_object* v_00_u03b1_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_00_u03b2_492_, lean_object* v_m_493_, lean_object* v_query_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3(v_00_u03b1_489_, v_inst_490_, v_inst_491_, v_00_u03b2_492_, v_m_493_, v_query_494_);
lean_dec_ref(v_m_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4(lean_object* v_00_u03b1_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_00_u03b2_499_, lean_object* v_m_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4___redArg(v_inst_497_, v_inst_498_, v_m_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4___boxed(lean_object* v_00_u03b1_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_00_u03b2_505_, lean_object* v_m_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4(v_00_u03b1_502_, v_inst_503_, v_inst_504_, v_00_u03b2_505_, v_m_506_);
lean_dec_ref(v_m_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__7(lean_object* v_00_u03b1_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_00_u03b2_511_, lean_object* v_m_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__7___redArg(v_inst_509_, v_inst_510_, v_m_512_, v_a_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__7___boxed(lean_object* v_00_u03b1_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_00_u03b2_518_, lean_object* v_m_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__7(v_00_u03b1_515_, v_inst_516_, v_inst_517_, v_00_u03b2_518_, v_m_519_, v_a_520_);
lean_dec_ref(v_m_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3(lean_object* v_00_u03b1_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_00_u03b2_525_, lean_object* v_m_526_, lean_object* v_query_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(v_inst_523_, v_inst_524_, v_m_526_, v_query_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___boxed(lean_object* v_00_u03b1_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_00_u03b2_532_, lean_object* v_m_533_, lean_object* v_query_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3(v_00_u03b1_529_, v_inst_530_, v_inst_531_, v_00_u03b2_532_, v_m_533_, v_query_534_);
lean_dec_ref(v_m_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(lean_object* v_00_u03b1_536_, lean_object* v_inst_537_, lean_object* v_00_u03b2_538_, lean_object* v_m_539_, lean_object* v_query_540_, lean_object* v_x_541_, lean_object* v_x_542_, lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_537_, v_m_539_, v_query_540_, v_x_541_, v_x_542_, v_x_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_546_, lean_object* v_inst_547_, lean_object* v_00_u03b2_548_, lean_object* v_m_549_, lean_object* v_query_550_, lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(v_00_u03b1_546_, v_inst_547_, v_00_u03b2_548_, v_m_549_, v_query_550_, v_x_551_, v_x_552_, v_x_553_, v_x_554_);
lean_dec_ref(v_m_549_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8(lean_object* v_00_u03b1_556_, lean_object* v_00_u03b2_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_init_560_, lean_object* v_b_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8___redArg(v_inst_558_, v_inst_559_, v_init_560_, v_b_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8___boxed(lean_object* v_00_u03b1_563_, lean_object* v_00_u03b2_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_init_567_, lean_object* v_b_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8(v_00_u03b1_563_, v_00_u03b2_564_, v_inst_565_, v_inst_566_, v_init_567_, v_b_568_);
lean_dec_ref(v_b_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8_spec__11(lean_object* v_00_u03b1_570_, lean_object* v_00_u03b2_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_b_574_, lean_object* v_acc_575_, lean_object* v_i_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8_spec__11___redArg(v_inst_572_, v_inst_573_, v_b_574_, v_acc_575_, v_i_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8_spec__11___boxed(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_b_582_, lean_object* v_acc_583_, lean_object* v_i_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ShareCommon_objectFactory___elam__2_spec__4_spec__8_spec__11(v_00_u03b1_578_, v_00_u03b2_579_, v_inst_580_, v_inst_581_, v_b_582_, v_acc_583_, v_i_584_);
lean_dec_ref(v_b_582_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(lean_object* v_inst_586_, lean_object* v_keys_587_, lean_object* v_vals_588_, lean_object* v_i_589_, lean_object* v_k_590_){
_start:
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = lean_array_get_size(v_keys_587_);
v___x_592_ = lean_nat_dec_lt(v_i_589_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
lean_dec(v_k_590_);
lean_dec(v_i_589_);
lean_dec_ref(v_inst_586_);
v___x_593_ = lean_box(0);
return v___x_593_;
}
else
{
lean_object* v_k_x27_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_k_x27_594_ = lean_array_fget_borrowed(v_keys_587_, v_i_589_);
lean_inc_ref(v_inst_586_);
lean_inc(v_k_x27_594_);
lean_inc(v_k_590_);
v___x_595_ = lean_apply_2(v_inst_586_, v_k_590_, v_k_x27_594_);
v___x_596_ = lean_unbox(v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_nat_add(v_i_589_, v___x_597_);
lean_dec(v_i_589_);
v_i_589_ = v___x_598_;
goto _start;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v_k_590_);
lean_dec_ref(v_inst_586_);
v___x_600_ = lean_array_fget_borrowed(v_vals_588_, v_i_589_);
lean_dec(v_i_589_);
lean_inc(v___x_600_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg___boxed(lean_object* v_inst_602_, lean_object* v_keys_603_, lean_object* v_vals_604_, lean_object* v_i_605_, lean_object* v_k_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_602_, v_keys_603_, v_vals_604_, v_i_605_, v_k_606_);
lean_dec_ref(v_vals_604_);
lean_dec_ref(v_keys_603_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(lean_object* v_inst_608_, lean_object* v_x_609_, size_t v_x_610_, lean_object* v_x_611_){
_start:
{
if (lean_obj_tag(v_x_609_) == 0)
{
lean_object* v_es_612_; lean_object* v___x_613_; size_t v___x_614_; size_t v___x_615_; lean_object* v_j_616_; lean_object* v___x_617_; 
v_es_612_ = lean_ctor_get(v_x_609_, 0);
lean_inc_ref(v_es_612_);
lean_dec_ref_known(v_x_609_, 1);
v___x_613_ = lean_box(2);
v___x_614_ = ((size_t)31ULL);
v___x_615_ = lean_usize_land(v_x_610_, v___x_614_);
v_j_616_ = lean_usize_to_nat(v___x_615_);
v___x_617_ = lean_array_get(v___x_613_, v_es_612_, v_j_616_);
lean_dec(v_j_616_);
lean_dec_ref(v_es_612_);
switch(lean_obj_tag(v___x_617_))
{
case 0:
{
lean_object* v_key_618_; lean_object* v_val_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_key_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_key_618_);
v_val_619_ = lean_ctor_get(v___x_617_, 1);
lean_inc(v_val_619_);
lean_dec_ref_known(v___x_617_, 2);
v___x_620_ = lean_apply_2(v_inst_608_, v_x_611_, v_key_618_);
v___x_621_ = lean_unbox(v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
lean_dec(v_val_619_);
v___x_622_ = lean_box(0);
return v___x_622_;
}
else
{
lean_object* v___x_623_; 
v___x_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_623_, 0, v_val_619_);
return v___x_623_;
}
}
case 1:
{
lean_object* v_node_624_; size_t v___x_625_; size_t v___x_626_; 
v_node_624_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_node_624_);
lean_dec_ref_known(v___x_617_, 1);
v___x_625_ = ((size_t)5ULL);
v___x_626_ = lean_usize_shift_right(v_x_610_, v___x_625_);
v_x_609_ = v_node_624_;
v_x_610_ = v___x_626_;
goto _start;
}
default: 
{
lean_object* v___x_628_; 
lean_dec(v_x_611_);
lean_dec_ref(v_inst_608_);
v___x_628_ = lean_box(0);
return v___x_628_;
}
}
}
else
{
lean_object* v_ks_629_; lean_object* v_vs_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_ks_629_ = lean_ctor_get(v_x_609_, 0);
lean_inc_ref(v_ks_629_);
v_vs_630_ = lean_ctor_get(v_x_609_, 1);
lean_inc_ref(v_vs_630_);
lean_dec_ref_known(v_x_609_, 2);
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_608_, v_ks_629_, v_vs_630_, v___x_631_, v_x_611_);
lean_dec_ref(v_vs_630_);
lean_dec_ref(v_ks_629_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___boxed(lean_object* v_inst_633_, lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
size_t v_x_688__boxed_637_; lean_object* v_res_638_; 
v_x_688__boxed_637_ = lean_unbox_usize(v_x_635_);
lean_dec(v_x_635_);
v_res_638_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_633_, v_x_634_, v_x_688__boxed_637_, v_x_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
lean_object* v___x_643_; uint64_t v___x_644_; size_t v___x_645_; lean_object* v___x_646_; 
lean_inc(v_x_642_);
v___x_643_ = lean_apply_1(v_inst_640_, v_x_642_);
v___x_644_ = lean_unbox_uint64(v___x_643_);
lean_dec_ref(v___x_643_);
v___x_645_ = lean_uint64_to_usize(v___x_644_);
lean_inc_ref(v_x_641_);
v___x_646_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_639_, v_x_641_, v___x_645_, v_x_642_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg___boxed(lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_647_, v_inst_648_, v_x_649_, v_x_650_);
lean_dec_ref(v_x_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1(lean_object* v_00_u03b1_652_, lean_object* v_00_u03b2_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_x_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_654_, v_inst_655_, v_x_656_, v___y_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___boxed(lean_object* v_00_u03b1_659_, lean_object* v_00_u03b2_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_x_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_ShareCommon_persistentObjectFactory___elam__1(v_00_u03b1_659_, v_00_u03b2_660_, v_inst_661_, v_inst_662_, v_x_663_, v___y_664_);
lean_dec_ref(v_x_663_);
return v_res_665_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_666_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_object* v_00_u03b1_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_00_u03b2_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___boxed(lean_object* v_00_u03b1_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_00_u03b2_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(v_00_u03b1_674_, v_inst_675_, v_inst_676_, v_00_u03b2_677_);
lean_dec_ref(v_inst_676_);
lean_dec_ref(v_inst_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0(lean_object* v_00_u03b1_679_, lean_object* v_00_u03b2_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_x_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_box(0), v_inst_681_, v_inst_682_, lean_box(0));
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___boxed(lean_object* v_00_u03b1_685_, lean_object* v_00_u03b2_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_x_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_ShareCommon_persistentObjectFactory___elam__0(v_00_u03b1_685_, v_00_u03b2_686_, v_inst_687_, v_inst_688_, v_x_689_);
lean_dec(v_x_689_);
lean_dec_ref(v_inst_688_);
lean_dec_ref(v_inst_687_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3(lean_object* v_00_u03b1_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_x_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_box(0), v_inst_692_, v_inst_693_, lean_box(0));
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___boxed(lean_object* v_00_u03b1_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_x_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_ShareCommon_persistentObjectFactory___elam__3(v_00_u03b1_696_, v_inst_697_, v_inst_698_, v_x_699_);
lean_dec(v_x_699_);
lean_dec_ref(v_inst_698_);
lean_dec_ref(v_inst_697_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(lean_object* v_inst_701_, lean_object* v_keys_702_, lean_object* v_vals_703_, lean_object* v_i_704_, lean_object* v_k_705_){
_start:
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_array_get_size(v_keys_702_);
v___x_707_ = lean_nat_dec_lt(v_i_704_, v___x_706_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; 
lean_dec(v_k_705_);
lean_dec(v_i_704_);
lean_dec_ref(v_inst_701_);
v___x_708_ = lean_box(0);
return v___x_708_;
}
else
{
lean_object* v_k_x27_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_k_x27_709_ = lean_array_fget_borrowed(v_keys_702_, v_i_704_);
lean_inc_ref(v_inst_701_);
lean_inc(v_k_x27_709_);
lean_inc(v_k_705_);
v___x_710_ = lean_apply_2(v_inst_701_, v_k_705_, v_k_x27_709_);
v___x_711_ = lean_unbox(v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_add(v_i_704_, v___x_712_);
lean_dec(v_i_704_);
v_i_704_ = v___x_713_;
goto _start;
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v_k_705_);
lean_dec_ref(v_inst_701_);
v___x_715_ = lean_array_fget_borrowed(v_vals_703_, v_i_704_);
lean_dec(v_i_704_);
lean_inc(v___x_715_);
lean_inc(v_k_x27_709_);
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v_k_x27_709_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object* v_inst_718_, lean_object* v_keys_719_, lean_object* v_vals_720_, lean_object* v_i_721_, lean_object* v_k_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_718_, v_keys_719_, v_vals_720_, v_i_721_, v_k_722_);
lean_dec_ref(v_vals_720_);
lean_dec_ref(v_keys_719_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(lean_object* v_inst_724_, lean_object* v_x_725_, size_t v_x_726_, lean_object* v_x_727_){
_start:
{
if (lean_obj_tag(v_x_725_) == 0)
{
lean_object* v_es_728_; lean_object* v___x_729_; size_t v___x_730_; size_t v___x_731_; lean_object* v_j_732_; lean_object* v___x_733_; 
v_es_728_ = lean_ctor_get(v_x_725_, 0);
lean_inc_ref(v_es_728_);
lean_dec_ref_known(v_x_725_, 1);
v___x_729_ = lean_box(2);
v___x_730_ = ((size_t)31ULL);
v___x_731_ = lean_usize_land(v_x_726_, v___x_730_);
v_j_732_ = lean_usize_to_nat(v___x_731_);
v___x_733_ = lean_array_get(v___x_729_, v_es_728_, v_j_732_);
lean_dec(v_j_732_);
lean_dec_ref(v_es_728_);
switch(lean_obj_tag(v___x_733_))
{
case 0:
{
lean_object* v_key_734_; lean_object* v_val_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_key_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc_n(v_key_734_, 2);
v_val_735_ = lean_ctor_get(v___x_733_, 1);
lean_inc(v_val_735_);
lean_dec_ref_known(v___x_733_, 2);
v___x_736_ = lean_apply_2(v_inst_724_, v_x_727_, v_key_734_);
v___x_737_ = lean_unbox(v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
lean_dec(v_val_735_);
lean_dec(v_key_734_);
v___x_738_ = lean_box(0);
return v___x_738_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v_key_734_);
lean_ctor_set(v___x_739_, 1, v_val_735_);
v___x_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
}
case 1:
{
lean_object* v_node_741_; size_t v___x_742_; size_t v___x_743_; 
v_node_741_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_node_741_);
lean_dec_ref_known(v___x_733_, 1);
v___x_742_ = ((size_t)5ULL);
v___x_743_ = lean_usize_shift_right(v_x_726_, v___x_742_);
v_x_725_ = v_node_741_;
v_x_726_ = v___x_743_;
goto _start;
}
default: 
{
lean_object* v___x_745_; 
lean_dec(v_x_727_);
lean_dec_ref(v_inst_724_);
v___x_745_ = lean_box(0);
return v___x_745_;
}
}
}
else
{
lean_object* v_ks_746_; lean_object* v_vs_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_ks_746_ = lean_ctor_get(v_x_725_, 0);
lean_inc_ref(v_ks_746_);
v_vs_747_ = lean_ctor_get(v_x_725_, 1);
lean_inc_ref(v_vs_747_);
lean_dec_ref_known(v_x_725_, 2);
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_724_, v_ks_746_, v_vs_747_, v___x_748_, v_x_727_);
lean_dec_ref(v_vs_747_);
lean_dec_ref(v_ks_746_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg___boxed(lean_object* v_inst_750_, lean_object* v_x_751_, lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
size_t v_x_856__boxed_754_; lean_object* v_res_755_; 
v_x_856__boxed_754_ = lean_unbox_usize(v_x_752_);
lean_dec(v_x_752_);
v_res_755_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_750_, v_x_751_, v_x_856__boxed_754_, v_x_753_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
lean_object* v___x_760_; uint64_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
lean_inc(v_x_759_);
v___x_760_ = lean_apply_1(v_inst_757_, v_x_759_);
v___x_761_ = lean_unbox_uint64(v___x_760_);
lean_dec_ref(v___x_760_);
v___x_762_ = lean_uint64_to_usize(v___x_761_);
lean_inc_ref(v_x_758_);
v___x_763_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_756_, v_x_758_, v___x_762_, v_x_759_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg___boxed(lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_764_, v_inst_765_, v_x_766_, v_x_767_);
lean_dec_ref(v_x_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_x_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_769_, v_inst_770_, v_x_771_, v___y_772_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v___x_774_; 
v___x_774_ = lean_box(0);
return v___x_774_;
}
else
{
lean_object* v_val_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_783_; 
v_val_775_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_783_ == 0)
{
v___x_777_ = v___x_773_;
v_isShared_778_ = v_isSharedCheck_783_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_val_775_);
lean_dec(v___x_773_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_783_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_fst_779_; lean_object* v___x_781_; 
v_fst_779_ = lean_ctor_get(v_val_775_, 0);
lean_inc(v_fst_779_);
lean_dec(v_val_775_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v_fst_779_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_fst_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg___boxed(lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_x_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(v_inst_784_, v_inst_785_, v_x_786_, v___y_787_);
lean_dec_ref(v_x_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4(lean_object* v_00_u03b1_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_x_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(v_inst_790_, v_inst_791_, v_x_792_, v___y_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__4___boxed(lean_object* v_00_u03b1_795_, lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_x_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4(v_00_u03b1_795_, v_inst_796_, v_inst_797_, v_x_798_, v___y_799_);
lean_dec_ref(v_x_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(lean_object* v_inst_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
lean_object* v_ks_806_; lean_object* v_vs_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_832_; 
v_ks_806_ = lean_ctor_get(v_x_802_, 0);
v_vs_807_ = lean_ctor_get(v_x_802_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_x_802_);
if (v_isSharedCheck_832_ == 0)
{
v___x_809_ = v_x_802_;
v_isShared_810_ = v_isSharedCheck_832_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_vs_807_);
lean_inc(v_ks_806_);
lean_dec(v_x_802_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_832_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = lean_array_get_size(v_ks_806_);
v___x_812_ = lean_nat_dec_lt(v_x_803_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
lean_dec(v_x_803_);
lean_dec_ref(v_inst_801_);
v___x_813_ = lean_array_push(v_ks_806_, v_x_804_);
v___x_814_ = lean_array_push(v_vs_807_, v_x_805_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 1, v___x_814_);
lean_ctor_set(v___x_809_, 0, v___x_813_);
v___x_816_ = v___x_809_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
else
{
lean_object* v_k_x27_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_k_x27_818_ = lean_array_fget_borrowed(v_ks_806_, v_x_803_);
lean_inc_ref(v_inst_801_);
lean_inc(v_k_x27_818_);
lean_inc(v_x_804_);
v___x_819_ = lean_apply_2(v_inst_801_, v_x_804_, v_k_x27_818_);
v___x_820_ = lean_unbox(v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_822_; 
if (v_isShared_810_ == 0)
{
v___x_822_ = v___x_809_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_ks_806_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_vs_807_);
v___x_822_ = v_reuseFailAlloc_826_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_nat_add(v_x_803_, v___x_823_);
lean_dec(v_x_803_);
v_x_802_ = v___x_822_;
v_x_803_ = v___x_824_;
goto _start;
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
lean_dec_ref(v_inst_801_);
v___x_827_ = lean_array_fset(v_ks_806_, v_x_803_, v_x_804_);
v___x_828_ = lean_array_fset(v_vs_807_, v_x_803_, v_x_805_);
lean_dec(v_x_803_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 1, v___x_828_);
lean_ctor_set(v___x_809_, 0, v___x_827_);
v___x_830_ = v___x_809_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(lean_object* v_inst_833_, lean_object* v_n_834_, lean_object* v_k_835_, lean_object* v_v_836_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(v_inst_833_, v_n_834_, v___x_837_, v_k_835_, v_v_836_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_x_842_, size_t v_x_843_, size_t v_x_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
if (lean_obj_tag(v_x_842_) == 0)
{
lean_object* v_es_847_; size_t v___x_848_; size_t v___x_849_; lean_object* v_j_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_es_847_ = lean_ctor_get(v_x_842_, 0);
v___x_848_ = ((size_t)31ULL);
v___x_849_ = lean_usize_land(v_x_843_, v___x_848_);
v_j_850_ = lean_usize_to_nat(v___x_849_);
v___x_851_ = lean_array_get_size(v_es_847_);
v___x_852_ = lean_nat_dec_lt(v_j_850_, v___x_851_);
if (v___x_852_ == 0)
{
lean_dec(v_j_850_);
lean_dec(v_x_846_);
lean_dec(v_x_845_);
lean_dec_ref(v_inst_841_);
lean_dec_ref(v_inst_840_);
return v_x_842_;
}
else
{
lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_892_; 
lean_inc_ref(v_es_847_);
v_isSharedCheck_892_ = !lean_is_exclusive(v_x_842_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_x_842_, 0);
lean_dec(v_unused_893_);
v___x_854_ = v_x_842_;
v_isShared_855_ = v_isSharedCheck_892_;
goto v_resetjp_853_;
}
else
{
lean_dec(v_x_842_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_892_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v_v_856_; lean_object* v___x_857_; lean_object* v_xs_x27_858_; lean_object* v___y_860_; 
v_v_856_ = lean_array_fget(v_es_847_, v_j_850_);
v___x_857_ = lean_box(0);
v_xs_x27_858_ = lean_array_fset(v_es_847_, v_j_850_, v___x_857_);
switch(lean_obj_tag(v_v_856_))
{
case 0:
{
lean_object* v_key_865_; lean_object* v_val_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_877_; 
lean_dec_ref(v_inst_841_);
v_key_865_ = lean_ctor_get(v_v_856_, 0);
v_val_866_ = lean_ctor_get(v_v_856_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_v_856_);
if (v_isSharedCheck_877_ == 0)
{
v___x_868_ = v_v_856_;
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_val_866_);
lean_inc(v_key_865_);
lean_dec(v_v_856_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; uint8_t v___x_871_; 
lean_inc(v_key_865_);
lean_inc(v_x_845_);
v___x_870_ = lean_apply_2(v_inst_840_, v_x_845_, v_key_865_);
v___x_871_ = lean_unbox(v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; 
lean_del_object(v___x_868_);
v___x_872_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_865_, v_val_866_, v_x_845_, v_x_846_);
v___x_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
v___y_860_ = v___x_873_;
goto v___jp_859_;
}
else
{
lean_object* v___x_875_; 
lean_dec(v_val_866_);
lean_dec(v_key_865_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v_x_846_);
lean_ctor_set(v___x_868_, 0, v_x_845_);
v___x_875_ = v___x_868_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_x_845_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_x_846_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
v___y_860_ = v___x_875_;
goto v___jp_859_;
}
}
}
}
case 1:
{
lean_object* v_node_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_890_; 
v_node_878_ = lean_ctor_get(v_v_856_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v_v_856_);
if (v_isSharedCheck_890_ == 0)
{
v___x_880_ = v_v_856_;
v_isShared_881_ = v_isSharedCheck_890_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_node_878_);
lean_dec(v_v_856_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_890_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
size_t v___x_882_; size_t v___x_883_; size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_882_ = ((size_t)5ULL);
v___x_883_ = lean_usize_shift_right(v_x_843_, v___x_882_);
v___x_884_ = ((size_t)1ULL);
v___x_885_ = lean_usize_add(v_x_844_, v___x_884_);
v___x_886_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_840_, v_inst_841_, v_node_878_, v___x_883_, v___x_885_, v_x_845_, v_x_846_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_886_);
v___x_888_ = v___x_880_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
v___y_860_ = v___x_888_;
goto v___jp_859_;
}
}
}
default: 
{
lean_object* v___x_891_; 
lean_dec_ref(v_inst_841_);
lean_dec_ref(v_inst_840_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_x_845_);
lean_ctor_set(v___x_891_, 1, v_x_846_);
v___y_860_ = v___x_891_;
goto v___jp_859_;
}
}
v___jp_859_:
{
lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_861_ = lean_array_fset(v_xs_x27_858_, v_j_850_, v___y_860_);
lean_dec(v_j_850_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_861_);
v___x_863_ = v___x_854_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
else
{
lean_object* v_ks_894_; lean_object* v_vs_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_915_; 
v_ks_894_ = lean_ctor_get(v_x_842_, 0);
v_vs_895_ = lean_ctor_get(v_x_842_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_x_842_);
if (v_isSharedCheck_915_ == 0)
{
v___x_897_ = v_x_842_;
v_isShared_898_ = v_isSharedCheck_915_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_vs_895_);
lean_inc(v_ks_894_);
lean_dec(v_x_842_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_915_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_ks_894_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_vs_895_);
v___x_900_ = v_reuseFailAlloc_914_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v_newNode_901_; uint8_t v___y_903_; size_t v___x_909_; uint8_t v___x_910_; 
lean_inc_ref(v_inst_840_);
v_newNode_901_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(v_inst_840_, v___x_900_, v_x_845_, v_x_846_);
v___x_909_ = ((size_t)7ULL);
v___x_910_ = lean_usize_dec_le(v___x_909_, v_x_844_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_911_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_901_);
v___x_912_ = lean_unsigned_to_nat(4u);
v___x_913_ = lean_nat_dec_lt(v___x_911_, v___x_912_);
lean_dec(v___x_911_);
v___y_903_ = v___x_913_;
goto v___jp_902_;
}
else
{
v___y_903_ = v___x_910_;
goto v___jp_902_;
}
v___jp_902_:
{
if (v___y_903_ == 0)
{
lean_object* v_ks_904_; lean_object* v_vs_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_ks_904_ = lean_ctor_get(v_newNode_901_, 0);
lean_inc_ref(v_ks_904_);
v_vs_905_ = lean_ctor_get(v_newNode_901_, 1);
lean_inc_ref(v_vs_905_);
lean_dec_ref(v_newNode_901_);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0);
v___x_908_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_840_, v_inst_841_, v_x_844_, v_ks_904_, v_vs_905_, v___x_906_, v___x_907_);
lean_dec_ref(v_vs_905_);
lean_dec_ref(v_ks_904_);
return v___x_908_;
}
else
{
lean_dec_ref(v_inst_841_);
lean_dec_ref(v_inst_840_);
return v_newNode_901_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(lean_object* v_inst_916_, lean_object* v_inst_917_, size_t v_depth_918_, lean_object* v_keys_919_, lean_object* v_vals_920_, lean_object* v_i_921_, lean_object* v_entries_922_){
_start:
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_array_get_size(v_keys_919_);
v___x_924_ = lean_nat_dec_lt(v_i_921_, v___x_923_);
if (v___x_924_ == 0)
{
lean_dec(v_i_921_);
lean_dec_ref(v_inst_917_);
lean_dec_ref(v_inst_916_);
return v_entries_922_;
}
else
{
lean_object* v_k_925_; lean_object* v_v_926_; lean_object* v___x_927_; uint64_t v___x_928_; size_t v_h_929_; size_t v___x_930_; lean_object* v___x_931_; size_t v___x_932_; size_t v___x_933_; size_t v___x_934_; size_t v_h_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_k_925_ = lean_array_fget_borrowed(v_keys_919_, v_i_921_);
v_v_926_ = lean_array_fget_borrowed(v_vals_920_, v_i_921_);
lean_inc_ref_n(v_inst_917_, 2);
lean_inc_n(v_k_925_, 2);
v___x_927_ = lean_apply_1(v_inst_917_, v_k_925_);
v___x_928_ = lean_unbox_uint64(v___x_927_);
lean_dec_ref(v___x_927_);
v_h_929_ = lean_uint64_to_usize(v___x_928_);
v___x_930_ = ((size_t)5ULL);
v___x_931_ = lean_unsigned_to_nat(1u);
v___x_932_ = ((size_t)1ULL);
v___x_933_ = lean_usize_sub(v_depth_918_, v___x_932_);
v___x_934_ = lean_usize_mul(v___x_930_, v___x_933_);
v_h_935_ = lean_usize_shift_right(v_h_929_, v___x_934_);
v___x_936_ = lean_nat_add(v_i_921_, v___x_931_);
lean_dec(v_i_921_);
lean_inc(v_v_926_);
lean_inc_ref(v_inst_916_);
v___x_937_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_916_, v_inst_917_, v_entries_922_, v_h_935_, v_depth_918_, v_k_925_, v_v_926_);
v_i_921_ = v___x_936_;
v_entries_922_ = v___x_937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg___boxed(lean_object* v_inst_939_, lean_object* v_inst_940_, lean_object* v_depth_941_, lean_object* v_keys_942_, lean_object* v_vals_943_, lean_object* v_i_944_, lean_object* v_entries_945_){
_start:
{
size_t v_depth_boxed_946_; lean_object* v_res_947_; 
v_depth_boxed_946_ = lean_unbox_usize(v_depth_941_);
lean_dec(v_depth_941_);
v_res_947_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_939_, v_inst_940_, v_depth_boxed_946_, v_keys_942_, v_vals_943_, v_i_944_, v_entries_945_);
lean_dec_ref(v_vals_943_);
lean_dec_ref(v_keys_942_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___boxed(lean_object* v_inst_948_, lean_object* v_inst_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
size_t v_x_1067__boxed_955_; size_t v_x_1068__boxed_956_; lean_object* v_res_957_; 
v_x_1067__boxed_955_ = lean_unbox_usize(v_x_951_);
lean_dec(v_x_951_);
v_x_1068__boxed_956_ = lean_unbox_usize(v_x_952_);
lean_dec(v_x_952_);
v_res_957_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_948_, v_inst_949_, v_x_950_, v_x_1067__boxed_955_, v_x_1068__boxed_956_, v_x_953_, v_x_954_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_x_960_, lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
lean_object* v___x_963_; uint64_t v___x_964_; size_t v___x_965_; size_t v___x_966_; lean_object* v___x_967_; 
lean_inc_ref(v_inst_959_);
lean_inc(v_x_961_);
v___x_963_ = lean_apply_1(v_inst_959_, v_x_961_);
v___x_964_ = lean_unbox_uint64(v___x_963_);
lean_dec_ref(v___x_963_);
v___x_965_ = lean_uint64_to_usize(v___x_964_);
v___x_966_ = ((size_t)1ULL);
v___x_967_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_958_, v_inst_959_, v_x_960_, v___x_965_, v___x_966_, v_x_961_, v_x_962_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__2(lean_object* v_00_u03b1_968_, lean_object* v_00_u03b2_969_, lean_object* v_inst_970_, lean_object* v_inst_971_, lean_object* v_x_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_970_, v_inst_971_, v_x_972_, v___y_973_, v___y_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(lean_object* v_inst_976_, lean_object* v_inst_977_, lean_object* v_x_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_box(0);
v___x_981_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_976_, v_inst_977_, v_x_978_, v___y_979_, v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__5(lean_object* v_00_u03b1_982_, lean_object* v_inst_983_, lean_object* v_inst_984_, lean_object* v_x_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(v_inst_983_, v_inst_984_, v_x_985_, v___y_986_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_ShareCommon_persistentObjectFactory___closed__7(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_ShareCommon_persistentObjectFactory___closed__6));
v___x_1002_ = l_ShareCommon_StateFactory_mkImpl(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_ShareCommon_persistentObjectFactory(void){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_obj_once(&l_Lean_ShareCommon_persistentObjectFactory___closed__7, &l_Lean_ShareCommon_persistentObjectFactory___closed__7_once, _init_l_Lean_ShareCommon_persistentObjectFactory___closed__7);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(lean_object* v_inst_1004_, lean_object* v_inst_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_box(0), v_inst_1004_, v_inst_1005_, lean_box(0));
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg___boxed(lean_object* v_inst_1007_, lean_object* v_inst_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(v_inst_1007_, v_inst_1008_);
lean_dec_ref(v_inst_1008_);
lean_dec_ref(v_inst_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg(lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_x_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_1010_, v_inst_1011_, v_x_1012_, v___y_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg___boxed(lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_x_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg(v_inst_1015_, v_inst_1016_, v_x_1017_, v___y_1018_);
lean_dec_ref(v_x_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__2___redArg(lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_x_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_1020_, v_inst_1021_, v_x_1022_, v___y_1023_, v___y_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(lean_object* v_inst_1026_, lean_object* v_inst_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(lean_box(0), v_inst_1026_, v_inst_1027_, lean_box(0));
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg___boxed(lean_object* v_inst_1029_, lean_object* v_inst_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(v_inst_1029_, v_inst_1030_);
lean_dec_ref(v_inst_1030_);
lean_dec_ref(v_inst_1029_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(lean_object* v_00_u03b1_1032_, lean_object* v_inst_1033_, lean_object* v_inst_1034_, lean_object* v_00_u03b2_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_1033_, v_inst_1034_, v_x_1036_, v_x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___boxed(lean_object* v_00_u03b1_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_00_u03b2_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(v_00_u03b1_1039_, v_inst_1040_, v_inst_1041_, v_00_u03b2_1042_, v_x_1043_, v_x_1044_);
lean_dec_ref(v_x_1043_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4(lean_object* v_00_u03b1_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_1047_, v_inst_1048_, v_x_1050_, v_x_1051_, v_x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(lean_object* v_00_u03b1_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_00_u03b2_1057_, lean_object* v_x_1058_, lean_object* v_x_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_1055_, v_inst_1056_, v_x_1058_, v_x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___boxed(lean_object* v_00_u03b1_1061_, lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_00_u03b2_1064_, lean_object* v_x_1065_, lean_object* v_x_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(v_00_u03b1_1061_, v_inst_1062_, v_inst_1063_, v_00_u03b2_1064_, v_x_1065_, v_x_1066_);
lean_dec_ref(v_x_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(lean_object* v_00_u03b1_1068_, lean_object* v_inst_1069_, lean_object* v_00_u03b2_1070_, lean_object* v_x_1071_, size_t v_x_1072_, lean_object* v_x_1073_){
_start:
{
lean_object* v___x_1074_; 
lean_inc_ref(v_x_1071_);
v___x_1074_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_1069_, v_x_1071_, v_x_1072_, v_x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1075_, lean_object* v_inst_1076_, lean_object* v_00_u03b2_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
size_t v_x_1434__boxed_1081_; lean_object* v_res_1082_; 
v_x_1434__boxed_1081_ = lean_unbox_usize(v_x_1079_);
lean_dec(v_x_1079_);
v_res_1082_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(v_00_u03b1_1075_, v_inst_1076_, v_00_u03b2_1077_, v_x_1078_, v_x_1434__boxed_1081_, v_x_1080_);
lean_dec_ref(v_x_1078_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(lean_object* v_00_u03b1_1083_, lean_object* v_inst_1084_, lean_object* v_inst_1085_, lean_object* v_00_u03b2_1086_, lean_object* v_x_1087_, size_t v_x_1088_, size_t v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_1084_, v_inst_1085_, v_x_1087_, v_x_1088_, v_x_1089_, v_x_1090_, v_x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1093_, lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_00_u03b2_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
size_t v_x_1452__boxed_1102_; size_t v_x_1453__boxed_1103_; lean_object* v_res_1104_; 
v_x_1452__boxed_1102_ = lean_unbox_usize(v_x_1098_);
lean_dec(v_x_1098_);
v_x_1453__boxed_1103_ = lean_unbox_usize(v_x_1099_);
lean_dec(v_x_1099_);
v_res_1104_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(v_00_u03b1_1093_, v_inst_1094_, v_inst_1095_, v_00_u03b2_1096_, v_x_1097_, v_x_1452__boxed_1102_, v_x_1453__boxed_1103_, v_x_1100_, v_x_1101_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(lean_object* v_00_u03b1_1105_, lean_object* v_inst_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_x_1108_, size_t v_x_1109_, lean_object* v_x_1110_){
_start:
{
lean_object* v___x_1111_; 
lean_inc_ref(v_x_1108_);
v___x_1111_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_1106_, v_x_1108_, v_x_1109_, v_x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1112_, lean_object* v_inst_1113_, lean_object* v_00_u03b2_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
size_t v_x_1477__boxed_1118_; lean_object* v_res_1119_; 
v_x_1477__boxed_1118_ = lean_unbox_usize(v_x_1116_);
lean_dec(v_x_1116_);
v_res_1119_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(v_00_u03b1_1112_, v_inst_1113_, v_00_u03b2_1114_, v_x_1115_, v_x_1477__boxed_1118_, v_x_1117_);
lean_dec_ref(v_x_1115_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(lean_object* v_00_u03b1_1120_, lean_object* v_inst_1121_, lean_object* v_00_u03b2_1122_, lean_object* v_keys_1123_, lean_object* v_vals_1124_, lean_object* v_heq_1125_, lean_object* v_i_1126_, lean_object* v_k_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_1121_, v_keys_1123_, v_vals_1124_, v_i_1126_, v_k_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_inst_1130_, lean_object* v_00_u03b2_1131_, lean_object* v_keys_1132_, lean_object* v_vals_1133_, lean_object* v_heq_1134_, lean_object* v_i_1135_, lean_object* v_k_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(v_00_u03b1_1129_, v_inst_1130_, v_00_u03b2_1131_, v_keys_1132_, v_vals_1133_, v_heq_1134_, v_i_1135_, v_k_1136_);
lean_dec_ref(v_vals_1133_);
lean_dec_ref(v_keys_1132_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11(lean_object* v_00_u03b1_1138_, lean_object* v_inst_1139_, lean_object* v_00_u03b2_1140_, lean_object* v_n_1141_, lean_object* v_k_1142_, lean_object* v_v_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(v_inst_1139_, v_n_1141_, v_k_1142_, v_v_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(lean_object* v_00_u03b1_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_00_u03b2_1148_, size_t v_depth_1149_, lean_object* v_keys_1150_, lean_object* v_vals_1151_, lean_object* v_heq_1152_, lean_object* v_i_1153_, lean_object* v_entries_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_1146_, v_inst_1147_, v_depth_1149_, v_keys_1150_, v_vals_1151_, v_i_1153_, v_entries_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___boxed(lean_object* v_00_u03b1_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_00_u03b2_1159_, lean_object* v_depth_1160_, lean_object* v_keys_1161_, lean_object* v_vals_1162_, lean_object* v_heq_1163_, lean_object* v_i_1164_, lean_object* v_entries_1165_){
_start:
{
size_t v_depth_boxed_1166_; lean_object* v_res_1167_; 
v_depth_boxed_1166_ = lean_unbox_usize(v_depth_1160_);
lean_dec(v_depth_1160_);
v_res_1167_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(v_00_u03b1_1156_, v_inst_1157_, v_inst_1158_, v_00_u03b2_1159_, v_depth_boxed_1166_, v_keys_1161_, v_vals_1162_, v_heq_1163_, v_i_1164_, v_entries_1165_);
lean_dec_ref(v_vals_1162_);
lean_dec_ref(v_keys_1161_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(lean_object* v_00_u03b1_1168_, lean_object* v_inst_1169_, lean_object* v_00_u03b2_1170_, lean_object* v_keys_1171_, lean_object* v_vals_1172_, lean_object* v_heq_1173_, lean_object* v_i_1174_, lean_object* v_k_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_1169_, v_keys_1171_, v_vals_1172_, v_i_1174_, v_k_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___boxed(lean_object* v_00_u03b1_1177_, lean_object* v_inst_1178_, lean_object* v_00_u03b2_1179_, lean_object* v_keys_1180_, lean_object* v_vals_1181_, lean_object* v_heq_1182_, lean_object* v_i_1183_, lean_object* v_k_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(v_00_u03b1_1177_, v_inst_1178_, v_00_u03b2_1179_, v_keys_1180_, v_vals_1181_, v_heq_1182_, v_i_1183_, v_k_1184_);
lean_dec_ref(v_vals_1181_);
lean_dec_ref(v_keys_1180_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13(lean_object* v_00_u03b1_1186_, lean_object* v_inst_1187_, lean_object* v_00_u03b2_1188_, lean_object* v_x_1189_, lean_object* v_x_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(v_inst_1187_, v_x_1189_, v_x_1190_, v_x_1191_, v_x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(lean_object* v_inst_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_toApplicative_1197_; lean_object* v_toPure_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v_toApplicative_1197_ = lean_ctor_get(v_inst_1194_, 0);
lean_inc_ref(v_toApplicative_1197_);
lean_dec_ref(v_inst_1194_);
v_toPure_1198_ = lean_ctor_get(v_toApplicative_1197_, 1);
lean_inc(v_toPure_1198_);
lean_dec_ref(v_toApplicative_1197_);
v___x_1199_ = l_Lean_ShareCommon_objectFactory;
v___x_1200_ = lean_state_sharecommon(v___x_1199_, v_a_1196_, v_a_1195_);
v___x_1201_ = lean_apply_2(v_toPure_1198_, lean_box(0), v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon(lean_object* v_m_1202_, lean_object* v_00_u03b1_1203_, lean_object* v_inst_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(v_inst_1204_, v_a_1205_, v_a_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(lean_object* v_inst_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v_toApplicative_1211_; lean_object* v_toPure_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_toApplicative_1211_ = lean_ctor_get(v_inst_1208_, 0);
lean_inc_ref(v_toApplicative_1211_);
lean_dec_ref(v_inst_1208_);
v_toPure_1212_ = lean_ctor_get(v_toApplicative_1211_, 1);
lean_inc(v_toPure_1212_);
lean_dec_ref(v_toApplicative_1211_);
v___x_1213_ = l_Lean_ShareCommon_persistentObjectFactory;
v___x_1214_ = lean_state_sharecommon(v___x_1213_, v_a_1210_, v_a_1209_);
v___x_1215_ = lean_apply_2(v_toPure_1212_, lean_box(0), v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_withShareCommon(lean_object* v_m_1216_, lean_object* v_00_u03b1_1217_, lean_object* v_inst_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(v_inst_1218_, v_a_1219_, v_a_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0(lean_object* v_inst_1222_, lean_object* v_00_u03b1_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(v_inst_1222_, v___y_1224_, v___y_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg(lean_object* v_inst_1227_){
_start:
{
lean_object* v___f_1228_; 
v___f_1228_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1228_, 0, v_inst_1227_);
return v___f_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_monadShareCommon(lean_object* v_m_1229_, lean_object* v_inst_1230_){
_start:
{
lean_object* v___f_1231_; 
v___f_1231_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1231_, 0, v_inst_1230_);
return v___f_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0(lean_object* v_inst_1232_, lean_object* v_00_u03b1_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(v_inst_1232_, v___y_1234_, v___y_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg(lean_object* v_inst_1237_){
_start:
{
lean_object* v___f_1238_; 
v___f_1238_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1238_, 0, v_inst_1237_);
return v___f_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_monadShareCommon(lean_object* v_m_1239_, lean_object* v_inst_1240_){
_start:
{
lean_object* v___f_1241_; 
v___f_1241_ = lean_alloc_closure((void*)(l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1241_, 0, v_inst_1240_);
return v___f_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(lean_object* v_x_1242_){
_start:
{
lean_object* v_fst_1243_; 
v_fst_1243_ = lean_ctor_get(v_x_1242_, 0);
lean_inc(v_fst_1243_);
return v_fst_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0___boxed(lean_object* v_x_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(v_x_1244_);
lean_dec_ref(v_x_1244_);
return v_res_1245_;
}
}
static lean_object* _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = l_Lean_ShareCommon_objectFactory;
v___x_1248_ = l_ShareCommon_mkStateImpl(v___x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run___redArg(lean_object* v_inst_1249_, lean_object* v_x_1250_){
_start:
{
lean_object* v_toApplicative_1251_; lean_object* v_toFunctor_1252_; lean_object* v_map_1253_; lean_object* v___f_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_toApplicative_1251_ = lean_ctor_get(v_inst_1249_, 0);
lean_inc_ref(v_toApplicative_1251_);
lean_dec_ref(v_inst_1249_);
v_toFunctor_1252_ = lean_ctor_get(v_toApplicative_1251_, 0);
lean_inc_ref(v_toFunctor_1252_);
lean_dec_ref(v_toApplicative_1251_);
v_map_1253_ = lean_ctor_get(v_toFunctor_1252_, 0);
lean_inc(v_map_1253_);
lean_dec_ref(v_toFunctor_1252_);
v___f_1254_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1255_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1256_ = lean_apply_1(v_x_1250_, v___x_1255_);
v___x_1257_ = lean_apply_4(v_map_1253_, lean_box(0), lean_box(0), v___f_1254_, v___x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_run(lean_object* v_m_1258_, lean_object* v_00_u03b1_1259_, lean_object* v_inst_1260_, lean_object* v_x_1261_){
_start:
{
lean_object* v_toApplicative_1262_; lean_object* v_toFunctor_1263_; lean_object* v_map_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v_toApplicative_1262_ = lean_ctor_get(v_inst_1260_, 0);
lean_inc_ref(v_toApplicative_1262_);
lean_dec_ref(v_inst_1260_);
v_toFunctor_1263_ = lean_ctor_get(v_toApplicative_1262_, 0);
lean_inc_ref(v_toFunctor_1263_);
lean_dec_ref(v_toApplicative_1262_);
v_map_1264_ = lean_ctor_get(v_toFunctor_1263_, 0);
lean_inc(v_map_1264_);
lean_dec_ref(v_toFunctor_1263_);
v___f_1265_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1266_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1267_ = lean_apply_1(v_x_1261_, v___x_1266_);
v___x_1268_ = lean_apply_4(v_map_1264_, lean_box(0), lean_box(0), v___f_1265_, v___x_1267_);
return v___x_1268_;
}
}
static lean_object* _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = l_Lean_ShareCommon_persistentObjectFactory;
v___x_1270_ = l_ShareCommon_mkStateImpl(v___x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_run___redArg(lean_object* v_inst_1271_, lean_object* v_x_1272_){
_start:
{
lean_object* v_toApplicative_1273_; lean_object* v_toFunctor_1274_; lean_object* v_map_1275_; lean_object* v___f_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_toApplicative_1273_ = lean_ctor_get(v_inst_1271_, 0);
lean_inc_ref(v_toApplicative_1273_);
lean_dec_ref(v_inst_1271_);
v_toFunctor_1274_ = lean_ctor_get(v_toApplicative_1273_, 0);
lean_inc_ref(v_toFunctor_1274_);
lean_dec_ref(v_toApplicative_1273_);
v_map_1275_ = lean_ctor_get(v_toFunctor_1274_, 0);
lean_inc(v_map_1275_);
lean_dec_ref(v_toFunctor_1274_);
v___f_1276_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1277_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1278_ = lean_apply_1(v_x_1272_, v___x_1277_);
v___x_1279_ = lean_apply_4(v_map_1275_, lean_box(0), lean_box(0), v___f_1276_, v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonT_run(lean_object* v_m_1280_, lean_object* v_00_u03b1_1281_, lean_object* v_inst_1282_, lean_object* v_x_1283_){
_start:
{
lean_object* v_toApplicative_1284_; lean_object* v_toFunctor_1285_; lean_object* v_map_1286_; lean_object* v___f_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_toApplicative_1284_ = lean_ctor_get(v_inst_1282_, 0);
lean_inc_ref(v_toApplicative_1284_);
lean_dec_ref(v_inst_1282_);
v_toFunctor_1285_ = lean_ctor_get(v_toApplicative_1284_, 0);
lean_inc_ref(v_toFunctor_1285_);
lean_dec_ref(v_toApplicative_1284_);
v_map_1286_ = lean_ctor_get(v_toFunctor_1285_, 0);
lean_inc(v_map_1286_);
lean_dec_ref(v_toFunctor_1285_);
v___f_1287_ = ((lean_object*)(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0));
v___x_1288_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1289_ = lean_apply_1(v_x_1283_, v___x_1288_);
v___x_1290_ = lean_apply_4(v_map_1286_, lean_box(0), lean_box(0), v___f_1287_, v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonM_run___redArg(lean_object* v_a_1291_){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v_fst_1294_; 
v___x_1292_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1293_ = lean_apply_1(v_a_1291_, v___x_1292_);
v_fst_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_fst_1294_);
lean_dec_ref(v___x_1293_);
return v_fst_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonM_run(lean_object* v_00_u03b1_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v_fst_1299_; 
v___x_1297_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1298_ = lean_apply_1(v_a_1296_, v___x_1297_);
v_fst_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_fst_1299_);
lean_dec_ref(v___x_1298_);
return v_fst_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonM_run___redArg(lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v_fst_1303_; 
v___x_1301_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1302_ = lean_apply_1(v_a_1300_, v___x_1301_);
v_fst_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_fst_1303_);
lean_dec_ref(v___x_1302_);
return v_fst_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_PShareCommonM_run(lean_object* v_00_u03b1_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_fst_1308_; 
v___x_1306_ = lean_obj_once(&l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0, &l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once, _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0);
v___x_1307_ = lean_apply_1(v_a_1305_, v___x_1306_);
v_fst_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_fst_1308_);
lean_dec_ref(v___x_1307_);
return v_fst_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = l_Lean_ShareCommon_objectFactory;
v___x_1312_ = lean_state_sharecommon(v___x_1311_, v_a_1310_, v_a_1309_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0(lean_object* v_00_u03b1_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(v_a_1314_, v_a_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_shareCommon___redArg(lean_object* v_a_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v_fst_1320_; 
v___x_1318_ = lean_obj_once(&l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1, &l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once, _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1);
v___x_1319_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(v_a_1317_, v___x_1318_);
v_fst_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_fst_1320_);
lean_dec_ref(v___x_1319_);
return v_fst_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_ShareCommon_shareCommon(lean_object* v_00_u03b1_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_ShareCommon_shareCommon___redArg(v_a_1322_);
return v___x_1323_;
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
