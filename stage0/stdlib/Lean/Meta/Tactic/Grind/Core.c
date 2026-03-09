// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Core
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Inv import Lean.Meta.Tactic.Grind.PP import Lean.Meta.Tactic.Grind.Ctor import Lean.Meta.Tactic.Grind.Beta import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Internalize import Init.Omega
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_setENode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant___boxed(lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__2_value;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_instBEqCongrKey___private__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_instHashableCongrKey___private__1(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "parent"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3_value_aux_1),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(5, 81, 119, 21, 241, 124, 41, 97)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "remove: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__4_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getParents___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ParentSet_elems(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reinsert: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1;
lean_object* l_Lean_Meta_Grind_addCongrTable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__5_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__6_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8;
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_false_of_decide"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 157, 112, 124, 91, 52, 64, 56)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
extern lean_object* l_Lean_eagerReflBoolFalse;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "beta"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 64, 101, 181, 200, 140, 42, 219)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "curr: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3;
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_propagateBetaEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "parent: "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fn: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ", parents: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__3;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_propagateBeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "fns: "};
static const lean_object* l_Lean_Meta_Grind_propagateBeta___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBeta___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBeta___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBeta___closed__1;
static const lean_string_object l_Lean_Meta_Grind_propagateBeta___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", lams: "};
static const lean_object* l_Lean_Meta_Grind_propagateBeta___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBeta___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBeta___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBeta___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object**);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Inhabited"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(174, 152, 115, 107, 166, 56, 116, 8)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Subsingleton"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(23, 130, 42, 228, 248, 162, 23, 186)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_DelayedTheoremInstance_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isCongrRoot(lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " new root "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "adding "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↦ "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8;
lean_object* l_Lean_Meta_Grind_PendingSolverPropagations_propagate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_resetParentsOf___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_copyParentsTo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_ppENodeRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getFnRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getEqcLambdas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "after addEqStep, "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eqc"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 235, 244, 178, 10, 61, 92, 220)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " and "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = " are already in the same equivalence class"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7;
lean_object* l_Lean_Meta_Grind_checkInvariants(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_ppState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsInconsistent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1_value;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2_value),LEAN_SCALAR_PTR_LITERAL(157, 181, 250, 47, 64, 71, 92, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0_value;
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_st_ref_get(x_5);
lean_inc_ref(x_1);
x_12 = l_Lean_Meta_Grind_Goal_getENode(x_11, x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; uint8_t x_53; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 2);
x_17 = lean_ctor_get(x_13, 3);
x_18 = lean_ctor_get(x_13, 4);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get_uint8(x_13, sizeof(void*)*11);
x_21 = lean_ctor_get(x_13, 6);
x_22 = lean_ctor_get_uint8(x_13, sizeof(void*)*11 + 1);
x_23 = lean_ctor_get_uint8(x_13, sizeof(void*)*11 + 2);
x_24 = lean_ctor_get_uint8(x_13, sizeof(void*)*11 + 3);
x_25 = lean_ctor_get_uint8(x_13, sizeof(void*)*11 + 4);
x_26 = lean_ctor_get(x_13, 7);
x_27 = lean_ctor_get(x_13, 8);
x_28 = lean_ctor_get(x_13, 9);
x_29 = lean_ctor_get(x_13, 10);
x_30 = lean_ctor_get_uint8(x_13, sizeof(void*)*11 + 5);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
x_31 = x_13;
x_32 = x_53;
goto block_52;
}
else
{
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_31 = lean_box(0);
x_32 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_33; 
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_51; 
x_39 = lean_ctor_get(x_18, 0);
x_51 = !lean_is_exclusive(x_18);
if (x_51 == 0)
{
x_40 = x_18;
x_41 = x_51;
goto block_50;
}
else
{
lean_inc(x_39);
lean_dec(x_18);
x_40 = lean_box(0);
x_41 = x_51;
goto block_50;
}
block_50:
{
uint8_t x_42; 
if (x_20 == 0)
{
uint8_t x_48; 
x_48 = 1;
x_42 = x_48;
goto block_47;
}
else
{
uint8_t x_49; 
x_49 = 0;
x_42 = x_49;
goto block_47;
}
block_47:
{
lean_object* x_43; 
lean_inc_ref(x_1);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_1);
x_43 = x_40;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_1);
x_43 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_44; 
x_44 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(x_39, x_42, x_43, x_19, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_44) == 0)
{
lean_dec_ref(x_44);
x_33 = x_5;
goto block_38;
}
else
{
lean_del_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_44;
}
}
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_18);
x_33 = x_5;
goto block_38;
}
block_38:
{
lean_object* x_34; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 5, x_4);
lean_ctor_set(x_31, 4, x_3);
x_34 = x_31;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(x_37, 0, x_14);
lean_ctor_set(x_37, 1, x_15);
lean_ctor_set(x_37, 2, x_16);
lean_ctor_set(x_37, 3, x_17);
lean_ctor_set(x_37, 4, x_3);
lean_ctor_set(x_37, 5, x_4);
lean_ctor_set(x_37, 6, x_21);
lean_ctor_set(x_37, 7, x_26);
lean_ctor_set(x_37, 8, x_27);
lean_ctor_set(x_37, 9, x_28);
lean_ctor_set(x_37, 10, x_29);
lean_ctor_set_uint8(x_37, sizeof(void*)*11 + 1, x_22);
lean_ctor_set_uint8(x_37, sizeof(void*)*11 + 2, x_23);
lean_ctor_set_uint8(x_37, sizeof(void*)*11 + 3, x_24);
lean_ctor_set_uint8(x_37, sizeof(void*)*11 + 4, x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*11 + 5, x_30);
x_34 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_35; 
lean_ctor_set_uint8(x_34, sizeof(void*)*11, x_2);
x_35 = l_Lean_Meta_Grind_setENode___redArg(x_1, x_34, x_33);
return x_35;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_54 = lean_ctor_get(x_12, 0);
x_61 = !lean_is_exclusive(x_12);
if (x_61 == 0)
{
x_55 = x_12;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_12);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(x_1, x_2, x_3, x_4, x_5, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
x_17 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_box(0);
x_10 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(x_1, x_8, x_9, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isApp(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isArrow(x_1);
return x_3;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(x_1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2_spec__3(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__2));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
lean_inc_ref(x_3);
lean_inc(x_8);
lean_inc_ref(x_1);
x_9 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_8, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2_spec__6(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2_spec__6(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
x_9 = lean_usize_land(x_3, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_4, x_12);
if (x_13 == 0)
{
lean_dec(x_10);
return x_2;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_21; 
lean_inc_ref(x_5);
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_2, 0);
lean_dec(x_22);
x_14 = x_2;
x_15 = x_21;
goto block_20;
}
else
{
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_set(x_5, x_10, x_6);
lean_dec(x_10);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
case 1:
{
lean_object* x_23; uint8_t x_24; uint8_t x_56; 
lean_inc_ref(x_5);
x_56 = !lean_is_exclusive(x_2);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_2, 0);
lean_dec(x_57);
x_23 = x_2;
x_24 = x_56;
goto block_55;
}
else
{
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_54; 
x_25 = lean_ctor_get(x_11, 0);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
x_26 = x_11;
x_27 = x_54;
goto block_53;
}
else
{
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_box(0);
x_27 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_array_set(x_5, x_10, x_6);
x_29 = lean_usize_shift_right(x_3, x_7);
x_30 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(x_1, x_25, x_29, x_4);
lean_inc_ref(x_30);
x_31 = l_Lean_PersistentHashMap_isUnaryNode___redArg(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_30);
x_32 = x_26;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_30);
x_32 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_array_set(x_28, x_10, x_32);
lean_dec(x_10);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_33);
x_34 = x_23;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_52; 
lean_dec_ref(x_30);
lean_del_object(x_26);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec_ref(x_31);
x_40 = lean_ctor_get(x_39, 0);
x_41 = lean_ctor_get(x_39, 1);
x_52 = !lean_is_exclusive(x_39);
if (x_52 == 0)
{
x_42 = x_39;
x_43 = x_52;
goto block_51;
}
else
{
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_41);
x_44 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_array_set(x_28, x_10, x_44);
lean_dec(x_10);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_45);
x_46 = x_23;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
}
}
default: 
{
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_2;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_73; 
x_58 = lean_ctor_get(x_2, 0);
x_59 = lean_ctor_get(x_2, 1);
x_73 = !lean_is_exclusive(x_2);
if (x_73 == 0)
{
x_60 = x_2;
x_61 = x_73;
goto block_72;
}
else
{
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_2);
x_60 = lean_box(0);
x_61 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_62; 
x_62 = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2(x_1, x_58, x_4);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
if (x_61 == 0)
{
x_63 = x_60;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_58);
lean_ctor_set(x_65, 1, x_59);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
lean_dec_ref(x_62);
lean_inc(x_66);
x_67 = l_Array_eraseIdx___redArg(x_58, x_66);
x_68 = l_Array_eraseIdx___redArg(x_59, x_66);
if (x_61 == 0)
{
lean_ctor_set(x_60, 1, x_68);
lean_ctor_set(x_60, 0, x_67);
x_69 = x_60;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_68);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; lean_object* x_6; 
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_4 = l_Lean_Meta_Grind_instHashableCongrKey___private__1(x_1, x_3);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(x_1, x_2, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_88; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_88 = !lean_is_exclusive(x_1);
if (x_88 == 0)
{
x_17 = x_1;
x_18 = x_88;
goto block_87;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_19; lean_object* x_20; uint8_t x_61; uint8_t x_75; 
x_19 = lean_box(0);
x_75 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(x_15);
if (x_75 == 0)
{
x_61 = x_75;
goto block_74;
}
else
{
lean_object* x_76; 
lean_inc(x_15);
x_76 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_15, x_3, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
x_61 = x_78;
goto block_74;
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_79 = lean_ctor_get(x_76, 0);
x_86 = !lean_is_exclusive(x_76);
if (x_86 == 0)
{
x_80 = x_76;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
block_60:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_59; 
x_21 = lean_st_ref_take(x_20);
x_22 = lean_ctor_get(x_21, 0);
x_23 = lean_ctor_get(x_21, 1);
x_59 = !lean_is_exclusive(x_21);
if (x_59 == 0)
{
x_24 = x_21;
x_25 = x_59;
goto block_58;
}
else
{
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_57; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
x_28 = lean_ctor_get(x_22, 2);
x_29 = lean_ctor_get(x_22, 3);
x_30 = lean_ctor_get(x_22, 4);
x_31 = lean_ctor_get(x_22, 5);
x_32 = lean_ctor_get(x_22, 6);
x_33 = lean_ctor_get(x_22, 7);
x_34 = lean_ctor_get(x_22, 8);
x_35 = lean_ctor_get_uint8(x_22, sizeof(void*)*18);
x_36 = lean_ctor_get(x_22, 9);
x_37 = lean_ctor_get(x_22, 10);
x_38 = lean_ctor_get(x_22, 11);
x_39 = lean_ctor_get(x_22, 12);
x_40 = lean_ctor_get(x_22, 13);
x_41 = lean_ctor_get(x_22, 14);
x_42 = lean_ctor_get(x_22, 15);
x_43 = lean_ctor_get(x_22, 16);
x_44 = lean_ctor_get(x_22, 17);
x_57 = !lean_is_exclusive(x_22);
if (x_57 == 0)
{
x_45 = x_22;
x_46 = x_57;
goto block_56;
}
else
{
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_45 = lean_box(0);
x_46 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_47; lean_object* x_48; 
lean_inc_ref(x_28);
x_47 = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(x_28, x_31, x_15);
if (x_46 == 0)
{
lean_ctor_set(x_45, 5, x_47);
x_48 = x_45;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_55, 0, x_26);
lean_ctor_set(x_55, 1, x_27);
lean_ctor_set(x_55, 2, x_28);
lean_ctor_set(x_55, 3, x_29);
lean_ctor_set(x_55, 4, x_30);
lean_ctor_set(x_55, 5, x_47);
lean_ctor_set(x_55, 6, x_32);
lean_ctor_set(x_55, 7, x_33);
lean_ctor_set(x_55, 8, x_34);
lean_ctor_set(x_55, 9, x_36);
lean_ctor_set(x_55, 10, x_37);
lean_ctor_set(x_55, 11, x_38);
lean_ctor_set(x_55, 12, x_39);
lean_ctor_set(x_55, 13, x_40);
lean_ctor_set(x_55, 14, x_41);
lean_ctor_set(x_55, 15, x_42);
lean_ctor_set(x_55, 16, x_43);
lean_ctor_set(x_55, 17, x_44);
lean_ctor_set_uint8(x_55, sizeof(void*)*18, x_35);
x_48 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_49; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_48);
x_49 = x_24;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_23);
x_49 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_50; 
x_50 = lean_st_ref_set(x_20, x_49);
x_1 = x_16;
x_2 = x_19;
goto _start;
}
}
}
}
}
block_74:
{
if (x_61 == 0)
{
lean_del_object(x_17);
lean_dec(x_15);
x_1 = x_16;
x_2 = x_19;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3));
x_64 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(x_63, x_11);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_del_object(x_17);
x_20 = x_3;
goto block_60;
}
else
{
lean_object* x_67; 
x_67 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_67);
x_68 = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__5);
lean_inc(x_15);
x_69 = l_Lean_MessageData_ofExpr(x_15);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_69);
lean_ctor_set(x_17, 0, x_68);
x_70 = x_17;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_69);
x_70 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_71; 
x_71 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(x_63, x_70, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_71) == 0)
{
lean_dec_ref(x_71);
x_20 = x_3;
goto block_60;
}
else
{
lean_dec(x_16);
lean_dec(x_15);
return x_71;
}
}
}
else
{
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_15);
return x_67;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_getParents___redArg(x_1, x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Meta_Grind_ParentSet_elems(x_14);
x_16 = lean_box(0);
x_17 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg(x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_18 = x_17;
x_19 = x_24;
goto block_23;
}
else
{
lean_dec(x_17);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_14);
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_14);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_14);
x_26 = lean_ctor_get(x_17, 0);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
x_27 = x_17;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_60; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_60 = !lean_is_exclusive(x_1);
if (x_60 == 0)
{
x_17 = x_1;
x_18 = x_60;
goto block_59;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_33; uint8_t x_47; 
x_19 = lean_box(0);
x_47 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(x_15);
if (x_47 == 0)
{
x_33 = x_47;
goto block_46;
}
else
{
lean_object* x_48; 
lean_inc(x_15);
x_48 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_15, x_3, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
x_33 = x_50;
goto block_46;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_51 = lean_ctor_get(x_48, 0);
x_58 = !lean_is_exclusive(x_48);
if (x_58 == 0)
{
x_52 = x_48;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
block_32:
{
lean_object* x_30; 
x_30 = l_Lean_Meta_Grind_addCongrTable(x_15, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_dec_ref(x_30);
x_1 = x_16;
x_2 = x_19;
goto _start;
}
else
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_30;
}
}
block_46:
{
if (x_33 == 0)
{
lean_del_object(x_17);
lean_dec(x_15);
x_1 = x_16;
x_2 = x_19;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3));
x_36 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(x_35, x_11);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_del_object(x_17);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_20 = x_3;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_11;
x_29 = x_12;
goto block_32;
}
else
{
lean_object* x_39; 
x_39 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_39);
x_40 = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(x_15);
x_41 = l_Lean_MessageData_ofExpr(x_15);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_41);
lean_ctor_set(x_17, 0, x_40);
x_42 = x_17;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
x_42 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_43; 
x_43 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(x_35, x_42, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_43) == 0)
{
lean_dec_ref(x_43);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_20 = x_3;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_11;
x_29 = x_12;
goto block_32;
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_43;
}
}
}
else
{
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_39;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Meta_Grind_ParentSet_elems(x_1);
x_14 = lean_box(0);
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_16 = x_15;
x_17 = x_22;
goto block_21;
}
else
{
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_14);
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_14);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqMVarId_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqMVarId_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableMVarId_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 7);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(x_6, x_1);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3));
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_68; 
x_12 = lean_st_ref_get(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(x_13, x_8);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
x_68 = !lean_is_exclusive(x_14);
if (x_68 == 0)
{
x_16 = x_14;
x_17 = x_68;
goto block_67;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_68;
goto block_67;
}
block_67:
{
uint8_t x_18; 
x_18 = lean_unbox(x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_del_object(x_16);
x_19 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Lean_Meta_Grind_mkEqFalseProof(x_20, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_5);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_5);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
x_28 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8);
x_29 = l_Lean_mkApp4(x_27, x_24, x_26, x_22, x_28);
x_30 = l_Lean_Meta_Grind_closeGoal(x_29, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_25, 0);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
x_32 = x_25;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_22);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_ctor_get(x_23, 0);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
x_40 = x_23;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_23);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_21, 0);
x_54 = !lean_is_exclusive(x_21);
if (x_54 == 0)
{
x_48 = x_21;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_21);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_19, 0);
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
x_56 = x_19;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_19);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_63);
x_64 = x_16;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_63);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(x_1, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_14 = l_Lean_Meta_mkEq(x_1, x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_grind_mk_eq_proof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_15);
x_18 = l_Lean_Meta_mkDecide(x_15, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
x_23 = l_Lean_Expr_appArg_x21(x_19);
lean_dec(x_19);
x_24 = l_Lean_eagerReflBoolFalse;
lean_inc(x_15);
x_25 = l_Lean_mkApp3(x_22, x_15, x_23, x_24);
x_26 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
x_27 = l_Lean_mkApp4(x_26, x_15, x_21, x_25, x_17);
x_28 = l_Lean_Meta_Grind_closeGoal(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_ctor_get(x_20, 0);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
x_30 = x_20;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = lean_ctor_get(x_18, 0);
x_44 = !lean_is_exclusive(x_18);
if (x_44 == 0)
{
x_38 = x_18;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_18);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = lean_ctor_get(x_16, 0);
x_52 = !lean_is_exclusive(x_16);
if (x_52 == 0)
{
x_46 = x_16;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_16);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = lean_ctor_get(x_14, 0);
x_60 = !lean_is_exclusive(x_14);
if (x_60 == 0)
{
x_54 = x_14;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_14);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec_ref(x_2);
x_18 = lean_st_ref_get(x_4);
lean_inc(x_16);
x_19 = l_Lean_Meta_Grind_Goal_getENode(x_18, x_16, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; uint8_t x_50; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 0);
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 2);
x_24 = lean_ctor_get(x_20, 3);
x_25 = lean_ctor_get(x_20, 4);
x_26 = lean_ctor_get(x_20, 5);
x_27 = lean_ctor_get_uint8(x_20, sizeof(void*)*11);
x_28 = lean_ctor_get(x_20, 6);
x_29 = lean_ctor_get_uint8(x_20, sizeof(void*)*11 + 1);
x_30 = lean_ctor_get_uint8(x_20, sizeof(void*)*11 + 2);
x_31 = lean_ctor_get_uint8(x_20, sizeof(void*)*11 + 3);
x_32 = lean_ctor_get_uint8(x_20, sizeof(void*)*11 + 4);
x_33 = lean_ctor_get(x_20, 7);
x_34 = lean_ctor_get(x_20, 8);
x_35 = lean_ctor_get(x_20, 9);
x_36 = lean_ctor_get(x_20, 10);
x_37 = lean_ctor_get_uint8(x_20, sizeof(void*)*11 + 5);
x_50 = !lean_is_exclusive(x_20);
if (x_50 == 0)
{
x_38 = x_20;
x_39 = x_50;
goto block_49;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_20);
x_38 = lean_box(0);
x_39 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_box(0);
x_41 = lean_nat_dec_lt(x_35, x_1);
lean_dec(x_35);
if (x_41 == 0)
{
lean_del_object(x_38);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
x_2 = x_17;
x_3 = x_40;
goto _start;
}
else
{
lean_object* x_43; 
lean_inc(x_1);
if (x_39 == 0)
{
lean_ctor_set(x_38, 9, x_1);
x_43 = x_38;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_22);
lean_ctor_set(x_48, 2, x_23);
lean_ctor_set(x_48, 3, x_24);
lean_ctor_set(x_48, 4, x_25);
lean_ctor_set(x_48, 5, x_26);
lean_ctor_set(x_48, 6, x_28);
lean_ctor_set(x_48, 7, x_33);
lean_ctor_set(x_48, 8, x_34);
lean_ctor_set(x_48, 9, x_1);
lean_ctor_set(x_48, 10, x_36);
lean_ctor_set_uint8(x_48, sizeof(void*)*11, x_27);
lean_ctor_set_uint8(x_48, sizeof(void*)*11 + 1, x_29);
lean_ctor_set_uint8(x_48, sizeof(void*)*11 + 2, x_30);
lean_ctor_set_uint8(x_48, sizeof(void*)*11 + 3, x_31);
lean_ctor_set_uint8(x_48, sizeof(void*)*11 + 4, x_32);
lean_ctor_set_uint8(x_48, sizeof(void*)*11 + 5, x_37);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
lean_inc(x_16);
x_44 = l_Lean_Meta_Grind_setENode___redArg(x_16, x_43, x_4);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec_ref(x_44);
x_45 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_16);
if (lean_obj_tag(x_45) == 0)
{
lean_dec_ref(x_45);
x_2 = x_17;
x_3 = x_40;
goto _start;
}
else
{
lean_dec(x_17);
lean_dec(x_1);
return x_45;
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
return x_44;
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
x_51 = lean_ctor_get(x_19, 0);
x_58 = !lean_is_exclusive(x_19);
if (x_58 == 0)
{
x_52 = x_19;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_19);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_st_ref_get(x_2);
x_14 = l_Lean_Meta_Grind_getParents___redArg(x_1, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 13);
lean_inc_ref(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lean_Meta_Grind_ParentSet_elems(x_17);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(x_18, x_19, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_21, 0);
lean_dec(x_29);
x_22 = x_21;
x_23 = x_28;
goto block_27;
}
else
{
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_20);
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_20);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
else
{
return x_21;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_13);
x_30 = lean_ctor_get(x_14, 0);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
x_31 = x_14;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(x_1, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_MessageData_ofExpr(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_56; lean_object* x_57; 
x_56 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
x_57 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(x_56, x_13);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_120; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_ctor_get(x_4, 0);
x_60 = lean_ctor_get(x_4, 1);
x_120 = !lean_is_exclusive(x_4);
if (x_120 == 0)
{
x_61 = x_4;
x_62 = x_120;
goto block_119;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_4);
x_61 = lean_box(0);
x_62 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_95; 
x_95 = lean_unbox(x_58);
lean_dec(x_58);
if (x_95 == 0)
{
lean_del_object(x_61);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_63 = x_5;
x_64 = x_6;
x_65 = x_7;
x_66 = x_8;
x_67 = x_9;
x_68 = x_10;
x_69 = x_11;
x_70 = x_12;
x_71 = x_13;
x_72 = x_14;
goto block_94;
}
else
{
lean_object* x_96; 
x_96 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec_ref(x_96);
x_97 = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3);
lean_inc(x_60);
x_98 = l_Lean_MessageData_ofExpr(x_60);
if (x_62 == 0)
{
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_98);
lean_ctor_set(x_61, 0, x_97);
x_99 = x_61;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_97);
lean_ctor_set(x_110, 1, x_98);
x_99 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_100; 
x_100 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(x_56, x_99, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_100) == 0)
{
lean_dec_ref(x_100);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_63 = x_5;
x_64 = x_6;
x_65 = x_7;
x_66 = x_8;
x_67 = x_9;
x_68 = x_10;
x_69 = x_11;
x_70 = x_12;
x_71 = x_13;
x_72 = x_14;
goto block_94;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_108; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_101 = lean_ctor_get(x_100, 0);
x_108 = !lean_is_exclusive(x_100);
if (x_108 == 0)
{
x_102 = x_100;
x_103 = x_108;
goto block_107;
}
else
{
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_box(0);
x_103 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_104; 
if (x_103 == 0)
{
x_104 = x_102;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_118; 
lean_del_object(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_111 = lean_ctor_get(x_96, 0);
x_118 = !lean_is_exclusive(x_96);
if (x_118 == 0)
{
x_112 = x_96;
x_113 = x_118;
goto block_117;
}
else
{
lean_inc(x_111);
lean_dec(x_96);
x_112 = lean_box(0);
x_113 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
}
block_94:
{
lean_object* x_73; 
x_73 = l_Lean_Meta_Grind_isEqv___redArg(x_60, x_2, x_63);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
x_16 = x_59;
x_17 = x_60;
x_18 = x_63;
x_19 = x_64;
x_20 = x_65;
x_21 = x_66;
x_22 = x_67;
x_23 = x_68;
x_24 = x_69;
x_25 = x_70;
x_26 = x_71;
x_27 = x_72;
goto block_55;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_inc(x_59);
x_76 = l_Array_reverse___redArg(x_59);
lean_inc(x_72);
lean_inc_ref(x_71);
lean_inc(x_70);
lean_inc_ref(x_69);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_60);
x_77 = l_Lean_Meta_Grind_propagateBetaEqs(x_3, x_60, x_76, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70, x_71, x_72);
if (lean_obj_tag(x_77) == 0)
{
lean_dec_ref(x_77);
x_16 = x_59;
x_17 = x_60;
x_18 = x_63;
x_19 = x_64;
x_20 = x_65;
x_21 = x_66;
x_22 = x_67;
x_23 = x_68;
x_24 = x_69;
x_25 = x_70;
x_26 = x_71;
x_27 = x_72;
goto block_55;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_78 = lean_ctor_get(x_77, 0);
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
x_79 = x_77;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_93; 
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_86 = lean_ctor_get(x_73, 0);
x_93 = !lean_is_exclusive(x_73);
if (x_93 == 0)
{
x_87 = x_73;
x_88 = x_93;
goto block_92;
}
else
{
lean_inc(x_86);
lean_dec(x_73);
x_87 = lean_box(0);
x_88 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_89; 
if (x_88 == 0)
{
x_89 = x_87;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_86);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_128; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_121 = lean_ctor_get(x_57, 0);
x_128 = !lean_is_exclusive(x_57);
if (x_128 == 0)
{
x_122 = x_57;
x_123 = x_128;
goto block_127;
}
else
{
lean_inc(x_121);
lean_dec(x_57);
x_122 = lean_box(0);
x_123 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_124; 
if (x_123 == 0)
{
x_124 = x_122;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_121);
x_124 = x_126;
goto block_125;
}
block_125:
{
return x_124;
}
}
}
block_55:
{
if (lean_obj_tag(x_17) == 5)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_29);
x_30 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_18);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_box(0);
x_33 = lean_grind_internalize(x_17, x_31, x_32, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_33);
x_34 = lean_array_push(x_16, x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_28);
x_4 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_37 = lean_ctor_get(x_33, 0);
x_44 = !lean_is_exclusive(x_33);
if (x_44 == 0)
{
x_38 = x_33;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_17);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_45 = lean_ctor_get(x_30, 0);
x_52 = !lean_is_exclusive(x_30);
if (x_52 == 0)
{
x_46 = x_30;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_30);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_16);
lean_ctor_set(x_53, 1, x_17);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_16;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_59; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
x_59 = !lean_is_exclusive(x_3);
if (x_59 == 0)
{
x_19 = x_3;
x_20 = x_59;
goto block_58;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = lean_box(0);
x_20 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_51; uint8_t x_52; 
x_21 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
x_22 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(x_21, x_13);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_box(0);
x_51 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__0));
x_52 = lean_unbox(x_23);
lean_dec(x_23);
if (x_52 == 0)
{
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_25 = x_51;
x_26 = x_17;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_13;
x_36 = x_14;
goto block_50;
}
else
{
lean_object* x_53; 
x_53 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_53);
x_54 = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__2);
lean_inc(x_17);
x_55 = l_Lean_MessageData_ofExpr(x_17);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(x_21, x_56, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_57) == 0)
{
lean_dec_ref(x_57);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_25 = x_51;
x_26 = x_17;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_13;
x_36 = x_14;
goto block_50;
}
else
{
lean_del_object(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_57;
}
}
else
{
lean_del_object(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_53;
}
}
block_50:
{
lean_object* x_37; 
if (x_20 == 0)
{
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 1, x_26);
lean_ctor_set(x_19, 0, x_25);
x_37 = x_19;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_25);
lean_ctor_set(x_49, 1, x_26);
x_37 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_38; 
x_38 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(x_17, x_1, x_2, x_37, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
lean_dec(x_17);
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_38);
x_3 = x_18;
x_4 = x_24;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_40 = lean_ctor_get(x_38, 0);
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
x_41 = x_38;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_16;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_5, x_4);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
x_21 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(x_20, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_51; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_box(0);
x_24 = lean_array_uget_borrowed(x_3, x_5);
x_51 = lean_unbox(x_22);
lean_dec(x_22);
if (x_51 == 0)
{
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
x_28 = x_10;
x_29 = x_11;
x_30 = x_12;
x_31 = x_13;
x_32 = x_14;
x_33 = x_15;
x_34 = x_16;
goto block_50;
}
else
{
lean_object* x_52; 
x_52 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
lean_dec_ref(x_52);
x_53 = l_Lean_Meta_Grind_getParents___redArg(x_24, x_7);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__1);
lean_inc(x_24);
x_56 = l_Lean_MessageData_ofExpr(x_24);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__3);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Meta_Grind_ParentSet_elems(x_54);
lean_dec(x_54);
x_61 = lean_box(0);
x_62 = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(x_60, x_61);
x_63 = l_Lean_MessageData_ofList(x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(x_20, x_64, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_65) == 0)
{
lean_dec_ref(x_65);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
x_28 = x_10;
x_29 = x_11;
x_30 = x_12;
x_31 = x_13;
x_32 = x_14;
x_33 = x_15;
x_34 = x_16;
goto block_50;
}
else
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_73; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_66 = lean_ctor_get(x_53, 0);
x_73 = !lean_is_exclusive(x_53);
if (x_73 == 0)
{
x_67 = x_53;
x_68 = x_73;
goto block_72;
}
else
{
lean_inc(x_66);
lean_dec(x_53);
x_67 = lean_box(0);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
if (x_68 == 0)
{
x_69 = x_67;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_66);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
else
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_52;
}
}
block_50:
{
lean_object* x_35; 
x_35 = l_Lean_Meta_Grind_getParents___redArg(x_24, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_Meta_Grind_ParentSet_elems(x_36);
lean_dec(x_36);
x_38 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(x_1, x_2, x_37, x_23, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_38) == 0)
{
size_t x_39; size_t x_40; 
lean_dec_ref(x_38);
x_39 = 1;
x_40 = lean_usize_add(x_5, x_39);
x_5 = x_40;
x_6 = x_23;
goto _start;
}
else
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_38;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_42 = lean_ctor_get(x_35, 0);
x_49 = !lean_is_exclusive(x_35);
if (x_49 == 0)
{
x_43 = x_35;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_74 = lean_ctor_get(x_21, 0);
x_81 = !lean_is_exclusive(x_21);
if (x_81 == 0)
{
x_75 = x_21;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_21);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_20;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_st_ref_get(x_3);
x_18 = l_Lean_instInhabitedExpr;
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_14, x_19);
x_21 = lean_array_get_borrowed(x_18, x_1, x_20);
lean_dec(x_20);
lean_inc(x_21);
x_22 = l_Lean_Meta_Grind_Goal_getRoot(x_17, x_21, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_47 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
x_48 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(x_47, x_11);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_12;
goto block_46;
}
else
{
lean_object* x_51; 
x_51 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_51);
x_52 = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(x_2);
x_53 = lean_array_to_list(x_2);
x_54 = lean_box(0);
x_55 = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(x_53, x_54);
x_56 = l_Lean_MessageData_ofList(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_inc_ref(x_1);
x_60 = lean_array_to_list(x_1);
x_61 = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(x_60, x_54);
x_62 = l_Lean_MessageData_ofList(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(x_47, x_63, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_12;
goto block_46;
}
else
{
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_64;
}
}
else
{
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_51;
}
}
block_46:
{
lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; 
x_34 = lean_box(0);
x_35 = lean_array_size(x_2);
x_36 = 0;
x_37 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(x_23, x_1, x_2, x_35, x_36, x_34, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_dec(x_23);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; uint8_t x_44; 
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
x_38 = x_37;
x_39 = x_44;
goto block_43;
}
else
{
lean_dec(x_37);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_34);
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_34);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
else
{
return x_37;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = lean_ctor_get(x_22, 0);
x_72 = !lean_is_exclusive(x_22);
if (x_72 == 0)
{
x_66 = x_22;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_22);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_propagateBeta(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(x_1, x_2, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_5);
x_12 = lean_box(0);
x_13 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
x_14 = lean_array_uget_borrowed(x_2, x_4);
if (lean_obj_tag(x_14) == 6)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 1);
x_16 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_1, x_15);
if (x_16 == 0)
{
x_6 = x_13;
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
}
else
{
x_6 = x_13;
goto block_10;
}
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_4, x_7);
x_4 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_box(0);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
x_5 = lean_array_size(x_1);
x_6 = 0;
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(x_2, x_1, x_5, x_6, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_8) == 0)
{
return x_3;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_5, x_4);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_6);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = lean_array_uget_borrowed(x_3, x_5);
if (lean_obj_tag(x_26) == 6)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
x_28 = lean_ctor_get(x_26, 2);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_27);
x_29 = l_Lean_Meta_getLevel(x_27, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
lean_inc_ref(x_33);
x_34 = l_Lean_mkConst(x_31, x_33);
lean_inc_ref(x_27);
x_35 = l_Lean_Expr_app___override(x_34, x_27);
x_36 = lean_box(0);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_37 = l_Lean_Meta_synthInstance_x3f(x_35, x_36, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_105; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_unsigned_to_nat(0u);
x_105 = l_Lean_Expr_hasLooseBVars(x_28);
if (x_105 == 0)
{
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_41 = x_7;
x_42 = x_8;
x_43 = x_9;
x_44 = x_10;
x_45 = x_11;
x_46 = x_12;
x_47 = x_13;
x_48 = x_14;
x_49 = x_15;
x_50 = x_16;
goto block_104;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(x_33);
x_107 = l_Lean_mkConst(x_106, x_33);
lean_inc_ref(x_27);
x_108 = l_Lean_Expr_app___override(x_107, x_27);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_109 = l_Lean_Meta_synthInstance_x3f(x_108, x_36, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_dec(x_39);
lean_dec_ref(x_33);
x_18 = x_25;
goto block_22;
}
else
{
lean_dec_ref(x_110);
if (x_105 == 0)
{
lean_dec(x_39);
lean_dec_ref(x_33);
x_18 = x_25;
goto block_22;
}
else
{
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_41 = x_7;
x_42 = x_8;
x_43 = x_9;
x_44 = x_10;
x_45 = x_11;
x_46 = x_12;
x_47 = x_13;
x_48 = x_14;
x_49 = x_15;
x_50 = x_16;
goto block_104;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_118; 
lean_dec(x_39);
lean_dec_ref(x_33);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_111 = lean_ctor_get(x_109, 0);
x_118 = !lean_is_exclusive(x_109);
if (x_118 == 0)
{
x_112 = x_109;
x_113 = x_118;
goto block_117;
}
else
{
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_box(0);
x_113 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
}
block_104:
{
lean_object* x_51; 
x_51 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(x_1, x_27);
if (lean_obj_tag(x_51) == 1)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
if (lean_obj_tag(x_52) == 6)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_52, 2);
lean_inc_ref(x_54);
lean_dec_ref(x_52);
x_55 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
x_56 = l_Lean_mkConst(x_55, x_33);
x_57 = l_Lean_mkAppB(x_56, x_53, x_39);
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc(x_41);
x_58 = l_Lean_Meta_Grind_preprocessLight(x_57, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_array_fget_borrowed(x_2, x_40);
x_61 = lean_array_fget_borrowed(x_1, x_40);
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_61);
lean_inc(x_60);
x_62 = lean_grind_mk_eq_proof(x_60, x_61, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_expr_instantiate1(x_28, x_59);
x_65 = lean_expr_instantiate1(x_54, x_59);
lean_dec_ref(x_54);
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc(x_48);
lean_inc_ref(x_47);
x_66 = l_Lean_Meta_mkCongrFun(x_63, x_59, x_47, x_48, x_49, x_50);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc(x_48);
lean_inc_ref(x_47);
x_68 = l_Lean_Meta_mkEq(x_64, x_65, x_47, x_48, x_49, x_50);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = l_Lean_Meta_mkExpectedPropHint(x_67, x_69);
x_71 = l_Lean_Meta_Grind_pushNewFact(x_70, x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50);
if (lean_obj_tag(x_71) == 0)
{
lean_dec_ref(x_71);
x_18 = x_25;
goto block_22;
}
else
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec(x_67);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_72 = lean_ctor_get(x_68, 0);
x_79 = !lean_is_exclusive(x_68);
if (x_79 == 0)
{
x_73 = x_68;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_68);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_87; 
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_80 = lean_ctor_get(x_66, 0);
x_87 = !lean_is_exclusive(x_66);
if (x_87 == 0)
{
x_81 = x_66;
x_82 = x_87;
goto block_86;
}
else
{
lean_inc(x_80);
lean_dec(x_66);
x_81 = lean_box(0);
x_82 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_83; 
if (x_82 == 0)
{
x_83 = x_81;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_80);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_95; 
lean_dec(x_59);
lean_dec_ref(x_54);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_88 = lean_ctor_get(x_62, 0);
x_95 = !lean_is_exclusive(x_62);
if (x_95 == 0)
{
x_89 = x_62;
x_90 = x_95;
goto block_94;
}
else
{
lean_inc(x_88);
lean_dec(x_62);
x_89 = lean_box(0);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_90 == 0)
{
x_91 = x_89;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_88);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_103; 
lean_dec_ref(x_54);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_96 = lean_ctor_get(x_58, 0);
x_103 = !lean_is_exclusive(x_58);
if (x_103 == 0)
{
x_97 = x_58;
x_98 = x_103;
goto block_102;
}
else
{
lean_inc(x_96);
lean_dec(x_58);
x_97 = lean_box(0);
x_98 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_99; 
if (x_98 == 0)
{
x_99 = x_97;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_96);
x_99 = x_101;
goto block_100;
}
block_100:
{
return x_99;
}
}
}
}
else
{
lean_dec(x_52);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_39);
lean_dec_ref(x_33);
x_18 = x_25;
goto block_22;
}
}
else
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_39);
lean_dec_ref(x_33);
x_18 = x_25;
goto block_22;
}
}
}
else
{
lean_dec(x_38);
lean_dec_ref(x_33);
x_18 = x_25;
goto block_22;
}
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_126; 
lean_dec_ref(x_33);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_119 = lean_ctor_get(x_37, 0);
x_126 = !lean_is_exclusive(x_37);
if (x_126 == 0)
{
x_120 = x_37;
x_121 = x_126;
goto block_125;
}
else
{
lean_inc(x_119);
lean_dec(x_37);
x_120 = lean_box(0);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_121 == 0)
{
x_122 = x_120;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_119);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_134; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_127 = lean_ctor_get(x_29, 0);
x_134 = !lean_is_exclusive(x_29);
if (x_134 == 0)
{
x_128 = x_29;
x_129 = x_134;
goto block_133;
}
else
{
lean_inc(x_127);
lean_dec(x_29);
x_128 = lean_box(0);
x_129 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_130; 
if (x_129 == 0)
{
x_130 = x_128;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_127);
x_130 = x_132;
goto block_131;
}
block_131:
{
return x_130;
}
}
}
}
else
{
x_18 = x_25;
goto block_22;
}
}
block_22:
{
size_t x_19; size_t x_20; 
x_19 = 1;
x_20 = lean_usize_add(x_5, x_19);
x_5 = x_20;
x_6 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_2);
x_18 = lean_nat_dec_eq(x_17, x_15);
if (x_18 == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_19 = lean_box(0);
x_20 = lean_array_size(x_1);
x_21 = 0;
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(x_2, x_1, x_1, x_20, x_21, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; uint8_t x_29; 
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_22, 0);
lean_dec(x_30);
x_23 = x_22;
x_24 = x_29;
goto block_28;
}
else
{
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_19);
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_19);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
return x_22;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_PersistentHashMap_Node_isEmpty___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_PersistentHashMap_Node_isEmpty___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget_borrowed(x_1, x_3);
x_8 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_7, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_9);
return x_1;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_20; 
lean_inc_ref(x_4);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 0);
lean_dec(x_21);
x_13 = x_1;
x_14 = x_20;
goto block_19;
}
else
{
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_set(x_4, x_9, x_5);
lean_dec(x_9);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
case 1:
{
lean_object* x_22; uint8_t x_23; uint8_t x_55; 
lean_inc_ref(x_4);
x_55 = !lean_is_exclusive(x_1);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_1, 0);
lean_dec(x_56);
x_22 = x_1;
x_23 = x_55;
goto block_54;
}
else
{
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_53; 
x_24 = lean_ctor_get(x_10, 0);
x_53 = !lean_is_exclusive(x_10);
if (x_53 == 0)
{
x_25 = x_10;
x_26 = x_53;
goto block_52;
}
else
{
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_box(0);
x_26 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_array_set(x_4, x_9, x_5);
x_28 = lean_usize_shift_right(x_2, x_6);
x_29 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(x_24, x_28, x_3);
lean_inc_ref(x_29);
x_30 = l_Lean_PersistentHashMap_isUnaryNode___redArg(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_29);
x_31 = x_25;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_29);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_array_set(x_27, x_9, x_31);
lean_dec(x_9);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_32);
x_33 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_51; 
lean_dec_ref(x_29);
lean_del_object(x_25);
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
lean_dec_ref(x_30);
x_39 = lean_ctor_get(x_38, 0);
x_40 = lean_ctor_get(x_38, 1);
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
x_41 = x_38;
x_42 = x_51;
goto block_50;
}
else
{
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_38);
x_41 = lean_box(0);
x_42 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_40);
x_43 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_array_set(x_27, x_9, x_43);
lean_dec(x_9);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_44);
x_45 = x_22;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
}
}
default: 
{
lean_dec(x_9);
return x_1;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_72; 
x_57 = lean_ctor_get(x_1, 0);
x_58 = lean_ctor_get(x_1, 1);
x_72 = !lean_is_exclusive(x_1);
if (x_72 == 0)
{
x_59 = x_1;
x_60 = x_72;
goto block_71;
}
else
{
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_61; 
x_61 = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(x_57, x_3);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
if (x_60 == 0)
{
x_62 = x_59;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_58);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
lean_dec_ref(x_61);
lean_inc(x_65);
x_66 = l_Array_eraseIdx___redArg(x_57, x_65);
x_67 = l_Array_eraseIdx___redArg(x_58, x_65);
if (x_60 == 0)
{
lean_ctor_set(x_59, 1, x_67);
lean_ctor_set(x_59, 0, x_66);
x_68 = x_59;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec_ref(x_1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Meta_Grind_DelayedTheoremInstance_check(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_17);
x_1 = x_16;
goto _start;
}
else
{
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_25; 
x_4 = lean_ctor_get(x_1, 0);
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
x_5 = x_1;
x_6 = x_25;
goto block_24;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_box(2);
x_8 = 5;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get(x_7, x_4, x_11);
lean_dec(x_11);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_del_object(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_14);
x_17 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
case 1:
{
lean_object* x_20; size_t x_21; 
lean_del_object(x_5);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec_ref(x_12);
x_21 = lean_usize_shift_right(x_2, x_8);
x_1 = x_20;
x_2 = x_21;
goto _start;
}
default: 
{
lean_object* x_23; 
lean_del_object(x_5);
x_23 = lean_box(0);
return x_23;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(x_26, x_27, x_28, x_3);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_st_ref_get(x_3);
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 13);
lean_inc_ref(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 10);
lean_inc_ref(x_20);
lean_dec_ref(x_19);
x_21 = lean_box(0);
x_22 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(x_20, x_15);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_82; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_st_ref_take(x_3);
x_25 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_25, 13);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_24, 1);
x_82 = !lean_is_exclusive(x_24);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_24, 0);
lean_dec(x_83);
x_28 = x_24;
x_29 = x_82;
goto block_81;
}
else
{
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_79; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
x_32 = lean_ctor_get(x_25, 2);
x_33 = lean_ctor_get(x_25, 3);
x_34 = lean_ctor_get(x_25, 4);
x_35 = lean_ctor_get(x_25, 5);
x_36 = lean_ctor_get(x_25, 6);
x_37 = lean_ctor_get(x_25, 7);
x_38 = lean_ctor_get(x_25, 8);
x_39 = lean_ctor_get_uint8(x_25, sizeof(void*)*18);
x_40 = lean_ctor_get(x_25, 9);
x_41 = lean_ctor_get(x_25, 10);
x_42 = lean_ctor_get(x_25, 11);
x_43 = lean_ctor_get(x_25, 12);
x_44 = lean_ctor_get(x_25, 14);
x_45 = lean_ctor_get(x_25, 15);
x_46 = lean_ctor_get(x_25, 16);
x_47 = lean_ctor_get(x_25, 17);
x_79 = !lean_is_exclusive(x_25);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_25, 13);
lean_dec(x_80);
x_48 = x_25;
x_49 = x_79;
goto block_78;
}
else
{
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_48 = lean_box(0);
x_49 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_77; 
x_50 = lean_ctor_get(x_26, 0);
x_51 = lean_ctor_get(x_26, 1);
x_52 = lean_ctor_get(x_26, 2);
x_53 = lean_ctor_get(x_26, 3);
x_54 = lean_ctor_get(x_26, 4);
x_55 = lean_ctor_get(x_26, 5);
x_56 = lean_ctor_get(x_26, 6);
x_57 = lean_ctor_get(x_26, 7);
x_58 = lean_ctor_get(x_26, 8);
x_59 = lean_ctor_get(x_26, 9);
x_60 = lean_ctor_get(x_26, 10);
x_77 = !lean_is_exclusive(x_26);
if (x_77 == 0)
{
x_61 = x_26;
x_62 = x_77;
goto block_76;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_26);
x_61 = lean_box(0);
x_62 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(x_60, x_15);
if (x_62 == 0)
{
lean_ctor_set(x_61, 10, x_63);
x_64 = x_61;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_75, 0, x_50);
lean_ctor_set(x_75, 1, x_51);
lean_ctor_set(x_75, 2, x_52);
lean_ctor_set(x_75, 3, x_53);
lean_ctor_set(x_75, 4, x_54);
lean_ctor_set(x_75, 5, x_55);
lean_ctor_set(x_75, 6, x_56);
lean_ctor_set(x_75, 7, x_57);
lean_ctor_set(x_75, 8, x_58);
lean_ctor_set(x_75, 9, x_59);
lean_ctor_set(x_75, 10, x_63);
x_64 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_65; 
if (x_49 == 0)
{
lean_ctor_set(x_48, 13, x_64);
x_65 = x_48;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_73, 0, x_30);
lean_ctor_set(x_73, 1, x_31);
lean_ctor_set(x_73, 2, x_32);
lean_ctor_set(x_73, 3, x_33);
lean_ctor_set(x_73, 4, x_34);
lean_ctor_set(x_73, 5, x_35);
lean_ctor_set(x_73, 6, x_36);
lean_ctor_set(x_73, 7, x_37);
lean_ctor_set(x_73, 8, x_38);
lean_ctor_set(x_73, 9, x_40);
lean_ctor_set(x_73, 10, x_41);
lean_ctor_set(x_73, 11, x_42);
lean_ctor_set(x_73, 12, x_43);
lean_ctor_set(x_73, 13, x_64);
lean_ctor_set(x_73, 14, x_44);
lean_ctor_set(x_73, 15, x_45);
lean_ctor_set(x_73, 16, x_46);
lean_ctor_set(x_73, 17, x_47);
lean_ctor_set_uint8(x_73, sizeof(void*)*18, x_39);
x_65 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_66; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_65);
x_66 = x_28;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_27);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_st_ref_set(x_3, x_66);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_68 = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_68) == 0)
{
lean_dec_ref(x_68);
x_1 = x_16;
x_2 = x_21;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_68;
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
lean_dec(x_22);
x_1 = x_16;
x_2 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_isInconsistent___redArg(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_42; 
x_14 = lean_ctor_get(x_13, 0);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
x_15 = x_13;
x_16 = x_42;
goto block_41;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_42;
goto block_41;
}
block_41:
{
uint8_t x_17; 
x_17 = lean_unbox(x_14);
lean_dec(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_st_ref_get(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 13);
lean_inc_ref(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 10);
lean_inc_ref(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_PersistentHashMap_Node_isEmpty___redArg(x_21);
lean_dec_ref(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_del_object(x_15);
x_23 = lean_box(0);
x_24 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(x_1, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_25 = x_24;
x_26 = x_31;
goto block_30;
}
else
{
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_23);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_23);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
return x_24;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_33);
x_34 = x_15;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_box(0);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_37);
x_38 = x_15;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_ctor_get(x_13, 0);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
x_44 = x_13;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_13);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget_borrowed(x_2, x_4);
lean_inc(x_9);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_10 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_14 = lean_array_fget_borrowed(x_3, x_4);
lean_dec(x_4);
lean_inc(x_14);
lean_inc(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_33; 
x_5 = lean_ctor_get(x_2, 0);
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
x_6 = x_2;
x_7 = x_33;
goto block_32;
}
else
{
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_box(2);
x_9 = 5;
x_10 = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
x_11 = lean_usize_land(x_3, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get(x_8, x_5, x_12);
lean_dec(x_12);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_27; 
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
x_16 = x_13;
x_17 = x_27;
goto block_26;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_27;
goto block_26;
}
block_26:
{
uint8_t x_18; 
lean_inc(x_14);
x_18 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_4, x_14);
if (x_18 == 0)
{
lean_object* x_19; 
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_del_object(x_6);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; 
if (x_17 == 0)
{
x_20 = x_16;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_15);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_20);
x_21 = x_6;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
case 1:
{
lean_object* x_28; size_t x_29; 
lean_del_object(x_6);
x_28 = lean_ctor_get(x_13, 0);
lean_inc(x_28);
lean_dec_ref(x_13);
x_29 = lean_usize_shift_right(x_3, x_9);
x_2 = x_28;
x_3 = x_29;
goto _start;
}
default: 
{
lean_object* x_31; 
lean_del_object(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_31 = lean_box(0);
return x_31;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_35);
lean_dec_ref(x_2);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(x_1, x_34, x_35, x_36, x_4);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; lean_object* x_6; 
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_4 = l_Lean_Meta_Grind_instHashableCongrKey___private__1(x_1, x_3);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(x_1, x_2, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_31; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
x_8 = x_2;
x_9 = x_31;
goto block_30;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_6);
x_11 = lean_nat_dec_lt(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_12 = lean_array_push(x_6, x_4);
x_13 = lean_array_push(x_7, x_5);
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_13);
lean_ctor_set(x_8, 0, x_12);
x_14 = x_8;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget_borrowed(x_6, x_3);
lean_inc(x_17);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_18 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_4, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
if (x_9 == 0)
{
x_19 = x_8;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_7);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_2 = x_19;
x_3 = x_21;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_1);
x_25 = lean_array_fset(x_6, x_3, x_4);
x_26 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_26);
lean_ctor_set(x_8, 0, x_25);
x_27 = x_8;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = 5;
x_9 = 1;
x_10 = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
x_11 = lean_usize_land(x_3, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_15; uint8_t x_16; uint8_t x_51; 
lean_inc_ref(x_7);
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_2, 0);
lean_dec(x_52);
x_15 = x_2;
x_16 = x_51;
goto block_50;
}
else
{
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_fget(x_7, x_12);
x_18 = lean_box(0);
x_19 = lean_array_fset(x_7, x_12, x_18);
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_37; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
x_28 = x_17;
x_29 = x_37;
goto block_36;
}
else
{
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_box(0);
x_29 = x_37;
goto block_36;
}
block_36:
{
uint8_t x_30; 
lean_inc(x_26);
lean_inc_ref(x_5);
x_30 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_5, x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_del_object(x_28);
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_26, x_27, x_5, x_6);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_20 = x_32;
goto block_25;
}
else
{
lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
if (x_29 == 0)
{
lean_ctor_set(x_28, 1, x_6);
lean_ctor_set(x_28, 0, x_5);
x_33 = x_28;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_6);
x_33 = x_35;
goto block_34;
}
block_34:
{
x_20 = x_33;
goto block_25;
}
}
}
}
case 1:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_48; 
x_38 = lean_ctor_get(x_17, 0);
x_48 = !lean_is_exclusive(x_17);
if (x_48 == 0)
{
x_39 = x_17;
x_40 = x_48;
goto block_47;
}
else
{
lean_inc(x_38);
lean_dec(x_17);
x_39 = lean_box(0);
x_40 = x_48;
goto block_47;
}
block_47:
{
size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_usize_shift_right(x_3, x_8);
x_42 = lean_usize_add(x_4, x_9);
x_43 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(x_1, x_38, x_41, x_42, x_5, x_6);
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_43);
x_44 = x_39;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
x_20 = x_44;
goto block_25;
}
}
}
default: 
{
lean_object* x_49; 
lean_dec_ref(x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_6);
x_20 = x_49;
goto block_25;
}
}
block_25:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_array_fset(x_19, x_12, x_20);
lean_dec(x_12);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_21);
x_22 = x_15;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_74; 
x_53 = lean_ctor_get(x_2, 0);
x_54 = lean_ctor_get(x_2, 1);
x_74 = !lean_is_exclusive(x_2);
if (x_74 == 0)
{
x_55 = x_2;
x_56 = x_74;
goto block_73;
}
else
{
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_2);
x_55 = lean_box(0);
x_56 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_53);
lean_ctor_set(x_72, 1, x_54);
x_57 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_58; uint8_t x_59; size_t x_66; uint8_t x_67; 
lean_inc_ref(x_1);
x_58 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(x_1, x_57, x_5, x_6);
x_66 = 7;
x_67 = lean_usize_dec_le(x_66, x_4);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_58);
x_69 = lean_unsigned_to_nat(4u);
x_70 = lean_nat_dec_lt(x_68, x_69);
lean_dec(x_68);
x_59 = x_70;
goto block_65;
}
else
{
x_59 = x_67;
goto block_65;
}
block_65:
{
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_61);
lean_dec_ref(x_58);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
x_64 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(x_1, x_4, x_60, x_61, x_62, x_63);
lean_dec_ref(x_61);
lean_dec_ref(x_60);
return x_64;
}
else
{
lean_dec_ref(x_1);
return x_58;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_5, x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_1);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; lean_object* x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget_borrowed(x_3, x_5);
x_10 = lean_array_fget_borrowed(x_4, x_5);
lean_inc(x_9);
lean_inc_ref(x_1);
x_11 = l_Lean_Meta_Grind_instHashableCongrKey___private__1(x_1, x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 5;
x_14 = lean_unsigned_to_nat(1u);
x_15 = 1;
x_16 = lean_usize_sub(x_2, x_15);
x_17 = lean_usize_mul(x_13, x_16);
x_18 = lean_usize_shift_right(x_12, x_17);
x_19 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_1);
x_20 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(x_1, x_6, x_18, x_2, x_9, x_10);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_5 = l_Lean_Meta_Grind_instHashableCongrKey___private__1(x_1, x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = 1;
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(x_1, x_2, x_6, x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_179; 
x_12 = lean_st_ref_get(x_5);
x_13 = lean_ctor_get(x_4, 1);
x_179 = !lean_is_exclusive(x_4);
if (x_179 == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_4, 0);
lean_dec(x_180);
x_14 = x_4;
x_15 = x_179;
goto block_178;
}
else
{
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = x_179;
goto block_178;
}
block_178:
{
lean_object* x_16; 
lean_inc(x_13);
x_16 = l_Lean_Meta_Grind_Goal_getENode(x_12, x_13, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_169; 
x_17 = lean_ctor_get(x_16, 0);
x_169 = !lean_is_exclusive(x_16);
if (x_169 == 0)
{
x_18 = x_16;
x_19 = x_169;
goto block_168;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; uint8_t x_166; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 3);
x_23 = lean_ctor_get(x_17, 4);
x_24 = lean_ctor_get(x_17, 5);
x_25 = lean_ctor_get_uint8(x_17, sizeof(void*)*11);
x_26 = lean_ctor_get(x_17, 6);
x_27 = lean_ctor_get_uint8(x_17, sizeof(void*)*11 + 1);
x_28 = lean_ctor_get_uint8(x_17, sizeof(void*)*11 + 2);
x_29 = lean_ctor_get_uint8(x_17, sizeof(void*)*11 + 3);
x_30 = lean_ctor_get_uint8(x_17, sizeof(void*)*11 + 4);
x_31 = lean_ctor_get(x_17, 7);
x_32 = lean_ctor_get(x_17, 8);
x_33 = lean_ctor_get(x_17, 9);
x_34 = lean_ctor_get(x_17, 10);
x_35 = lean_ctor_get_uint8(x_17, sizeof(void*)*11 + 5);
x_166 = !lean_is_exclusive(x_17);
if (x_166 == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_17, 2);
lean_dec(x_167);
x_36 = x_17;
x_37 = x_166;
goto block_165;
}
else
{
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
x_36 = lean_box(0);
x_37 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_38; lean_object* x_52; lean_object* x_62; 
x_38 = lean_box(0);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc_ref(x_2);
lean_inc_ref(x_21);
lean_inc_ref(x_20);
if (x_37 == 0)
{
lean_ctor_set(x_36, 2, x_2);
x_62 = x_36;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(x_164, 0, x_20);
lean_ctor_set(x_164, 1, x_21);
lean_ctor_set(x_164, 2, x_2);
lean_ctor_set(x_164, 3, x_22);
lean_ctor_set(x_164, 4, x_23);
lean_ctor_set(x_164, 5, x_24);
lean_ctor_set(x_164, 6, x_26);
lean_ctor_set(x_164, 7, x_31);
lean_ctor_set(x_164, 8, x_32);
lean_ctor_set(x_164, 9, x_33);
lean_ctor_set(x_164, 10, x_34);
lean_ctor_set_uint8(x_164, sizeof(void*)*11, x_25);
lean_ctor_set_uint8(x_164, sizeof(void*)*11 + 1, x_27);
lean_ctor_set_uint8(x_164, sizeof(void*)*11 + 2, x_28);
lean_ctor_set_uint8(x_164, sizeof(void*)*11 + 3, x_29);
lean_ctor_set_uint8(x_164, sizeof(void*)*11 + 4, x_30);
lean_ctor_set_uint8(x_164, sizeof(void*)*11 + 5, x_35);
x_62 = x_164;
goto block_163;
}
block_51:
{
uint8_t x_39; 
x_39 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_21, x_1);
if (x_39 == 0)
{
lean_object* x_40; 
lean_del_object(x_18);
lean_dec(x_13);
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_21);
lean_ctor_set(x_14, 0, x_38);
x_40 = x_14;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_21);
x_40 = x_43;
goto block_42;
}
block_42:
{
x_4 = x_40;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_21);
lean_dec_ref(x_2);
x_44 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_44);
x_45 = x_14;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_13);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_45);
x_46 = x_18;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
block_61:
{
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_52);
goto block_51;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec_ref(x_21);
lean_del_object(x_18);
lean_del_object(x_14);
lean_dec(x_13);
lean_dec_ref(x_2);
x_53 = lean_ctor_get(x_52, 0);
x_60 = !lean_is_exclusive(x_52);
if (x_60 == 0)
{
x_54 = x_52;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
block_163:
{
lean_object* x_63; 
lean_inc_ref(x_62);
lean_inc_ref(x_20);
x_63 = l_Lean_Meta_Grind_setENode___redArg(x_20, x_62, x_5);
if (lean_obj_tag(x_63) == 0)
{
lean_dec_ref(x_63);
if (x_3 == 0)
{
lean_dec_ref(x_62);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_20);
goto block_51;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
x_65 = lean_unsigned_to_nat(3u);
x_66 = l_Lean_Expr_isAppOfArity(x_20, x_64, x_65);
if (x_66 == 0)
{
lean_dec_ref(x_62);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_20);
goto block_51;
}
else
{
uint8_t x_67; 
x_67 = l_Lean_Meta_Grind_ENode_isCongrRoot(x_62);
lean_dec_ref(x_62);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_st_ref_get(x_5);
x_69 = lean_ctor_get(x_68, 0);
lean_inc_ref(x_69);
lean_dec(x_68);
x_70 = lean_ctor_get(x_69, 2);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_69, 5);
lean_inc_ref(x_71);
lean_dec_ref(x_69);
lean_inc_ref(x_20);
x_72 = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(x_70, x_71, x_20);
if (lean_obj_tag(x_72) == 0)
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_20);
goto block_51;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_74, x_6);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_154; 
x_78 = lean_st_ref_take(x_5);
x_79 = lean_ctor_get(x_78, 0);
x_80 = lean_ctor_get(x_78, 1);
x_154 = !lean_is_exclusive(x_78);
if (x_154 == 0)
{
x_81 = x_78;
x_82 = x_154;
goto block_153;
}
else
{
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_78);
x_81 = lean_box(0);
x_82 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_152; 
x_83 = lean_ctor_get(x_79, 0);
x_84 = lean_ctor_get(x_79, 1);
x_85 = lean_ctor_get(x_79, 2);
x_86 = lean_ctor_get(x_79, 3);
x_87 = lean_ctor_get(x_79, 4);
x_88 = lean_ctor_get(x_79, 5);
x_89 = lean_ctor_get(x_79, 6);
x_90 = lean_ctor_get(x_79, 7);
x_91 = lean_ctor_get(x_79, 8);
x_92 = lean_ctor_get_uint8(x_79, sizeof(void*)*18);
x_93 = lean_ctor_get(x_79, 9);
x_94 = lean_ctor_get(x_79, 10);
x_95 = lean_ctor_get(x_79, 11);
x_96 = lean_ctor_get(x_79, 12);
x_97 = lean_ctor_get(x_79, 13);
x_98 = lean_ctor_get(x_79, 14);
x_99 = lean_ctor_get(x_79, 15);
x_100 = lean_ctor_get(x_79, 16);
x_101 = lean_ctor_get(x_79, 17);
x_152 = !lean_is_exclusive(x_79);
if (x_152 == 0)
{
x_102 = x_79;
x_103 = x_152;
goto block_151;
}
else
{
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_79);
x_102 = lean_box(0);
x_103 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_box(0);
lean_inc_ref(x_20);
lean_inc_ref(x_85);
x_105 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(x_85, x_88, x_20, x_104);
if (x_103 == 0)
{
lean_ctor_set(x_102, 5, x_105);
x_106 = x_102;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_150, 0, x_83);
lean_ctor_set(x_150, 1, x_84);
lean_ctor_set(x_150, 2, x_85);
lean_ctor_set(x_150, 3, x_86);
lean_ctor_set(x_150, 4, x_87);
lean_ctor_set(x_150, 5, x_105);
lean_ctor_set(x_150, 6, x_89);
lean_ctor_set(x_150, 7, x_90);
lean_ctor_set(x_150, 8, x_91);
lean_ctor_set(x_150, 9, x_93);
lean_ctor_set(x_150, 10, x_94);
lean_ctor_set(x_150, 11, x_95);
lean_ctor_set(x_150, 12, x_96);
lean_ctor_set(x_150, 13, x_97);
lean_ctor_set(x_150, 14, x_98);
lean_ctor_set(x_150, 15, x_99);
lean_ctor_set(x_150, 16, x_100);
lean_ctor_set(x_150, 17, x_101);
lean_ctor_set_uint8(x_150, sizeof(void*)*18, x_92);
x_106 = x_150;
goto block_149;
}
block_149:
{
lean_object* x_107; 
if (x_82 == 0)
{
lean_ctor_set(x_81, 0, x_106);
x_107 = x_81;
goto block_147;
}
else
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_106);
lean_ctor_set(x_148, 1, x_80);
x_107 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_st_ref_set(x_5, x_107);
lean_inc_ref(x_2);
lean_inc_ref(x_21);
lean_inc_ref_n(x_20, 2);
x_109 = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(x_109, 0, x_20);
lean_ctor_set(x_109, 1, x_21);
lean_ctor_set(x_109, 2, x_2);
lean_ctor_set(x_109, 3, x_20);
lean_ctor_set(x_109, 4, x_23);
lean_ctor_set(x_109, 5, x_24);
lean_ctor_set(x_109, 6, x_26);
lean_ctor_set(x_109, 7, x_31);
lean_ctor_set(x_109, 8, x_32);
lean_ctor_set(x_109, 9, x_33);
lean_ctor_set(x_109, 10, x_34);
lean_ctor_set_uint8(x_109, sizeof(void*)*11, x_25);
lean_ctor_set_uint8(x_109, sizeof(void*)*11 + 1, x_27);
lean_ctor_set_uint8(x_109, sizeof(void*)*11 + 2, x_28);
lean_ctor_set_uint8(x_109, sizeof(void*)*11 + 3, x_29);
lean_ctor_set_uint8(x_109, sizeof(void*)*11 + 4, x_30);
lean_ctor_set_uint8(x_109, sizeof(void*)*11 + 5, x_35);
lean_inc_ref(x_20);
x_110 = l_Lean_Meta_Grind_setENode___redArg(x_20, x_109, x_5);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_110);
x_111 = lean_st_ref_get(x_5);
lean_inc(x_74);
x_112 = l_Lean_Meta_Grind_Goal_getENode(x_111, x_74, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; uint8_t x_131; uint8_t x_137; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = lean_ctor_get(x_113, 0);
x_115 = lean_ctor_get(x_113, 1);
x_116 = lean_ctor_get(x_113, 2);
x_117 = lean_ctor_get(x_113, 4);
x_118 = lean_ctor_get(x_113, 5);
x_119 = lean_ctor_get_uint8(x_113, sizeof(void*)*11);
x_120 = lean_ctor_get(x_113, 6);
x_121 = lean_ctor_get_uint8(x_113, sizeof(void*)*11 + 1);
x_122 = lean_ctor_get_uint8(x_113, sizeof(void*)*11 + 2);
x_123 = lean_ctor_get_uint8(x_113, sizeof(void*)*11 + 3);
x_124 = lean_ctor_get_uint8(x_113, sizeof(void*)*11 + 4);
x_125 = lean_ctor_get(x_113, 7);
x_126 = lean_ctor_get(x_113, 8);
x_127 = lean_ctor_get(x_113, 9);
x_128 = lean_ctor_get(x_113, 10);
x_129 = lean_ctor_get_uint8(x_113, sizeof(void*)*11 + 5);
x_137 = !lean_is_exclusive(x_113);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_113, 3);
lean_dec(x_138);
x_130 = x_113;
x_131 = x_137;
goto block_136;
}
else
{
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_120);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_113);
x_130 = lean_box(0);
x_131 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_132; 
if (x_131 == 0)
{
lean_ctor_set(x_130, 3, x_20);
x_132 = x_130;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(x_135, 0, x_114);
lean_ctor_set(x_135, 1, x_115);
lean_ctor_set(x_135, 2, x_116);
lean_ctor_set(x_135, 3, x_20);
lean_ctor_set(x_135, 4, x_117);
lean_ctor_set(x_135, 5, x_118);
lean_ctor_set(x_135, 6, x_120);
lean_ctor_set(x_135, 7, x_125);
lean_ctor_set(x_135, 8, x_126);
lean_ctor_set(x_135, 9, x_127);
lean_ctor_set(x_135, 10, x_128);
lean_ctor_set_uint8(x_135, sizeof(void*)*11, x_119);
lean_ctor_set_uint8(x_135, sizeof(void*)*11 + 1, x_121);
lean_ctor_set_uint8(x_135, sizeof(void*)*11 + 2, x_122);
lean_ctor_set_uint8(x_135, sizeof(void*)*11 + 3, x_123);
lean_ctor_set_uint8(x_135, sizeof(void*)*11 + 4, x_124);
lean_ctor_set_uint8(x_135, sizeof(void*)*11 + 5, x_129);
x_132 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_133; 
x_133 = l_Lean_Meta_Grind_setENode___redArg(x_74, x_132, x_5);
x_52 = x_133;
goto block_61;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_146; 
lean_dec(x_74);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_del_object(x_18);
lean_del_object(x_14);
lean_dec(x_13);
lean_dec_ref(x_2);
x_139 = lean_ctor_get(x_112, 0);
x_146 = !lean_is_exclusive(x_112);
if (x_146 == 0)
{
x_140 = x_112;
x_141 = x_146;
goto block_145;
}
else
{
lean_inc(x_139);
lean_dec(x_112);
x_140 = lean_box(0);
x_141 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_142; 
if (x_141 == 0)
{
x_142 = x_140;
goto block_143;
}
else
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_139);
x_142 = x_144;
goto block_143;
}
block_143:
{
return x_142;
}
}
}
}
else
{
lean_dec(x_74);
lean_dec_ref(x_20);
x_52 = x_110;
goto block_61;
}
}
}
}
}
}
else
{
lean_dec(x_74);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_20);
goto block_51;
}
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_162; 
lean_dec(x_74);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_del_object(x_18);
lean_del_object(x_14);
lean_dec(x_13);
lean_dec_ref(x_2);
x_155 = lean_ctor_get(x_75, 0);
x_162 = !lean_is_exclusive(x_75);
if (x_162 == 0)
{
x_156 = x_75;
x_157 = x_162;
goto block_161;
}
else
{
lean_inc(x_155);
lean_dec(x_75);
x_156 = lean_box(0);
x_157 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_158; 
if (x_157 == 0)
{
x_158 = x_156;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_155);
x_158 = x_160;
goto block_159;
}
block_159:
{
return x_158;
}
}
}
}
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_20);
goto block_51;
}
}
}
}
else
{
lean_dec_ref(x_62);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_20);
x_52 = x_63;
goto block_61;
}
}
}
}
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_177; 
lean_del_object(x_14);
lean_dec(x_13);
lean_dec_ref(x_2);
x_170 = lean_ctor_get(x_16, 0);
x_177 = !lean_is_exclusive(x_16);
if (x_177 == 0)
{
x_171 = x_16;
x_172 = x_177;
goto block_176;
}
else
{
lean_inc(x_170);
lean_dec(x_16);
x_171 = lean_box(0);
x_172 = x_177;
goto block_176;
}
block_176:
{
lean_object* x_173; 
if (x_172 == 0)
{
x_173 = x_171;
goto block_174;
}
else
{
lean_object* x_175; 
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_170);
x_173 = x_175;
goto block_174;
}
block_174:
{
return x_173;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_2, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_box(0);
lean_inc_ref(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
x_18 = lean_unbox(x_15);
lean_dec(x_15);
x_19 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(x_1, x_2, x_18, x_17, x_3, x_7, x_9, x_10, x_11, x_12);
lean_dec_ref(x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_33; 
x_20 = lean_ctor_get(x_19, 0);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
x_21 = x_19;
x_22 = x_33;
goto block_32;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_24);
x_25 = x_21;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec_ref(x_23);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_28);
x_29 = x_21;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
x_34 = lean_ctor_get(x_19, 0);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
x_35 = x_19;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_42 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_43 = x_14;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_14);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
x_17 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(x_1, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(x_1, x_3, x_4, x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec_ref(x_1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_Grind_propagateUp(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
x_18 = lean_box(0);
x_1 = x_16;
x_2 = x_18;
goto _start;
}
else
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec_ref(x_1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_Grind_propagateDown(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
x_18 = lean_box(0);
x_1 = x_16;
x_2 = x_18;
goto _start;
}
else
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_172; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_451; lean_object* x_452; uint8_t x_453; 
x_255 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
x_451 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(x_255, x_18);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
lean_dec_ref(x_451);
x_453 = lean_unbox(x_452);
lean_dec(x_452);
if (x_453 == 0)
{
x_371 = x_10;
x_372 = x_11;
x_373 = x_12;
x_374 = x_13;
x_375 = x_14;
x_376 = x_15;
x_377 = x_16;
x_378 = x_17;
x_379 = x_18;
x_380 = x_19;
goto block_450;
}
else
{
lean_object* x_454; 
x_454 = l_Lean_Meta_Grind_updateLastTag(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; 
lean_dec_ref(x_454);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_3);
x_455 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_3, x_10, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
lean_dec_ref(x_455);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_4);
x_457 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_4, x_10, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
lean_dec_ref(x_457);
x_459 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6);
x_460 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_456);
x_461 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8);
x_462 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_461);
x_463 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_458);
x_464 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(x_255, x_463, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_464) == 0)
{
lean_dec_ref(x_464);
x_371 = x_10;
x_372 = x_11;
x_373 = x_12;
x_374 = x_13;
x_375 = x_14;
x_376 = x_15;
x_377 = x_16;
x_378 = x_17;
x_379 = x_18;
x_380 = x_19;
goto block_450;
}
else
{
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_464;
}
}
else
{
lean_object* x_465; lean_object* x_466; uint8_t x_467; uint8_t x_472; 
lean_dec(x_456);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_465 = lean_ctor_get(x_457, 0);
x_472 = !lean_is_exclusive(x_457);
if (x_472 == 0)
{
x_466 = x_457;
x_467 = x_472;
goto block_471;
}
else
{
lean_inc(x_465);
lean_dec(x_457);
x_466 = lean_box(0);
x_467 = x_472;
goto block_471;
}
block_471:
{
lean_object* x_468; 
if (x_467 == 0)
{
x_468 = x_466;
goto block_469;
}
else
{
lean_object* x_470; 
x_470 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_470, 0, x_465);
x_468 = x_470;
goto block_469;
}
block_469:
{
return x_468;
}
}
}
}
else
{
lean_object* x_473; lean_object* x_474; uint8_t x_475; uint8_t x_480; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_473 = lean_ctor_get(x_455, 0);
x_480 = !lean_is_exclusive(x_455);
if (x_480 == 0)
{
x_474 = x_455;
x_475 = x_480;
goto block_479;
}
else
{
lean_inc(x_473);
lean_dec(x_455);
x_474 = lean_box(0);
x_475 = x_480;
goto block_479;
}
block_479:
{
lean_object* x_476; 
if (x_475 == 0)
{
x_476 = x_474;
goto block_477;
}
else
{
lean_object* x_478; 
x_478 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_478, 0, x_473);
x_476 = x_478;
goto block_477;
}
block_477:
{
return x_476;
}
}
}
}
else
{
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_454;
}
}
block_72:
{
lean_object* x_37; 
x_37 = l_Lean_Meta_Grind_isInconsistent___redArg(x_27);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_63; 
x_38 = lean_ctor_get(x_37, 0);
x_63 = !lean_is_exclusive(x_37);
if (x_63 == 0)
{
x_39 = x_37;
x_40 = x_63;
goto block_62;
}
else
{
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = x_63;
goto block_62;
}
block_62:
{
uint8_t x_41; 
x_41 = lean_unbox(x_38);
lean_dec(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_del_object(x_39);
x_42 = l_Lean_Meta_Grind_ParentSet_elems(x_26);
lean_dec(x_26);
x_43 = lean_box(0);
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_44 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(x_42, x_43, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec_ref(x_44);
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_24);
x_45 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(x_24, x_43, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
lean_dec_ref(x_45);
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_46 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(x_23, x_22, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
lean_dec_ref(x_22);
lean_dec_ref(x_23);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
lean_dec_ref(x_46);
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_47 = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(x_25, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; uint8_t x_56; 
x_56 = !lean_is_exclusive(x_47);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_47, 0);
lean_dec(x_57);
x_48 = x_47;
x_49 = x_56;
goto block_55;
}
else
{
lean_dec(x_47);
x_48 = lean_box(0);
x_49 = x_56;
goto block_55;
}
block_55:
{
uint8_t x_50; 
x_50 = l_Lean_Expr_isTrue(x_21);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
if (x_49 == 0)
{
lean_ctor_set(x_48, 0, x_43);
x_51 = x_48;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_43);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
else
{
lean_object* x_54; 
lean_del_object(x_48);
x_54 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(x_24, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
lean_dec(x_24);
return x_54;
}
}
}
else
{
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
return x_47;
}
}
else
{
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_21);
return x_46;
}
}
else
{
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
return x_45;
}
}
else
{
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
return x_44;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
x_58 = lean_box(0);
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_58);
x_59 = x_39;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
x_64 = lean_ctor_get(x_37, 0);
x_71 = !lean_is_exclusive(x_37);
if (x_71 == 0)
{
x_65 = x_37;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_37);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
block_136:
{
lean_object* x_108; lean_object* x_109; 
lean_inc_ref(x_100);
x_108 = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(x_108, 0, x_100);
lean_ctor_set(x_108, 1, x_83);
lean_ctor_set(x_108, 2, x_98);
lean_ctor_set(x_108, 3, x_81);
lean_ctor_set(x_108, 4, x_79);
lean_ctor_set(x_108, 5, x_74);
lean_ctor_set(x_108, 6, x_96);
lean_ctor_set(x_108, 7, x_97);
lean_ctor_set(x_108, 8, x_84);
lean_ctor_set(x_108, 9, x_82);
lean_ctor_set(x_108, 10, x_87);
lean_ctor_set_uint8(x_108, sizeof(void*)*11, x_94);
lean_ctor_set_uint8(x_108, sizeof(void*)*11 + 1, x_89);
lean_ctor_set_uint8(x_108, sizeof(void*)*11 + 2, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*11 + 3, x_102);
lean_ctor_set_uint8(x_108, sizeof(void*)*11 + 4, x_107);
lean_ctor_set_uint8(x_108, sizeof(void*)*11 + 5, x_86);
lean_inc_ref(x_99);
x_109 = l_Lean_Meta_Grind_setENode___redArg(x_99, x_108, x_80);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
lean_dec_ref(x_109);
lean_inc(x_90);
lean_inc_ref(x_78);
lean_inc(x_95);
lean_inc_ref(x_101);
lean_inc(x_77);
lean_inc_ref(x_75);
lean_inc(x_88);
lean_inc_ref(x_85);
lean_inc(x_105);
lean_inc(x_80);
lean_inc_ref(x_92);
x_110 = l_Lean_Meta_Grind_propagateBeta(x_92, x_104, x_80, x_105, x_85, x_88, x_75, x_77, x_101, x_95, x_78, x_90);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
lean_dec_ref(x_110);
lean_inc(x_90);
lean_inc_ref(x_78);
lean_inc(x_95);
lean_inc_ref(x_101);
lean_inc(x_77);
lean_inc_ref(x_75);
lean_inc(x_88);
lean_inc_ref(x_85);
lean_inc(x_105);
lean_inc(x_80);
lean_inc_ref(x_73);
x_111 = l_Lean_Meta_Grind_propagateBeta(x_73, x_76, x_80, x_105, x_85, x_88, x_75, x_77, x_101, x_95, x_78, x_90);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
lean_dec_ref(x_111);
x_112 = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(x_8, x_7, x_80, x_101, x_95, x_78, x_90);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = l_Lean_Meta_Grind_resetParentsOf___redArg(x_103, x_80);
lean_dec_ref(x_103);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
lean_dec_ref(x_114);
lean_inc_ref(x_99);
lean_inc(x_91);
x_115 = l_Lean_Meta_Grind_copyParentsTo(x_91, x_99, x_80, x_105, x_85, x_88, x_75, x_77, x_101, x_95, x_78, x_90);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
lean_dec_ref(x_115);
x_116 = l_Lean_Meta_Grind_isInconsistent___redArg(x_80);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(x_100, x_80, x_105, x_85, x_88, x_75, x_77, x_101, x_95, x_78, x_90);
lean_dec_ref(x_100);
if (lean_obj_tag(x_119) == 0)
{
lean_dec_ref(x_119);
x_21 = x_99;
x_22 = x_73;
x_23 = x_92;
x_24 = x_93;
x_25 = x_113;
x_26 = x_91;
x_27 = x_80;
x_28 = x_105;
x_29 = x_85;
x_30 = x_88;
x_31 = x_75;
x_32 = x_77;
x_33 = x_101;
x_34 = x_95;
x_35 = x_78;
x_36 = x_90;
goto block_72;
}
else
{
lean_dec(x_113);
lean_dec(x_105);
lean_dec_ref(x_101);
lean_dec_ref(x_99);
lean_dec(x_95);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec_ref(x_85);
lean_dec(x_80);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_75);
lean_dec_ref(x_73);
return x_119;
}
}
else
{
lean_dec_ref(x_100);
x_21 = x_99;
x_22 = x_73;
x_23 = x_92;
x_24 = x_93;
x_25 = x_113;
x_26 = x_91;
x_27 = x_80;
x_28 = x_105;
x_29 = x_85;
x_30 = x_88;
x_31 = x_75;
x_32 = x_77;
x_33 = x_101;
x_34 = x_95;
x_35 = x_78;
x_36 = x_90;
goto block_72;
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_127; 
lean_dec(x_113);
lean_dec(x_105);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec(x_95);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec_ref(x_85);
lean_dec(x_80);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_75);
lean_dec_ref(x_73);
x_120 = lean_ctor_get(x_116, 0);
x_127 = !lean_is_exclusive(x_116);
if (x_127 == 0)
{
x_121 = x_116;
x_122 = x_127;
goto block_126;
}
else
{
lean_inc(x_120);
lean_dec(x_116);
x_121 = lean_box(0);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
if (x_122 == 0)
{
x_123 = x_121;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_120);
x_123 = x_125;
goto block_124;
}
block_124:
{
return x_123;
}
}
}
}
else
{
lean_dec(x_113);
lean_dec(x_105);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec(x_95);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec_ref(x_85);
lean_dec(x_80);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_75);
lean_dec_ref(x_73);
return x_115;
}
}
else
{
lean_dec(x_113);
lean_dec(x_105);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec(x_95);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec_ref(x_85);
lean_dec(x_80);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_75);
lean_dec_ref(x_73);
return x_114;
}
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_135; 
lean_dec(x_105);
lean_dec_ref(x_103);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec(x_95);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec_ref(x_85);
lean_dec(x_80);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_75);
lean_dec_ref(x_73);
x_128 = lean_ctor_get(x_112, 0);
x_135 = !lean_is_exclusive(x_112);
if (x_135 == 0)
{
x_129 = x_112;
x_130 = x_135;
goto block_134;
}
else
{
lean_inc(x_128);
lean_dec(x_112);
x_129 = lean_box(0);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_130 == 0)
{
x_131 = x_129;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_128);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
}
}
else
{
lean_dec(x_105);
lean_dec_ref(x_103);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec(x_95);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec_ref(x_85);
lean_dec(x_80);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_75);
lean_dec_ref(x_73);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
return x_111;
}
}
else
{
lean_dec(x_105);
lean_dec_ref(x_103);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec(x_95);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec_ref(x_85);
lean_dec(x_80);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_73);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
return x_110;
}
}
else
{
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec_ref(x_103);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec(x_95);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec_ref(x_85);
lean_dec(x_80);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_73);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
return x_109;
}
}
block_173:
{
if (x_2 == 0)
{
if (x_162 == 0)
{
x_73 = x_137;
x_74 = x_138;
x_75 = x_139;
x_76 = x_140;
x_77 = x_141;
x_78 = x_144;
x_79 = x_143;
x_80 = x_142;
x_81 = x_146;
x_82 = x_145;
x_83 = x_147;
x_84 = x_150;
x_85 = x_149;
x_86 = x_151;
x_87 = x_152;
x_88 = x_153;
x_89 = x_154;
x_90 = x_155;
x_91 = x_156;
x_92 = x_157;
x_93 = x_158;
x_94 = x_159;
x_95 = x_160;
x_96 = x_161;
x_97 = x_165;
x_98 = x_164;
x_99 = x_163;
x_100 = x_166;
x_101 = x_167;
x_102 = x_172;
x_103 = x_168;
x_104 = x_169;
x_105 = x_170;
x_106 = x_171;
x_107 = x_148;
goto block_136;
}
else
{
x_73 = x_137;
x_74 = x_138;
x_75 = x_139;
x_76 = x_140;
x_77 = x_141;
x_78 = x_144;
x_79 = x_143;
x_80 = x_142;
x_81 = x_146;
x_82 = x_145;
x_83 = x_147;
x_84 = x_150;
x_85 = x_149;
x_86 = x_151;
x_87 = x_152;
x_88 = x_153;
x_89 = x_154;
x_90 = x_155;
x_91 = x_156;
x_92 = x_157;
x_93 = x_158;
x_94 = x_159;
x_95 = x_160;
x_96 = x_161;
x_97 = x_165;
x_98 = x_164;
x_99 = x_163;
x_100 = x_166;
x_101 = x_167;
x_102 = x_172;
x_103 = x_168;
x_104 = x_169;
x_105 = x_170;
x_106 = x_171;
x_107 = x_162;
goto block_136;
}
}
else
{
x_73 = x_137;
x_74 = x_138;
x_75 = x_139;
x_76 = x_140;
x_77 = x_141;
x_78 = x_144;
x_79 = x_143;
x_80 = x_142;
x_81 = x_146;
x_82 = x_145;
x_83 = x_147;
x_84 = x_150;
x_85 = x_149;
x_86 = x_151;
x_87 = x_152;
x_88 = x_153;
x_89 = x_154;
x_90 = x_155;
x_91 = x_156;
x_92 = x_157;
x_93 = x_158;
x_94 = x_159;
x_95 = x_160;
x_96 = x_161;
x_97 = x_165;
x_98 = x_164;
x_99 = x_163;
x_100 = x_166;
x_101 = x_167;
x_102 = x_172;
x_103 = x_168;
x_104 = x_169;
x_105 = x_170;
x_106 = x_171;
x_107 = x_2;
goto block_136;
}
}
block_254:
{
lean_object* x_196; 
lean_inc(x_195);
lean_inc_ref(x_194);
lean_inc(x_193);
lean_inc_ref(x_192);
x_196 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(x_185, x_186, x_187, x_188, x_189, x_190, x_191, x_192, x_193, x_194, x_195);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec_ref(x_196);
x_197 = lean_st_ref_get(x_186);
x_198 = lean_st_ref_get(x_186);
lean_inc_ref(x_183);
x_199 = l_Lean_Meta_Grind_Goal_getENode(x_198, x_183, x_192, x_193, x_194, x_195);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; uint8_t x_218; uint8_t x_244; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
lean_dec_ref(x_199);
x_201 = lean_ctor_get(x_200, 0);
x_202 = lean_ctor_get(x_200, 2);
x_203 = lean_ctor_get(x_200, 3);
x_204 = lean_ctor_get(x_200, 4);
x_205 = lean_ctor_get(x_200, 5);
x_206 = lean_ctor_get_uint8(x_200, sizeof(void*)*11);
x_207 = lean_ctor_get(x_200, 6);
x_208 = lean_ctor_get_uint8(x_200, sizeof(void*)*11 + 1);
x_209 = lean_ctor_get_uint8(x_200, sizeof(void*)*11 + 2);
x_210 = lean_ctor_get_uint8(x_200, sizeof(void*)*11 + 3);
x_211 = lean_ctor_get_uint8(x_200, sizeof(void*)*11 + 4);
x_212 = lean_ctor_get(x_200, 7);
x_213 = lean_ctor_get(x_200, 8);
x_214 = lean_ctor_get(x_200, 9);
x_215 = lean_ctor_get(x_200, 10);
x_216 = lean_ctor_get_uint8(x_200, sizeof(void*)*11 + 5);
x_244 = !lean_is_exclusive(x_200);
if (x_244 == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_200, 1);
lean_dec(x_245);
x_217 = x_200;
x_218 = x_244;
goto block_243;
}
else
{
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_207);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_200);
x_217 = lean_box(0);
x_218 = x_244;
goto block_243;
}
block_243:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; 
x_219 = lean_ctor_get(x_8, 0);
x_220 = lean_ctor_get(x_8, 1);
x_221 = lean_ctor_get(x_8, 2);
x_222 = lean_ctor_get(x_8, 3);
x_223 = lean_ctor_get(x_8, 4);
x_224 = lean_ctor_get(x_8, 5);
x_225 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
x_226 = lean_ctor_get(x_8, 6);
x_227 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 1);
x_228 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 2);
x_229 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 3);
x_230 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 4);
x_231 = lean_ctor_get(x_8, 7);
x_232 = lean_ctor_get(x_8, 8);
x_233 = lean_ctor_get(x_8, 9);
x_234 = lean_ctor_get(x_8, 10);
x_235 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 5);
lean_inc_ref(x_220);
if (x_218 == 0)
{
lean_ctor_set(x_217, 1, x_220);
x_236 = x_217;
goto block_241;
}
else
{
lean_object* x_242; 
x_242 = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(x_242, 0, x_201);
lean_ctor_set(x_242, 1, x_220);
lean_ctor_set(x_242, 2, x_202);
lean_ctor_set(x_242, 3, x_203);
lean_ctor_set(x_242, 4, x_204);
lean_ctor_set(x_242, 5, x_205);
lean_ctor_set(x_242, 6, x_207);
lean_ctor_set(x_242, 7, x_212);
lean_ctor_set(x_242, 8, x_213);
lean_ctor_set(x_242, 9, x_214);
lean_ctor_set(x_242, 10, x_215);
lean_ctor_set_uint8(x_242, sizeof(void*)*11, x_206);
lean_ctor_set_uint8(x_242, sizeof(void*)*11 + 1, x_208);
lean_ctor_set_uint8(x_242, sizeof(void*)*11 + 2, x_209);
lean_ctor_set_uint8(x_242, sizeof(void*)*11 + 3, x_210);
lean_ctor_set_uint8(x_242, sizeof(void*)*11 + 4, x_211);
lean_ctor_set_uint8(x_242, sizeof(void*)*11 + 5, x_216);
x_236 = x_242;
goto block_241;
}
block_241:
{
lean_object* x_237; 
x_237 = l_Lean_Meta_Grind_setENode___redArg(x_179, x_236, x_186);
if (lean_obj_tag(x_237) == 0)
{
uint8_t x_238; lean_object* x_239; lean_object* x_240; 
lean_dec_ref(x_237);
x_238 = 0;
x_239 = l_Lean_Meta_Grind_Goal_getEqc(x_197, x_3, x_238);
x_240 = lean_nat_add(x_226, x_182);
lean_dec(x_182);
if (x_229 == 0)
{
lean_inc_ref(x_219);
lean_inc(x_231);
lean_inc_ref(x_221);
lean_inc(x_234);
lean_inc(x_232);
lean_inc_ref(x_222);
lean_inc(x_233);
lean_inc(x_223);
lean_inc(x_224);
x_137 = x_175;
x_138 = x_224;
x_139 = x_190;
x_140 = x_181;
x_141 = x_191;
x_142 = x_186;
x_143 = x_223;
x_144 = x_194;
x_145 = x_233;
x_146 = x_222;
x_147 = x_177;
x_148 = x_178;
x_149 = x_188;
x_150 = x_232;
x_151 = x_235;
x_152 = x_234;
x_153 = x_189;
x_154 = x_227;
x_155 = x_195;
x_156 = x_185;
x_157 = x_176;
x_158 = x_239;
x_159 = x_225;
x_160 = x_193;
x_161 = x_240;
x_162 = x_230;
x_163 = x_174;
x_164 = x_221;
x_165 = x_231;
x_166 = x_219;
x_167 = x_192;
x_168 = x_183;
x_169 = x_184;
x_170 = x_187;
x_171 = x_228;
x_172 = x_180;
goto block_173;
}
else
{
lean_inc_ref(x_219);
lean_inc(x_231);
lean_inc_ref(x_221);
lean_inc(x_234);
lean_inc(x_232);
lean_inc_ref(x_222);
lean_inc(x_233);
lean_inc(x_223);
lean_inc(x_224);
x_137 = x_175;
x_138 = x_224;
x_139 = x_190;
x_140 = x_181;
x_141 = x_191;
x_142 = x_186;
x_143 = x_223;
x_144 = x_194;
x_145 = x_233;
x_146 = x_222;
x_147 = x_177;
x_148 = x_178;
x_149 = x_188;
x_150 = x_232;
x_151 = x_235;
x_152 = x_234;
x_153 = x_189;
x_154 = x_227;
x_155 = x_195;
x_156 = x_185;
x_157 = x_176;
x_158 = x_239;
x_159 = x_225;
x_160 = x_193;
x_161 = x_240;
x_162 = x_230;
x_163 = x_174;
x_164 = x_221;
x_165 = x_231;
x_166 = x_219;
x_167 = x_192;
x_168 = x_183;
x_169 = x_184;
x_170 = x_187;
x_171 = x_228;
x_172 = x_229;
goto block_173;
}
}
else
{
lean_dec(x_197);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec_ref(x_177);
lean_dec_ref(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_237;
}
}
}
}
else
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; uint8_t x_253; 
lean_dec(x_197);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec_ref(x_179);
lean_dec_ref(x_177);
lean_dec_ref(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
x_246 = lean_ctor_get(x_199, 0);
x_253 = !lean_is_exclusive(x_199);
if (x_253 == 0)
{
x_247 = x_199;
x_248 = x_253;
goto block_252;
}
else
{
lean_inc(x_246);
lean_dec(x_199);
x_247 = lean_box(0);
x_248 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_249; 
if (x_248 == 0)
{
x_249 = x_247;
goto block_250;
}
else
{
lean_object* x_251; 
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_246);
x_249 = x_251;
goto block_250;
}
block_250:
{
return x_249;
}
}
}
}
else
{
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec_ref(x_179);
lean_dec_ref(x_177);
lean_dec_ref(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_196;
}
}
block_340:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; uint8_t x_275; lean_object* x_276; 
x_271 = lean_ctor_get(x_7, 0);
x_272 = lean_ctor_get(x_7, 1);
x_273 = lean_ctor_get(x_7, 6);
x_274 = lean_ctor_get_uint8(x_7, sizeof(void*)*11 + 3);
x_275 = lean_ctor_get_uint8(x_7, sizeof(void*)*11 + 4);
x_276 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(x_271, x_261, x_262, x_263, x_264, x_265, x_266, x_267, x_268, x_269, x_270);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
lean_dec_ref(x_276);
x_278 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_278);
lean_dec_ref(x_6);
lean_inc_ref(x_278);
lean_inc_ref(x_3);
x_279 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(x_3, x_278, x_261, x_262, x_263, x_264, x_265, x_266, x_267, x_268, x_269, x_270);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; uint8_t x_282; 
lean_dec_ref(x_279);
x_280 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(x_255, x_269);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
lean_dec_ref(x_280);
x_282 = lean_unbox(x_281);
lean_dec(x_281);
if (x_282 == 0)
{
lean_inc_ref(x_271);
lean_inc(x_273);
lean_inc_ref(x_272);
x_174 = x_278;
x_175 = x_256;
x_176 = x_257;
x_177 = x_272;
x_178 = x_275;
x_179 = x_258;
x_180 = x_274;
x_181 = x_260;
x_182 = x_273;
x_183 = x_271;
x_184 = x_259;
x_185 = x_277;
x_186 = x_261;
x_187 = x_262;
x_188 = x_263;
x_189 = x_264;
x_190 = x_265;
x_191 = x_266;
x_192 = x_267;
x_193 = x_268;
x_194 = x_269;
x_195 = x_270;
goto block_254;
}
else
{
lean_object* x_283; 
x_283 = l_Lean_Meta_Grind_updateLastTag(x_261, x_262, x_263, x_264, x_265, x_266, x_267, x_268, x_269, x_270);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; 
lean_dec_ref(x_283);
lean_inc(x_270);
lean_inc_ref(x_269);
lean_inc(x_268);
lean_inc_ref(x_267);
lean_inc_ref(x_3);
x_284 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_3, x_261, x_267, x_268, x_269, x_270);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
lean_dec_ref(x_284);
lean_inc(x_270);
lean_inc_ref(x_269);
lean_inc(x_268);
lean_inc_ref(x_267);
lean_inc_ref(x_278);
x_286 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_278, x_261, x_267, x_268, x_269, x_270);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
lean_dec_ref(x_286);
x_288 = lean_st_ref_get(x_261);
lean_inc_ref(x_3);
x_289 = l_Lean_Meta_Grind_Goal_getRoot(x_288, x_3, x_267, x_268, x_269, x_270);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
lean_dec_ref(x_289);
lean_inc(x_270);
lean_inc_ref(x_269);
lean_inc(x_268);
lean_inc_ref(x_267);
x_291 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_290, x_261, x_267, x_268, x_269, x_270);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
lean_dec_ref(x_291);
x_293 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2);
x_294 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_294, 0, x_285);
lean_ctor_set(x_294, 1, x_293);
x_295 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_287);
x_296 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4);
x_297 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
x_298 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_292);
x_299 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(x_255, x_298, x_267, x_268, x_269, x_270);
if (lean_obj_tag(x_299) == 0)
{
lean_dec_ref(x_299);
lean_inc_ref(x_271);
lean_inc(x_273);
lean_inc_ref(x_272);
x_174 = x_278;
x_175 = x_256;
x_176 = x_257;
x_177 = x_272;
x_178 = x_275;
x_179 = x_258;
x_180 = x_274;
x_181 = x_260;
x_182 = x_273;
x_183 = x_271;
x_184 = x_259;
x_185 = x_277;
x_186 = x_261;
x_187 = x_262;
x_188 = x_263;
x_189 = x_264;
x_190 = x_265;
x_191 = x_266;
x_192 = x_267;
x_193 = x_268;
x_194 = x_269;
x_195 = x_270;
goto block_254;
}
else
{
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; uint8_t x_307; 
lean_dec(x_287);
lean_dec(x_285);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
x_300 = lean_ctor_get(x_291, 0);
x_307 = !lean_is_exclusive(x_291);
if (x_307 == 0)
{
x_301 = x_291;
x_302 = x_307;
goto block_306;
}
else
{
lean_inc(x_300);
lean_dec(x_291);
x_301 = lean_box(0);
x_302 = x_307;
goto block_306;
}
block_306:
{
lean_object* x_303; 
if (x_302 == 0)
{
x_303 = x_301;
goto block_304;
}
else
{
lean_object* x_305; 
x_305 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_305, 0, x_300);
x_303 = x_305;
goto block_304;
}
block_304:
{
return x_303;
}
}
}
}
else
{
lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_315; 
lean_dec(x_287);
lean_dec(x_285);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
x_308 = lean_ctor_get(x_289, 0);
x_315 = !lean_is_exclusive(x_289);
if (x_315 == 0)
{
x_309 = x_289;
x_310 = x_315;
goto block_314;
}
else
{
lean_inc(x_308);
lean_dec(x_289);
x_309 = lean_box(0);
x_310 = x_315;
goto block_314;
}
block_314:
{
lean_object* x_311; 
if (x_310 == 0)
{
x_311 = x_309;
goto block_312;
}
else
{
lean_object* x_313; 
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_308);
x_311 = x_313;
goto block_312;
}
block_312:
{
return x_311;
}
}
}
}
else
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; uint8_t x_323; 
lean_dec(x_285);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
x_316 = lean_ctor_get(x_286, 0);
x_323 = !lean_is_exclusive(x_286);
if (x_323 == 0)
{
x_317 = x_286;
x_318 = x_323;
goto block_322;
}
else
{
lean_inc(x_316);
lean_dec(x_286);
x_317 = lean_box(0);
x_318 = x_323;
goto block_322;
}
block_322:
{
lean_object* x_319; 
if (x_318 == 0)
{
x_319 = x_317;
goto block_320;
}
else
{
lean_object* x_321; 
x_321 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_321, 0, x_316);
x_319 = x_321;
goto block_320;
}
block_320:
{
return x_319;
}
}
}
}
else
{
lean_object* x_324; lean_object* x_325; uint8_t x_326; uint8_t x_331; 
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
x_324 = lean_ctor_get(x_284, 0);
x_331 = !lean_is_exclusive(x_284);
if (x_331 == 0)
{
x_325 = x_284;
x_326 = x_331;
goto block_330;
}
else
{
lean_inc(x_324);
lean_dec(x_284);
x_325 = lean_box(0);
x_326 = x_331;
goto block_330;
}
block_330:
{
lean_object* x_327; 
if (x_326 == 0)
{
x_327 = x_325;
goto block_328;
}
else
{
lean_object* x_329; 
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_324);
x_327 = x_329;
goto block_328;
}
block_328:
{
return x_327;
}
}
}
}
else
{
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_283;
}
}
}
else
{
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_279;
}
}
else
{
lean_object* x_332; lean_object* x_333; uint8_t x_334; uint8_t x_339; 
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_332 = lean_ctor_get(x_276, 0);
x_339 = !lean_is_exclusive(x_276);
if (x_339 == 0)
{
x_333 = x_276;
x_334 = x_339;
goto block_338;
}
else
{
lean_inc(x_332);
lean_dec(x_276);
x_333 = lean_box(0);
x_334 = x_339;
goto block_338;
}
block_338:
{
lean_object* x_335; 
if (x_334 == 0)
{
x_335 = x_333;
goto block_336;
}
else
{
lean_object* x_337; 
x_337 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_337, 0, x_332);
x_335 = x_337;
goto block_336;
}
block_336:
{
return x_335;
}
}
}
}
block_370:
{
lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_355 = lean_array_get_size(x_341);
x_356 = lean_unsigned_to_nat(0u);
x_357 = lean_nat_dec_eq(x_355, x_356);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_7, 0);
lean_inc(x_354);
lean_inc_ref(x_353);
lean_inc(x_352);
lean_inc_ref(x_351);
lean_inc(x_350);
lean_inc_ref(x_349);
lean_inc(x_348);
lean_inc_ref(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc_ref(x_358);
x_359 = l_Lean_Meta_Grind_getFnRoots(x_358, x_345, x_346, x_347, x_348, x_349, x_350, x_351, x_352, x_353, x_354);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
lean_dec_ref(x_359);
x_256 = x_341;
x_257 = x_342;
x_258 = x_343;
x_259 = x_344;
x_260 = x_360;
x_261 = x_345;
x_262 = x_346;
x_263 = x_347;
x_264 = x_348;
x_265 = x_349;
x_266 = x_350;
x_267 = x_351;
x_268 = x_352;
x_269 = x_353;
x_270 = x_354;
goto block_340;
}
else
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; uint8_t x_368; 
lean_dec(x_354);
lean_dec_ref(x_353);
lean_dec(x_352);
lean_dec_ref(x_351);
lean_dec(x_350);
lean_dec_ref(x_349);
lean_dec(x_348);
lean_dec_ref(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec_ref(x_344);
lean_dec_ref(x_343);
lean_dec_ref(x_342);
lean_dec_ref(x_341);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_361 = lean_ctor_get(x_359, 0);
x_368 = !lean_is_exclusive(x_359);
if (x_368 == 0)
{
x_362 = x_359;
x_363 = x_368;
goto block_367;
}
else
{
lean_inc(x_361);
lean_dec(x_359);
x_362 = lean_box(0);
x_363 = x_368;
goto block_367;
}
block_367:
{
lean_object* x_364; 
if (x_363 == 0)
{
x_364 = x_362;
goto block_365;
}
else
{
lean_object* x_366; 
x_366 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_366, 0, x_361);
x_364 = x_366;
goto block_365;
}
block_365:
{
return x_364;
}
}
}
}
else
{
lean_object* x_369; 
x_369 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__0));
x_256 = x_341;
x_257 = x_342;
x_258 = x_343;
x_259 = x_344;
x_260 = x_369;
x_261 = x_345;
x_262 = x_346;
x_263 = x_347;
x_264 = x_348;
x_265 = x_349;
x_266 = x_350;
x_267 = x_351;
x_268 = x_352;
x_269 = x_353;
x_270 = x_354;
goto block_340;
}
}
block_450:
{
lean_object* x_381; 
lean_inc_ref(x_3);
x_381 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(x_3, x_371, x_377, x_378, x_379, x_380);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; uint8_t x_383; uint8_t x_448; 
x_448 = !lean_is_exclusive(x_381);
if (x_448 == 0)
{
lean_object* x_449; 
x_449 = lean_ctor_get(x_381, 0);
lean_dec(x_449);
x_382 = x_381;
x_383 = x_448;
goto block_447;
}
else
{
lean_dec(x_381);
x_382 = lean_box(0);
x_383 = x_448;
goto block_447;
}
block_447:
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; uint8_t x_390; uint8_t x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; uint8_t x_399; uint8_t x_444; 
x_384 = lean_ctor_get(x_5, 0);
x_385 = lean_ctor_get(x_5, 1);
x_386 = lean_ctor_get(x_5, 2);
x_387 = lean_ctor_get(x_5, 3);
x_388 = lean_ctor_get(x_5, 6);
x_389 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 1);
x_390 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 2);
x_391 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 3);
x_392 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 4);
x_393 = lean_ctor_get(x_5, 7);
x_394 = lean_ctor_get(x_5, 8);
x_395 = lean_ctor_get(x_5, 9);
x_396 = lean_ctor_get(x_5, 10);
x_397 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 5);
x_444 = !lean_is_exclusive(x_5);
if (x_444 == 0)
{
lean_object* x_445; lean_object* x_446; 
x_445 = lean_ctor_get(x_5, 5);
lean_dec(x_445);
x_446 = lean_ctor_get(x_5, 4);
lean_dec(x_446);
x_398 = x_5;
x_399 = x_444;
goto block_443;
}
else
{
lean_inc(x_396);
lean_inc(x_395);
lean_inc(x_394);
lean_inc(x_393);
lean_inc(x_388);
lean_inc(x_387);
lean_inc(x_386);
lean_inc(x_385);
lean_inc(x_384);
lean_dec(x_5);
x_398 = lean_box(0);
x_399 = x_444;
goto block_443;
}
block_443:
{
lean_object* x_400; 
if (x_383 == 0)
{
lean_ctor_set_tag(x_382, 1);
lean_ctor_set(x_382, 0, x_4);
x_400 = x_382;
goto block_441;
}
else
{
lean_object* x_442; 
x_442 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_442, 0, x_4);
x_400 = x_442;
goto block_441;
}
block_441:
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_401, 0, x_1);
lean_inc_ref(x_386);
if (x_399 == 0)
{
lean_ctor_set(x_398, 5, x_401);
lean_ctor_set(x_398, 4, x_400);
x_402 = x_398;
goto block_439;
}
else
{
lean_object* x_440; 
x_440 = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(x_440, 0, x_384);
lean_ctor_set(x_440, 1, x_385);
lean_ctor_set(x_440, 2, x_386);
lean_ctor_set(x_440, 3, x_387);
lean_ctor_set(x_440, 4, x_400);
lean_ctor_set(x_440, 5, x_401);
lean_ctor_set(x_440, 6, x_388);
lean_ctor_set(x_440, 7, x_393);
lean_ctor_set(x_440, 8, x_394);
lean_ctor_set(x_440, 9, x_395);
lean_ctor_set(x_440, 10, x_396);
lean_ctor_set_uint8(x_440, sizeof(void*)*11 + 1, x_389);
lean_ctor_set_uint8(x_440, sizeof(void*)*11 + 2, x_390);
lean_ctor_set_uint8(x_440, sizeof(void*)*11 + 3, x_391);
lean_ctor_set_uint8(x_440, sizeof(void*)*11 + 4, x_392);
lean_ctor_set_uint8(x_440, sizeof(void*)*11 + 5, x_397);
x_402 = x_440;
goto block_439;
}
block_439:
{
lean_object* x_403; 
lean_ctor_set_uint8(x_402, sizeof(void*)*11, x_9);
lean_inc_ref(x_3);
x_403 = l_Lean_Meta_Grind_setENode___redArg(x_3, x_402, x_371);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; 
lean_dec_ref(x_403);
lean_inc(x_380);
lean_inc_ref(x_379);
lean_inc(x_378);
lean_inc_ref(x_377);
lean_inc(x_376);
lean_inc_ref(x_375);
lean_inc(x_374);
lean_inc_ref(x_373);
lean_inc(x_372);
lean_inc(x_371);
x_404 = l_Lean_Meta_Grind_getEqcLambdas(x_7, x_371, x_372, x_373, x_374, x_375, x_376, x_377, x_378, x_379, x_380);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
lean_dec_ref(x_404);
lean_inc(x_380);
lean_inc_ref(x_379);
lean_inc(x_378);
lean_inc_ref(x_377);
lean_inc(x_376);
lean_inc_ref(x_375);
lean_inc(x_374);
lean_inc_ref(x_373);
lean_inc(x_372);
lean_inc(x_371);
x_406 = l_Lean_Meta_Grind_getEqcLambdas(x_8, x_371, x_372, x_373, x_374, x_375, x_376, x_377, x_378, x_379, x_380);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
lean_dec_ref(x_406);
x_408 = lean_array_get_size(x_405);
x_409 = lean_unsigned_to_nat(0u);
x_410 = lean_nat_dec_eq(x_408, x_409);
if (x_410 == 0)
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_8, 0);
lean_inc(x_380);
lean_inc_ref(x_379);
lean_inc(x_378);
lean_inc_ref(x_377);
lean_inc(x_376);
lean_inc_ref(x_375);
lean_inc(x_374);
lean_inc_ref(x_373);
lean_inc(x_372);
lean_inc(x_371);
lean_inc_ref(x_411);
x_412 = l_Lean_Meta_Grind_getFnRoots(x_411, x_371, x_372, x_373, x_374, x_375, x_376, x_377, x_378, x_379, x_380);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
lean_dec_ref(x_412);
x_341 = x_407;
x_342 = x_405;
x_343 = x_386;
x_344 = x_413;
x_345 = x_371;
x_346 = x_372;
x_347 = x_373;
x_348 = x_374;
x_349 = x_375;
x_350 = x_376;
x_351 = x_377;
x_352 = x_378;
x_353 = x_379;
x_354 = x_380;
goto block_370;
}
else
{
lean_object* x_414; lean_object* x_415; uint8_t x_416; uint8_t x_421; 
lean_dec(x_407);
lean_dec(x_405);
lean_dec_ref(x_386);
lean_dec(x_380);
lean_dec_ref(x_379);
lean_dec(x_378);
lean_dec_ref(x_377);
lean_dec(x_376);
lean_dec_ref(x_375);
lean_dec(x_374);
lean_dec_ref(x_373);
lean_dec(x_372);
lean_dec(x_371);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_414 = lean_ctor_get(x_412, 0);
x_421 = !lean_is_exclusive(x_412);
if (x_421 == 0)
{
x_415 = x_412;
x_416 = x_421;
goto block_420;
}
else
{
lean_inc(x_414);
lean_dec(x_412);
x_415 = lean_box(0);
x_416 = x_421;
goto block_420;
}
block_420:
{
lean_object* x_417; 
if (x_416 == 0)
{
x_417 = x_415;
goto block_418;
}
else
{
lean_object* x_419; 
x_419 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_419, 0, x_414);
x_417 = x_419;
goto block_418;
}
block_418:
{
return x_417;
}
}
}
}
else
{
lean_object* x_422; 
x_422 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__0));
x_341 = x_407;
x_342 = x_405;
x_343 = x_386;
x_344 = x_422;
x_345 = x_371;
x_346 = x_372;
x_347 = x_373;
x_348 = x_374;
x_349 = x_375;
x_350 = x_376;
x_351 = x_377;
x_352 = x_378;
x_353 = x_379;
x_354 = x_380;
goto block_370;
}
}
else
{
lean_object* x_423; lean_object* x_424; uint8_t x_425; uint8_t x_430; 
lean_dec(x_405);
lean_dec_ref(x_386);
lean_dec(x_380);
lean_dec_ref(x_379);
lean_dec(x_378);
lean_dec_ref(x_377);
lean_dec(x_376);
lean_dec_ref(x_375);
lean_dec(x_374);
lean_dec_ref(x_373);
lean_dec(x_372);
lean_dec(x_371);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_423 = lean_ctor_get(x_406, 0);
x_430 = !lean_is_exclusive(x_406);
if (x_430 == 0)
{
x_424 = x_406;
x_425 = x_430;
goto block_429;
}
else
{
lean_inc(x_423);
lean_dec(x_406);
x_424 = lean_box(0);
x_425 = x_430;
goto block_429;
}
block_429:
{
lean_object* x_426; 
if (x_425 == 0)
{
x_426 = x_424;
goto block_427;
}
else
{
lean_object* x_428; 
x_428 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_428, 0, x_423);
x_426 = x_428;
goto block_427;
}
block_427:
{
return x_426;
}
}
}
}
else
{
lean_object* x_431; lean_object* x_432; uint8_t x_433; uint8_t x_438; 
lean_dec_ref(x_386);
lean_dec(x_380);
lean_dec_ref(x_379);
lean_dec(x_378);
lean_dec_ref(x_377);
lean_dec(x_376);
lean_dec_ref(x_375);
lean_dec(x_374);
lean_dec_ref(x_373);
lean_dec(x_372);
lean_dec(x_371);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_431 = lean_ctor_get(x_404, 0);
x_438 = !lean_is_exclusive(x_404);
if (x_438 == 0)
{
x_432 = x_404;
x_433 = x_438;
goto block_437;
}
else
{
lean_inc(x_431);
lean_dec(x_404);
x_432 = lean_box(0);
x_433 = x_438;
goto block_437;
}
block_437:
{
lean_object* x_434; 
if (x_433 == 0)
{
x_434 = x_432;
goto block_435;
}
else
{
lean_object* x_436; 
x_436 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_436, 0, x_431);
x_434 = x_436;
goto block_435;
}
block_435:
{
return x_434;
}
}
}
}
else
{
lean_dec_ref(x_386);
lean_dec(x_380);
lean_dec_ref(x_379);
lean_dec(x_378);
lean_dec_ref(x_377);
lean_dec(x_376);
lean_dec_ref(x_375);
lean_dec(x_374);
lean_dec_ref(x_373);
lean_dec(x_372);
lean_dec(x_371);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
return x_403;
}
}
}
}
}
}
else
{
lean_dec(x_380);
lean_dec_ref(x_379);
lean_dec(x_378);
lean_dec_ref(x_377);
lean_dec(x_376);
lean_dec_ref(x_375);
lean_dec(x_374);
lean_dec_ref(x_373);
lean_dec(x_372);
lean_dec(x_371);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_381;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_unbox(x_2);
x_22 = lean_unbox(x_9);
x_23 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_23;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_st_ref_get(x_5);
lean_inc_ref(x_1);
x_20 = l_Lean_Meta_Grind_Goal_getENode(x_19, x_1, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_st_ref_get(x_5);
lean_inc_ref(x_2);
x_23 = l_Lean_Meta_Grind_Goal_getENode(x_22, x_2, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_ctor_get(x_21, 2);
x_26 = lean_ctor_get(x_24, 2);
x_27 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_133; uint8_t x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_243; uint8_t x_244; lean_object* x_245; uint8_t x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_260; lean_object* x_261; uint8_t x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_375; lean_object* x_376; lean_object* x_389; lean_object* x_390; uint8_t x_391; 
x_375 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
x_389 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(x_375, x_13);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
lean_dec_ref(x_389);
x_391 = lean_unbox(x_390);
lean_dec(x_390);
if (x_391 == 0)
{
x_339 = x_5;
x_340 = x_6;
x_341 = x_7;
x_342 = x_8;
x_343 = x_9;
x_344 = x_10;
x_345 = x_11;
x_346 = x_12;
x_347 = x_13;
x_348 = x_14;
goto block_374;
}
else
{
lean_object* x_392; 
x_392 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_392) == 0)
{
lean_dec_ref(x_392);
if (x_4 == 0)
{
lean_object* x_393; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_393 = l_Lean_Meta_mkEq(x_1, x_2, x_11, x_12, x_13, x_14);
x_376 = x_393;
goto block_388;
}
else
{
lean_object* x_394; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_394 = l_Lean_Meta_mkHEq(x_1, x_2, x_11, x_12, x_13, x_14);
x_376 = x_394;
goto block_388;
}
}
else
{
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_392;
}
}
block_59:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
x_39 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(x_38, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Lean_Meta_Grind_checkInvariants(x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Meta_Grind_updateLastTag(x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_43);
x_44 = lean_st_ref_get(x_28);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc(x_35);
lean_inc_ref(x_34);
x_45 = l_Lean_Meta_Grind_Goal_ppState(x_44, x_34, x_35, x_36, x_37);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(x_38, x_48, x_34, x_35, x_36, x_37);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
lean_dec_ref(x_49);
x_50 = l_Lean_Meta_Grind_checkInvariants(x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37);
return x_50;
}
else
{
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
return x_49;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
x_51 = lean_ctor_get(x_45, 0);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
x_52 = x_45;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_45);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
else
{
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
return x_43;
}
}
}
block_87:
{
lean_object* x_73; 
x_73 = l_Lean_Meta_Grind_isInconsistent___redArg(x_63);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
if (x_61 == 0)
{
lean_dec_ref(x_62);
lean_dec_ref(x_60);
x_28 = x_63;
x_29 = x_64;
x_30 = x_65;
x_31 = x_66;
x_32 = x_67;
x_33 = x_68;
x_34 = x_69;
x_35 = x_70;
x_36 = x_71;
x_37 = x_72;
goto block_59;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_76);
lean_dec_ref(x_60);
x_77 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_77);
lean_dec_ref(x_62);
lean_inc(x_72);
lean_inc_ref(x_71);
lean_inc(x_70);
lean_inc_ref(x_69);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc(x_64);
lean_inc(x_63);
x_78 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(x_76, x_77, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70, x_71, x_72);
if (lean_obj_tag(x_78) == 0)
{
lean_dec_ref(x_78);
x_28 = x_63;
x_29 = x_64;
x_30 = x_65;
x_31 = x_66;
x_32 = x_67;
x_33 = x_68;
x_34 = x_69;
x_35 = x_70;
x_36 = x_71;
x_37 = x_72;
goto block_59;
}
else
{
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec(x_63);
return x_78;
}
}
}
else
{
lean_dec_ref(x_62);
lean_dec_ref(x_60);
x_28 = x_63;
x_29 = x_64;
x_30 = x_65;
x_31 = x_66;
x_32 = x_67;
x_33 = x_68;
x_34 = x_69;
x_35 = x_70;
x_36 = x_71;
x_37 = x_72;
goto block_59;
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_60);
x_79 = lean_ctor_get(x_73, 0);
x_86 = !lean_is_exclusive(x_73);
if (x_86 == 0)
{
x_80 = x_73;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_73);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
block_105:
{
if (x_101 == 0)
{
x_60 = x_94;
x_61 = x_95;
x_62 = x_98;
x_63 = x_97;
x_64 = x_92;
x_65 = x_90;
x_66 = x_99;
x_67 = x_88;
x_68 = x_100;
x_69 = x_89;
x_70 = x_93;
x_71 = x_91;
x_72 = x_96;
goto block_87;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_94, 0);
x_103 = lean_ctor_get(x_98, 0);
lean_inc(x_96);
lean_inc_ref(x_91);
lean_inc(x_93);
lean_inc_ref(x_89);
lean_inc(x_100);
lean_inc_ref(x_88);
lean_inc(x_99);
lean_inc_ref(x_90);
lean_inc(x_92);
lean_inc(x_97);
lean_inc_ref(x_103);
lean_inc_ref(x_102);
x_104 = l_Lean_Meta_Grind_propagateCtor(x_102, x_103, x_97, x_92, x_90, x_99, x_88, x_100, x_89, x_93, x_91, x_96);
if (lean_obj_tag(x_104) == 0)
{
lean_dec_ref(x_104);
x_60 = x_94;
x_61 = x_95;
x_62 = x_98;
x_63 = x_97;
x_64 = x_92;
x_65 = x_90;
x_66 = x_99;
x_67 = x_88;
x_68 = x_100;
x_69 = x_89;
x_70 = x_93;
x_71 = x_91;
x_72 = x_96;
goto block_87;
}
else
{
lean_dec(x_100);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec_ref(x_90);
lean_dec_ref(x_89);
lean_dec_ref(x_88);
return x_104;
}
}
}
block_132:
{
lean_object* x_119; 
x_119 = l_Lean_Meta_Grind_isInconsistent___redArg(x_109);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = lean_unbox(x_120);
lean_dec(x_120);
if (x_121 == 0)
{
uint8_t x_122; 
x_122 = lean_ctor_get_uint8(x_106, sizeof(void*)*11 + 2);
if (x_122 == 0)
{
x_88 = x_113;
x_89 = x_115;
x_90 = x_111;
x_91 = x_117;
x_92 = x_110;
x_93 = x_116;
x_94 = x_106;
x_95 = x_107;
x_96 = x_118;
x_97 = x_109;
x_98 = x_108;
x_99 = x_112;
x_100 = x_114;
x_101 = x_27;
goto block_105;
}
else
{
uint8_t x_123; 
x_123 = lean_ctor_get_uint8(x_108, sizeof(void*)*11 + 2);
x_88 = x_113;
x_89 = x_115;
x_90 = x_111;
x_91 = x_117;
x_92 = x_110;
x_93 = x_116;
x_94 = x_106;
x_95 = x_107;
x_96 = x_118;
x_97 = x_109;
x_98 = x_108;
x_99 = x_112;
x_100 = x_114;
x_101 = x_123;
goto block_105;
}
}
else
{
x_60 = x_106;
x_61 = x_107;
x_62 = x_108;
x_63 = x_109;
x_64 = x_110;
x_65 = x_111;
x_66 = x_112;
x_67 = x_113;
x_68 = x_114;
x_69 = x_115;
x_70 = x_116;
x_71 = x_117;
x_72 = x_118;
goto block_87;
}
}
else
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_131; 
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_108);
lean_dec_ref(x_106);
x_124 = lean_ctor_get(x_119, 0);
x_131 = !lean_is_exclusive(x_119);
if (x_131 == 0)
{
x_125 = x_119;
x_126 = x_131;
goto block_130;
}
else
{
lean_inc(x_124);
lean_dec(x_119);
x_125 = lean_box(0);
x_126 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_127; 
if (x_126 == 0)
{
x_127 = x_125;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_124);
x_127 = x_129;
goto block_128;
}
block_128:
{
return x_127;
}
}
}
}
block_148:
{
if (x_135 == 0)
{
x_106 = x_133;
x_107 = x_134;
x_108 = x_136;
x_109 = x_137;
x_110 = x_138;
x_111 = x_139;
x_112 = x_140;
x_113 = x_141;
x_114 = x_142;
x_115 = x_143;
x_116 = x_144;
x_117 = x_145;
x_118 = x_146;
goto block_132;
}
else
{
lean_object* x_147; 
lean_inc(x_146);
lean_inc_ref(x_145);
lean_inc(x_144);
lean_inc_ref(x_143);
lean_inc(x_142);
lean_inc_ref(x_141);
lean_inc(x_140);
lean_inc_ref(x_139);
lean_inc(x_138);
lean_inc(x_137);
x_147 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(x_137, x_138, x_139, x_140, x_141, x_142, x_143, x_144, x_145, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_dec_ref(x_147);
x_106 = x_133;
x_107 = x_134;
x_108 = x_136;
x_109 = x_137;
x_110 = x_138;
x_111 = x_139;
x_112 = x_140;
x_113 = x_141;
x_114 = x_142;
x_115 = x_143;
x_116 = x_144;
x_117 = x_145;
x_118 = x_146;
goto block_132;
}
else
{
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_140);
lean_dec_ref(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec_ref(x_133);
return x_147;
}
}
}
block_165:
{
uint8_t x_163; lean_object* x_164; 
x_163 = 1;
lean_inc(x_155);
lean_inc_ref(x_156);
lean_inc(x_149);
lean_inc_ref(x_152);
lean_inc(x_160);
lean_inc_ref(x_151);
lean_inc(x_150);
lean_inc_ref(x_161);
lean_inc(x_157);
lean_inc(x_153);
lean_inc_ref(x_158);
lean_inc_ref(x_162);
x_164 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(x_3, x_4, x_2, x_1, x_24, x_21, x_162, x_158, x_163, x_153, x_157, x_161, x_150, x_151, x_160, x_152, x_149, x_156, x_155);
if (lean_obj_tag(x_164) == 0)
{
lean_dec_ref(x_164);
x_133 = x_158;
x_134 = x_159;
x_135 = x_154;
x_136 = x_162;
x_137 = x_153;
x_138 = x_157;
x_139 = x_161;
x_140 = x_150;
x_141 = x_151;
x_142 = x_160;
x_143 = x_152;
x_144 = x_149;
x_145 = x_156;
x_146 = x_155;
goto block_148;
}
else
{
lean_dec_ref(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec(x_149);
return x_164;
}
}
block_181:
{
lean_object* x_180; 
lean_inc(x_172);
lean_inc_ref(x_173);
lean_inc(x_166);
lean_inc_ref(x_169);
lean_inc(x_177);
lean_inc_ref(x_168);
lean_inc(x_167);
lean_inc_ref(x_178);
lean_inc(x_174);
lean_inc(x_170);
lean_inc_ref(x_179);
lean_inc_ref(x_175);
x_180 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(x_3, x_4, x_1, x_2, x_21, x_24, x_175, x_179, x_27, x_170, x_174, x_178, x_167, x_168, x_177, x_169, x_166, x_173, x_172);
if (lean_obj_tag(x_180) == 0)
{
lean_dec_ref(x_180);
x_133 = x_175;
x_134 = x_176;
x_135 = x_171;
x_136 = x_179;
x_137 = x_170;
x_138 = x_174;
x_139 = x_178;
x_140 = x_167;
x_141 = x_168;
x_142 = x_177;
x_143 = x_169;
x_144 = x_166;
x_145 = x_173;
x_146 = x_172;
goto block_148;
}
else
{
lean_dec_ref(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec_ref(x_175);
lean_dec(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec(x_170);
lean_dec_ref(x_169);
lean_dec_ref(x_168);
lean_dec(x_167);
lean_dec(x_166);
return x_180;
}
}
block_197:
{
if (x_196 == 0)
{
x_166 = x_182;
x_167 = x_183;
x_168 = x_184;
x_169 = x_185;
x_170 = x_186;
x_171 = x_187;
x_172 = x_188;
x_173 = x_189;
x_174 = x_190;
x_175 = x_191;
x_176 = x_192;
x_177 = x_193;
x_178 = x_194;
x_179 = x_195;
goto block_181;
}
else
{
x_149 = x_182;
x_150 = x_183;
x_151 = x_184;
x_152 = x_185;
x_153 = x_186;
x_154 = x_187;
x_155 = x_188;
x_156 = x_189;
x_157 = x_190;
x_158 = x_191;
x_159 = x_192;
x_160 = x_193;
x_161 = x_194;
x_162 = x_195;
goto block_165;
}
}
block_217:
{
uint8_t x_216; 
x_216 = lean_nat_dec_lt(x_213, x_208);
lean_dec(x_208);
lean_dec(x_213);
if (x_216 == 0)
{
x_182 = x_198;
x_183 = x_199;
x_184 = x_200;
x_185 = x_201;
x_186 = x_202;
x_187 = x_203;
x_188 = x_204;
x_189 = x_205;
x_190 = x_206;
x_191 = x_207;
x_192 = x_209;
x_193 = x_210;
x_194 = x_211;
x_195 = x_212;
x_196 = x_27;
goto block_197;
}
else
{
if (x_214 == 0)
{
if (x_216 == 0)
{
x_182 = x_198;
x_183 = x_199;
x_184 = x_200;
x_185 = x_201;
x_186 = x_202;
x_187 = x_203;
x_188 = x_204;
x_189 = x_205;
x_190 = x_206;
x_191 = x_207;
x_192 = x_209;
x_193 = x_210;
x_194 = x_211;
x_195 = x_212;
x_196 = x_27;
goto block_197;
}
else
{
if (x_215 == 0)
{
x_182 = x_198;
x_183 = x_199;
x_184 = x_200;
x_185 = x_201;
x_186 = x_202;
x_187 = x_203;
x_188 = x_204;
x_189 = x_205;
x_190 = x_206;
x_191 = x_207;
x_192 = x_209;
x_193 = x_210;
x_194 = x_211;
x_195 = x_212;
x_196 = x_216;
goto block_197;
}
else
{
x_166 = x_198;
x_167 = x_199;
x_168 = x_200;
x_169 = x_201;
x_170 = x_202;
x_171 = x_203;
x_172 = x_204;
x_173 = x_205;
x_174 = x_206;
x_175 = x_207;
x_176 = x_209;
x_177 = x_210;
x_178 = x_211;
x_179 = x_212;
goto block_181;
}
}
}
else
{
x_182 = x_198;
x_183 = x_199;
x_184 = x_200;
x_185 = x_201;
x_186 = x_202;
x_187 = x_203;
x_188 = x_204;
x_189 = x_205;
x_190 = x_206;
x_191 = x_207;
x_192 = x_209;
x_193 = x_210;
x_194 = x_211;
x_195 = x_212;
x_196 = x_27;
goto block_197;
}
}
}
block_242:
{
if (x_232 == 0)
{
uint8_t x_233; 
x_233 = lean_ctor_get_uint8(x_227, sizeof(void*)*11 + 2);
if (x_233 == 0)
{
if (x_27 == 0)
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; uint8_t x_237; 
x_234 = lean_ctor_get(x_227, 6);
lean_inc(x_234);
x_235 = lean_ctor_get(x_231, 6);
lean_inc(x_235);
x_236 = lean_ctor_get_uint8(x_231, sizeof(void*)*11 + 1);
x_237 = lean_ctor_get_uint8(x_231, sizeof(void*)*11 + 2);
x_198 = x_218;
x_199 = x_219;
x_200 = x_220;
x_201 = x_221;
x_202 = x_222;
x_203 = x_223;
x_204 = x_224;
x_205 = x_225;
x_206 = x_226;
x_207 = x_227;
x_208 = x_234;
x_209 = x_228;
x_210 = x_229;
x_211 = x_230;
x_212 = x_231;
x_213 = x_235;
x_214 = x_236;
x_215 = x_237;
goto block_217;
}
else
{
x_149 = x_218;
x_150 = x_219;
x_151 = x_220;
x_152 = x_221;
x_153 = x_222;
x_154 = x_223;
x_155 = x_224;
x_156 = x_225;
x_157 = x_226;
x_158 = x_227;
x_159 = x_228;
x_160 = x_229;
x_161 = x_230;
x_162 = x_231;
goto block_165;
}
}
else
{
uint8_t x_238; 
x_238 = lean_ctor_get_uint8(x_231, sizeof(void*)*11 + 2);
if (x_238 == 0)
{
x_149 = x_218;
x_150 = x_219;
x_151 = x_220;
x_152 = x_221;
x_153 = x_222;
x_154 = x_223;
x_155 = x_224;
x_156 = x_225;
x_157 = x_226;
x_158 = x_227;
x_159 = x_228;
x_160 = x_229;
x_161 = x_230;
x_162 = x_231;
goto block_165;
}
else
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_239 = lean_ctor_get(x_227, 6);
lean_inc(x_239);
x_240 = lean_ctor_get(x_231, 6);
lean_inc(x_240);
x_241 = lean_ctor_get_uint8(x_231, sizeof(void*)*11 + 1);
x_198 = x_218;
x_199 = x_219;
x_200 = x_220;
x_201 = x_221;
x_202 = x_222;
x_203 = x_223;
x_204 = x_224;
x_205 = x_225;
x_206 = x_226;
x_207 = x_227;
x_208 = x_239;
x_209 = x_228;
x_210 = x_229;
x_211 = x_230;
x_212 = x_231;
x_213 = x_240;
x_214 = x_241;
x_215 = x_238;
goto block_217;
}
}
}
else
{
x_149 = x_218;
x_150 = x_219;
x_151 = x_220;
x_152 = x_221;
x_153 = x_222;
x_154 = x_223;
x_155 = x_224;
x_156 = x_225;
x_157 = x_226;
x_158 = x_227;
x_159 = x_228;
x_160 = x_229;
x_161 = x_230;
x_162 = x_231;
goto block_165;
}
}
block_259:
{
if (x_244 == 0)
{
x_218 = x_255;
x_219 = x_251;
x_220 = x_252;
x_221 = x_254;
x_222 = x_248;
x_223 = x_246;
x_224 = x_257;
x_225 = x_256;
x_226 = x_249;
x_227 = x_243;
x_228 = x_247;
x_229 = x_253;
x_230 = x_250;
x_231 = x_245;
x_232 = x_27;
goto block_242;
}
else
{
uint8_t x_258; 
x_258 = lean_ctor_get_uint8(x_245, sizeof(void*)*11 + 1);
if (x_258 == 0)
{
x_149 = x_255;
x_150 = x_251;
x_151 = x_252;
x_152 = x_254;
x_153 = x_248;
x_154 = x_246;
x_155 = x_257;
x_156 = x_256;
x_157 = x_249;
x_158 = x_243;
x_159 = x_247;
x_160 = x_253;
x_161 = x_250;
x_162 = x_245;
goto block_165;
}
else
{
x_218 = x_255;
x_219 = x_251;
x_220 = x_252;
x_221 = x_254;
x_222 = x_248;
x_223 = x_246;
x_224 = x_257;
x_225 = x_256;
x_226 = x_249;
x_227 = x_243;
x_228 = x_247;
x_229 = x_253;
x_230 = x_250;
x_231 = x_245;
x_232 = x_27;
goto block_242;
}
}
}
block_275:
{
uint8_t x_274; 
x_274 = lean_ctor_get_uint8(x_260, sizeof(void*)*11 + 1);
x_243 = x_260;
x_244 = x_274;
x_245 = x_261;
x_246 = x_262;
x_247 = x_263;
x_248 = x_264;
x_249 = x_265;
x_250 = x_266;
x_251 = x_267;
x_252 = x_268;
x_253 = x_269;
x_254 = x_270;
x_255 = x_271;
x_256 = x_272;
x_257 = x_273;
goto block_259;
}
block_290:
{
lean_object* x_289; 
x_289 = l_Lean_Meta_Grind_markAsInconsistent___redArg(x_280, x_287, x_286, x_277, x_278);
if (lean_obj_tag(x_289) == 0)
{
lean_dec_ref(x_289);
x_260 = x_282;
x_261 = x_285;
x_262 = x_276;
x_263 = x_27;
x_264 = x_280;
x_265 = x_288;
x_266 = x_281;
x_267 = x_284;
x_268 = x_283;
x_269 = x_279;
x_270 = x_287;
x_271 = x_286;
x_272 = x_277;
x_273 = x_278;
goto block_275;
}
else
{
lean_dec(x_288);
lean_dec_ref(x_287);
lean_dec(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec_ref(x_282);
lean_dec_ref(x_281);
lean_dec(x_280);
lean_dec(x_279);
lean_dec(x_278);
lean_dec_ref(x_277);
lean_dec(x_24);
lean_dec(x_21);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_289;
}
}
block_319:
{
if (x_295 == 0)
{
lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_ctor_get(x_298, 0);
x_306 = lean_ctor_get_uint8(x_298, sizeof(void*)*11 + 1);
x_307 = lean_ctor_get(x_301, 0);
lean_inc(x_293);
lean_inc_ref(x_292);
lean_inc(x_302);
lean_inc_ref(x_303);
lean_inc_ref(x_307);
lean_inc_ref(x_305);
x_308 = l_Lean_Meta_Grind_hasSameType(x_305, x_307, x_303, x_302, x_292, x_293);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; uint8_t x_310; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
lean_dec_ref(x_308);
x_310 = lean_unbox(x_309);
lean_dec(x_309);
if (x_310 == 0)
{
x_243 = x_298;
x_244 = x_306;
x_245 = x_301;
x_246 = x_27;
x_247 = x_27;
x_248 = x_296;
x_249 = x_304;
x_250 = x_297;
x_251 = x_300;
x_252 = x_299;
x_253 = x_294;
x_254 = x_303;
x_255 = x_302;
x_256 = x_292;
x_257 = x_293;
goto block_259;
}
else
{
x_243 = x_298;
x_244 = x_306;
x_245 = x_301;
x_246 = x_27;
x_247 = x_291;
x_248 = x_296;
x_249 = x_304;
x_250 = x_297;
x_251 = x_300;
x_252 = x_299;
x_253 = x_294;
x_254 = x_303;
x_255 = x_302;
x_256 = x_292;
x_257 = x_293;
goto block_259;
}
}
else
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; uint8_t x_318; 
lean_dec(x_304);
lean_dec_ref(x_303);
lean_dec(x_302);
lean_dec_ref(x_301);
lean_dec(x_300);
lean_dec_ref(x_299);
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec(x_296);
lean_dec(x_294);
lean_dec(x_293);
lean_dec_ref(x_292);
lean_dec(x_24);
lean_dec(x_21);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_311 = lean_ctor_get(x_308, 0);
x_318 = !lean_is_exclusive(x_308);
if (x_318 == 0)
{
x_312 = x_308;
x_313 = x_318;
goto block_317;
}
else
{
lean_inc(x_311);
lean_dec(x_308);
x_312 = lean_box(0);
x_313 = x_318;
goto block_317;
}
block_317:
{
lean_object* x_314; 
if (x_313 == 0)
{
x_314 = x_312;
goto block_315;
}
else
{
lean_object* x_316; 
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_311);
x_314 = x_316;
goto block_315;
}
block_315:
{
return x_314;
}
}
}
}
else
{
x_260 = x_298;
x_261 = x_301;
x_262 = x_27;
x_263 = x_291;
x_264 = x_296;
x_265 = x_304;
x_266 = x_297;
x_267 = x_300;
x_268 = x_299;
x_269 = x_294;
x_270 = x_303;
x_271 = x_302;
x_272 = x_292;
x_273 = x_293;
goto block_275;
}
}
block_338:
{
if (x_332 == 0)
{
x_260 = x_325;
x_261 = x_329;
x_262 = x_27;
x_263 = x_27;
x_264 = x_323;
x_265 = x_330;
x_266 = x_324;
x_267 = x_327;
x_268 = x_326;
x_269 = x_322;
x_270 = x_331;
x_271 = x_328;
x_272 = x_320;
x_273 = x_321;
goto block_275;
}
else
{
uint8_t x_333; 
lean_inc_ref(x_25);
x_333 = l_Lean_Expr_isTrue(x_25);
if (x_333 == 0)
{
uint8_t x_334; 
lean_inc_ref(x_26);
x_334 = l_Lean_Expr_isTrue(x_26);
if (x_334 == 0)
{
if (x_4 == 0)
{
uint8_t x_335; 
x_335 = lean_ctor_get_uint8(x_325, sizeof(void*)*11 + 4);
if (x_335 == 0)
{
uint8_t x_336; 
x_336 = lean_ctor_get_uint8(x_329, sizeof(void*)*11 + 4);
if (x_336 == 0)
{
uint8_t x_337; 
x_337 = lean_ctor_get_uint8(x_325, sizeof(void*)*11 + 1);
x_243 = x_325;
x_244 = x_337;
x_245 = x_329;
x_246 = x_27;
x_247 = x_332;
x_248 = x_323;
x_249 = x_330;
x_250 = x_324;
x_251 = x_327;
x_252 = x_326;
x_253 = x_322;
x_254 = x_331;
x_255 = x_328;
x_256 = x_320;
x_257 = x_321;
goto block_259;
}
else
{
x_291 = x_332;
x_292 = x_320;
x_293 = x_321;
x_294 = x_322;
x_295 = x_334;
x_296 = x_323;
x_297 = x_324;
x_298 = x_325;
x_299 = x_326;
x_300 = x_327;
x_301 = x_329;
x_302 = x_328;
x_303 = x_331;
x_304 = x_330;
goto block_319;
}
}
else
{
x_291 = x_332;
x_292 = x_320;
x_293 = x_321;
x_294 = x_322;
x_295 = x_334;
x_296 = x_323;
x_297 = x_324;
x_298 = x_325;
x_299 = x_326;
x_300 = x_327;
x_301 = x_329;
x_302 = x_328;
x_303 = x_331;
x_304 = x_330;
goto block_319;
}
}
else
{
x_291 = x_332;
x_292 = x_320;
x_293 = x_321;
x_294 = x_322;
x_295 = x_334;
x_296 = x_323;
x_297 = x_324;
x_298 = x_325;
x_299 = x_326;
x_300 = x_327;
x_301 = x_329;
x_302 = x_328;
x_303 = x_331;
x_304 = x_330;
goto block_319;
}
}
else
{
x_276 = x_332;
x_277 = x_320;
x_278 = x_321;
x_279 = x_322;
x_280 = x_323;
x_281 = x_324;
x_282 = x_325;
x_283 = x_326;
x_284 = x_327;
x_285 = x_329;
x_286 = x_328;
x_287 = x_331;
x_288 = x_330;
goto block_290;
}
}
else
{
x_276 = x_332;
x_277 = x_320;
x_278 = x_321;
x_279 = x_322;
x_280 = x_323;
x_281 = x_324;
x_282 = x_325;
x_283 = x_326;
x_284 = x_327;
x_285 = x_329;
x_286 = x_328;
x_287 = x_331;
x_288 = x_330;
goto block_290;
}
}
}
block_374:
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_st_ref_get(x_339);
lean_inc_ref(x_25);
x_350 = l_Lean_Meta_Grind_Goal_getENode(x_349, x_25, x_345, x_346, x_347, x_348);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
lean_dec_ref(x_350);
x_352 = lean_st_ref_get(x_339);
lean_inc_ref(x_26);
x_353 = l_Lean_Meta_Grind_Goal_getENode(x_352, x_26, x_345, x_346, x_347, x_348);
if (lean_obj_tag(x_353) == 0)
{
uint8_t x_354; 
x_354 = lean_ctor_get_uint8(x_351, sizeof(void*)*11 + 1);
if (x_354 == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_353, 0);
lean_inc(x_355);
lean_dec_ref(x_353);
x_320 = x_347;
x_321 = x_348;
x_322 = x_344;
x_323 = x_339;
x_324 = x_341;
x_325 = x_351;
x_326 = x_343;
x_327 = x_342;
x_328 = x_346;
x_329 = x_355;
x_330 = x_340;
x_331 = x_345;
x_332 = x_27;
goto block_338;
}
else
{
lean_object* x_356; uint8_t x_357; 
x_356 = lean_ctor_get(x_353, 0);
lean_inc(x_356);
lean_dec_ref(x_353);
x_357 = lean_ctor_get_uint8(x_356, sizeof(void*)*11 + 1);
x_320 = x_347;
x_321 = x_348;
x_322 = x_344;
x_323 = x_339;
x_324 = x_341;
x_325 = x_351;
x_326 = x_343;
x_327 = x_342;
x_328 = x_346;
x_329 = x_356;
x_330 = x_340;
x_331 = x_345;
x_332 = x_357;
goto block_338;
}
}
else
{
lean_object* x_358; lean_object* x_359; uint8_t x_360; uint8_t x_365; 
lean_dec(x_351);
lean_dec(x_348);
lean_dec_ref(x_347);
lean_dec(x_346);
lean_dec_ref(x_345);
lean_dec(x_344);
lean_dec_ref(x_343);
lean_dec(x_342);
lean_dec_ref(x_341);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_24);
lean_dec(x_21);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_358 = lean_ctor_get(x_353, 0);
x_365 = !lean_is_exclusive(x_353);
if (x_365 == 0)
{
x_359 = x_353;
x_360 = x_365;
goto block_364;
}
else
{
lean_inc(x_358);
lean_dec(x_353);
x_359 = lean_box(0);
x_360 = x_365;
goto block_364;
}
block_364:
{
lean_object* x_361; 
if (x_360 == 0)
{
x_361 = x_359;
goto block_362;
}
else
{
lean_object* x_363; 
x_363 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_363, 0, x_358);
x_361 = x_363;
goto block_362;
}
block_362:
{
return x_361;
}
}
}
}
else
{
lean_object* x_366; lean_object* x_367; uint8_t x_368; uint8_t x_373; 
lean_dec(x_348);
lean_dec_ref(x_347);
lean_dec(x_346);
lean_dec_ref(x_345);
lean_dec(x_344);
lean_dec_ref(x_343);
lean_dec(x_342);
lean_dec_ref(x_341);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_24);
lean_dec(x_21);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_366 = lean_ctor_get(x_350, 0);
x_373 = !lean_is_exclusive(x_350);
if (x_373 == 0)
{
x_367 = x_350;
x_368 = x_373;
goto block_372;
}
else
{
lean_inc(x_366);
lean_dec(x_350);
x_367 = lean_box(0);
x_368 = x_373;
goto block_372;
}
block_372:
{
lean_object* x_369; 
if (x_368 == 0)
{
x_369 = x_367;
goto block_370;
}
else
{
lean_object* x_371; 
x_371 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_371, 0, x_366);
x_369 = x_371;
goto block_370;
}
block_370:
{
return x_369;
}
}
}
}
block_388:
{
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
lean_dec_ref(x_376);
x_378 = l_Lean_MessageData_ofExpr(x_377);
x_379 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(x_375, x_378, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_379) == 0)
{
lean_dec_ref(x_379);
x_339 = x_5;
x_340 = x_6;
x_341 = x_7;
x_342 = x_8;
x_343 = x_9;
x_344 = x_10;
x_345 = x_11;
x_346 = x_12;
x_347 = x_13;
x_348 = x_14;
goto block_374;
}
else
{
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint8_t x_387; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_380 = lean_ctor_get(x_376, 0);
x_387 = !lean_is_exclusive(x_376);
if (x_387 == 0)
{
x_381 = x_376;
x_382 = x_387;
goto block_386;
}
else
{
lean_inc(x_380);
lean_dec(x_376);
x_381 = lean_box(0);
x_382 = x_387;
goto block_386;
}
block_386:
{
lean_object* x_383; 
if (x_382 == 0)
{
x_383 = x_381;
goto block_384;
}
else
{
lean_object* x_385; 
x_385 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_385, 0, x_380);
x_383 = x_385;
goto block_384;
}
block_384:
{
return x_383;
}
}
}
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec_ref(x_3);
x_395 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
x_396 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(x_395, x_13);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
lean_dec_ref(x_396);
x_398 = lean_unbox(x_397);
lean_dec(x_397);
if (x_398 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_18;
}
else
{
lean_object* x_399; 
x_399 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; 
lean_dec_ref(x_399);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_400 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_1, x_5, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec_ref(x_400);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_402 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_2, x_5, x_11, x_12, x_13, x_14);
lean_dec(x_5);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
lean_dec_ref(x_402);
x_404 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5);
x_405 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_405, 0, x_401);
lean_ctor_set(x_405, 1, x_404);
x_406 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_403);
x_407 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7);
x_408 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
x_409 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(x_395, x_408, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_409) == 0)
{
lean_dec_ref(x_409);
goto block_18;
}
else
{
return x_409;
}
}
else
{
lean_object* x_410; lean_object* x_411; uint8_t x_412; uint8_t x_417; 
lean_dec(x_401);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_410 = lean_ctor_get(x_402, 0);
x_417 = !lean_is_exclusive(x_402);
if (x_417 == 0)
{
x_411 = x_402;
x_412 = x_417;
goto block_416;
}
else
{
lean_inc(x_410);
lean_dec(x_402);
x_411 = lean_box(0);
x_412 = x_417;
goto block_416;
}
block_416:
{
lean_object* x_413; 
if (x_412 == 0)
{
x_413 = x_411;
goto block_414;
}
else
{
lean_object* x_415; 
x_415 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_415, 0, x_410);
x_413 = x_415;
goto block_414;
}
block_414:
{
return x_413;
}
}
}
}
else
{
lean_object* x_418; lean_object* x_419; uint8_t x_420; uint8_t x_425; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_5);
lean_dec_ref(x_2);
x_418 = lean_ctor_get(x_400, 0);
x_425 = !lean_is_exclusive(x_400);
if (x_425 == 0)
{
x_419 = x_400;
x_420 = x_425;
goto block_424;
}
else
{
lean_inc(x_418);
lean_dec(x_400);
x_419 = lean_box(0);
x_420 = x_425;
goto block_424;
}
block_424:
{
lean_object* x_421; 
if (x_420 == 0)
{
x_421 = x_419;
goto block_422;
}
else
{
lean_object* x_423; 
x_423 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_423, 0, x_418);
x_421 = x_423;
goto block_422;
}
block_422:
{
return x_421;
}
}
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_399;
}
}
}
}
else
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; uint8_t x_433; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_426 = lean_ctor_get(x_23, 0);
x_433 = !lean_is_exclusive(x_23);
if (x_433 == 0)
{
x_427 = x_23;
x_428 = x_433;
goto block_432;
}
else
{
lean_inc(x_426);
lean_dec(x_23);
x_427 = lean_box(0);
x_428 = x_433;
goto block_432;
}
block_432:
{
lean_object* x_429; 
if (x_428 == 0)
{
x_429 = x_427;
goto block_430;
}
else
{
lean_object* x_431; 
x_431 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_431, 0, x_426);
x_429 = x_431;
goto block_430;
}
block_430:
{
return x_429;
}
}
}
}
else
{
lean_object* x_434; lean_object* x_435; uint8_t x_436; uint8_t x_441; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_434 = lean_ctor_get(x_20, 0);
x_441 = !lean_is_exclusive(x_20);
if (x_441 == 0)
{
x_435 = x_20;
x_436 = x_441;
goto block_440;
}
else
{
lean_inc(x_434);
lean_dec(x_20);
x_435 = lean_box(0);
x_436 = x_441;
goto block_440;
}
block_440:
{
lean_object* x_437; 
if (x_436 == 0)
{
x_437 = x_435;
goto block_438;
}
else
{
lean_object* x_439; 
x_439 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_439, 0, x_434);
x_437 = x_439;
goto block_438;
}
block_438:
{
return x_437;
}
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
x_17 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_42; 
x_3 = lean_st_ref_take(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
x_6 = x_3;
x_7 = x_42;
goto block_41;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_39; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 2);
x_11 = lean_ctor_get(x_4, 3);
x_12 = lean_ctor_get(x_4, 4);
x_13 = lean_ctor_get(x_4, 5);
x_14 = lean_ctor_get(x_4, 6);
x_15 = lean_ctor_get(x_4, 7);
x_16 = lean_ctor_get_uint8(x_4, sizeof(void*)*18);
x_17 = lean_ctor_get(x_4, 9);
x_18 = lean_ctor_get(x_4, 10);
x_19 = lean_ctor_get(x_4, 11);
x_20 = lean_ctor_get(x_4, 12);
x_21 = lean_ctor_get(x_4, 13);
x_22 = lean_ctor_get(x_4, 14);
x_23 = lean_ctor_get(x_4, 15);
x_24 = lean_ctor_get(x_4, 16);
x_25 = lean_ctor_get(x_4, 17);
x_39 = !lean_is_exclusive(x_4);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_4, 8);
lean_dec(x_40);
x_26 = x_4;
x_27 = x_39;
goto block_38;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_26 = lean_box(0);
x_27 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_28; lean_object* x_29; 
x_28 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (x_27 == 0)
{
lean_ctor_set(x_26, 8, x_28);
x_29 = x_26;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_9);
lean_ctor_set(x_37, 2, x_10);
lean_ctor_set(x_37, 3, x_11);
lean_ctor_set(x_37, 4, x_12);
lean_ctor_set(x_37, 5, x_13);
lean_ctor_set(x_37, 6, x_14);
lean_ctor_set(x_37, 7, x_15);
lean_ctor_set(x_37, 8, x_28);
lean_ctor_set(x_37, 9, x_17);
lean_ctor_set(x_37, 10, x_18);
lean_ctor_set(x_37, 11, x_19);
lean_ctor_set(x_37, 12, x_20);
lean_ctor_set(x_37, 13, x_21);
lean_ctor_set(x_37, 14, x_22);
lean_ctor_set(x_37, 15, x_23);
lean_ctor_set(x_37, 16, x_24);
lean_ctor_set(x_37, 17, x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*18, x_16);
x_29 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_30; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_29);
x_30 = x_6;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_5);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_st_ref_set(x_1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 8);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
x_9 = lean_nat_dec_lt(x_8, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_52; 
x_12 = lean_st_ref_take(x_1);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_12, 1);
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
x_15 = x_12;
x_16 = x_52;
goto block_51;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_50; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
x_19 = lean_ctor_get(x_13, 2);
x_20 = lean_ctor_get(x_13, 3);
x_21 = lean_ctor_get(x_13, 4);
x_22 = lean_ctor_get(x_13, 5);
x_23 = lean_ctor_get(x_13, 6);
x_24 = lean_ctor_get(x_13, 7);
x_25 = lean_ctor_get(x_13, 8);
x_26 = lean_ctor_get_uint8(x_13, sizeof(void*)*18);
x_27 = lean_ctor_get(x_13, 9);
x_28 = lean_ctor_get(x_13, 10);
x_29 = lean_ctor_get(x_13, 11);
x_30 = lean_ctor_get(x_13, 12);
x_31 = lean_ctor_get(x_13, 13);
x_32 = lean_ctor_get(x_13, 14);
x_33 = lean_ctor_get(x_13, 15);
x_34 = lean_ctor_get(x_13, 16);
x_35 = lean_ctor_get(x_13, 17);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
x_36 = x_13;
x_37 = x_50;
goto block_49;
}
else
{
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_36 = lean_box(0);
x_37 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_array_pop(x_25);
if (x_37 == 0)
{
lean_ctor_set(x_36, 8, x_38);
x_39 = x_36;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set(x_48, 1, x_18);
lean_ctor_set(x_48, 2, x_19);
lean_ctor_set(x_48, 3, x_20);
lean_ctor_set(x_48, 4, x_21);
lean_ctor_set(x_48, 5, x_22);
lean_ctor_set(x_48, 6, x_23);
lean_ctor_set(x_48, 7, x_24);
lean_ctor_set(x_48, 8, x_38);
lean_ctor_set(x_48, 9, x_27);
lean_ctor_set(x_48, 10, x_28);
lean_ctor_set(x_48, 11, x_29);
lean_ctor_set(x_48, 12, x_30);
lean_ctor_set(x_48, 13, x_31);
lean_ctor_set(x_48, 14, x_32);
lean_ctor_set(x_48, 15, x_33);
lean_ctor_set(x_48, 16, x_34);
lean_ctor_set(x_48, 17, x_35);
lean_ctor_set_uint8(x_48, sizeof(void*)*18, x_26);
x_39 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_40; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_39);
x_40 = x_15;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_14);
x_40 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_st_ref_set(x_1, x_40);
x_42 = lean_array_fget(x_5, x_8);
lean_dec(x_8);
lean_dec_ref(x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
x_17 = lean_grind_process_new_facts(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
x_17 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = 0;
x_16 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(x_1, x_2, x_3, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = 1;
x_16 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(x_1, x_2, x_3, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_43; 
x_4 = lean_st_ref_take(x_2);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_43 = !lean_is_exclusive(x_4);
if (x_43 == 0)
{
x_7 = x_4;
x_8 = x_43;
goto block_42;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_41; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_5, 2);
x_12 = lean_ctor_get(x_5, 3);
x_13 = lean_ctor_get(x_5, 4);
x_14 = lean_ctor_get(x_5, 5);
x_15 = lean_ctor_get(x_5, 6);
x_16 = lean_ctor_get(x_5, 7);
x_17 = lean_ctor_get(x_5, 8);
x_18 = lean_ctor_get_uint8(x_5, sizeof(void*)*18);
x_19 = lean_ctor_get(x_5, 9);
x_20 = lean_ctor_get(x_5, 10);
x_21 = lean_ctor_get(x_5, 11);
x_22 = lean_ctor_get(x_5, 12);
x_23 = lean_ctor_get(x_5, 13);
x_24 = lean_ctor_get(x_5, 14);
x_25 = lean_ctor_get(x_5, 15);
x_26 = lean_ctor_get(x_5, 16);
x_27 = lean_ctor_get(x_5, 17);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
x_28 = x_5;
x_29 = x_41;
goto block_40;
}
else
{
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_28 = lean_box(0);
x_29 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_PersistentArray_push___redArg(x_21, x_1);
if (x_29 == 0)
{
lean_ctor_set(x_28, 11, x_30);
x_31 = x_28;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_39, 0, x_9);
lean_ctor_set(x_39, 1, x_10);
lean_ctor_set(x_39, 2, x_11);
lean_ctor_set(x_39, 3, x_12);
lean_ctor_set(x_39, 4, x_13);
lean_ctor_set(x_39, 5, x_14);
lean_ctor_set(x_39, 6, x_15);
lean_ctor_set(x_39, 7, x_16);
lean_ctor_set(x_39, 8, x_17);
lean_ctor_set(x_39, 9, x_19);
lean_ctor_set(x_39, 10, x_20);
lean_ctor_set(x_39, 11, x_30);
lean_ctor_set(x_39, 12, x_22);
lean_ctor_set(x_39, 13, x_23);
lean_ctor_set(x_39, 14, x_24);
lean_ctor_set(x_39, 15, x_25);
lean_ctor_set(x_39, 16, x_26);
lean_ctor_set(x_39, 17, x_27);
lean_ctor_set_uint8(x_39, sizeof(void*)*18, x_18);
x_31 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_32; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_31);
x_32 = x_7;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_6);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_st_ref_set(x_2, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(x_1, x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_mkEq(x_1, x_2, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_28; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_17);
x_18 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(x_17, x_5);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_18, 0);
lean_dec(x_29);
x_19 = x_18;
x_20 = x_28;
goto block_27;
}
else
{
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_21; 
if (x_20 == 0)
{
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_17);
x_21 = x_19;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_17);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_21);
lean_inc(x_4);
lean_inc_ref(x_1);
x_22 = lean_grind_internalize(x_1, x_4, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec_ref(x_22);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_23 = lean_grind_internalize(x_2, x_4, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec_ref(x_23);
x_24 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_24;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_23;
}
}
else
{
lean_dec_ref(x_21);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_22;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_16, 0);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
x_31 = x_16;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_16);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_addNewEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_3);
x_17 = lean_grind_internalize(x_3, x_2, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_17);
if (x_4 == 0)
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_20 = l_Lean_Meta_mkEqTrue(x_1, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_3, x_19, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_23 = lean_ctor_get(x_20, 0);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
x_24 = x_20;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_31 = lean_ctor_get(x_18, 0);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
x_32 = x_18;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_39; 
x_39 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_9);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_41 = l_Lean_Meta_mkEqFalse(x_1, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_3, x_40, x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_dec(x_40);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_44 = lean_ctor_get(x_41, 0);
x_51 = !lean_is_exclusive(x_41);
if (x_51 == 0)
{
x_45 = x_41;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_52 = lean_ctor_get(x_39, 0);
x_59 = !lean_is_exclusive(x_39);
if (x_59 == 0)
{
x_53 = x_39;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_39);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
x_17 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (x_6 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_3);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_ref(x_19);
lean_inc(x_2);
lean_inc_ref(x_4);
x_20 = lean_grind_internalize(x_4, x_2, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec_ref(x_20);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_ref(x_5);
x_21 = lean_grind_internalize(x_5, x_2, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec_ref(x_21);
x_22 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_22;
}
else
{
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_21;
}
}
else
{
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_23 = lean_box(0);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_ref(x_3);
x_24 = lean_grind_internalize(x_3, x_2, x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec_ref(x_24);
x_25 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
x_27 = l_Lean_Meta_mkEqFalse(x_1, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_3, x_26, x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
x_30 = lean_ctor_get(x_27, 0);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
x_31 = x_27;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_25, 0);
x_45 = !lean_is_exclusive(x_25);
if (x_45 == 0)
{
x_39 = x_25;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_6);
x_20 = lean_unbox(x_7);
x_21 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(x_1, x_2, x_3, x_4, x_5, x_19, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc_ref(x_3);
x_16 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_3, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Expr_cleanupAnnotations(x_17);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec_ref(x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_22);
lean_dec_ref(x_21);
x_24 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_25);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_21);
x_28 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_29);
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_31 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
x_32 = l_Lean_Expr_isConstOf(x_30, x_31);
if (x_32 == 0)
{
uint8_t x_33; 
lean_dec_ref(x_25);
x_33 = l_Lean_Expr_isApp(x_30);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_21);
x_34 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_36 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
x_37 = l_Lean_Expr_isConstOf(x_35, x_36);
lean_dec_ref(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec_ref(x_29);
lean_dec_ref(x_21);
x_38 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(x_1, x_2, x_3, x_29, x_21, x_4, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec_ref(x_30);
x_40 = l_Lean_Expr_isProp(x_29);
lean_dec_ref(x_29);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(x_1, x_2, x_3, x_25, x_21, x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_41;
}
else
{
lean_object* x_42; 
lean_dec_ref(x_25);
lean_dec_ref(x_21);
x_42 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_42;
}
}
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_16, 0);
x_50 = !lean_is_exclusive(x_16);
if (x_50 == 0)
{
x_44 = x_16;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_16);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
x_17 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc_ref(x_1);
x_46 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(x_1, x_4);
lean_dec_ref(x_46);
x_47 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
x_48 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(x_47, x_12);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
x_35 = x_11;
x_36 = x_12;
x_37 = x_13;
goto block_45;
}
else
{
lean_object* x_51; 
x_51 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_51);
lean_inc_ref(x_1);
x_52 = l_Lean_MessageData_ofExpr(x_1);
x_53 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(x_47, x_52, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
x_35 = x_11;
x_36 = x_12;
x_37 = x_13;
goto block_45;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_53;
}
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_51;
}
}
block_27:
{
uint8_t x_25; lean_object* x_26; 
x_25 = 0;
x_26 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(x_2, x_3, x_1, x_25, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_26;
}
block_45:
{
lean_object* x_38; uint8_t x_39; 
lean_inc_ref(x_1);
x_38 = l_Lean_Expr_cleanupAnnotations(x_1);
x_39 = l_Lean_Expr_isApp(x_38);
if (x_39 == 0)
{
lean_dec_ref(x_38);
x_15 = x_28;
x_16 = x_29;
x_17 = x_30;
x_18 = x_31;
x_19 = x_32;
x_20 = x_33;
x_21 = x_34;
x_22 = x_35;
x_23 = x_36;
x_24 = x_37;
goto block_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc_ref(x_40);
x_41 = l_Lean_Expr_appFnCleanup___redArg(x_38);
x_42 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
x_43 = l_Lean_Expr_isConstOf(x_41, x_42);
lean_dec_ref(x_41);
if (x_43 == 0)
{
lean_dec_ref(x_40);
x_15 = x_28;
x_16 = x_29;
x_17 = x_30;
x_18 = x_31;
x_19 = x_32;
x_20 = x_33;
x_21 = x_34;
x_22 = x_35;
x_23 = x_36;
x_24 = x_37;
goto block_27;
}
else
{
lean_object* x_44; 
lean_dec_ref(x_1);
x_44 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(x_2, x_3, x_40, x_43, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_isInconsistent___redArg(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0));
x_16 = l_Lean_Core_checkSystem(x_15, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
x_17 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_54; 
x_18 = lean_ctor_get(x_17, 0);
x_54 = !lean_is_exclusive(x_17);
if (x_54 == 0)
{
x_19 = x_17;
x_20 = x_54;
goto block_53;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_54;
goto block_53;
}
block_53:
{
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_21; 
lean_del_object(x_19);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_21, 2);
lean_inc_ref(x_24);
x_25 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
lean_dec_ref(x_21);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(x_22, x_23, x_24, x_25, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_dec_ref(x_26);
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_26, 0);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
x_29 = x_26;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_21, 2);
lean_inc(x_38);
lean_dec_ref(x_21);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_39 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(x_36, x_37, x_38, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_dec_ref(x_39);
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_ctor_get(x_39, 0);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
x_42 = x_39;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_49);
x_50 = x_19;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_49);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_17, 0);
x_62 = !lean_is_exclusive(x_17);
if (x_62 == 0)
{
x_56 = x_17;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_17);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_16, 0);
x_70 = !lean_is_exclusive(x_16);
if (x_70 == 0)
{
x_64 = x_16;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_16);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
else
{
lean_object* x_71; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_71 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; uint8_t x_79; 
x_79 = !lean_is_exclusive(x_71);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_71, 0);
lean_dec(x_80);
x_72 = x_71;
x_73 = x_79;
goto block_78;
}
else
{
lean_dec(x_71);
x_72 = lean_box(0);
x_73 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_74; lean_object* x_75; 
x_74 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (x_73 == 0)
{
lean_ctor_set(x_72, 0, x_74);
x_75 = x_72;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_74);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
x_81 = lean_ctor_get(x_71, 0);
x_88 = !lean_is_exclusive(x_71);
if (x_88 == 0)
{
x_82 = x_71;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_71);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_ctor_get(x_12, 0);
x_96 = !lean_is_exclusive(x_12);
if (x_96 == 0)
{
x_90 = x_12;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_dec(x_12);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_26; 
x_13 = lean_ctor_get(x_12, 0);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
x_14 = x_12;
x_15 = x_26;
goto block_25;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_17);
x_18 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec_ref(x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_21);
x_22 = x_14;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
x_27 = lean_ctor_get(x_12, 0);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
x_28 = x_12;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_12);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_grind_process_new_facts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; 
lean_inc_ref(x_1);
x_15 = l_Lean_Expr_isTrue(x_1);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_isInconsistent___redArg(x_4);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_28; 
x_17 = lean_ctor_get(x_16, 0);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
x_18 = x_16;
x_19 = x_28;
goto block_27;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_28;
goto block_27;
}
block_27:
{
uint8_t x_20; 
x_20 = lean_unbox(x_17);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_del_object(x_18);
x_21 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(x_4);
lean_dec_ref(x_21);
x_22 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_23 = lean_box(0);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_23);
x_24 = x_18;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_16, 0);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_30 = x_16;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_16);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_add(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc_ref(x_9);
lean_inc(x_1);
x_14 = l_Lean_FVarId_getType___redArg(x_1, x_9, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_mkFVar(x_1);
x_17 = l_Lean_Meta_Grind_add(x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_14, 0);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
x_19 = x_14;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_addHypothesis(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Ctor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Inv(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PP(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Ctor(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Beta(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Internalize(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Ctor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Inv(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PP(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Ctor(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Beta(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Core(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Core(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Core(builtin);
}
#ifdef __cplusplus
}
#endif
