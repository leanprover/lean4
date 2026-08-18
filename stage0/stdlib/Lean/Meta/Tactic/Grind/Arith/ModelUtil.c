// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.ModelUtil
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Arith.Util import Init.Grind.Module.Envelope
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
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isRoot(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* l_Lean_Meta_Grind_ParentSet_elems(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot_x3f(lean_object*, lean_object*);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getGeneration(lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isIte(lean_object*);
uint8_t l_Lean_Expr_isDIte(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isNatNum(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isIntNum(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__5_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_pickUnusedValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_pickUnusedValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(142, 44, 53, 46, 180, 233, 253, 99)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3_value),LEAN_SCALAR_PTR_LITERAL(36, 9, 44, 71, 206, 78, 188, 190)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15_value),LEAN_SCALAR_PTR_LITERAL(23, 127, 6, 115, 121, 139, 223, 188)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "One"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value),LEAN_SCALAR_PTR_LITERAL(19, 85, 184, 168, 121, 55, 74, 19)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27_value),LEAN_SCALAR_PTR_LITERAL(31, 134, 200, 93, 163, 253, 252, 128)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Inv"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33_value),LEAN_SCALAR_PTR_LITERAL(63, 31, 248, 222, 13, 64, 40, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42_value),LEAN_SCALAR_PTR_LITERAL(165, 91, 87, 132, 175, 103, 206, 109)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "IntModule"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNatModule"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__48_value),LEAN_SCALAR_PTR_LITERAL(100, 80, 29, 215, 2, 174, 123, 91)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInterpretedTerm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_Arith_finalizeModel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_finalizeModel___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_finalizeModel___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_traceModel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_Arith_traceModel___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_traceModel___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_traceModel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_traceModel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_traceModel___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_traceModel___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__1(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_Rat_ofInt(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_m_3_, lean_object* v_query_4_, lean_object* v_x_5_, lean_object* v_x_6_, lean_object* v_x_7_){
_start:
{
lean_object* v_zero_8_; uint8_t v_isZero_9_; 
v_zero_8_ = lean_unsigned_to_nat(0u);
v_isZero_9_ = lean_nat_dec_eq(v_x_6_, v_zero_8_);
if (v_isZero_9_ == 1)
{
lean_dec(v_x_7_);
lean_dec(v_x_6_);
if (lean_obj_tag(v_x_5_) == 0)
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(2);
return v___x_10_;
}
else
{
lean_object* v_val_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_18_; 
v_val_11_ = lean_ctor_get(v_x_5_, 0);
v_isSharedCheck_18_ = !lean_is_exclusive(v_x_5_);
if (v_isSharedCheck_18_ == 0)
{
v___x_13_ = v_x_5_;
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_val_11_);
lean_dec(v_x_5_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_16_; 
if (v_isShared_14_ == 0)
{
v___x_16_ = v___x_13_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_val_11_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
else
{
lean_object* v_keyArray_19_; lean_object* v_valueArray_20_; lean_object* v___x_21_; uint8_t v_isSome_22_; 
v_keyArray_19_ = lean_ctor_get(v_m_3_, 1);
v_valueArray_20_ = lean_ctor_get(v_m_3_, 2);
v___x_21_ = lean_array_fget_borrowed(v_keyArray_19_, v_x_7_);
v_isSome_22_ = lean_noption_is_some(v___x_21_);
if (v_isSome_22_ == 0)
{
lean_dec(v_x_6_);
if (lean_obj_tag(v_x_5_) == 0)
{
lean_object* v___x_23_; 
v___x_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_23_, 0, v_x_7_);
return v___x_23_;
}
else
{
lean_object* v_val_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_31_; 
lean_dec(v_x_7_);
v_val_24_ = lean_ctor_get(v_x_5_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v_x_5_);
if (v_isSharedCheck_31_ == 0)
{
v___x_26_ = v_x_5_;
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_val_24_);
lean_dec(v_x_5_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_29_; 
if (v_isShared_27_ == 0)
{
v___x_29_ = v___x_26_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_val_24_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
else
{
lean_object* v_one_32_; lean_object* v_n_33_; lean_object* v___y_35_; 
v_one_32_ = lean_unsigned_to_nat(1u);
v_n_33_ = lean_nat_sub(v_x_6_, v_one_32_);
lean_dec(v_x_6_);
if (v_isSome_22_ == 0)
{
goto v___jp_41_;
}
else
{
lean_object* v___x_43_; uint8_t v_isSome_44_; 
v___x_43_ = lean_array_fget_borrowed(v_valueArray_20_, v_x_7_);
v_isSome_44_ = lean_noption_is_some(v___x_43_);
if (v_isSome_44_ == 0)
{
goto v___jp_41_;
}
else
{
lean_object* v_val_45_; uint8_t v___x_46_; 
lean_inc(v___x_21_);
v_val_45_ = lean_noption_get(v___x_21_);
v___x_46_ = lean_expr_eqv(v_val_45_, v_query_4_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
lean_dec(v_val_45_);
v___x_47_ = lean_array_get_size(v_keyArray_19_);
v___x_48_ = lean_nat_add(v_x_7_, v_one_32_);
lean_dec(v_x_7_);
v___x_49_ = lean_nat_dec_lt(v___x_48_, v___x_47_);
if (v___x_49_ == 0)
{
lean_dec(v___x_48_);
v_x_6_ = v_n_33_;
v_x_7_ = v_zero_8_;
goto _start;
}
else
{
v_x_6_ = v_n_33_;
v_x_7_ = v___x_48_;
goto _start;
}
}
else
{
lean_object* v_val_52_; lean_object* v___x_53_; 
lean_dec(v_n_33_);
lean_dec(v_x_5_);
lean_inc(v___x_43_);
v_val_52_ = lean_noption_get(v___x_43_);
v___x_53_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_53_, 0, v_x_7_);
lean_ctor_set(v___x_53_, 1, v_val_45_);
lean_ctor_set(v___x_53_, 2, v_val_52_);
return v___x_53_;
}
}
}
v___jp_34_:
{
lean_object* v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_36_ = lean_array_get_size(v_keyArray_19_);
v___x_37_ = lean_nat_add(v_x_7_, v_one_32_);
lean_dec(v_x_7_);
v___x_38_ = lean_nat_dec_lt(v___x_37_, v___x_36_);
if (v___x_38_ == 0)
{
lean_dec(v___x_37_);
v_x_5_ = v___y_35_;
v_x_6_ = v_n_33_;
v_x_7_ = v_zero_8_;
goto _start;
}
else
{
v_x_5_ = v___y_35_;
v_x_6_ = v_n_33_;
v_x_7_ = v___x_37_;
goto _start;
}
}
v___jp_41_:
{
if (lean_obj_tag(v_x_5_) == 0)
{
lean_object* v___x_42_; 
lean_inc(v_x_7_);
v___x_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_42_, 0, v_x_7_);
v___y_35_ = v___x_42_;
goto v___jp_34_;
}
else
{
v___y_35_ = v_x_5_;
goto v___jp_34_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_m_54_, lean_object* v_query_55_, lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2_spec__3___redArg(v_m_54_, v_query_55_, v_x_56_, v_x_57_, v_x_58_);
lean_dec_ref(v_query_55_);
lean_dec_ref(v_m_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2___redArg(lean_object* v_m_60_, lean_object* v_query_61_){
_start:
{
lean_object* v_keyArray_62_; lean_object* v___x_63_; uint64_t v___x_64_; uint64_t v___x_65_; uint64_t v___x_66_; uint64_t v_fold_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; size_t v___x_74_; size_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_keyArray_62_ = lean_ctor_get(v_m_60_, 1);
v___x_63_ = lean_array_get_size(v_keyArray_62_);
v___x_64_ = l_Lean_Expr_hash(v_query_61_);
v___x_65_ = 32ULL;
v___x_66_ = lean_uint64_shift_right(v___x_64_, v___x_65_);
v_fold_67_ = lean_uint64_xor(v___x_64_, v___x_66_);
v___x_68_ = 16ULL;
v___x_69_ = lean_uint64_shift_right(v_fold_67_, v___x_68_);
v___x_70_ = lean_uint64_xor(v_fold_67_, v___x_69_);
v___x_71_ = lean_uint64_to_usize(v___x_70_);
v___x_72_ = lean_usize_of_nat(v___x_63_);
v___x_73_ = ((size_t)1ULL);
v___x_74_ = lean_usize_sub(v___x_72_, v___x_73_);
v___x_75_ = lean_usize_land(v___x_71_, v___x_74_);
v___x_76_ = lean_usize_to_nat(v___x_75_);
v___x_77_ = lean_box(0);
v___x_78_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2_spec__3___redArg(v_m_60_, v_query_61_, v___x_77_, v___x_63_, v___x_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_79_, lean_object* v_query_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2___redArg(v_m_79_, v_query_80_);
lean_dec_ref(v_query_80_);
lean_dec_ref(v_m_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(lean_object* v_m_82_, lean_object* v_query_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2___redArg(v_m_82_, v_query_83_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_index_85_; lean_object* v_key_86_; lean_object* v_value_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
v_index_85_ = lean_ctor_get(v___x_84_, 0);
v_key_86_ = lean_ctor_get(v___x_84_, 1);
v_value_87_ = lean_ctor_get(v___x_84_, 2);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_84_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_value_87_);
lean_inc(v_key_86_);
lean_inc(v_index_85_);
lean_dec(v___x_84_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_index_85_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_key_86_);
lean_ctor_set(v_reuseFailAlloc_93_, 2, v_value_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
else
{
lean_object* v___x_95_; 
lean_dec(v___x_84_);
v___x_95_ = lean_box(1);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg___boxed(lean_object* v_m_96_, lean_object* v_query_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(v_m_96_, v_query_97_);
lean_dec_ref(v_query_97_);
lean_dec_ref(v_m_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(lean_object* v_m_99_, lean_object* v_a_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(v_m_99_, v_a_100_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_value_102_; lean_object* v___x_103_; 
v_value_102_ = lean_ctor_get(v___x_101_, 2);
lean_inc(v_value_102_);
lean_dec_ref_known(v___x_101_, 3);
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v_value_102_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; 
v___x_104_ = lean_box(0);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg___boxed(lean_object* v_m_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_m_105_, v_a_106_);
lean_dec_ref(v_a_106_);
lean_dec_ref(v_m_105_);
return v_res_107_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(lean_object* v_a_108_, lean_object* v_v_109_, lean_object* v_other_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_a_108_, v_other_110_);
if (lean_obj_tag(v___x_111_) == 1)
{
lean_object* v_val_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_val_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_val_112_);
lean_dec_ref_known(v___x_111_, 1);
v___x_113_ = l_Rat_ofInt(v_v_109_);
v___x_114_ = l_instDecidableEqRat_decEq(v_val_112_, v___x_113_);
lean_dec_ref(v___x_113_);
lean_dec(v_val_112_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; 
v___x_115_ = 1;
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
}
else
{
uint8_t v___x_117_; 
lean_dec(v___x_111_);
lean_dec(v_v_109_);
v___x_117_ = 1;
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq___boxed(lean_object* v_a_118_, lean_object* v_v_119_, lean_object* v_other_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_118_, v_v_119_, v_other_120_);
lean_dec_ref(v_other_120_);
lean_dec_ref(v_a_118_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0(lean_object* v_00_u03b2_123_, lean_object* v_m_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_m_124_, v_a_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___boxed(lean_object* v_00_u03b2_127_, lean_object* v_m_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0(v_00_u03b2_127_, v_m_128_, v_a_129_);
lean_dec_ref(v_a_129_);
lean_dec_ref(v_m_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0(lean_object* v_00_u03b2_131_, lean_object* v_m_132_, lean_object* v_query_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(v_m_132_, v_query_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___boxed(lean_object* v_00_u03b2_135_, lean_object* v_m_136_, lean_object* v_query_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0(v_00_u03b2_135_, v_m_136_, v_query_137_);
lean_dec_ref(v_query_137_);
lean_dec_ref(v_m_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_139_, lean_object* v_m_140_, lean_object* v_query_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2___redArg(v_m_140_, v_query_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_143_, lean_object* v_m_144_, lean_object* v_query_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2(v_00_u03b2_143_, v_m_144_, v_query_145_);
lean_dec_ref(v_query_145_);
lean_dec_ref(v_m_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_147_, lean_object* v_m_148_, lean_object* v_query_149_, lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2_spec__3___redArg(v_m_148_, v_query_149_, v_x_150_, v_x_151_, v_x_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_155_, lean_object* v_m_156_, lean_object* v_query_157_, lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2_spec__3(v_00_u03b2_155_, v_m_156_, v_query_157_, v_x_158_, v_x_159_, v_x_160_, v_x_161_);
lean_dec_ref(v_query_157_);
lean_dec_ref(v_m_156_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(lean_object* v_goal_178_, lean_object* v_e_179_, lean_object* v_a_180_, lean_object* v_v_181_, lean_object* v_as_x27_182_, lean_object* v_b_183_){
_start:
{
if (lean_obj_tag(v_as_x27_182_) == 0)
{
lean_dec(v_v_181_);
lean_inc_ref(v_b_183_);
return v_b_183_;
}
else
{
lean_object* v_head_184_; lean_object* v_tail_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___y_189_; uint8_t v___y_190_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_head_184_ = lean_ctor_get(v_as_x27_182_, 0);
v_tail_185_ = lean_ctor_get(v_as_x27_182_, 1);
v___x_186_ = lean_box(0);
v___x_187_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0));
lean_inc(v_head_184_);
v___x_195_ = l_Lean_Expr_cleanupAnnotations(v_head_184_);
v___x_196_ = l_Lean_Expr_isApp(v___x_195_);
if (v___x_196_ == 0)
{
lean_dec_ref(v___x_195_);
v_as_x27_182_ = v_tail_185_;
v_b_183_ = v___x_187_;
goto _start;
}
else
{
lean_object* v_arg_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_arg_198_ = lean_ctor_get(v___x_195_, 1);
lean_inc_ref(v_arg_198_);
v___x_199_ = l_Lean_Expr_appFnCleanup___redArg(v___x_195_);
v___x_200_ = l_Lean_Expr_isApp(v___x_199_);
if (v___x_200_ == 0)
{
lean_dec_ref(v___x_199_);
lean_dec_ref(v_arg_198_);
v_as_x27_182_ = v_tail_185_;
v_b_183_ = v___x_187_;
goto _start;
}
else
{
lean_object* v_arg_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_arg_202_ = lean_ctor_get(v___x_199_, 1);
lean_inc_ref(v_arg_202_);
v___x_203_ = l_Lean_Expr_appFnCleanup___redArg(v___x_199_);
v___x_204_ = l_Lean_Expr_isApp(v___x_203_);
if (v___x_204_ == 0)
{
lean_dec_ref(v___x_203_);
lean_dec_ref(v_arg_202_);
lean_dec_ref(v_arg_198_);
v_as_x27_182_ = v_tail_185_;
v_b_183_ = v___x_187_;
goto _start;
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_206_ = l_Lean_Expr_appFnCleanup___redArg(v___x_203_);
v___x_207_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2));
v___x_208_ = l_Lean_Expr_isConstOf(v___x_206_, v___x_207_);
lean_dec_ref(v___x_206_);
if (v___x_208_ == 0)
{
lean_dec_ref(v_arg_202_);
lean_dec_ref(v_arg_198_);
v_as_x27_182_ = v_tail_185_;
v_b_183_ = v___x_187_;
goto _start;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_178_, v_head_184_);
if (lean_obj_tag(v___x_210_) == 1)
{
lean_object* v_val_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_val_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_211_);
lean_dec_ref_known(v___x_210_, 1);
v___x_212_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4));
v___x_213_ = l_Lean_Expr_isConstOf(v_val_211_, v___x_212_);
lean_dec(v_val_211_);
if (v___x_213_ == 0)
{
lean_dec_ref(v_arg_202_);
lean_dec_ref(v_arg_198_);
v_as_x27_182_ = v_tail_185_;
v_b_183_ = v___x_187_;
goto _start;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_178_, v_arg_202_);
lean_dec_ref(v_arg_202_);
if (lean_obj_tag(v___x_215_) == 1)
{
lean_object* v_val_216_; lean_object* v___x_217_; 
v_val_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_val_216_);
lean_dec_ref_known(v___x_215_, 1);
v___x_217_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_178_, v_arg_198_);
lean_dec_ref(v_arg_198_);
if (lean_obj_tag(v___x_217_) == 1)
{
lean_object* v_val_218_; uint8_t v___y_220_; uint8_t v___y_225_; uint8_t v___x_227_; 
v_val_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v___x_217_, 1);
v___x_227_ = lean_expr_eqv(v_val_216_, v_e_179_);
if (v___x_227_ == 0)
{
v___y_225_ = v___x_227_;
goto v___jp_224_;
}
else
{
uint8_t v___x_228_; 
lean_inc(v_v_181_);
v___x_228_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_180_, v_v_181_, v_val_218_);
if (v___x_228_ == 0)
{
v___y_225_ = v___x_227_;
goto v___jp_224_;
}
else
{
uint8_t v___x_229_; 
v___x_229_ = 0;
v___y_220_ = v___x_229_;
goto v___jp_219_;
}
}
v___jp_219_:
{
uint8_t v___x_221_; 
v___x_221_ = lean_expr_eqv(v_val_218_, v_e_179_);
lean_dec(v_val_218_);
if (v___x_221_ == 0)
{
lean_dec(v_val_216_);
v___y_189_ = v___y_220_;
v___y_190_ = v___x_221_;
goto v___jp_188_;
}
else
{
uint8_t v___x_222_; 
lean_inc(v_v_181_);
v___x_222_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_180_, v_v_181_, v_val_216_);
lean_dec(v_val_216_);
if (v___x_222_ == 0)
{
v___y_189_ = v___y_220_;
v___y_190_ = v___x_221_;
goto v___jp_188_;
}
else
{
v_as_x27_182_ = v_tail_185_;
v_b_183_ = v___x_187_;
goto _start;
}
}
}
v___jp_224_:
{
if (v___y_225_ == 0)
{
v___y_220_ = v___y_225_;
goto v___jp_219_;
}
else
{
lean_object* v___x_226_; 
lean_dec(v_val_218_);
lean_dec(v_val_216_);
lean_dec(v_v_181_);
v___x_226_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6));
return v___x_226_;
}
}
}
else
{
lean_dec(v___x_217_);
lean_dec(v_val_216_);
v_as_x27_182_ = v_tail_185_;
v_b_183_ = v___x_187_;
goto _start;
}
}
else
{
lean_dec(v___x_215_);
lean_dec_ref(v_arg_198_);
v_as_x27_182_ = v_tail_185_;
v_b_183_ = v___x_187_;
goto _start;
}
}
}
else
{
lean_dec(v___x_210_);
lean_dec_ref(v_arg_202_);
lean_dec_ref(v_arg_198_);
v_as_x27_182_ = v_tail_185_;
v_b_183_ = v___x_187_;
goto _start;
}
}
}
}
}
v___jp_188_:
{
if (v___y_190_ == 0)
{
v_as_x27_182_ = v_tail_185_;
v_b_183_ = v___x_187_;
goto _start;
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_v_181_);
v___x_192_ = lean_box(v___y_189_);
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___x_186_);
return v___x_194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___boxed(lean_object* v_goal_233_, lean_object* v_e_234_, lean_object* v_a_235_, lean_object* v_v_236_, lean_object* v_as_x27_237_, lean_object* v_b_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_233_, v_e_234_, v_a_235_, v_v_236_, v_as_x27_237_, v_b_238_);
lean_dec_ref(v_b_238_);
lean_dec(v_as_x27_237_);
lean_dec_ref(v_a_235_);
lean_dec_ref(v_e_234_);
lean_dec_ref(v_goal_233_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_240_, lean_object* v_vals_241_, lean_object* v_i_242_, lean_object* v_k_243_){
_start:
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_array_get_size(v_keys_240_);
v___x_245_ = lean_nat_dec_lt(v_i_242_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
lean_dec(v_i_242_);
v___x_246_ = lean_box(0);
return v___x_246_;
}
else
{
lean_object* v_k_x27_247_; size_t v___x_248_; size_t v___x_249_; uint8_t v___x_250_; 
v_k_x27_247_ = lean_array_fget_borrowed(v_keys_240_, v_i_242_);
v___x_248_ = lean_ptr_addr(v_k_243_);
v___x_249_ = lean_ptr_addr(v_k_x27_247_);
v___x_250_ = lean_usize_dec_eq(v___x_248_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(1u);
v___x_252_ = lean_nat_add(v_i_242_, v___x_251_);
lean_dec(v_i_242_);
v_i_242_ = v___x_252_;
goto _start;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_array_fget_borrowed(v_vals_241_, v_i_242_);
lean_dec(v_i_242_);
lean_inc(v___x_254_);
v___x_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_256_, lean_object* v_vals_257_, lean_object* v_i_258_, lean_object* v_k_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_256_, v_vals_257_, v_i_258_, v_k_259_);
lean_dec_ref(v_k_259_);
lean_dec_ref(v_vals_257_);
lean_dec_ref(v_keys_256_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(lean_object* v_x_261_, size_t v_x_262_, lean_object* v_x_263_){
_start:
{
if (lean_obj_tag(v_x_261_) == 0)
{
lean_object* v_es_264_; lean_object* v___x_265_; size_t v___x_266_; size_t v___x_267_; lean_object* v_j_268_; lean_object* v___x_269_; 
v_es_264_ = lean_ctor_get(v_x_261_, 0);
v___x_265_ = lean_box(2);
v___x_266_ = ((size_t)31ULL);
v___x_267_ = lean_usize_land(v_x_262_, v___x_266_);
v_j_268_ = lean_usize_to_nat(v___x_267_);
v___x_269_ = lean_array_get_borrowed(v___x_265_, v_es_264_, v_j_268_);
lean_dec(v_j_268_);
switch(lean_obj_tag(v___x_269_))
{
case 0:
{
lean_object* v_key_270_; lean_object* v_val_271_; size_t v___x_272_; size_t v___x_273_; uint8_t v___x_274_; 
v_key_270_ = lean_ctor_get(v___x_269_, 0);
v_val_271_ = lean_ctor_get(v___x_269_, 1);
v___x_272_ = lean_ptr_addr(v_x_263_);
v___x_273_ = lean_ptr_addr(v_key_270_);
v___x_274_ = lean_usize_dec_eq(v___x_272_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
v___x_275_ = lean_box(0);
return v___x_275_;
}
else
{
lean_object* v___x_276_; 
lean_inc(v_val_271_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v_val_271_);
return v___x_276_;
}
}
case 1:
{
lean_object* v_node_277_; size_t v___x_278_; size_t v___x_279_; 
v_node_277_ = lean_ctor_get(v___x_269_, 0);
v___x_278_ = ((size_t)5ULL);
v___x_279_ = lean_usize_shift_right(v_x_262_, v___x_278_);
v_x_261_ = v_node_277_;
v_x_262_ = v___x_279_;
goto _start;
}
default: 
{
lean_object* v___x_281_; 
v___x_281_ = lean_box(0);
return v___x_281_;
}
}
}
else
{
lean_object* v_ks_282_; lean_object* v_vs_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_ks_282_ = lean_ctor_get(v_x_261_, 0);
v_vs_283_ = lean_ctor_get(v_x_261_, 1);
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_ks_282_, v_vs_283_, v___x_284_, v_x_263_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___boxed(lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
size_t v_x_2623__boxed_289_; lean_object* v_res_290_; 
v_x_2623__boxed_289_ = lean_unbox_usize(v_x_287_);
lean_dec(v_x_287_);
v_res_290_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_286_, v_x_2623__boxed_289_, v_x_288_);
lean_dec_ref(v_x_288_);
lean_dec_ref(v_x_286_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
size_t v___x_293_; size_t v___x_294_; size_t v___x_295_; uint64_t v___x_296_; size_t v___x_297_; lean_object* v___x_298_; 
v___x_293_ = lean_ptr_addr(v_x_292_);
v___x_294_ = ((size_t)3ULL);
v___x_295_ = lean_usize_shift_right(v___x_293_, v___x_294_);
v___x_296_ = lean_usize_to_uint64(v___x_295_);
v___x_297_ = lean_uint64_to_usize(v___x_296_);
v___x_298_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_291_, v___x_297_, v_x_292_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg___boxed(lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_299_, v_x_300_);
lean_dec_ref(v_x_300_);
lean_dec_ref(v_x_299_);
return v_res_301_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(lean_object* v_goal_302_, lean_object* v_a_303_, lean_object* v_e_304_, lean_object* v_v_305_){
_start:
{
lean_object* v_toGoalState_306_; lean_object* v_parents_307_; lean_object* v___x_308_; 
v_toGoalState_306_ = lean_ctor_get(v_goal_302_, 0);
v_parents_307_ = lean_ctor_get(v_toGoalState_306_, 3);
v___x_308_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_parents_307_, v_e_304_);
if (lean_obj_tag(v___x_308_) == 1)
{
lean_object* v_val_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_fst_313_; 
v_val_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_val_309_);
lean_dec_ref_known(v___x_308_, 1);
v___x_310_ = l_Lean_Meta_Grind_ParentSet_elems(v_val_309_);
lean_dec(v_val_309_);
v___x_311_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0));
v___x_312_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_302_, v_e_304_, v_a_303_, v_v_305_, v___x_310_, v___x_311_);
lean_dec(v___x_310_);
v_fst_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_fst_313_);
lean_dec_ref(v___x_312_);
if (lean_obj_tag(v_fst_313_) == 0)
{
uint8_t v___x_314_; 
v___x_314_ = 1;
return v___x_314_;
}
else
{
lean_object* v_val_315_; uint8_t v___x_316_; 
v_val_315_ = lean_ctor_get(v_fst_313_, 0);
lean_inc(v_val_315_);
lean_dec_ref_known(v_fst_313_, 1);
v___x_316_ = lean_unbox(v_val_315_);
lean_dec(v_val_315_);
return v___x_316_;
}
}
else
{
uint8_t v___x_317_; 
lean_dec(v___x_308_);
lean_dec(v_v_305_);
v___x_317_ = 1;
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs___boxed(lean_object* v_goal_318_, lean_object* v_a_319_, lean_object* v_e_320_, lean_object* v_v_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_318_, v_a_319_, v_e_320_, v_v_321_);
lean_dec_ref(v_e_320_);
lean_dec_ref(v_a_319_);
lean_dec_ref(v_goal_318_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(lean_object* v_00_u03b2_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_325_, v_x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___boxed(lean_object* v_00_u03b2_328_, lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(v_00_u03b2_328_, v_x_329_, v_x_330_);
lean_dec_ref(v_x_330_);
lean_dec_ref(v_x_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(lean_object* v_goal_332_, lean_object* v_e_333_, lean_object* v_a_334_, lean_object* v_v_335_, lean_object* v_as_336_, lean_object* v_as_x27_337_, lean_object* v_b_338_, lean_object* v_a_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_332_, v_e_333_, v_a_334_, v_v_335_, v_as_x27_337_, v_b_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___boxed(lean_object* v_goal_341_, lean_object* v_e_342_, lean_object* v_a_343_, lean_object* v_v_344_, lean_object* v_as_345_, lean_object* v_as_x27_346_, lean_object* v_b_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(v_goal_341_, v_e_342_, v_a_343_, v_v_344_, v_as_345_, v_as_x27_346_, v_b_347_, v_a_348_);
lean_dec_ref(v_b_347_);
lean_dec(v_as_x27_346_);
lean_dec(v_as_345_);
lean_dec_ref(v_a_343_);
lean_dec_ref(v_e_342_);
lean_dec_ref(v_goal_341_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(lean_object* v_00_u03b2_350_, lean_object* v_x_351_, size_t v_x_352_, lean_object* v_x_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_351_, v_x_352_, v_x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_355_, lean_object* v_x_356_, lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
size_t v_x_2728__boxed_359_; lean_object* v_res_360_; 
v_x_2728__boxed_359_ = lean_unbox_usize(v_x_357_);
lean_dec(v_x_357_);
v_res_360_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(v_00_u03b2_355_, v_x_356_, v_x_2728__boxed_359_, v_x_358_);
lean_dec_ref(v_x_358_);
lean_dec_ref(v_x_356_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_361_, lean_object* v_keys_362_, lean_object* v_vals_363_, lean_object* v_heq_364_, lean_object* v_i_365_, lean_object* v_k_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_362_, v_vals_363_, v_i_365_, v_k_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_368_, lean_object* v_keys_369_, lean_object* v_vals_370_, lean_object* v_heq_371_, lean_object* v_i_372_, lean_object* v_k_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(v_00_u03b2_368_, v_keys_369_, v_vals_370_, v_heq_371_, v_i_372_, v_k_373_);
lean_dec_ref(v_k_373_);
lean_dec_ref(v_vals_370_);
lean_dec_ref(v_keys_369_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_m_375_, lean_object* v_query_376_, lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
lean_object* v_zero_380_; uint8_t v_isZero_381_; 
v_zero_380_ = lean_unsigned_to_nat(0u);
v_isZero_381_ = lean_nat_dec_eq(v_x_378_, v_zero_380_);
if (v_isZero_381_ == 1)
{
lean_dec(v_x_379_);
lean_dec(v_x_378_);
if (lean_obj_tag(v_x_377_) == 0)
{
lean_object* v___x_382_; 
v___x_382_ = lean_box(2);
return v___x_382_;
}
else
{
lean_object* v_val_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
v_val_383_ = lean_ctor_get(v_x_377_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v_x_377_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v_x_377_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_val_383_);
lean_dec(v_x_377_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_val_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v_keyArray_391_; lean_object* v_valueArray_392_; lean_object* v___x_393_; uint8_t v_isSome_394_; 
v_keyArray_391_ = lean_ctor_get(v_m_375_, 1);
v_valueArray_392_ = lean_ctor_get(v_m_375_, 2);
v___x_393_ = lean_array_fget_borrowed(v_keyArray_391_, v_x_379_);
v_isSome_394_ = lean_noption_is_some(v___x_393_);
if (v_isSome_394_ == 0)
{
lean_dec(v_x_378_);
if (lean_obj_tag(v_x_377_) == 0)
{
lean_object* v___x_395_; 
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v_x_379_);
return v___x_395_;
}
else
{
lean_object* v_val_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec(v_x_379_);
v_val_396_ = lean_ctor_get(v_x_377_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_377_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v_x_377_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_val_396_);
lean_dec(v_x_377_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_val_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
else
{
lean_object* v_one_404_; lean_object* v_n_405_; lean_object* v___y_407_; 
v_one_404_ = lean_unsigned_to_nat(1u);
v_n_405_ = lean_nat_sub(v_x_378_, v_one_404_);
lean_dec(v_x_378_);
if (v_isSome_394_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v___x_415_; uint8_t v_isSome_416_; 
v___x_415_ = lean_array_fget_borrowed(v_valueArray_392_, v_x_379_);
v_isSome_416_ = lean_noption_is_some(v___x_415_);
if (v_isSome_416_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v_val_417_; uint8_t v___x_418_; 
lean_inc(v___x_393_);
v_val_417_ = lean_noption_get(v___x_393_);
v___x_418_ = lean_int_dec_eq(v_val_417_, v_query_376_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
lean_dec(v_val_417_);
v___x_419_ = lean_array_get_size(v_keyArray_391_);
v___x_420_ = lean_nat_add(v_x_379_, v_one_404_);
lean_dec(v_x_379_);
v___x_421_ = lean_nat_dec_lt(v___x_420_, v___x_419_);
if (v___x_421_ == 0)
{
lean_dec(v___x_420_);
v_x_378_ = v_n_405_;
v_x_379_ = v_zero_380_;
goto _start;
}
else
{
v_x_378_ = v_n_405_;
v_x_379_ = v___x_420_;
goto _start;
}
}
else
{
lean_object* v_val_424_; lean_object* v___x_425_; 
lean_dec(v_n_405_);
lean_dec(v_x_377_);
lean_inc(v___x_415_);
v_val_424_ = lean_noption_get(v___x_415_);
v___x_425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_425_, 0, v_x_379_);
lean_ctor_set(v___x_425_, 1, v_val_417_);
lean_ctor_set(v___x_425_, 2, v_val_424_);
return v___x_425_;
}
}
}
v___jp_406_:
{
lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_408_ = lean_array_get_size(v_keyArray_391_);
v___x_409_ = lean_nat_add(v_x_379_, v_one_404_);
lean_dec(v_x_379_);
v___x_410_ = lean_nat_dec_lt(v___x_409_, v___x_408_);
if (v___x_410_ == 0)
{
lean_dec(v___x_409_);
v_x_377_ = v___y_407_;
v_x_378_ = v_n_405_;
v_x_379_ = v_zero_380_;
goto _start;
}
else
{
v_x_377_ = v___y_407_;
v_x_378_ = v_n_405_;
v_x_379_ = v___x_409_;
goto _start;
}
}
v___jp_413_:
{
if (lean_obj_tag(v_x_377_) == 0)
{
lean_object* v___x_414_; 
lean_inc(v_x_379_);
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v_x_379_);
v___y_407_ = v___x_414_;
goto v___jp_406_;
}
else
{
v___y_407_ = v_x_377_;
goto v___jp_406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_m_426_, lean_object* v_query_427_, lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1_spec__2___redArg(v_m_426_, v_query_427_, v_x_428_, v_x_429_, v_x_430_);
lean_dec(v_query_427_);
lean_dec_ref(v_m_426_);
return v_res_431_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_432_; lean_object* v_intZero_433_; 
v_natZero_432_ = lean_unsigned_to_nat(0u);
v_intZero_433_ = lean_nat_to_int(v_natZero_432_);
return v_intZero_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(lean_object* v_m_434_, lean_object* v_query_435_){
_start:
{
lean_object* v_keyArray_436_; lean_object* v___x_437_; uint64_t v___y_439_; lean_object* v_intZero_454_; uint8_t v_isNeg_455_; 
v_keyArray_436_ = lean_ctor_get(v_m_434_, 1);
v___x_437_ = lean_array_get_size(v_keyArray_436_);
v_intZero_454_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg___closed__0);
v_isNeg_455_ = lean_int_dec_lt(v_query_435_, v_intZero_454_);
if (v_isNeg_455_ == 0)
{
lean_object* v_a_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint64_t v___x_459_; 
v_a_456_ = lean_nat_abs(v_query_435_);
v___x_457_ = lean_unsigned_to_nat(2u);
v___x_458_ = lean_nat_mul(v___x_457_, v_a_456_);
lean_dec(v_a_456_);
v___x_459_ = lean_uint64_of_nat(v___x_458_);
lean_dec(v___x_458_);
v___y_439_ = v___x_459_;
goto v___jp_438_;
}
else
{
lean_object* v_abs_460_; lean_object* v_one_461_; lean_object* v_a_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint64_t v___x_466_; 
v_abs_460_ = lean_nat_abs(v_query_435_);
v_one_461_ = lean_unsigned_to_nat(1u);
v_a_462_ = lean_nat_sub(v_abs_460_, v_one_461_);
lean_dec(v_abs_460_);
v___x_463_ = lean_unsigned_to_nat(2u);
v___x_464_ = lean_nat_mul(v___x_463_, v_a_462_);
lean_dec(v_a_462_);
v___x_465_ = lean_nat_add(v___x_464_, v_one_461_);
lean_dec(v___x_464_);
v___x_466_ = lean_uint64_of_nat(v___x_465_);
lean_dec(v___x_465_);
v___y_439_ = v___x_466_;
goto v___jp_438_;
}
v___jp_438_:
{
uint64_t v___x_440_; uint64_t v___x_441_; uint64_t v_fold_442_; uint64_t v___x_443_; uint64_t v___x_444_; uint64_t v___x_445_; size_t v___x_446_; size_t v___x_447_; size_t v___x_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_440_ = 32ULL;
v___x_441_ = lean_uint64_shift_right(v___y_439_, v___x_440_);
v_fold_442_ = lean_uint64_xor(v___y_439_, v___x_441_);
v___x_443_ = 16ULL;
v___x_444_ = lean_uint64_shift_right(v_fold_442_, v___x_443_);
v___x_445_ = lean_uint64_xor(v_fold_442_, v___x_444_);
v___x_446_ = lean_uint64_to_usize(v___x_445_);
v___x_447_ = lean_usize_of_nat(v___x_437_);
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_sub(v___x_447_, v___x_448_);
v___x_450_ = lean_usize_land(v___x_446_, v___x_449_);
v___x_451_ = lean_usize_to_nat(v___x_450_);
v___x_452_ = lean_box(0);
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1_spec__2___redArg(v_m_434_, v_query_435_, v___x_452_, v___x_437_, v___x_451_);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_467_, lean_object* v_query_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v_m_467_, v_query_468_);
lean_dec(v_query_468_);
lean_dec_ref(v_m_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(lean_object* v_m_470_, lean_object* v_query_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v_m_470_, v_query_471_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_index_473_; lean_object* v_key_474_; lean_object* v_value_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
v_index_473_ = lean_ctor_get(v___x_472_, 0);
v_key_474_ = lean_ctor_get(v___x_472_, 1);
v_value_475_ = lean_ctor_get(v___x_472_, 2);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_472_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_value_475_);
lean_inc(v_key_474_);
lean_inc(v_index_473_);
lean_dec(v___x_472_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_index_473_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_key_474_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_value_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
lean_object* v___x_483_; 
lean_dec(v___x_472_);
v___x_483_ = lean_box(1);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg___boxed(lean_object* v_m_484_, lean_object* v_query_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_m_484_, v_query_485_);
lean_dec(v_query_485_);
lean_dec_ref(v_m_484_);
return v_res_486_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(lean_object* v_m_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_m_487_, v_a_488_);
if (lean_obj_tag(v___x_489_) == 0)
{
uint8_t v___x_490_; 
lean_dec_ref_known(v___x_489_, 3);
v___x_490_ = 1;
return v___x_490_;
}
else
{
uint8_t v___x_491_; 
v___x_491_ = 0;
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___boxed(lean_object* v_m_492_, lean_object* v_a_493_){
_start:
{
uint8_t v_res_494_; lean_object* v_r_495_; 
v_res_494_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_492_, v_a_493_);
lean_dec(v_a_493_);
lean_dec_ref(v_m_492_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_unsigned_to_nat(1u);
v___x_497_ = lean_nat_to_int(v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(lean_object* v_goal_498_, lean_object* v_a_499_, lean_object* v_e_500_, lean_object* v_alreadyUsed_501_, lean_object* v_next_502_){
_start:
{
uint8_t v___x_503_; 
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_alreadyUsed_501_, v_next_502_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; 
lean_inc(v_next_502_);
v___x_504_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_498_, v_a_499_, v_e_500_, v_next_502_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_506_ = lean_int_add(v_next_502_, v___x_505_);
lean_dec(v_next_502_);
v_next_502_ = v___x_506_;
goto _start;
}
else
{
return v_next_502_;
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_509_ = lean_int_add(v_next_502_, v___x_508_);
lean_dec(v_next_502_);
v_next_502_ = v___x_509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___boxed(lean_object* v_goal_511_, lean_object* v_a_512_, lean_object* v_e_513_, lean_object* v_alreadyUsed_514_, lean_object* v_next_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_511_, v_a_512_, v_e_513_, v_alreadyUsed_514_, v_next_515_);
lean_dec_ref(v_alreadyUsed_514_);
lean_dec_ref(v_e_513_);
lean_dec_ref(v_a_512_);
lean_dec_ref(v_goal_511_);
return v_res_516_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(lean_object* v_00_u03b2_517_, lean_object* v_m_518_, lean_object* v_a_519_){
_start:
{
uint8_t v___x_520_; 
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_518_, v_a_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___boxed(lean_object* v_00_u03b2_521_, lean_object* v_m_522_, lean_object* v_a_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(v_00_u03b2_521_, v_m_522_, v_a_523_);
lean_dec(v_a_523_);
lean_dec_ref(v_m_522_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(lean_object* v_00_u03b2_526_, lean_object* v_m_527_, lean_object* v_query_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_m_527_, v_query_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_530_, lean_object* v_m_531_, lean_object* v_query_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(v_00_u03b2_530_, v_m_531_, v_query_532_);
lean_dec(v_query_532_);
lean_dec_ref(v_m_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_534_, lean_object* v_m_535_, lean_object* v_query_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v_m_535_, v_query_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_538_, lean_object* v_m_539_, lean_object* v_query_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1(v_00_u03b2_538_, v_m_539_, v_query_540_);
lean_dec(v_query_540_);
lean_dec_ref(v_m_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_542_, lean_object* v_m_543_, lean_object* v_query_544_, lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1_spec__2___redArg(v_m_543_, v_query_544_, v_x_545_, v_x_546_, v_x_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_550_, lean_object* v_m_551_, lean_object* v_query_552_, lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_550_, v_m_551_, v_query_552_, v_x_553_, v_x_554_, v_x_555_, v_x_556_);
lean_dec(v_query_552_);
lean_dec_ref(v_m_551_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_pickUnusedValue(lean_object* v_goal_558_, lean_object* v_a_559_, lean_object* v_e_560_, lean_object* v_next_561_, lean_object* v_alreadyUsed_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_558_, v_a_559_, v_e_560_, v_alreadyUsed_562_, v_next_561_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_pickUnusedValue___boxed(lean_object* v_goal_564_, lean_object* v_a_565_, lean_object* v_e_566_, lean_object* v_next_567_, lean_object* v_alreadyUsed_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Meta_Grind_Arith_pickUnusedValue(v_goal_564_, v_a_565_, v_e_566_, v_next_567_, v_alreadyUsed_568_);
lean_dec_ref(v_alreadyUsed_568_);
lean_dec_ref(v_e_566_);
lean_dec_ref(v_a_565_);
lean_dec_ref(v_goal_564_);
return v_res_569_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInterpretedTerm(lean_object* v_e_655_){
_start:
{
uint8_t v___y_662_; uint8_t v___x_695_; 
lean_inc_ref(v_e_655_);
v___x_695_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_655_);
if (v___x_695_ == 0)
{
uint8_t v___x_696_; 
lean_inc_ref(v_e_655_);
v___x_696_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_655_);
v___y_662_ = v___x_696_;
goto v___jp_661_;
}
else
{
v___y_662_ = v___x_695_;
goto v___jp_661_;
}
v___jp_656_:
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2));
v___x_658_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4));
v___x_660_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_659_);
lean_dec_ref(v_e_655_);
return v___x_660_;
}
else
{
lean_dec_ref(v_e_655_);
return v___x_658_;
}
}
v___jp_661_:
{
if (v___y_662_ == 0)
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7));
v___x_664_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10));
v___x_666_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13));
v___x_668_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16));
v___x_670_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19));
v___x_672_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_673_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22));
v___x_674_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25));
v___x_676_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_677_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28));
v___x_678_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31));
v___x_680_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34));
v___x_682_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37));
v___x_684_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_683_);
if (v___x_684_ == 0)
{
uint8_t v___x_685_; 
v___x_685_ = l_Lean_Expr_isIte(v_e_655_);
if (v___x_685_ == 0)
{
uint8_t v___x_686_; 
v___x_686_ = l_Lean_Expr_isDIte(v_e_655_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40));
v___x_688_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43));
v___x_690_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49));
v___x_692_ = l_Lean_Expr_isAppOf(v_e_655_, v___x_691_);
if (v___x_692_ == 0)
{
if (lean_obj_tag(v_e_655_) == 9)
{
lean_object* v_a_693_; 
v_a_693_ = lean_ctor_get(v_e_655_, 0);
if (lean_obj_tag(v_a_693_) == 0)
{
uint8_t v___x_694_; 
lean_dec_ref_known(v_e_655_, 1);
v___x_694_ = 1;
return v___x_694_;
}
else
{
goto v___jp_656_;
}
}
else
{
goto v___jp_656_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_692_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_690_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_688_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_686_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_685_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_684_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_682_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_680_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_678_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_676_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_674_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_672_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_670_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_668_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_666_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___x_664_;
}
}
else
{
lean_dec_ref(v_e_655_);
return v___y_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___boxed(lean_object* v_e_697_){
_start:
{
uint8_t v_res_698_; lean_object* v_r_699_; 
v_res_698_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_697_);
v_r_699_ = lean_box(v_res_698_);
return v_r_699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0_spec__1___redArg(lean_object* v_b_700_, lean_object* v_acc_701_, lean_object* v_i_702_){
_start:
{
lean_object* v___y_704_; lean_object* v_keyArray_712_; lean_object* v_valueArray_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v_keyArray_712_ = lean_ctor_get(v_b_700_, 1);
v_valueArray_713_ = lean_ctor_get(v_b_700_, 2);
v___x_714_ = lean_array_get_size(v_keyArray_712_);
v___x_715_ = lean_nat_dec_lt(v_i_702_, v___x_714_);
if (v___x_715_ == 0)
{
lean_dec(v_i_702_);
return v_acc_701_;
}
else
{
lean_object* v___x_716_; uint8_t v_isSome_717_; 
v___x_716_ = lean_array_fget_borrowed(v_keyArray_712_, v_i_702_);
v_isSome_717_ = lean_noption_is_some(v___x_716_);
if (v_isSome_717_ == 0)
{
goto v___jp_708_;
}
else
{
lean_object* v___x_718_; uint8_t v_isSome_719_; 
v___x_718_ = lean_array_fget_borrowed(v_valueArray_713_, v_i_702_);
v_isSome_719_ = lean_noption_is_some(v___x_718_);
if (v_isSome_719_ == 0)
{
goto v___jp_708_;
}
else
{
lean_object* v_val_720_; lean_object* v_val_721_; lean_object* v_i_723_; lean_object* v___x_728_; 
lean_inc(v___x_716_);
v_val_720_ = lean_noption_get(v___x_716_);
lean_inc(v___x_718_);
v_val_721_ = lean_noption_get(v___x_718_);
v___x_728_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2___redArg(v_acc_701_, v_val_720_);
switch(lean_obj_tag(v___x_728_))
{
case 0:
{
lean_object* v_index_729_; lean_object* v_size_730_; lean_object* v___x_731_; 
v_index_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_index_729_);
lean_dec_ref_known(v___x_728_, 3);
v_size_730_ = lean_ctor_get(v_acc_701_, 0);
lean_inc(v_size_730_);
v___x_731_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_701_, v_size_730_, v_index_729_, v_val_720_, v_val_721_);
lean_dec(v_index_729_);
v___y_704_ = v___x_731_;
goto v___jp_703_;
}
case 1:
{
lean_object* v_index_732_; 
v_index_732_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_index_732_);
lean_dec_ref_known(v___x_728_, 1);
v_i_723_ = v_index_732_;
goto v___jp_722_;
}
default: 
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_701_, v___x_733_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_index_735_; 
v_index_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_index_735_);
lean_dec_ref_known(v___x_734_, 1);
v_i_723_ = v_index_735_;
goto v___jp_722_;
}
else
{
lean_dec(v_val_721_);
lean_dec(v_val_720_);
v___y_704_ = v_acc_701_;
goto v___jp_703_;
}
}
}
v___jp_722_:
{
lean_object* v_size_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_size_724_ = lean_ctor_get(v_acc_701_, 0);
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_add(v_size_724_, v___x_725_);
v___x_727_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_701_, v___x_726_, v_i_723_, v_val_720_, v_val_721_);
lean_dec(v_i_723_);
v___y_704_ = v___x_727_;
goto v___jp_703_;
}
}
}
}
v___jp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = lean_nat_add(v_i_702_, v___x_705_);
lean_dec(v_i_702_);
v_acc_701_ = v___y_704_;
v_i_702_ = v___x_706_;
goto _start;
}
v___jp_708_:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_unsigned_to_nat(1u);
v___x_710_ = lean_nat_add(v_i_702_, v___x_709_);
lean_dec(v_i_702_);
v_i_702_ = v___x_710_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_b_736_, lean_object* v_acc_737_, lean_object* v_i_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0_spec__1___redArg(v_b_736_, v_acc_737_, v_i_738_);
lean_dec_ref(v_b_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(lean_object* v_init_740_, lean_object* v_b_741_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0_spec__1___redArg(v_b_741_, v_init_740_, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg___boxed(lean_object* v_init_744_, lean_object* v_b_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_init_744_, v_b_745_);
lean_dec_ref(v_b_745_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(lean_object* v_m_747_){
_start:
{
lean_object* v_keyArray_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_cellCount_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v_target_755_; lean_object* v___x_756_; 
v_keyArray_748_ = lean_ctor_get(v_m_747_, 1);
v___x_749_ = lean_array_get_size(v_keyArray_748_);
v___x_750_ = lean_unsigned_to_nat(2u);
v_cellCount_751_ = lean_nat_mul(v___x_749_, v___x_750_);
v___x_752_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_751_);
v___x_753_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_751_);
v___x_754_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_751_);
v_target_755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_755_, 0, v___x_752_);
lean_ctor_set(v_target_755_, 1, v___x_753_);
lean_ctor_set(v_target_755_, 2, v___x_754_);
v___x_756_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_target_755_, v_m_747_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg___boxed(lean_object* v_m_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_m_757_);
lean_dec_ref(v_m_757_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(lean_object* v_v_759_, lean_object* v_as_x27_760_, lean_object* v_b_761_){
_start:
{
if (lean_obj_tag(v_as_x27_760_) == 0)
{
lean_dec_ref(v_v_759_);
return v_b_761_;
}
else
{
lean_object* v_head_762_; lean_object* v_tail_763_; lean_object* v___y_765_; lean_object* v_i_766_; lean_object* v___y_773_; lean_object* v___y_785_; lean_object* v_i_786_; lean_object* v___x_804_; 
v_head_762_ = lean_ctor_get(v_as_x27_760_, 0);
v_tail_763_ = lean_ctor_get(v_as_x27_760_, 1);
v___x_804_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2___redArg(v_b_761_, v_head_762_);
switch(lean_obj_tag(v___x_804_))
{
case 0:
{
lean_object* v_index_805_; lean_object* v_size_806_; lean_object* v___x_807_; 
v_index_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_index_805_);
lean_dec_ref_known(v___x_804_, 3);
v_size_806_ = lean_ctor_get(v_b_761_, 0);
lean_inc(v_size_806_);
lean_inc_ref(v_v_759_);
lean_inc(v_head_762_);
v___x_807_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_761_, v_size_806_, v_index_805_, v_head_762_, v_v_759_);
lean_dec(v_index_805_);
v_as_x27_760_ = v_tail_763_;
v_b_761_ = v___x_807_;
goto _start;
}
case 1:
{
lean_object* v_index_809_; lean_object* v_size_810_; lean_object* v_keyArray_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v_index_809_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_index_809_);
lean_dec_ref_known(v___x_804_, 1);
v_size_810_ = lean_ctor_get(v_b_761_, 0);
v_keyArray_811_ = lean_ctor_get(v_b_761_, 1);
v___x_812_ = lean_unsigned_to_nat(1u);
v___x_813_ = lean_nat_add(v_size_810_, v___x_812_);
v___x_814_ = lean_array_get_size(v_keyArray_811_);
v___x_815_ = lean_nat_dec_lt(v___x_813_, v___x_814_);
if (v___x_815_ == 0)
{
lean_dec(v___x_813_);
lean_dec(v_index_809_);
goto v___jp_792_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_816_ = lean_unsigned_to_nat(4u);
v___x_817_ = lean_nat_mul(v___x_813_, v___x_816_);
v___x_818_ = lean_unsigned_to_nat(3u);
v___x_819_ = lean_nat_mul(v___x_814_, v___x_818_);
v___x_820_ = lean_nat_dec_le(v___x_817_, v___x_819_);
lean_dec(v___x_819_);
lean_dec(v___x_817_);
if (v___x_820_ == 0)
{
lean_dec(v___x_813_);
lean_dec(v_index_809_);
goto v___jp_792_;
}
else
{
lean_object* v___x_821_; 
lean_inc_ref(v_v_759_);
lean_inc(v_head_762_);
v___x_821_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_761_, v___x_813_, v_index_809_, v_head_762_, v_v_759_);
lean_dec(v_index_809_);
v_as_x27_760_ = v_tail_763_;
v_b_761_ = v___x_821_;
goto _start;
}
}
}
default: 
{
lean_object* v_size_823_; lean_object* v_keyArray_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_size_823_ = lean_ctor_get(v_b_761_, 0);
v_keyArray_824_ = lean_ctor_get(v_b_761_, 1);
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = lean_nat_add(v_size_823_, v___x_825_);
v___x_827_ = lean_array_get_size(v_keyArray_824_);
v___x_828_ = lean_nat_dec_lt(v___x_826_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_dec(v___x_826_);
v___x_829_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_b_761_);
lean_dec_ref(v_b_761_);
v___y_773_ = v___x_829_;
goto v___jp_772_;
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_830_ = lean_unsigned_to_nat(4u);
v___x_831_ = lean_nat_mul(v___x_826_, v___x_830_);
lean_dec(v___x_826_);
v___x_832_ = lean_unsigned_to_nat(3u);
v___x_833_ = lean_nat_mul(v___x_827_, v___x_832_);
v___x_834_ = lean_nat_dec_le(v___x_831_, v___x_833_);
lean_dec(v___x_833_);
lean_dec(v___x_831_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_b_761_);
lean_dec_ref(v_b_761_);
v___y_773_ = v___x_835_;
goto v___jp_772_;
}
else
{
v___y_773_ = v_b_761_;
goto v___jp_772_;
}
}
}
}
v___jp_764_:
{
lean_object* v_size_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_size_767_ = lean_ctor_get(v___y_765_, 0);
v___x_768_ = lean_unsigned_to_nat(1u);
v___x_769_ = lean_nat_add(v_size_767_, v___x_768_);
lean_inc_ref(v_v_759_);
lean_inc(v_head_762_);
v___x_770_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_765_, v___x_769_, v_i_766_, v_head_762_, v_v_759_);
lean_dec(v_i_766_);
v_as_x27_760_ = v_tail_763_;
v_b_761_ = v___x_770_;
goto _start;
}
v___jp_772_:
{
lean_object* v___x_774_; 
v___x_774_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2___redArg(v___y_773_, v_head_762_);
switch(lean_obj_tag(v___x_774_))
{
case 0:
{
lean_object* v_index_775_; lean_object* v_size_776_; lean_object* v___x_777_; 
v_index_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_index_775_);
lean_dec_ref_known(v___x_774_, 3);
v_size_776_ = lean_ctor_get(v___y_773_, 0);
lean_inc(v_size_776_);
lean_inc_ref(v_v_759_);
lean_inc(v_head_762_);
v___x_777_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_773_, v_size_776_, v_index_775_, v_head_762_, v_v_759_);
lean_dec(v_index_775_);
v_as_x27_760_ = v_tail_763_;
v_b_761_ = v___x_777_;
goto _start;
}
case 1:
{
lean_object* v_index_779_; 
v_index_779_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_index_779_);
lean_dec_ref_known(v___x_774_, 1);
v___y_765_ = v___y_773_;
v_i_766_ = v_index_779_;
goto v___jp_764_;
}
default: 
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_773_, v___x_780_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_index_782_; 
v_index_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_index_782_);
lean_dec_ref_known(v___x_781_, 1);
v___y_765_ = v___y_773_;
v_i_766_ = v_index_782_;
goto v___jp_764_;
}
else
{
v_as_x27_760_ = v_tail_763_;
v_b_761_ = v___y_773_;
goto _start;
}
}
}
}
v___jp_784_:
{
lean_object* v_size_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_size_787_ = lean_ctor_get(v___y_785_, 0);
v___x_788_ = lean_unsigned_to_nat(1u);
v___x_789_ = lean_nat_add(v_size_787_, v___x_788_);
lean_inc_ref(v_v_759_);
lean_inc(v_head_762_);
v___x_790_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_785_, v___x_789_, v_i_786_, v_head_762_, v_v_759_);
lean_dec(v_i_786_);
v_as_x27_760_ = v_tail_763_;
v_b_761_ = v___x_790_;
goto _start;
}
v___jp_792_:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_b_761_);
lean_dec_ref(v_b_761_);
v___x_794_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0_spec__2___redArg(v___x_793_, v_head_762_);
switch(lean_obj_tag(v___x_794_))
{
case 0:
{
lean_object* v_index_795_; lean_object* v_size_796_; lean_object* v___x_797_; 
v_index_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_index_795_);
lean_dec_ref_known(v___x_794_, 3);
v_size_796_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_size_796_);
lean_inc_ref(v_v_759_);
lean_inc(v_head_762_);
v___x_797_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_793_, v_size_796_, v_index_795_, v_head_762_, v_v_759_);
lean_dec(v_index_795_);
v_as_x27_760_ = v_tail_763_;
v_b_761_ = v___x_797_;
goto _start;
}
case 1:
{
lean_object* v_index_799_; 
v_index_799_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_index_799_);
lean_dec_ref_known(v___x_794_, 1);
v___y_785_ = v___x_793_;
v_i_786_ = v_index_799_;
goto v___jp_784_;
}
default: 
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_793_, v___x_800_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_index_802_; 
v_index_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_index_802_);
lean_dec_ref_known(v___x_801_, 1);
v___y_785_ = v___x_793_;
v_i_786_ = v_index_802_;
goto v___jp_784_;
}
else
{
v_as_x27_760_ = v_tail_763_;
v_b_761_ = v___x_793_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg___boxed(lean_object* v_v_836_, lean_object* v_as_x27_837_, lean_object* v_b_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_836_, v_as_x27_837_, v_b_838_);
lean_dec(v_as_x27_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object* v_goal_840_, lean_object* v_e_841_, lean_object* v_v_842_, lean_object* v_a_843_){
_start:
{
uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = 0;
v___x_845_ = l_Lean_Meta_Grind_Goal_getEqc(v_goal_840_, v_e_841_, v___x_844_);
v___x_846_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_842_, v___x_845_, v_a_843_);
lean_dec(v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc___boxed(lean_object* v_goal_847_, lean_object* v_e_848_, lean_object* v_v_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_847_, v_e_848_, v_v_849_, v_a_850_);
lean_dec_ref(v_goal_847_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0(lean_object* v_00_u03b2_852_, lean_object* v_m_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_m_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___boxed(lean_object* v_00_u03b2_855_, lean_object* v_m_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0(v_00_u03b2_855_, v_m_856_);
lean_dec_ref(v_m_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(lean_object* v_v_858_, lean_object* v_as_859_, lean_object* v_as_x27_860_, lean_object* v_b_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_858_, v_as_x27_860_, v_b_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___boxed(lean_object* v_v_864_, lean_object* v_as_865_, lean_object* v_as_x27_866_, lean_object* v_b_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(v_v_864_, v_as_865_, v_as_x27_866_, v_b_867_, v_a_868_);
lean_dec(v_as_x27_866_);
lean_dec(v_as_865_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(lean_object* v_00_u03b2_870_, lean_object* v_init_871_, lean_object* v_b_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_init_871_, v_b_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_874_, lean_object* v_init_875_, lean_object* v_b_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(v_00_u03b2_874_, v_init_875_, v_b_876_);
lean_dec_ref(v_b_876_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_878_, lean_object* v_b_879_, lean_object* v_acc_880_, lean_object* v_i_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0_spec__1___redArg(v_b_879_, v_acc_880_, v_i_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_883_, lean_object* v_b_884_, lean_object* v_acc_885_, lean_object* v_i_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0_spec__1(v_00_u03b2_883_, v_b_884_, v_acc_885_, v_i_886_);
lean_dec_ref(v_b_884_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(lean_object* v_b_888_, lean_object* v_acc_889_, lean_object* v_i_890_){
_start:
{
lean_object* v___y_892_; lean_object* v_keyArray_900_; lean_object* v_valueArray_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v_keyArray_900_ = lean_ctor_get(v_b_888_, 1);
v_valueArray_901_ = lean_ctor_get(v_b_888_, 2);
v___x_902_ = lean_array_get_size(v_keyArray_900_);
v___x_903_ = lean_nat_dec_lt(v_i_890_, v___x_902_);
if (v___x_903_ == 0)
{
lean_dec(v_i_890_);
return v_acc_889_;
}
else
{
lean_object* v___x_904_; uint8_t v_isSome_905_; 
v___x_904_ = lean_array_fget_borrowed(v_keyArray_900_, v_i_890_);
v_isSome_905_ = lean_noption_is_some(v___x_904_);
if (v_isSome_905_ == 0)
{
goto v___jp_896_;
}
else
{
lean_object* v___x_906_; uint8_t v_isSome_907_; 
v___x_906_ = lean_array_fget_borrowed(v_valueArray_901_, v_i_890_);
v_isSome_907_ = lean_noption_is_some(v___x_906_);
if (v_isSome_907_ == 0)
{
goto v___jp_896_;
}
else
{
lean_object* v_val_908_; lean_object* v_val_909_; lean_object* v_i_911_; lean_object* v___x_916_; 
lean_inc(v___x_904_);
v_val_908_ = lean_noption_get(v___x_904_);
lean_inc(v___x_906_);
v_val_909_ = lean_noption_get(v___x_906_);
v___x_916_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v_acc_889_, v_val_908_);
switch(lean_obj_tag(v___x_916_))
{
case 0:
{
lean_object* v_index_917_; lean_object* v_size_918_; lean_object* v___x_919_; 
v_index_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_index_917_);
lean_dec_ref_known(v___x_916_, 3);
v_size_918_ = lean_ctor_get(v_acc_889_, 0);
lean_inc(v_size_918_);
v___x_919_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_889_, v_size_918_, v_index_917_, v_val_908_, v_val_909_);
lean_dec(v_index_917_);
v___y_892_ = v___x_919_;
goto v___jp_891_;
}
case 1:
{
lean_object* v_index_920_; 
v_index_920_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_index_920_);
lean_dec_ref_known(v___x_916_, 1);
v_i_911_ = v_index_920_;
goto v___jp_910_;
}
default: 
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_unsigned_to_nat(0u);
v___x_922_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_889_, v___x_921_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_index_923_; 
v_index_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_index_923_);
lean_dec_ref_known(v___x_922_, 1);
v_i_911_ = v_index_923_;
goto v___jp_910_;
}
else
{
lean_dec(v_val_909_);
lean_dec(v_val_908_);
v___y_892_ = v_acc_889_;
goto v___jp_891_;
}
}
}
v___jp_910_:
{
lean_object* v_size_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_size_912_ = lean_ctor_get(v_acc_889_, 0);
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = lean_nat_add(v_size_912_, v___x_913_);
v___x_915_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_889_, v___x_914_, v_i_911_, v_val_908_, v_val_909_);
lean_dec(v_i_911_);
v___y_892_ = v___x_915_;
goto v___jp_891_;
}
}
}
}
v___jp_891_:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_unsigned_to_nat(1u);
v___x_894_ = lean_nat_add(v_i_890_, v___x_893_);
lean_dec(v_i_890_);
v_acc_889_ = v___y_892_;
v_i_890_ = v___x_894_;
goto _start;
}
v___jp_896_:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = lean_unsigned_to_nat(1u);
v___x_898_ = lean_nat_add(v_i_890_, v___x_897_);
lean_dec(v_i_890_);
v_i_890_ = v___x_898_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_b_924_, lean_object* v_acc_925_, lean_object* v_i_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v_b_924_, v_acc_925_, v_i_926_);
lean_dec_ref(v_b_924_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(lean_object* v_init_928_, lean_object* v_b_929_){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v_b_929_, v_init_928_, v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg___boxed(lean_object* v_init_932_, lean_object* v_b_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_init_932_, v_b_933_);
lean_dec_ref(v_b_933_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(lean_object* v_m_935_){
_start:
{
lean_object* v_keyArray_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v_cellCount_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v_target_943_; lean_object* v___x_944_; 
v_keyArray_936_ = lean_ctor_get(v_m_935_, 1);
v___x_937_ = lean_array_get_size(v_keyArray_936_);
v___x_938_ = lean_unsigned_to_nat(2u);
v_cellCount_939_ = lean_nat_mul(v___x_937_, v___x_938_);
v___x_940_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_939_);
v___x_941_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_939_);
v___x_942_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_939_);
v_target_943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_943_, 0, v___x_940_);
lean_ctor_set(v_target_943_, 1, v___x_941_);
lean_ctor_set(v_target_943_, 2, v___x_942_);
v___x_944_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_target_943_, v_m_935_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg___boxed(lean_object* v_m_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_m_945_);
lean_dec_ref(v_m_945_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1_spec__2___redArg(lean_object* v_b_947_, lean_object* v_acc_948_, lean_object* v_i_949_){
_start:
{
lean_object* v_a_952_; lean_object* v_keyArray_960_; lean_object* v_valueArray_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v_keyArray_960_ = lean_ctor_get(v_b_947_, 1);
v_valueArray_961_ = lean_ctor_get(v_b_947_, 2);
v___x_962_ = lean_array_get_size(v_keyArray_960_);
v___x_963_ = lean_nat_dec_lt(v_i_949_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
lean_dec(v_i_949_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v_acc_948_);
return v___x_964_;
}
else
{
lean_object* v___x_965_; uint8_t v_isSome_966_; 
v___x_965_ = lean_array_fget_borrowed(v_keyArray_960_, v_i_949_);
v_isSome_966_ = lean_noption_is_some(v___x_965_);
if (v_isSome_966_ == 0)
{
goto v___jp_956_;
}
else
{
lean_object* v___x_967_; uint8_t v_isSome_968_; 
v___x_967_ = lean_array_fget_borrowed(v_valueArray_961_, v_i_949_);
v_isSome_968_ = lean_noption_is_some(v___x_967_);
if (v_isSome_968_ == 0)
{
goto v___jp_956_;
}
else
{
lean_object* v_val_969_; lean_object* v_num_970_; lean_object* v_den_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
lean_inc(v___x_967_);
v_val_969_ = lean_noption_get(v___x_967_);
v_num_970_ = lean_ctor_get(v_val_969_, 0);
lean_inc(v_num_970_);
v_den_971_ = lean_ctor_get(v_val_969_, 1);
lean_inc(v_den_971_);
lean_dec(v_val_969_);
v___x_972_ = lean_unsigned_to_nat(1u);
v___x_973_ = lean_nat_dec_eq(v_den_971_, v___x_972_);
lean_dec(v_den_971_);
if (v___x_973_ == 0)
{
lean_dec(v_num_970_);
v_a_952_ = v_acc_948_;
goto v___jp_951_;
}
else
{
lean_object* v___x_974_; lean_object* v___y_976_; lean_object* v_i_977_; lean_object* v___y_982_; lean_object* v___y_992_; lean_object* v_i_993_; lean_object* v___x_1007_; 
v___x_974_ = lean_box(0);
v___x_1007_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v_acc_948_, v_num_970_);
switch(lean_obj_tag(v___x_1007_))
{
case 0:
{
lean_dec_ref_known(v___x_1007_, 3);
lean_dec(v_num_970_);
v_a_952_ = v_acc_948_;
goto v___jp_951_;
}
case 1:
{
lean_object* v_index_1008_; lean_object* v_size_1009_; lean_object* v_keyArray_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v_index_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_index_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v_size_1009_ = lean_ctor_get(v_acc_948_, 0);
v_keyArray_1010_ = lean_ctor_get(v_acc_948_, 1);
v___x_1011_ = lean_nat_add(v_size_1009_, v___x_972_);
v___x_1012_ = lean_array_get_size(v_keyArray_1010_);
v___x_1013_ = lean_nat_dec_lt(v___x_1011_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_dec(v___x_1011_);
lean_dec(v_index_1008_);
goto v___jp_997_;
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1014_ = lean_unsigned_to_nat(4u);
v___x_1015_ = lean_nat_mul(v___x_1011_, v___x_1014_);
v___x_1016_ = lean_unsigned_to_nat(3u);
v___x_1017_ = lean_nat_mul(v___x_1012_, v___x_1016_);
v___x_1018_ = lean_nat_dec_le(v___x_1015_, v___x_1017_);
lean_dec(v___x_1017_);
lean_dec(v___x_1015_);
if (v___x_1018_ == 0)
{
lean_dec(v___x_1011_);
lean_dec(v_index_1008_);
goto v___jp_997_;
}
else
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_948_, v___x_1011_, v_index_1008_, v_num_970_, v___x_974_);
lean_dec(v_index_1008_);
v_a_952_ = v___x_1019_;
goto v___jp_951_;
}
}
}
default: 
{
lean_object* v_size_1020_; lean_object* v_keyArray_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_size_1020_ = lean_ctor_get(v_acc_948_, 0);
v_keyArray_1021_ = lean_ctor_get(v_acc_948_, 1);
v___x_1022_ = lean_nat_add(v_size_1020_, v___x_972_);
v___x_1023_ = lean_array_get_size(v_keyArray_1021_);
v___x_1024_ = lean_nat_dec_lt(v___x_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_dec(v___x_1022_);
v___x_1025_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_acc_948_);
lean_dec_ref(v_acc_948_);
v___y_982_ = v___x_1025_;
goto v___jp_981_;
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1026_ = lean_unsigned_to_nat(4u);
v___x_1027_ = lean_nat_mul(v___x_1022_, v___x_1026_);
lean_dec(v___x_1022_);
v___x_1028_ = lean_unsigned_to_nat(3u);
v___x_1029_ = lean_nat_mul(v___x_1023_, v___x_1028_);
v___x_1030_ = lean_nat_dec_le(v___x_1027_, v___x_1029_);
lean_dec(v___x_1029_);
lean_dec(v___x_1027_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_acc_948_);
lean_dec_ref(v_acc_948_);
v___y_982_ = v___x_1031_;
goto v___jp_981_;
}
else
{
v___y_982_ = v_acc_948_;
goto v___jp_981_;
}
}
}
}
v___jp_975_:
{
lean_object* v_size_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_size_978_ = lean_ctor_get(v___y_976_, 0);
v___x_979_ = lean_nat_add(v_size_978_, v___x_972_);
v___x_980_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_976_, v___x_979_, v_i_977_, v_num_970_, v___x_974_);
lean_dec(v_i_977_);
v_a_952_ = v___x_980_;
goto v___jp_951_;
}
v___jp_981_:
{
lean_object* v___x_983_; 
v___x_983_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v___y_982_, v_num_970_);
switch(lean_obj_tag(v___x_983_))
{
case 0:
{
lean_object* v_index_984_; lean_object* v_size_985_; lean_object* v___x_986_; 
v_index_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_index_984_);
lean_dec_ref_known(v___x_983_, 3);
v_size_985_ = lean_ctor_get(v___y_982_, 0);
lean_inc(v_size_985_);
v___x_986_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_982_, v_size_985_, v_index_984_, v_num_970_, v___x_974_);
lean_dec(v_index_984_);
v_a_952_ = v___x_986_;
goto v___jp_951_;
}
case 1:
{
lean_object* v_index_987_; 
v_index_987_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_index_987_);
lean_dec_ref_known(v___x_983_, 1);
v___y_976_ = v___y_982_;
v_i_977_ = v_index_987_;
goto v___jp_975_;
}
default: 
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_982_, v___x_988_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_index_990_; 
v_index_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_index_990_);
lean_dec_ref_known(v___x_989_, 1);
v___y_976_ = v___y_982_;
v_i_977_ = v_index_990_;
goto v___jp_975_;
}
else
{
lean_dec(v_num_970_);
v_a_952_ = v___y_982_;
goto v___jp_951_;
}
}
}
}
v___jp_991_:
{
lean_object* v_size_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_size_994_ = lean_ctor_get(v___y_992_, 0);
v___x_995_ = lean_nat_add(v_size_994_, v___x_972_);
v___x_996_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_992_, v___x_995_, v_i_993_, v_num_970_, v___x_974_);
lean_dec(v_i_993_);
v_a_952_ = v___x_996_;
goto v___jp_951_;
}
v___jp_997_:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_acc_948_);
lean_dec_ref(v_acc_948_);
v___x_999_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v___x_998_, v_num_970_);
switch(lean_obj_tag(v___x_999_))
{
case 0:
{
lean_object* v_index_1000_; lean_object* v_size_1001_; lean_object* v___x_1002_; 
v_index_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_index_1000_);
lean_dec_ref_known(v___x_999_, 3);
v_size_1001_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_size_1001_);
v___x_1002_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_998_, v_size_1001_, v_index_1000_, v_num_970_, v___x_974_);
lean_dec(v_index_1000_);
v_a_952_ = v___x_1002_;
goto v___jp_951_;
}
case 1:
{
lean_object* v_index_1003_; 
v_index_1003_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_index_1003_);
lean_dec_ref_known(v___x_999_, 1);
v___y_992_ = v___x_998_;
v_i_993_ = v_index_1003_;
goto v___jp_991_;
}
default: 
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_998_, v___x_1004_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_index_1006_; 
v_index_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_index_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___y_992_ = v___x_998_;
v_i_993_ = v_index_1006_;
goto v___jp_991_;
}
else
{
lean_dec(v_num_970_);
v_a_952_ = v___x_998_;
goto v___jp_951_;
}
}
}
}
}
}
}
}
v___jp_951_:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_nat_add(v_i_949_, v___x_953_);
lean_dec(v_i_949_);
v_acc_948_ = v_a_952_;
v_i_949_ = v___x_954_;
goto _start;
}
v___jp_956_:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_unsigned_to_nat(1u);
v___x_958_ = lean_nat_add(v_i_949_, v___x_957_);
lean_dec(v_i_949_);
v_i_949_ = v___x_958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1_spec__2___redArg___boxed(lean_object* v_b_1032_, lean_object* v_acc_1033_, lean_object* v_i_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1_spec__2___redArg(v_b_1032_, v_acc_1033_, v_i_1034_);
lean_dec_ref(v_b_1032_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(lean_object* v_init_1037_, lean_object* v_b_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1_spec__2___redArg(v_b_1038_, v_init_1037_, v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___boxed(lean_object* v_init_1046_, lean_object* v_b_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(v_init_1046_, v_b_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec_ref(v_b_1047_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__7_spec__8(lean_object* v_goal_1054_, lean_object* v_isTarget_1055_, lean_object* v_as_1056_, size_t v_sz_1057_, size_t v_i_1058_, lean_object* v_b_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
uint8_t v___x_1065_; 
v___x_1065_ = lean_usize_dec_lt(v_i_1058_, v_sz_1057_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
lean_dec_ref(v_isTarget_1055_);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_b_1059_);
return v___x_1066_;
}
else
{
lean_object* v_snd_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1211_; 
v_snd_1067_ = lean_ctor_get(v_b_1059_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_b_1059_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v_b_1059_, 0);
lean_dec(v_unused_1212_);
v___x_1069_ = v_b_1059_;
v_isShared_1070_ = v_isSharedCheck_1211_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_snd_1067_);
lean_dec(v_b_1059_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1211_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v_a_1071_; lean_object* v___x_1072_; 
v_a_1071_ = lean_array_uget_borrowed(v_as_1056_, v_i_1058_);
lean_inc(v_a_1071_);
v___x_1072_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1054_, v_a_1071_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_snd_1073_; lean_object* v_a_1074_; lean_object* v_fst_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1201_; 
v_snd_1073_ = lean_ctor_get(v_snd_1067_, 1);
lean_inc(v_snd_1073_);
v_a_1074_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1072_, 1);
v_fst_1075_ = lean_ctor_get(v_snd_1067_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_snd_1067_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v_snd_1067_, 1);
lean_dec(v_unused_1202_);
v___x_1077_ = v_snd_1067_;
v_isShared_1078_ = v_isSharedCheck_1201_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_fst_1075_);
lean_dec(v_snd_1067_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1201_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v_fst_1079_; lean_object* v_snd_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1200_; 
v_fst_1079_ = lean_ctor_get(v_snd_1073_, 0);
v_snd_1080_ = lean_ctor_get(v_snd_1073_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_snd_1073_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1082_ = v_snd_1073_;
v_isShared_1083_ = v_isSharedCheck_1200_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_snd_1080_);
lean_inc(v_fst_1079_);
lean_dec(v_snd_1073_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1200_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v_a_1086_; uint8_t v___x_1093_; 
v___x_1084_ = lean_box(0);
v___x_1093_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1074_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1095_; 
lean_dec(v_a_1074_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v_snd_1080_);
lean_ctor_set(v___x_1077_, 0, v_fst_1079_);
v___x_1095_ = v___x_1077_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_fst_1079_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_snd_1080_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 1, v___x_1095_);
lean_ctor_set(v___x_1069_, 0, v_fst_1075_);
v___x_1097_ = v___x_1069_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_fst_1075_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
v_a_1086_ = v___x_1097_;
goto v___jp_1085_;
}
}
}
else
{
lean_object* v___x_1100_; 
lean_inc_ref(v_isTarget_1055_);
lean_inc(v___y_1063_);
lean_inc_ref(v___y_1062_);
lean_inc(v___y_1061_);
lean_inc_ref(v___y_1060_);
lean_inc(v_a_1074_);
v___x_1100_ = lean_apply_6(v_isTarget_1055_, v_a_1074_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, lean_box(0));
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; uint8_t v___x_1102_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v___x_1102_ = lean_unbox(v_a_1101_);
lean_dec(v_a_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1104_; 
lean_dec(v_a_1074_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v_snd_1080_);
lean_ctor_set(v___x_1077_, 0, v_fst_1079_);
v___x_1104_ = v___x_1077_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_fst_1079_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_snd_1080_);
v___x_1104_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1106_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 1, v___x_1104_);
lean_ctor_set(v___x_1069_, 0, v_fst_1075_);
v___x_1106_ = v___x_1069_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_fst_1075_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
v_a_1086_ = v___x_1106_;
goto v___jp_1085_;
}
}
}
else
{
lean_object* v_self_1109_; lean_object* v___x_1110_; 
v_self_1109_ = lean_ctor_get(v_a_1074_, 0);
lean_inc_ref(v_self_1109_);
lean_dec(v_a_1074_);
v___x_1110_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1080_, v_self_1109_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___y_1115_; lean_object* v___x_1124_; lean_object* v___y_1126_; lean_object* v_i_1127_; lean_object* v___y_1133_; lean_object* v___y_1143_; lean_object* v_i_1144_; lean_object* v___x_1159_; 
v___x_1111_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1054_, v_snd_1080_, v_self_1109_, v_fst_1079_, v_fst_1075_);
lean_inc(v___x_1111_);
v___x_1112_ = l_Rat_ofInt(v___x_1111_);
v___x_1113_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1054_, v_self_1109_, v___x_1112_, v_snd_1080_);
v___x_1124_ = lean_box(0);
v___x_1159_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v_fst_1079_, v___x_1111_);
switch(lean_obj_tag(v___x_1159_))
{
case 0:
{
lean_dec_ref_known(v___x_1159_, 3);
v___y_1115_ = v_fst_1079_;
goto v___jp_1114_;
}
case 1:
{
lean_object* v_index_1160_; lean_object* v_size_1161_; lean_object* v_keyArray_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v_index_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_index_1160_);
lean_dec_ref_known(v___x_1159_, 1);
v_size_1161_ = lean_ctor_get(v_fst_1079_, 0);
v_keyArray_1162_ = lean_ctor_get(v_fst_1079_, 1);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_add(v_size_1161_, v___x_1163_);
v___x_1165_ = lean_array_get_size(v_keyArray_1162_);
v___x_1166_ = lean_nat_dec_lt(v___x_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_dec(v___x_1164_);
lean_dec(v_index_1160_);
goto v___jp_1149_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1167_ = lean_unsigned_to_nat(4u);
v___x_1168_ = lean_nat_mul(v___x_1164_, v___x_1167_);
v___x_1169_ = lean_unsigned_to_nat(3u);
v___x_1170_ = lean_nat_mul(v___x_1165_, v___x_1169_);
v___x_1171_ = lean_nat_dec_le(v___x_1168_, v___x_1170_);
lean_dec(v___x_1170_);
lean_dec(v___x_1168_);
if (v___x_1171_ == 0)
{
lean_dec(v___x_1164_);
lean_dec(v_index_1160_);
goto v___jp_1149_;
}
else
{
lean_object* v___x_1172_; 
lean_inc(v___x_1111_);
v___x_1172_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_1079_, v___x_1164_, v_index_1160_, v___x_1111_, v___x_1124_);
lean_dec(v_index_1160_);
v___y_1115_ = v___x_1172_;
goto v___jp_1114_;
}
}
}
default: 
{
lean_object* v_size_1173_; lean_object* v_keyArray_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_size_1173_ = lean_ctor_get(v_fst_1079_, 0);
v_keyArray_1174_ = lean_ctor_get(v_fst_1079_, 1);
v___x_1175_ = lean_unsigned_to_nat(1u);
v___x_1176_ = lean_nat_add(v_size_1173_, v___x_1175_);
v___x_1177_ = lean_array_get_size(v_keyArray_1174_);
v___x_1178_ = lean_nat_dec_lt(v___x_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
lean_dec(v___x_1176_);
v___x_1179_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1079_);
lean_dec(v_fst_1079_);
v___y_1133_ = v___x_1179_;
goto v___jp_1132_;
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1180_ = lean_unsigned_to_nat(4u);
v___x_1181_ = lean_nat_mul(v___x_1176_, v___x_1180_);
lean_dec(v___x_1176_);
v___x_1182_ = lean_unsigned_to_nat(3u);
v___x_1183_ = lean_nat_mul(v___x_1177_, v___x_1182_);
v___x_1184_ = lean_nat_dec_le(v___x_1181_, v___x_1183_);
lean_dec(v___x_1183_);
lean_dec(v___x_1181_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1079_);
lean_dec(v_fst_1079_);
v___y_1133_ = v___x_1185_;
goto v___jp_1132_;
}
else
{
v___y_1133_ = v_fst_1079_;
goto v___jp_1132_;
}
}
}
}
v___jp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1116_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1117_ = lean_int_add(v___x_1111_, v___x_1116_);
lean_dec(v___x_1111_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1113_);
lean_ctor_set(v___x_1077_, 0, v___y_1115_);
v___x_1119_ = v___x_1077_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___y_1115_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v___x_1113_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 1, v___x_1119_);
lean_ctor_set(v___x_1069_, 0, v___x_1117_);
v___x_1121_ = v___x_1069_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
v_a_1086_ = v___x_1121_;
goto v___jp_1085_;
}
}
}
v___jp_1125_:
{
lean_object* v_size_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_size_1128_ = lean_ctor_get(v___y_1126_, 0);
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = lean_nat_add(v_size_1128_, v___x_1129_);
lean_inc(v___x_1111_);
v___x_1131_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1126_, v___x_1130_, v_i_1127_, v___x_1111_, v___x_1124_);
lean_dec(v_i_1127_);
v___y_1115_ = v___x_1131_;
goto v___jp_1114_;
}
v___jp_1132_:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v___y_1133_, v___x_1111_);
switch(lean_obj_tag(v___x_1134_))
{
case 0:
{
lean_object* v_index_1135_; lean_object* v_size_1136_; lean_object* v___x_1137_; 
v_index_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_index_1135_);
lean_dec_ref_known(v___x_1134_, 3);
v_size_1136_ = lean_ctor_get(v___y_1133_, 0);
lean_inc(v_size_1136_);
lean_inc(v___x_1111_);
v___x_1137_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1133_, v_size_1136_, v_index_1135_, v___x_1111_, v___x_1124_);
lean_dec(v_index_1135_);
v___y_1115_ = v___x_1137_;
goto v___jp_1114_;
}
case 1:
{
lean_object* v_index_1138_; 
v_index_1138_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_index_1138_);
lean_dec_ref_known(v___x_1134_, 1);
v___y_1126_ = v___y_1133_;
v_i_1127_ = v_index_1138_;
goto v___jp_1125_;
}
default: 
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1133_, v___x_1139_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_index_1141_; 
v_index_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_index_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v___y_1126_ = v___y_1133_;
v_i_1127_ = v_index_1141_;
goto v___jp_1125_;
}
else
{
v___y_1115_ = v___y_1133_;
goto v___jp_1114_;
}
}
}
}
v___jp_1142_:
{
lean_object* v_size_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_size_1145_ = lean_ctor_get(v___y_1143_, 0);
v___x_1146_ = lean_unsigned_to_nat(1u);
v___x_1147_ = lean_nat_add(v_size_1145_, v___x_1146_);
lean_inc(v___x_1111_);
v___x_1148_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1143_, v___x_1147_, v_i_1144_, v___x_1111_, v___x_1124_);
lean_dec(v_i_1144_);
v___y_1115_ = v___x_1148_;
goto v___jp_1114_;
}
v___jp_1149_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1079_);
lean_dec(v_fst_1079_);
v___x_1151_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v___x_1150_, v___x_1111_);
switch(lean_obj_tag(v___x_1151_))
{
case 0:
{
lean_object* v_index_1152_; lean_object* v_size_1153_; lean_object* v___x_1154_; 
v_index_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_index_1152_);
lean_dec_ref_known(v___x_1151_, 3);
v_size_1153_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_size_1153_);
lean_inc(v___x_1111_);
v___x_1154_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1150_, v_size_1153_, v_index_1152_, v___x_1111_, v___x_1124_);
lean_dec(v_index_1152_);
v___y_1115_ = v___x_1154_;
goto v___jp_1114_;
}
case 1:
{
lean_object* v_index_1155_; 
v_index_1155_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_index_1155_);
lean_dec_ref_known(v___x_1151_, 1);
v___y_1143_ = v___x_1150_;
v_i_1144_ = v_index_1155_;
goto v___jp_1142_;
}
default: 
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1150_, v___x_1156_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_index_1158_; 
v_index_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_index_1158_);
lean_dec_ref_known(v___x_1157_, 1);
v___y_1143_ = v___x_1150_;
v_i_1144_ = v_index_1158_;
goto v___jp_1142_;
}
else
{
v___y_1115_ = v___x_1150_;
goto v___jp_1114_;
}
}
}
}
}
else
{
lean_object* v___x_1187_; 
lean_dec_ref_known(v___x_1110_, 1);
lean_dec_ref(v_self_1109_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v_snd_1080_);
lean_ctor_set(v___x_1077_, 0, v_fst_1079_);
v___x_1187_ = v___x_1077_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_fst_1079_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_snd_1080_);
v___x_1187_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 1, v___x_1187_);
lean_ctor_set(v___x_1069_, 0, v_fst_1075_);
v___x_1189_ = v___x_1069_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_fst_1075_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
v_a_1086_ = v___x_1189_;
goto v___jp_1085_;
}
}
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_del_object(v___x_1082_);
lean_dec(v_snd_1080_);
lean_dec(v_fst_1079_);
lean_del_object(v___x_1077_);
lean_dec(v_fst_1075_);
lean_dec(v_a_1074_);
lean_del_object(v___x_1069_);
lean_dec_ref(v_isTarget_1055_);
v_a_1192_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1100_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1100_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
v___jp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 1, v_a_1086_);
lean_ctor_set(v___x_1082_, 0, v___x_1084_);
v___x_1088_ = v___x_1082_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_a_1086_);
v___x_1088_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
size_t v___x_1089_; size_t v___x_1090_; 
v___x_1089_ = ((size_t)1ULL);
v___x_1090_ = lean_usize_add(v_i_1058_, v___x_1089_);
v_i_1058_ = v___x_1090_;
v_b_1059_ = v___x_1088_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_del_object(v___x_1069_);
lean_dec(v_snd_1067_);
lean_dec_ref(v_isTarget_1055_);
v_a_1203_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1072_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1072_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__7_spec__8___boxed(lean_object* v_goal_1213_, lean_object* v_isTarget_1214_, lean_object* v_as_1215_, lean_object* v_sz_1216_, lean_object* v_i_1217_, lean_object* v_b_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
size_t v_sz_boxed_1224_; size_t v_i_boxed_1225_; lean_object* v_res_1226_; 
v_sz_boxed_1224_ = lean_unbox_usize(v_sz_1216_);
lean_dec(v_sz_1216_);
v_i_boxed_1225_ = lean_unbox_usize(v_i_1217_);
lean_dec(v_i_1217_);
v_res_1226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__7_spec__8(v_goal_1213_, v_isTarget_1214_, v_as_1215_, v_sz_boxed_1224_, v_i_boxed_1225_, v_b_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v_as_1215_);
lean_dec_ref(v_goal_1213_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__7(lean_object* v_goal_1227_, lean_object* v_isTarget_1228_, lean_object* v_as_1229_, size_t v_sz_1230_, size_t v_i_1231_, lean_object* v_b_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
uint8_t v___x_1238_; 
v___x_1238_ = lean_usize_dec_lt(v_i_1231_, v_sz_1230_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_dec_ref(v_isTarget_1228_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v_b_1232_);
return v___x_1239_;
}
else
{
lean_object* v_snd_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1384_; 
v_snd_1240_ = lean_ctor_get(v_b_1232_, 1);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_b_1232_);
if (v_isSharedCheck_1384_ == 0)
{
lean_object* v_unused_1385_; 
v_unused_1385_ = lean_ctor_get(v_b_1232_, 0);
lean_dec(v_unused_1385_);
v___x_1242_ = v_b_1232_;
v_isShared_1243_ = v_isSharedCheck_1384_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_snd_1240_);
lean_dec(v_b_1232_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1384_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_a_1244_; lean_object* v___x_1245_; 
v_a_1244_ = lean_array_uget_borrowed(v_as_1229_, v_i_1231_);
lean_inc(v_a_1244_);
v___x_1245_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1227_, v_a_1244_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_snd_1246_; lean_object* v_a_1247_; lean_object* v_fst_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1374_; 
v_snd_1246_ = lean_ctor_get(v_snd_1240_, 1);
lean_inc(v_snd_1246_);
v_a_1247_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1245_, 1);
v_fst_1248_ = lean_ctor_get(v_snd_1240_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_snd_1240_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; 
v_unused_1375_ = lean_ctor_get(v_snd_1240_, 1);
lean_dec(v_unused_1375_);
v___x_1250_ = v_snd_1240_;
v_isShared_1251_ = v_isSharedCheck_1374_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_fst_1248_);
lean_dec(v_snd_1240_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1374_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v_fst_1252_; lean_object* v_snd_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1373_; 
v_fst_1252_ = lean_ctor_get(v_snd_1246_, 0);
v_snd_1253_ = lean_ctor_get(v_snd_1246_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_snd_1246_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1255_ = v_snd_1246_;
v_isShared_1256_ = v_isSharedCheck_1373_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_snd_1253_);
lean_inc(v_fst_1252_);
lean_dec(v_snd_1246_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1373_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v_a_1259_; uint8_t v___x_1266_; 
v___x_1257_ = lean_box(0);
v___x_1266_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1247_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1268_; 
lean_dec(v_a_1247_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v_snd_1253_);
lean_ctor_set(v___x_1250_, 0, v_fst_1252_);
v___x_1268_ = v___x_1250_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_fst_1252_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_snd_1253_);
v___x_1268_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1270_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___x_1268_);
lean_ctor_set(v___x_1242_, 0, v_fst_1248_);
v___x_1270_ = v___x_1242_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_fst_1248_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
v_a_1259_ = v___x_1270_;
goto v___jp_1258_;
}
}
}
else
{
lean_object* v___x_1273_; 
lean_inc_ref(v_isTarget_1228_);
lean_inc(v___y_1236_);
lean_inc_ref(v___y_1235_);
lean_inc(v___y_1234_);
lean_inc_ref(v___y_1233_);
lean_inc(v_a_1247_);
v___x_1273_ = lean_apply_6(v_isTarget_1228_, v_a_1247_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, lean_box(0));
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; uint8_t v___x_1275_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v___x_1273_, 1);
v___x_1275_ = lean_unbox(v_a_1274_);
lean_dec(v_a_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1277_; 
lean_dec(v_a_1247_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v_snd_1253_);
lean_ctor_set(v___x_1250_, 0, v_fst_1252_);
v___x_1277_ = v___x_1250_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_fst_1252_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_snd_1253_);
v___x_1277_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1279_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___x_1277_);
lean_ctor_set(v___x_1242_, 0, v_fst_1248_);
v___x_1279_ = v___x_1242_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_fst_1248_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
v_a_1259_ = v___x_1279_;
goto v___jp_1258_;
}
}
}
else
{
lean_object* v_self_1282_; lean_object* v___x_1283_; 
v_self_1282_ = lean_ctor_get(v_a_1247_, 0);
lean_inc_ref(v_self_1282_);
lean_dec(v_a_1247_);
v___x_1283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1253_, v_self_1282_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___y_1288_; lean_object* v___x_1297_; lean_object* v___y_1299_; lean_object* v_i_1300_; lean_object* v___y_1306_; lean_object* v___y_1316_; lean_object* v_i_1317_; lean_object* v___x_1332_; 
v___x_1284_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1227_, v_snd_1253_, v_self_1282_, v_fst_1252_, v_fst_1248_);
lean_inc(v___x_1284_);
v___x_1285_ = l_Rat_ofInt(v___x_1284_);
v___x_1286_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1227_, v_self_1282_, v___x_1285_, v_snd_1253_);
v___x_1297_ = lean_box(0);
v___x_1332_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v_fst_1252_, v___x_1284_);
switch(lean_obj_tag(v___x_1332_))
{
case 0:
{
lean_dec_ref_known(v___x_1332_, 3);
v___y_1288_ = v_fst_1252_;
goto v___jp_1287_;
}
case 1:
{
lean_object* v_index_1333_; lean_object* v_size_1334_; lean_object* v_keyArray_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v_index_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_index_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v_size_1334_ = lean_ctor_get(v_fst_1252_, 0);
v_keyArray_1335_ = lean_ctor_get(v_fst_1252_, 1);
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_nat_add(v_size_1334_, v___x_1336_);
v___x_1338_ = lean_array_get_size(v_keyArray_1335_);
v___x_1339_ = lean_nat_dec_lt(v___x_1337_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_dec(v___x_1337_);
lean_dec(v_index_1333_);
goto v___jp_1322_;
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1340_ = lean_unsigned_to_nat(4u);
v___x_1341_ = lean_nat_mul(v___x_1337_, v___x_1340_);
v___x_1342_ = lean_unsigned_to_nat(3u);
v___x_1343_ = lean_nat_mul(v___x_1338_, v___x_1342_);
v___x_1344_ = lean_nat_dec_le(v___x_1341_, v___x_1343_);
lean_dec(v___x_1343_);
lean_dec(v___x_1341_);
if (v___x_1344_ == 0)
{
lean_dec(v___x_1337_);
lean_dec(v_index_1333_);
goto v___jp_1322_;
}
else
{
lean_object* v___x_1345_; 
lean_inc(v___x_1284_);
v___x_1345_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_1252_, v___x_1337_, v_index_1333_, v___x_1284_, v___x_1297_);
lean_dec(v_index_1333_);
v___y_1288_ = v___x_1345_;
goto v___jp_1287_;
}
}
}
default: 
{
lean_object* v_size_1346_; lean_object* v_keyArray_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v_size_1346_ = lean_ctor_get(v_fst_1252_, 0);
v_keyArray_1347_ = lean_ctor_get(v_fst_1252_, 1);
v___x_1348_ = lean_unsigned_to_nat(1u);
v___x_1349_ = lean_nat_add(v_size_1346_, v___x_1348_);
v___x_1350_ = lean_array_get_size(v_keyArray_1347_);
v___x_1351_ = lean_nat_dec_lt(v___x_1349_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
lean_dec(v___x_1349_);
v___x_1352_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1252_);
lean_dec(v_fst_1252_);
v___y_1306_ = v___x_1352_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1353_ = lean_unsigned_to_nat(4u);
v___x_1354_ = lean_nat_mul(v___x_1349_, v___x_1353_);
lean_dec(v___x_1349_);
v___x_1355_ = lean_unsigned_to_nat(3u);
v___x_1356_ = lean_nat_mul(v___x_1350_, v___x_1355_);
v___x_1357_ = lean_nat_dec_le(v___x_1354_, v___x_1356_);
lean_dec(v___x_1356_);
lean_dec(v___x_1354_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1252_);
lean_dec(v_fst_1252_);
v___y_1306_ = v___x_1358_;
goto v___jp_1305_;
}
else
{
v___y_1306_ = v_fst_1252_;
goto v___jp_1305_;
}
}
}
}
v___jp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1289_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1290_ = lean_int_add(v___x_1284_, v___x_1289_);
lean_dec(v___x_1284_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v___x_1286_);
lean_ctor_set(v___x_1250_, 0, v___y_1288_);
v___x_1292_ = v___x_1250_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___y_1288_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v___x_1286_);
v___x_1292_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1294_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___x_1292_);
lean_ctor_set(v___x_1242_, 0, v___x_1290_);
v___x_1294_ = v___x_1242_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
v_a_1259_ = v___x_1294_;
goto v___jp_1258_;
}
}
}
v___jp_1298_:
{
lean_object* v_size_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_size_1301_ = lean_ctor_get(v___y_1299_, 0);
v___x_1302_ = lean_unsigned_to_nat(1u);
v___x_1303_ = lean_nat_add(v_size_1301_, v___x_1302_);
lean_inc(v___x_1284_);
v___x_1304_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1299_, v___x_1303_, v_i_1300_, v___x_1284_, v___x_1297_);
lean_dec(v_i_1300_);
v___y_1288_ = v___x_1304_;
goto v___jp_1287_;
}
v___jp_1305_:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v___y_1306_, v___x_1284_);
switch(lean_obj_tag(v___x_1307_))
{
case 0:
{
lean_object* v_index_1308_; lean_object* v_size_1309_; lean_object* v___x_1310_; 
v_index_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_index_1308_);
lean_dec_ref_known(v___x_1307_, 3);
v_size_1309_ = lean_ctor_get(v___y_1306_, 0);
lean_inc(v_size_1309_);
lean_inc(v___x_1284_);
v___x_1310_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1306_, v_size_1309_, v_index_1308_, v___x_1284_, v___x_1297_);
lean_dec(v_index_1308_);
v___y_1288_ = v___x_1310_;
goto v___jp_1287_;
}
case 1:
{
lean_object* v_index_1311_; 
v_index_1311_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_index_1311_);
lean_dec_ref_known(v___x_1307_, 1);
v___y_1299_ = v___y_1306_;
v_i_1300_ = v_index_1311_;
goto v___jp_1298_;
}
default: 
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1306_, v___x_1312_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_index_1314_; 
v_index_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_index_1314_);
lean_dec_ref_known(v___x_1313_, 1);
v___y_1299_ = v___y_1306_;
v_i_1300_ = v_index_1314_;
goto v___jp_1298_;
}
else
{
v___y_1288_ = v___y_1306_;
goto v___jp_1287_;
}
}
}
}
v___jp_1315_:
{
lean_object* v_size_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_size_1318_ = lean_ctor_get(v___y_1316_, 0);
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1320_ = lean_nat_add(v_size_1318_, v___x_1319_);
lean_inc(v___x_1284_);
v___x_1321_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1316_, v___x_1320_, v_i_1317_, v___x_1284_, v___x_1297_);
lean_dec(v_i_1317_);
v___y_1288_ = v___x_1321_;
goto v___jp_1287_;
}
v___jp_1322_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1252_);
lean_dec(v_fst_1252_);
v___x_1324_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v___x_1323_, v___x_1284_);
switch(lean_obj_tag(v___x_1324_))
{
case 0:
{
lean_object* v_index_1325_; lean_object* v_size_1326_; lean_object* v___x_1327_; 
v_index_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_index_1325_);
lean_dec_ref_known(v___x_1324_, 3);
v_size_1326_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_size_1326_);
lean_inc(v___x_1284_);
v___x_1327_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1323_, v_size_1326_, v_index_1325_, v___x_1284_, v___x_1297_);
lean_dec(v_index_1325_);
v___y_1288_ = v___x_1327_;
goto v___jp_1287_;
}
case 1:
{
lean_object* v_index_1328_; 
v_index_1328_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_index_1328_);
lean_dec_ref_known(v___x_1324_, 1);
v___y_1316_ = v___x_1323_;
v_i_1317_ = v_index_1328_;
goto v___jp_1315_;
}
default: 
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1323_, v___x_1329_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_index_1331_; 
v_index_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_index_1331_);
lean_dec_ref_known(v___x_1330_, 1);
v___y_1316_ = v___x_1323_;
v_i_1317_ = v_index_1331_;
goto v___jp_1315_;
}
else
{
v___y_1288_ = v___x_1323_;
goto v___jp_1287_;
}
}
}
}
}
else
{
lean_object* v___x_1360_; 
lean_dec_ref_known(v___x_1283_, 1);
lean_dec_ref(v_self_1282_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v_snd_1253_);
lean_ctor_set(v___x_1250_, 0, v_fst_1252_);
v___x_1360_ = v___x_1250_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_fst_1252_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_snd_1253_);
v___x_1360_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1362_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___x_1360_);
lean_ctor_set(v___x_1242_, 0, v_fst_1248_);
v___x_1362_ = v___x_1242_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_fst_1248_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
v_a_1259_ = v___x_1362_;
goto v___jp_1258_;
}
}
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_del_object(v___x_1255_);
lean_dec(v_snd_1253_);
lean_dec(v_fst_1252_);
lean_del_object(v___x_1250_);
lean_dec(v_fst_1248_);
lean_dec(v_a_1247_);
lean_del_object(v___x_1242_);
lean_dec_ref(v_isTarget_1228_);
v_a_1365_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1273_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1273_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
v___jp_1258_:
{
lean_object* v___x_1261_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 1, v_a_1259_);
lean_ctor_set(v___x_1255_, 0, v___x_1257_);
v___x_1261_ = v___x_1255_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_a_1259_);
v___x_1261_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
size_t v___x_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = ((size_t)1ULL);
v___x_1263_ = lean_usize_add(v_i_1231_, v___x_1262_);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__7_spec__8(v_goal_1227_, v_isTarget_1228_, v_as_1229_, v_sz_1230_, v___x_1263_, v___x_1261_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
return v___x_1264_;
}
}
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
lean_dec_ref(v_isTarget_1228_);
v_a_1376_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1245_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1245_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__7___boxed(lean_object* v_goal_1386_, lean_object* v_isTarget_1387_, lean_object* v_as_1388_, lean_object* v_sz_1389_, lean_object* v_i_1390_, lean_object* v_b_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
size_t v_sz_boxed_1397_; size_t v_i_boxed_1398_; lean_object* v_res_1399_; 
v_sz_boxed_1397_ = lean_unbox_usize(v_sz_1389_);
lean_dec(v_sz_1389_);
v_i_boxed_1398_ = lean_unbox_usize(v_i_1390_);
lean_dec(v_i_1390_);
v_res_1399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__7(v_goal_1386_, v_isTarget_1387_, v_as_1388_, v_sz_boxed_1397_, v_i_boxed_1398_, v_b_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec_ref(v_as_1388_);
lean_dec_ref(v_goal_1386_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4(lean_object* v_init_1400_, lean_object* v_goal_1401_, lean_object* v_isTarget_1402_, lean_object* v_n_1403_, lean_object* v_b_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
if (lean_obj_tag(v_n_1403_) == 0)
{
lean_object* v_cs_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; size_t v_sz_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
v_cs_1410_ = lean_ctor_get(v_n_1403_, 0);
v___x_1411_ = lean_box(0);
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
lean_ctor_set(v___x_1412_, 1, v_b_1404_);
v_sz_1413_ = lean_array_size(v_cs_1410_);
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__6(v_init_1400_, v_goal_1401_, v_isTarget_1402_, v_cs_1410_, v_sz_1413_, v___x_1414_, v___x_1412_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1430_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1430_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1430_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_fst_1420_; 
v_fst_1420_ = lean_ctor_get(v_a_1416_, 0);
if (lean_obj_tag(v_fst_1420_) == 0)
{
lean_object* v_snd_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
v_snd_1421_ = lean_ctor_get(v_a_1416_, 1);
lean_inc(v_snd_1421_);
lean_dec(v_a_1416_);
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v_snd_1421_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1422_);
v___x_1424_ = v___x_1418_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
else
{
lean_object* v_val_1426_; lean_object* v___x_1428_; 
lean_inc_ref(v_fst_1420_);
lean_dec(v_a_1416_);
v_val_1426_ = lean_ctor_get(v_fst_1420_, 0);
lean_inc(v_val_1426_);
lean_dec_ref_known(v_fst_1420_, 1);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v_val_1426_);
v___x_1428_ = v___x_1418_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_val_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
v_a_1431_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1415_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1415_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_vs_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; size_t v_sz_1442_; size_t v___x_1443_; lean_object* v___x_1444_; 
v_vs_1439_ = lean_ctor_get(v_n_1403_, 0);
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
lean_ctor_set(v___x_1441_, 1, v_b_1404_);
v_sz_1442_ = lean_array_size(v_vs_1439_);
v___x_1443_ = ((size_t)0ULL);
v___x_1444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__7(v_goal_1401_, v_isTarget_1402_, v_vs_1439_, v_sz_1442_, v___x_1443_, v___x_1441_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1459_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1447_ = v___x_1444_;
v_isShared_1448_ = v_isSharedCheck_1459_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1459_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v_fst_1449_; 
v_fst_1449_ = lean_ctor_get(v_a_1445_, 0);
if (lean_obj_tag(v_fst_1449_) == 0)
{
lean_object* v_snd_1450_; lean_object* v___x_1451_; lean_object* v___x_1453_; 
v_snd_1450_ = lean_ctor_get(v_a_1445_, 1);
lean_inc(v_snd_1450_);
lean_dec(v_a_1445_);
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_snd_1450_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1451_);
v___x_1453_ = v___x_1447_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
else
{
lean_object* v_val_1455_; lean_object* v___x_1457_; 
lean_inc_ref(v_fst_1449_);
lean_dec(v_a_1445_);
v_val_1455_ = lean_ctor_get(v_fst_1449_, 0);
lean_inc(v_val_1455_);
lean_dec_ref_known(v_fst_1449_, 1);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v_val_1455_);
v___x_1457_ = v___x_1447_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_val_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
v_a_1460_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1444_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1444_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__6(lean_object* v_init_1468_, lean_object* v_goal_1469_, lean_object* v_isTarget_1470_, lean_object* v_as_1471_, size_t v_sz_1472_, size_t v_i_1473_, lean_object* v_b_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
uint8_t v___x_1480_; 
v___x_1480_ = lean_usize_dec_lt(v_i_1473_, v_sz_1472_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; 
lean_dec_ref(v_isTarget_1470_);
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v_b_1474_);
return v___x_1481_;
}
else
{
lean_object* v_snd_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1516_; 
v_snd_1482_ = lean_ctor_get(v_b_1474_, 1);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_b_1474_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v_b_1474_, 0);
lean_dec(v_unused_1517_);
v___x_1484_ = v_b_1474_;
v_isShared_1485_ = v_isSharedCheck_1516_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_snd_1482_);
lean_dec(v_b_1474_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1516_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_a_1486_; lean_object* v___x_1487_; 
v_a_1486_ = lean_array_uget_borrowed(v_as_1471_, v_i_1473_);
lean_inc(v_snd_1482_);
lean_inc_ref(v_isTarget_1470_);
v___x_1487_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4(v_init_1468_, v_goal_1469_, v_isTarget_1470_, v_a_1486_, v_snd_1482_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1507_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1507_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1507_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
if (lean_obj_tag(v_a_1488_) == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
lean_dec_ref(v_isTarget_1470_);
v___x_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1492_, 0, v_a_1488_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1492_);
v___x_1494_ = v___x_1484_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_snd_1482_);
v___x_1494_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1496_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1494_);
v___x_1496_ = v___x_1490_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
lean_del_object(v___x_1490_);
lean_dec(v_snd_1482_);
v_a_1499_ = lean_ctor_get(v_a_1488_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v_a_1488_, 1);
v___x_1500_ = lean_box(0);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 1, v_a_1499_);
lean_ctor_set(v___x_1484_, 0, v___x_1500_);
v___x_1502_ = v___x_1484_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_a_1499_);
v___x_1502_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
size_t v___x_1503_; size_t v___x_1504_; 
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = lean_usize_add(v_i_1473_, v___x_1503_);
v_i_1473_ = v___x_1504_;
v_b_1474_ = v___x_1502_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_del_object(v___x_1484_);
lean_dec(v_snd_1482_);
lean_dec_ref(v_isTarget_1470_);
v_a_1508_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1487_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1487_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__6___boxed(lean_object* v_init_1518_, lean_object* v_goal_1519_, lean_object* v_isTarget_1520_, lean_object* v_as_1521_, lean_object* v_sz_1522_, lean_object* v_i_1523_, lean_object* v_b_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
size_t v_sz_boxed_1530_; size_t v_i_boxed_1531_; lean_object* v_res_1532_; 
v_sz_boxed_1530_ = lean_unbox_usize(v_sz_1522_);
lean_dec(v_sz_1522_);
v_i_boxed_1531_ = lean_unbox_usize(v_i_1523_);
lean_dec(v_i_1523_);
v_res_1532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4_spec__6(v_init_1518_, v_goal_1519_, v_isTarget_1520_, v_as_1521_, v_sz_boxed_1530_, v_i_boxed_1531_, v_b_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v_as_1521_);
lean_dec_ref(v_goal_1519_);
lean_dec_ref(v_init_1518_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4___boxed(lean_object* v_init_1533_, lean_object* v_goal_1534_, lean_object* v_isTarget_1535_, lean_object* v_n_1536_, lean_object* v_b_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4(v_init_1533_, v_goal_1534_, v_isTarget_1535_, v_n_1536_, v_b_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec_ref(v_n_1536_);
lean_dec_ref(v_goal_1534_);
lean_dec_ref(v_init_1533_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__5_spec__9(lean_object* v_goal_1544_, lean_object* v_isTarget_1545_, lean_object* v_as_1546_, size_t v_sz_1547_, size_t v_i_1548_, lean_object* v_b_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
uint8_t v___x_1555_; 
v___x_1555_ = lean_usize_dec_lt(v_i_1548_, v_sz_1547_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
lean_dec_ref(v_isTarget_1545_);
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_b_1549_);
return v___x_1556_;
}
else
{
lean_object* v_snd_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1701_; 
v_snd_1557_ = lean_ctor_get(v_b_1549_, 1);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_b_1549_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; 
v_unused_1702_ = lean_ctor_get(v_b_1549_, 0);
lean_dec(v_unused_1702_);
v___x_1559_ = v_b_1549_;
v_isShared_1560_ = v_isSharedCheck_1701_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_snd_1557_);
lean_dec(v_b_1549_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1701_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_a_1561_; lean_object* v___x_1562_; 
v_a_1561_ = lean_array_uget_borrowed(v_as_1546_, v_i_1548_);
lean_inc(v_a_1561_);
v___x_1562_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1544_, v_a_1561_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_snd_1563_; lean_object* v_a_1564_; lean_object* v_fst_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1691_; 
v_snd_1563_ = lean_ctor_get(v_snd_1557_, 1);
lean_inc(v_snd_1563_);
v_a_1564_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1562_, 1);
v_fst_1565_ = lean_ctor_get(v_snd_1557_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_snd_1557_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; 
v_unused_1692_ = lean_ctor_get(v_snd_1557_, 1);
lean_dec(v_unused_1692_);
v___x_1567_ = v_snd_1557_;
v_isShared_1568_ = v_isSharedCheck_1691_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_fst_1565_);
lean_dec(v_snd_1557_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1691_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v_fst_1569_; lean_object* v_snd_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1690_; 
v_fst_1569_ = lean_ctor_get(v_snd_1563_, 0);
v_snd_1570_ = lean_ctor_get(v_snd_1563_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_snd_1563_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1572_ = v_snd_1563_;
v_isShared_1573_ = v_isSharedCheck_1690_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_snd_1570_);
lean_inc(v_fst_1569_);
lean_dec(v_snd_1563_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1690_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v_a_1576_; uint8_t v___x_1583_; 
v___x_1574_ = lean_box(0);
v___x_1583_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1564_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1585_; 
lean_dec(v_a_1564_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 1, v_snd_1570_);
lean_ctor_set(v___x_1567_, 0, v_fst_1569_);
v___x_1585_ = v___x_1567_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_fst_1569_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_snd_1570_);
v___x_1585_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1587_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 1, v___x_1585_);
lean_ctor_set(v___x_1559_, 0, v_fst_1565_);
v___x_1587_ = v___x_1559_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_fst_1565_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
v_a_1576_ = v___x_1587_;
goto v___jp_1575_;
}
}
}
else
{
lean_object* v___x_1590_; 
lean_inc_ref(v_isTarget_1545_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v_a_1564_);
v___x_1590_ = lean_apply_6(v_isTarget_1545_, v_a_1564_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, lean_box(0));
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; uint8_t v___x_1592_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1592_ = lean_unbox(v_a_1591_);
lean_dec(v_a_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1594_; 
lean_dec(v_a_1564_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 1, v_snd_1570_);
lean_ctor_set(v___x_1567_, 0, v_fst_1569_);
v___x_1594_ = v___x_1567_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_fst_1569_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_snd_1570_);
v___x_1594_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1596_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 1, v___x_1594_);
lean_ctor_set(v___x_1559_, 0, v_fst_1565_);
v___x_1596_ = v___x_1559_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_fst_1565_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
v_a_1576_ = v___x_1596_;
goto v___jp_1575_;
}
}
}
else
{
lean_object* v_self_1599_; lean_object* v___x_1600_; 
v_self_1599_ = lean_ctor_get(v_a_1564_, 0);
lean_inc_ref(v_self_1599_);
lean_dec(v_a_1564_);
v___x_1600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1570_, v_self_1599_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___y_1605_; lean_object* v___x_1614_; lean_object* v___y_1616_; lean_object* v_i_1617_; lean_object* v___y_1623_; lean_object* v___y_1633_; lean_object* v_i_1634_; lean_object* v___x_1649_; 
v___x_1601_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1544_, v_snd_1570_, v_self_1599_, v_fst_1569_, v_fst_1565_);
lean_inc(v___x_1601_);
v___x_1602_ = l_Rat_ofInt(v___x_1601_);
v___x_1603_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1544_, v_self_1599_, v___x_1602_, v_snd_1570_);
v___x_1614_ = lean_box(0);
v___x_1649_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v_fst_1569_, v___x_1601_);
switch(lean_obj_tag(v___x_1649_))
{
case 0:
{
lean_dec_ref_known(v___x_1649_, 3);
v___y_1605_ = v_fst_1569_;
goto v___jp_1604_;
}
case 1:
{
lean_object* v_index_1650_; lean_object* v_size_1651_; lean_object* v_keyArray_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v_index_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_index_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v_size_1651_ = lean_ctor_get(v_fst_1569_, 0);
v_keyArray_1652_ = lean_ctor_get(v_fst_1569_, 1);
v___x_1653_ = lean_unsigned_to_nat(1u);
v___x_1654_ = lean_nat_add(v_size_1651_, v___x_1653_);
v___x_1655_ = lean_array_get_size(v_keyArray_1652_);
v___x_1656_ = lean_nat_dec_lt(v___x_1654_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_dec(v___x_1654_);
lean_dec(v_index_1650_);
goto v___jp_1639_;
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1657_ = lean_unsigned_to_nat(4u);
v___x_1658_ = lean_nat_mul(v___x_1654_, v___x_1657_);
v___x_1659_ = lean_unsigned_to_nat(3u);
v___x_1660_ = lean_nat_mul(v___x_1655_, v___x_1659_);
v___x_1661_ = lean_nat_dec_le(v___x_1658_, v___x_1660_);
lean_dec(v___x_1660_);
lean_dec(v___x_1658_);
if (v___x_1661_ == 0)
{
lean_dec(v___x_1654_);
lean_dec(v_index_1650_);
goto v___jp_1639_;
}
else
{
lean_object* v___x_1662_; 
lean_inc(v___x_1601_);
v___x_1662_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_1569_, v___x_1654_, v_index_1650_, v___x_1601_, v___x_1614_);
lean_dec(v_index_1650_);
v___y_1605_ = v___x_1662_;
goto v___jp_1604_;
}
}
}
default: 
{
lean_object* v_size_1663_; lean_object* v_keyArray_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
v_size_1663_ = lean_ctor_get(v_fst_1569_, 0);
v_keyArray_1664_ = lean_ctor_get(v_fst_1569_, 1);
v___x_1665_ = lean_unsigned_to_nat(1u);
v___x_1666_ = lean_nat_add(v_size_1663_, v___x_1665_);
v___x_1667_ = lean_array_get_size(v_keyArray_1664_);
v___x_1668_ = lean_nat_dec_lt(v___x_1666_, v___x_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; 
lean_dec(v___x_1666_);
v___x_1669_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1569_);
lean_dec(v_fst_1569_);
v___y_1623_ = v___x_1669_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1670_ = lean_unsigned_to_nat(4u);
v___x_1671_ = lean_nat_mul(v___x_1666_, v___x_1670_);
lean_dec(v___x_1666_);
v___x_1672_ = lean_unsigned_to_nat(3u);
v___x_1673_ = lean_nat_mul(v___x_1667_, v___x_1672_);
v___x_1674_ = lean_nat_dec_le(v___x_1671_, v___x_1673_);
lean_dec(v___x_1673_);
lean_dec(v___x_1671_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1569_);
lean_dec(v_fst_1569_);
v___y_1623_ = v___x_1675_;
goto v___jp_1622_;
}
else
{
v___y_1623_ = v_fst_1569_;
goto v___jp_1622_;
}
}
}
}
v___jp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1606_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1607_ = lean_int_add(v___x_1601_, v___x_1606_);
lean_dec(v___x_1601_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 1, v___x_1603_);
lean_ctor_set(v___x_1567_, 0, v___y_1605_);
v___x_1609_ = v___x_1567_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___y_1605_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v___x_1603_);
v___x_1609_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 1, v___x_1609_);
lean_ctor_set(v___x_1559_, 0, v___x_1607_);
v___x_1611_ = v___x_1559_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
v_a_1576_ = v___x_1611_;
goto v___jp_1575_;
}
}
}
v___jp_1615_:
{
lean_object* v_size_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_size_1618_ = lean_ctor_get(v___y_1616_, 0);
v___x_1619_ = lean_unsigned_to_nat(1u);
v___x_1620_ = lean_nat_add(v_size_1618_, v___x_1619_);
lean_inc(v___x_1601_);
v___x_1621_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1616_, v___x_1620_, v_i_1617_, v___x_1601_, v___x_1614_);
lean_dec(v_i_1617_);
v___y_1605_ = v___x_1621_;
goto v___jp_1604_;
}
v___jp_1622_:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v___y_1623_, v___x_1601_);
switch(lean_obj_tag(v___x_1624_))
{
case 0:
{
lean_object* v_index_1625_; lean_object* v_size_1626_; lean_object* v___x_1627_; 
v_index_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_index_1625_);
lean_dec_ref_known(v___x_1624_, 3);
v_size_1626_ = lean_ctor_get(v___y_1623_, 0);
lean_inc(v_size_1626_);
lean_inc(v___x_1601_);
v___x_1627_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1623_, v_size_1626_, v_index_1625_, v___x_1601_, v___x_1614_);
lean_dec(v_index_1625_);
v___y_1605_ = v___x_1627_;
goto v___jp_1604_;
}
case 1:
{
lean_object* v_index_1628_; 
v_index_1628_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_index_1628_);
lean_dec_ref_known(v___x_1624_, 1);
v___y_1616_ = v___y_1623_;
v_i_1617_ = v_index_1628_;
goto v___jp_1615_;
}
default: 
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1623_, v___x_1629_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_index_1631_; 
v_index_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_index_1631_);
lean_dec_ref_known(v___x_1630_, 1);
v___y_1616_ = v___y_1623_;
v_i_1617_ = v_index_1631_;
goto v___jp_1615_;
}
else
{
v___y_1605_ = v___y_1623_;
goto v___jp_1604_;
}
}
}
}
v___jp_1632_:
{
lean_object* v_size_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_size_1635_ = lean_ctor_get(v___y_1633_, 0);
v___x_1636_ = lean_unsigned_to_nat(1u);
v___x_1637_ = lean_nat_add(v_size_1635_, v___x_1636_);
lean_inc(v___x_1601_);
v___x_1638_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1633_, v___x_1637_, v_i_1634_, v___x_1601_, v___x_1614_);
lean_dec(v_i_1634_);
v___y_1605_ = v___x_1638_;
goto v___jp_1604_;
}
v___jp_1639_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1569_);
lean_dec(v_fst_1569_);
v___x_1641_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v___x_1640_, v___x_1601_);
switch(lean_obj_tag(v___x_1641_))
{
case 0:
{
lean_object* v_index_1642_; lean_object* v_size_1643_; lean_object* v___x_1644_; 
v_index_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_index_1642_);
lean_dec_ref_known(v___x_1641_, 3);
v_size_1643_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_size_1643_);
lean_inc(v___x_1601_);
v___x_1644_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1640_, v_size_1643_, v_index_1642_, v___x_1601_, v___x_1614_);
lean_dec(v_index_1642_);
v___y_1605_ = v___x_1644_;
goto v___jp_1604_;
}
case 1:
{
lean_object* v_index_1645_; 
v_index_1645_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_index_1645_);
lean_dec_ref_known(v___x_1641_, 1);
v___y_1633_ = v___x_1640_;
v_i_1634_ = v_index_1645_;
goto v___jp_1632_;
}
default: 
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_unsigned_to_nat(0u);
v___x_1647_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1640_, v___x_1646_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_index_1648_; 
v_index_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_index_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___y_1633_ = v___x_1640_;
v_i_1634_ = v_index_1648_;
goto v___jp_1632_;
}
else
{
v___y_1605_ = v___x_1640_;
goto v___jp_1604_;
}
}
}
}
}
else
{
lean_object* v___x_1677_; 
lean_dec_ref_known(v___x_1600_, 1);
lean_dec_ref(v_self_1599_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 1, v_snd_1570_);
lean_ctor_set(v___x_1567_, 0, v_fst_1569_);
v___x_1677_ = v___x_1567_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_fst_1569_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_snd_1570_);
v___x_1677_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1679_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 1, v___x_1677_);
lean_ctor_set(v___x_1559_, 0, v_fst_1565_);
v___x_1679_ = v___x_1559_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_fst_1565_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
v_a_1576_ = v___x_1679_;
goto v___jp_1575_;
}
}
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_del_object(v___x_1572_);
lean_dec(v_snd_1570_);
lean_dec(v_fst_1569_);
lean_del_object(v___x_1567_);
lean_dec(v_fst_1565_);
lean_dec(v_a_1564_);
lean_del_object(v___x_1559_);
lean_dec_ref(v_isTarget_1545_);
v_a_1682_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1590_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1590_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
v___jp_1575_:
{
lean_object* v___x_1578_; 
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 1, v_a_1576_);
lean_ctor_set(v___x_1572_, 0, v___x_1574_);
v___x_1578_ = v___x_1572_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_a_1576_);
v___x_1578_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
size_t v___x_1579_; size_t v___x_1580_; 
v___x_1579_ = ((size_t)1ULL);
v___x_1580_ = lean_usize_add(v_i_1548_, v___x_1579_);
v_i_1548_ = v___x_1580_;
v_b_1549_ = v___x_1578_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_del_object(v___x_1559_);
lean_dec(v_snd_1557_);
lean_dec_ref(v_isTarget_1545_);
v_a_1693_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1562_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1562_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__5_spec__9___boxed(lean_object* v_goal_1703_, lean_object* v_isTarget_1704_, lean_object* v_as_1705_, lean_object* v_sz_1706_, lean_object* v_i_1707_, lean_object* v_b_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
size_t v_sz_boxed_1714_; size_t v_i_boxed_1715_; lean_object* v_res_1716_; 
v_sz_boxed_1714_ = lean_unbox_usize(v_sz_1706_);
lean_dec(v_sz_1706_);
v_i_boxed_1715_ = lean_unbox_usize(v_i_1707_);
lean_dec(v_i_1707_);
v_res_1716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__5_spec__9(v_goal_1703_, v_isTarget_1704_, v_as_1705_, v_sz_boxed_1714_, v_i_boxed_1715_, v_b_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec_ref(v_as_1705_);
lean_dec_ref(v_goal_1703_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__5(lean_object* v_goal_1717_, lean_object* v_isTarget_1718_, lean_object* v_as_1719_, size_t v_sz_1720_, size_t v_i_1721_, lean_object* v_b_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
uint8_t v___x_1728_; 
v___x_1728_ = lean_usize_dec_lt(v_i_1721_, v_sz_1720_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; 
lean_dec_ref(v_isTarget_1718_);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v_b_1722_);
return v___x_1729_;
}
else
{
lean_object* v_snd_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1874_; 
v_snd_1730_ = lean_ctor_get(v_b_1722_, 1);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_b_1722_);
if (v_isSharedCheck_1874_ == 0)
{
lean_object* v_unused_1875_; 
v_unused_1875_ = lean_ctor_get(v_b_1722_, 0);
lean_dec(v_unused_1875_);
v___x_1732_ = v_b_1722_;
v_isShared_1733_ = v_isSharedCheck_1874_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_snd_1730_);
lean_dec(v_b_1722_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1874_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v_a_1734_; lean_object* v___x_1735_; 
v_a_1734_ = lean_array_uget_borrowed(v_as_1719_, v_i_1721_);
lean_inc(v_a_1734_);
v___x_1735_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1717_, v_a_1734_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_snd_1736_; lean_object* v_a_1737_; lean_object* v_fst_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1864_; 
v_snd_1736_ = lean_ctor_get(v_snd_1730_, 1);
lean_inc(v_snd_1736_);
v_a_1737_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1735_, 1);
v_fst_1738_ = lean_ctor_get(v_snd_1730_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_snd_1730_);
if (v_isSharedCheck_1864_ == 0)
{
lean_object* v_unused_1865_; 
v_unused_1865_ = lean_ctor_get(v_snd_1730_, 1);
lean_dec(v_unused_1865_);
v___x_1740_ = v_snd_1730_;
v_isShared_1741_ = v_isSharedCheck_1864_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_fst_1738_);
lean_dec(v_snd_1730_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1864_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v_fst_1742_; lean_object* v_snd_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1863_; 
v_fst_1742_ = lean_ctor_get(v_snd_1736_, 0);
v_snd_1743_ = lean_ctor_get(v_snd_1736_, 1);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_snd_1736_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1745_ = v_snd_1736_;
v_isShared_1746_ = v_isSharedCheck_1863_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_snd_1743_);
lean_inc(v_fst_1742_);
lean_dec(v_snd_1736_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1863_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v_a_1749_; uint8_t v___x_1756_; 
v___x_1747_ = lean_box(0);
v___x_1756_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1737_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1758_; 
lean_dec(v_a_1737_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 1, v_snd_1743_);
lean_ctor_set(v___x_1740_, 0, v_fst_1742_);
v___x_1758_ = v___x_1740_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_fst_1742_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_snd_1743_);
v___x_1758_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1760_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v___x_1758_);
lean_ctor_set(v___x_1732_, 0, v_fst_1738_);
v___x_1760_ = v___x_1732_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_fst_1738_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
v_a_1749_ = v___x_1760_;
goto v___jp_1748_;
}
}
}
else
{
lean_object* v___x_1763_; 
lean_inc_ref(v_isTarget_1718_);
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1725_);
lean_inc(v___y_1724_);
lean_inc_ref(v___y_1723_);
lean_inc(v_a_1737_);
v___x_1763_ = lean_apply_6(v_isTarget_1718_, v_a_1737_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, lean_box(0));
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; uint8_t v___x_1765_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1765_ = lean_unbox(v_a_1764_);
lean_dec(v_a_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1767_; 
lean_dec(v_a_1737_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 1, v_snd_1743_);
lean_ctor_set(v___x_1740_, 0, v_fst_1742_);
v___x_1767_ = v___x_1740_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_fst_1742_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_snd_1743_);
v___x_1767_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1769_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v___x_1767_);
lean_ctor_set(v___x_1732_, 0, v_fst_1738_);
v___x_1769_ = v___x_1732_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_fst_1738_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
v_a_1749_ = v___x_1769_;
goto v___jp_1748_;
}
}
}
else
{
lean_object* v_self_1772_; lean_object* v___x_1773_; 
v_self_1772_ = lean_ctor_get(v_a_1737_, 0);
lean_inc_ref(v_self_1772_);
lean_dec(v_a_1737_);
v___x_1773_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1743_, v_self_1772_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___y_1778_; lean_object* v___x_1787_; lean_object* v___y_1789_; lean_object* v_i_1790_; lean_object* v___y_1796_; lean_object* v___y_1806_; lean_object* v_i_1807_; lean_object* v___x_1822_; 
v___x_1774_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1717_, v_snd_1743_, v_self_1772_, v_fst_1742_, v_fst_1738_);
lean_inc(v___x_1774_);
v___x_1775_ = l_Rat_ofInt(v___x_1774_);
v___x_1776_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1717_, v_self_1772_, v___x_1775_, v_snd_1743_);
v___x_1787_ = lean_box(0);
v___x_1822_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v_fst_1742_, v___x_1774_);
switch(lean_obj_tag(v___x_1822_))
{
case 0:
{
lean_dec_ref_known(v___x_1822_, 3);
v___y_1778_ = v_fst_1742_;
goto v___jp_1777_;
}
case 1:
{
lean_object* v_index_1823_; lean_object* v_size_1824_; lean_object* v_keyArray_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v_index_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_index_1823_);
lean_dec_ref_known(v___x_1822_, 1);
v_size_1824_ = lean_ctor_get(v_fst_1742_, 0);
v_keyArray_1825_ = lean_ctor_get(v_fst_1742_, 1);
v___x_1826_ = lean_unsigned_to_nat(1u);
v___x_1827_ = lean_nat_add(v_size_1824_, v___x_1826_);
v___x_1828_ = lean_array_get_size(v_keyArray_1825_);
v___x_1829_ = lean_nat_dec_lt(v___x_1827_, v___x_1828_);
if (v___x_1829_ == 0)
{
lean_dec(v___x_1827_);
lean_dec(v_index_1823_);
goto v___jp_1812_;
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1830_ = lean_unsigned_to_nat(4u);
v___x_1831_ = lean_nat_mul(v___x_1827_, v___x_1830_);
v___x_1832_ = lean_unsigned_to_nat(3u);
v___x_1833_ = lean_nat_mul(v___x_1828_, v___x_1832_);
v___x_1834_ = lean_nat_dec_le(v___x_1831_, v___x_1833_);
lean_dec(v___x_1833_);
lean_dec(v___x_1831_);
if (v___x_1834_ == 0)
{
lean_dec(v___x_1827_);
lean_dec(v_index_1823_);
goto v___jp_1812_;
}
else
{
lean_object* v___x_1835_; 
lean_inc(v___x_1774_);
v___x_1835_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_1742_, v___x_1827_, v_index_1823_, v___x_1774_, v___x_1787_);
lean_dec(v_index_1823_);
v___y_1778_ = v___x_1835_;
goto v___jp_1777_;
}
}
}
default: 
{
lean_object* v_size_1836_; lean_object* v_keyArray_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v_size_1836_ = lean_ctor_get(v_fst_1742_, 0);
v_keyArray_1837_ = lean_ctor_get(v_fst_1742_, 1);
v___x_1838_ = lean_unsigned_to_nat(1u);
v___x_1839_ = lean_nat_add(v_size_1836_, v___x_1838_);
v___x_1840_ = lean_array_get_size(v_keyArray_1837_);
v___x_1841_ = lean_nat_dec_lt(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
lean_dec(v___x_1839_);
v___x_1842_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1742_);
lean_dec(v_fst_1742_);
v___y_1796_ = v___x_1842_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1843_ = lean_unsigned_to_nat(4u);
v___x_1844_ = lean_nat_mul(v___x_1839_, v___x_1843_);
lean_dec(v___x_1839_);
v___x_1845_ = lean_unsigned_to_nat(3u);
v___x_1846_ = lean_nat_mul(v___x_1840_, v___x_1845_);
v___x_1847_ = lean_nat_dec_le(v___x_1844_, v___x_1846_);
lean_dec(v___x_1846_);
lean_dec(v___x_1844_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1742_);
lean_dec(v_fst_1742_);
v___y_1796_ = v___x_1848_;
goto v___jp_1795_;
}
else
{
v___y_1796_ = v_fst_1742_;
goto v___jp_1795_;
}
}
}
}
v___jp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1780_ = lean_int_add(v___x_1774_, v___x_1779_);
lean_dec(v___x_1774_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 1, v___x_1776_);
lean_ctor_set(v___x_1740_, 0, v___y_1778_);
v___x_1782_ = v___x_1740_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___y_1778_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___x_1776_);
v___x_1782_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v___x_1782_);
lean_ctor_set(v___x_1732_, 0, v___x_1780_);
v___x_1784_ = v___x_1732_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
v_a_1749_ = v___x_1784_;
goto v___jp_1748_;
}
}
}
v___jp_1788_:
{
lean_object* v_size_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v_size_1791_ = lean_ctor_get(v___y_1789_, 0);
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = lean_nat_add(v_size_1791_, v___x_1792_);
lean_inc(v___x_1774_);
v___x_1794_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1789_, v___x_1793_, v_i_1790_, v___x_1774_, v___x_1787_);
lean_dec(v_i_1790_);
v___y_1778_ = v___x_1794_;
goto v___jp_1777_;
}
v___jp_1795_:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v___y_1796_, v___x_1774_);
switch(lean_obj_tag(v___x_1797_))
{
case 0:
{
lean_object* v_index_1798_; lean_object* v_size_1799_; lean_object* v___x_1800_; 
v_index_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_index_1798_);
lean_dec_ref_known(v___x_1797_, 3);
v_size_1799_ = lean_ctor_get(v___y_1796_, 0);
lean_inc(v_size_1799_);
lean_inc(v___x_1774_);
v___x_1800_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1796_, v_size_1799_, v_index_1798_, v___x_1774_, v___x_1787_);
lean_dec(v_index_1798_);
v___y_1778_ = v___x_1800_;
goto v___jp_1777_;
}
case 1:
{
lean_object* v_index_1801_; 
v_index_1801_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_index_1801_);
lean_dec_ref_known(v___x_1797_, 1);
v___y_1789_ = v___y_1796_;
v_i_1790_ = v_index_1801_;
goto v___jp_1788_;
}
default: 
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1796_, v___x_1802_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_index_1804_; 
v_index_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_index_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v___y_1789_ = v___y_1796_;
v_i_1790_ = v_index_1804_;
goto v___jp_1788_;
}
else
{
v___y_1778_ = v___y_1796_;
goto v___jp_1777_;
}
}
}
}
v___jp_1805_:
{
lean_object* v_size_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_size_1808_ = lean_ctor_get(v___y_1806_, 0);
v___x_1809_ = lean_unsigned_to_nat(1u);
v___x_1810_ = lean_nat_add(v_size_1808_, v___x_1809_);
lean_inc(v___x_1774_);
v___x_1811_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1806_, v___x_1810_, v_i_1807_, v___x_1774_, v___x_1787_);
lean_dec(v_i_1807_);
v___y_1778_ = v___x_1811_;
goto v___jp_1777_;
}
v___jp_1812_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1742_);
lean_dec(v_fst_1742_);
v___x_1814_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg(v___x_1813_, v___x_1774_);
switch(lean_obj_tag(v___x_1814_))
{
case 0:
{
lean_object* v_index_1815_; lean_object* v_size_1816_; lean_object* v___x_1817_; 
v_index_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_index_1815_);
lean_dec_ref_known(v___x_1814_, 3);
v_size_1816_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_size_1816_);
lean_inc(v___x_1774_);
v___x_1817_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1813_, v_size_1816_, v_index_1815_, v___x_1774_, v___x_1787_);
lean_dec(v_index_1815_);
v___y_1778_ = v___x_1817_;
goto v___jp_1777_;
}
case 1:
{
lean_object* v_index_1818_; 
v_index_1818_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_index_1818_);
lean_dec_ref_known(v___x_1814_, 1);
v___y_1806_ = v___x_1813_;
v_i_1807_ = v_index_1818_;
goto v___jp_1805_;
}
default: 
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1813_, v___x_1819_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_index_1821_; 
v_index_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_index_1821_);
lean_dec_ref_known(v___x_1820_, 1);
v___y_1806_ = v___x_1813_;
v_i_1807_ = v_index_1821_;
goto v___jp_1805_;
}
else
{
v___y_1778_ = v___x_1813_;
goto v___jp_1777_;
}
}
}
}
}
else
{
lean_object* v___x_1850_; 
lean_dec_ref_known(v___x_1773_, 1);
lean_dec_ref(v_self_1772_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 1, v_snd_1743_);
lean_ctor_set(v___x_1740_, 0, v_fst_1742_);
v___x_1850_ = v___x_1740_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_fst_1742_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_snd_1743_);
v___x_1850_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1852_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v___x_1850_);
lean_ctor_set(v___x_1732_, 0, v_fst_1738_);
v___x_1852_ = v___x_1732_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_fst_1738_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
v_a_1749_ = v___x_1852_;
goto v___jp_1748_;
}
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_del_object(v___x_1745_);
lean_dec(v_snd_1743_);
lean_dec(v_fst_1742_);
lean_del_object(v___x_1740_);
lean_dec(v_fst_1738_);
lean_dec(v_a_1737_);
lean_del_object(v___x_1732_);
lean_dec_ref(v_isTarget_1718_);
v_a_1855_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1763_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1763_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
v___jp_1748_:
{
lean_object* v___x_1751_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_a_1749_);
lean_ctor_set(v___x_1745_, 0, v___x_1747_);
v___x_1751_ = v___x_1745_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_a_1749_);
v___x_1751_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
size_t v___x_1752_; size_t v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = ((size_t)1ULL);
v___x_1753_ = lean_usize_add(v_i_1721_, v___x_1752_);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__5_spec__9(v_goal_1717_, v_isTarget_1718_, v_as_1719_, v_sz_1720_, v___x_1753_, v___x_1751_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
return v___x_1754_;
}
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_del_object(v___x_1732_);
lean_dec(v_snd_1730_);
lean_dec_ref(v_isTarget_1718_);
v_a_1866_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1735_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1735_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__5___boxed(lean_object* v_goal_1876_, lean_object* v_isTarget_1877_, lean_object* v_as_1878_, lean_object* v_sz_1879_, lean_object* v_i_1880_, lean_object* v_b_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
size_t v_sz_boxed_1887_; size_t v_i_boxed_1888_; lean_object* v_res_1889_; 
v_sz_boxed_1887_ = lean_unbox_usize(v_sz_1879_);
lean_dec(v_sz_1879_);
v_i_boxed_1888_ = lean_unbox_usize(v_i_1880_);
lean_dec(v_i_1880_);
v_res_1889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__5(v_goal_1876_, v_isTarget_1877_, v_as_1878_, v_sz_boxed_1887_, v_i_boxed_1888_, v_b_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec_ref(v_as_1878_);
lean_dec_ref(v_goal_1876_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(lean_object* v_goal_1890_, lean_object* v_isTarget_1891_, lean_object* v_t_1892_, lean_object* v_init_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_root_1899_; lean_object* v_tail_1900_; lean_object* v___x_1901_; 
v_root_1899_ = lean_ctor_get(v_t_1892_, 0);
v_tail_1900_ = lean_ctor_get(v_t_1892_, 1);
lean_inc_ref(v_isTarget_1891_);
lean_inc_ref(v_init_1893_);
v___x_1901_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__4(v_init_1893_, v_goal_1890_, v_isTarget_1891_, v_root_1899_, v_init_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec_ref(v_init_1893_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1938_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1938_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1938_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
if (lean_obj_tag(v_a_1902_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; 
lean_dec_ref(v_isTarget_1891_);
v_a_1906_ = lean_ctor_get(v_a_1902_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v_a_1902_, 1);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v_a_1906_);
v___x_1908_ = v___x_1904_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; size_t v_sz_1913_; size_t v___x_1914_; lean_object* v___x_1915_; 
lean_del_object(v___x_1904_);
v_a_1910_ = lean_ctor_get(v_a_1902_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v_a_1902_, 1);
v___x_1911_ = lean_box(0);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
lean_ctor_set(v___x_1912_, 1, v_a_1910_);
v_sz_1913_ = lean_array_size(v_tail_1900_);
v___x_1914_ = ((size_t)0ULL);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_spec__5(v_goal_1890_, v_isTarget_1891_, v_tail_1900_, v_sz_1913_, v___x_1914_, v___x_1912_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1929_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1929_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1929_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v_fst_1920_; 
v_fst_1920_ = lean_ctor_get(v_a_1916_, 0);
if (lean_obj_tag(v_fst_1920_) == 0)
{
lean_object* v_snd_1921_; lean_object* v___x_1923_; 
v_snd_1921_ = lean_ctor_get(v_a_1916_, 1);
lean_inc(v_snd_1921_);
lean_dec(v_a_1916_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v_snd_1921_);
v___x_1923_ = v___x_1918_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_snd_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
else
{
lean_object* v_val_1925_; lean_object* v___x_1927_; 
lean_inc_ref(v_fst_1920_);
lean_dec(v_a_1916_);
v_val_1925_ = lean_ctor_get(v_fst_1920_, 0);
lean_inc(v_val_1925_);
lean_dec_ref_known(v_fst_1920_, 1);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v_val_1925_);
v___x_1927_ = v___x_1918_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_val_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v_a_1930_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1915_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1915_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec_ref(v_isTarget_1891_);
v_a_1939_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1901_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1901_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2___boxed(lean_object* v_goal_1947_, lean_object* v_isTarget_1948_, lean_object* v_t_1949_, lean_object* v_init_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_goal_1947_, v_isTarget_1948_, v_t_1949_, v_init_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec_ref(v_t_1949_);
lean_dec_ref(v_goal_1947_);
return v_res_1956_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0(void){
_start:
{
lean_object* v_cellCount_1957_; lean_object* v___x_1958_; 
v_cellCount_1957_ = lean_unsigned_to_nat(16u);
v___x_1958_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1957_);
return v___x_1958_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1(void){
_start:
{
lean_object* v_cellCount_1959_; lean_object* v___x_1960_; 
v_cellCount_1959_ = lean_unsigned_to_nat(16u);
v___x_1960_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1959_);
return v___x_1960_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__2(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v_used_1964_; 
v___x_1961_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1);
v___x_1962_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0);
v___x_1963_ = lean_unsigned_to_nat(0u);
v_used_1964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_used_1964_, 0, v___x_1963_);
lean_ctor_set(v_used_1964_, 1, v___x_1962_);
lean_ctor_set(v_used_1964_, 2, v___x_1961_);
return v_used_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(lean_object* v_goal_1965_, lean_object* v_isTarget_1966_, lean_object* v_model_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v_used_1973_; lean_object* v___x_1974_; lean_object* v_toGoalState_1975_; lean_object* v_a_1976_; lean_object* v_exprs_1977_; lean_object* v_nextVal_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_used_1973_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__2);
v___x_1974_ = l_Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(v_used_1973_, v_model_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
v_toGoalState_1975_ = lean_ctor_get(v_goal_1965_, 0);
v_a_1976_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1976_);
lean_dec_ref(v___x_1974_);
v_exprs_1977_ = lean_ctor_get(v_toGoalState_1975_, 2);
v_nextVal_1978_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1979_, 0, v_a_1976_);
lean_ctor_set(v___x_1979_, 1, v_model_1967_);
v___x_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1980_, 0, v_nextVal_1978_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_goal_1965_, v_isTarget_1966_, v_exprs_1977_, v___x_1980_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1991_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1991_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1991_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v_snd_1986_; lean_object* v_snd_1987_; lean_object* v___x_1989_; 
v_snd_1986_ = lean_ctor_get(v_a_1982_, 1);
lean_inc(v_snd_1986_);
lean_dec(v_a_1982_);
v_snd_1987_ = lean_ctor_get(v_snd_1986_, 1);
lean_inc(v_snd_1987_);
lean_dec(v_snd_1986_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v_snd_1987_);
v___x_1989_ = v___x_1984_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_snd_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
v_a_1992_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1981_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1981_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___boxed(lean_object* v_goal_2000_, lean_object* v_isTarget_2001_, lean_object* v_model_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_2000_, v_isTarget_2001_, v_model_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec_ref(v_goal_2000_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0(lean_object* v_00_u03b2_2009_, lean_object* v_m_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_m_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___boxed(lean_object* v_00_u03b2_2012_, lean_object* v_m_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0(v_00_u03b2_2012_, v_m_2013_);
lean_dec_ref(v_m_2013_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0(lean_object* v_00_u03b2_2015_, lean_object* v_init_2016_, lean_object* v_b_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_init_2016_, v_b_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2019_, lean_object* v_init_2020_, lean_object* v_b_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0(v_00_u03b2_2019_, v_init_2020_, v_b_2021_);
lean_dec_ref(v_b_2021_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1_spec__2(lean_object* v_b_2023_, lean_object* v_acc_2024_, lean_object* v_i_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1_spec__2___redArg(v_b_2023_, v_acc_2024_, v_i_2025_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1_spec__2___boxed(lean_object* v_b_2032_, lean_object* v_acc_2033_, lean_object* v_i_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1_spec__2(v_b_2032_, v_acc_2033_, v_i_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec_ref(v_b_2032_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2041_, lean_object* v_b_2042_, lean_object* v_acc_2043_, lean_object* v_i_2044_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v_b_2042_, v_acc_2043_, v_i_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2046_, lean_object* v_b_2047_, lean_object* v_acc_2048_, lean_object* v_i_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1(v_00_u03b2_2046_, v_b_2047_, v_acc_2048_, v_i_2049_);
lean_dec_ref(v_b_2047_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(lean_object* v_goal_2051_, lean_object* v_hi_2052_, lean_object* v_pivot_2053_, lean_object* v_as_2054_, lean_object* v_i_2055_, lean_object* v_k_2056_){
_start:
{
uint8_t v___y_2058_; uint8_t v___x_2067_; 
v___x_2067_ = lean_nat_dec_lt(v_k_2056_, v_hi_2052_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec(v_k_2056_);
v___x_2068_ = lean_array_fswap(v_as_2054_, v_i_2055_, v_hi_2052_);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_i_2055_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
return v___x_2069_;
}
else
{
lean_object* v___x_2070_; lean_object* v_fst_2071_; lean_object* v_fst_2072_; lean_object* v_g_u2081_2073_; lean_object* v_g_u2082_2074_; uint8_t v___x_2075_; 
v___x_2070_ = lean_array_fget_borrowed(v_as_2054_, v_k_2056_);
v_fst_2071_ = lean_ctor_get(v___x_2070_, 0);
v_fst_2072_ = lean_ctor_get(v_pivot_2053_, 0);
v_g_u2081_2073_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_2051_, v_fst_2071_);
v_g_u2082_2074_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_2051_, v_fst_2072_);
v___x_2075_ = lean_nat_dec_eq(v_g_u2081_2073_, v_g_u2082_2074_);
if (v___x_2075_ == 0)
{
uint8_t v___x_2076_; 
v___x_2076_ = lean_nat_dec_lt(v_g_u2081_2073_, v_g_u2082_2074_);
lean_dec(v_g_u2082_2074_);
lean_dec(v_g_u2081_2073_);
v___y_2058_ = v___x_2076_;
goto v___jp_2057_;
}
else
{
uint8_t v___x_2077_; 
lean_dec(v_g_u2082_2074_);
lean_dec(v_g_u2081_2073_);
v___x_2077_ = lean_expr_lt(v_fst_2071_, v_fst_2072_);
v___y_2058_ = v___x_2077_;
goto v___jp_2057_;
}
}
v___jp_2057_:
{
if (v___y_2058_ == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_unsigned_to_nat(1u);
v___x_2060_ = lean_nat_add(v_k_2056_, v___x_2059_);
lean_dec(v_k_2056_);
v_k_2056_ = v___x_2060_;
goto _start;
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2062_ = lean_array_fswap(v_as_2054_, v_i_2055_, v_k_2056_);
v___x_2063_ = lean_unsigned_to_nat(1u);
v___x_2064_ = lean_nat_add(v_i_2055_, v___x_2063_);
lean_dec(v_i_2055_);
v___x_2065_ = lean_nat_add(v_k_2056_, v___x_2063_);
lean_dec(v_k_2056_);
v_as_2054_ = v___x_2062_;
v_i_2055_ = v___x_2064_;
v_k_2056_ = v___x_2065_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg___boxed(lean_object* v_goal_2078_, lean_object* v_hi_2079_, lean_object* v_pivot_2080_, lean_object* v_as_2081_, lean_object* v_i_2082_, lean_object* v_k_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_2078_, v_hi_2079_, v_pivot_2080_, v_as_2081_, v_i_2082_, v_k_2083_);
lean_dec_ref(v_pivot_2080_);
lean_dec(v_hi_2079_);
lean_dec_ref(v_goal_2078_);
return v_res_2084_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(lean_object* v_goal_2085_, lean_object* v_x_2086_, lean_object* v_x_2087_){
_start:
{
lean_object* v_fst_2088_; lean_object* v_fst_2089_; lean_object* v_g_u2081_2090_; lean_object* v_g_u2082_2091_; uint8_t v___x_2092_; 
v_fst_2088_ = lean_ctor_get(v_x_2086_, 0);
v_fst_2089_ = lean_ctor_get(v_x_2087_, 0);
v_g_u2081_2090_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_2085_, v_fst_2088_);
v_g_u2082_2091_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_2085_, v_fst_2089_);
v___x_2092_ = lean_nat_dec_eq(v_g_u2081_2090_, v_g_u2082_2091_);
if (v___x_2092_ == 0)
{
uint8_t v___x_2093_; 
v___x_2093_ = lean_nat_dec_lt(v_g_u2081_2090_, v_g_u2082_2091_);
lean_dec(v_g_u2082_2091_);
lean_dec(v_g_u2081_2090_);
return v___x_2093_;
}
else
{
uint8_t v___x_2094_; 
lean_dec(v_g_u2082_2091_);
lean_dec(v_g_u2081_2090_);
v___x_2094_ = lean_expr_lt(v_fst_2088_, v_fst_2089_);
return v___x_2094_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0___boxed(lean_object* v_goal_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_){
_start:
{
uint8_t v_res_2098_; lean_object* v_r_2099_; 
v_res_2098_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_2095_, v_x_2096_, v_x_2097_);
lean_dec_ref(v_x_2097_);
lean_dec_ref(v_x_2096_);
lean_dec_ref(v_goal_2095_);
v_r_2099_ = lean_box(v_res_2098_);
return v_r_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(lean_object* v_goal_2100_, lean_object* v_n_2101_, lean_object* v_as_2102_, lean_object* v_lo_2103_, lean_object* v_hi_2104_){
_start:
{
lean_object* v___y_2106_; uint8_t v___x_2116_; 
v___x_2116_ = lean_nat_dec_lt(v_lo_2103_, v_hi_2104_);
if (v___x_2116_ == 0)
{
lean_dec(v_lo_2103_);
return v_as_2102_;
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v_mid_2119_; lean_object* v___y_2121_; lean_object* v___y_2127_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2117_ = lean_nat_add(v_lo_2103_, v_hi_2104_);
v___x_2118_ = lean_unsigned_to_nat(1u);
v_mid_2119_ = lean_nat_shiftr(v___x_2117_, v___x_2118_);
lean_dec(v___x_2117_);
v___x_2132_ = lean_array_fget_borrowed(v_as_2102_, v_mid_2119_);
v___x_2133_ = lean_array_fget_borrowed(v_as_2102_, v_lo_2103_);
v___x_2134_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_2100_, v___x_2132_, v___x_2133_);
if (v___x_2134_ == 0)
{
v___y_2127_ = v_as_2102_;
goto v___jp_2126_;
}
else
{
lean_object* v___x_2135_; 
v___x_2135_ = lean_array_fswap(v_as_2102_, v_lo_2103_, v_mid_2119_);
v___y_2127_ = v___x_2135_;
goto v___jp_2126_;
}
v___jp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2122_ = lean_array_fget_borrowed(v___y_2121_, v_mid_2119_);
v___x_2123_ = lean_array_fget_borrowed(v___y_2121_, v_hi_2104_);
v___x_2124_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_2100_, v___x_2122_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_dec(v_mid_2119_);
v___y_2106_ = v___y_2121_;
goto v___jp_2105_;
}
else
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_array_fswap(v___y_2121_, v_mid_2119_, v_hi_2104_);
lean_dec(v_mid_2119_);
v___y_2106_ = v___x_2125_;
goto v___jp_2105_;
}
}
v___jp_2126_:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2128_ = lean_array_fget_borrowed(v___y_2127_, v_hi_2104_);
v___x_2129_ = lean_array_fget_borrowed(v___y_2127_, v_lo_2103_);
v___x_2130_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_2100_, v___x_2128_, v___x_2129_);
if (v___x_2130_ == 0)
{
v___y_2121_ = v___y_2127_;
goto v___jp_2120_;
}
else
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_array_fswap(v___y_2127_, v_lo_2103_, v_hi_2104_);
v___y_2121_ = v___x_2131_;
goto v___jp_2120_;
}
}
}
v___jp_2105_:
{
lean_object* v_pivot_2107_; lean_object* v___x_2108_; lean_object* v_fst_2109_; lean_object* v_snd_2110_; uint8_t v___x_2111_; 
v_pivot_2107_ = lean_array_fget(v___y_2106_, v_hi_2104_);
lean_inc_n(v_lo_2103_, 2);
v___x_2108_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_2100_, v_hi_2104_, v_pivot_2107_, v___y_2106_, v_lo_2103_, v_lo_2103_);
lean_dec(v_pivot_2107_);
v_fst_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_fst_2109_);
v_snd_2110_ = lean_ctor_get(v___x_2108_, 1);
lean_inc(v_snd_2110_);
lean_dec_ref(v___x_2108_);
v___x_2111_ = lean_nat_dec_le(v_hi_2104_, v_fst_2109_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_2100_, v_n_2101_, v_snd_2110_, v_lo_2103_, v_fst_2109_);
v___x_2113_ = lean_unsigned_to_nat(1u);
v___x_2114_ = lean_nat_add(v_fst_2109_, v___x_2113_);
lean_dec(v_fst_2109_);
v_as_2102_ = v___x_2112_;
v_lo_2103_ = v___x_2114_;
goto _start;
}
else
{
lean_dec(v_fst_2109_);
lean_dec(v_lo_2103_);
return v_snd_2110_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___boxed(lean_object* v_goal_2136_, lean_object* v_n_2137_, lean_object* v_as_2138_, lean_object* v_lo_2139_, lean_object* v_hi_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_2136_, v_n_2137_, v_as_2138_, v_lo_2139_, v_hi_2140_);
lean_dec(v_hi_2140_);
lean_dec(v_n_2137_);
lean_dec_ref(v_goal_2136_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(lean_object* v_goal_2142_, lean_object* v_m_2143_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2144_ = lean_array_get_size(v_m_2143_);
v___x_2145_ = lean_unsigned_to_nat(0u);
v___x_2146_ = lean_nat_dec_eq(v___x_2144_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___y_2150_; uint8_t v___x_2154_; 
v___x_2147_ = lean_unsigned_to_nat(1u);
v___x_2148_ = lean_nat_sub(v___x_2144_, v___x_2147_);
v___x_2154_ = lean_nat_dec_le(v___x_2145_, v___x_2148_);
if (v___x_2154_ == 0)
{
lean_inc(v___x_2148_);
v___y_2150_ = v___x_2148_;
goto v___jp_2149_;
}
else
{
v___y_2150_ = v___x_2145_;
goto v___jp_2149_;
}
v___jp_2149_:
{
uint8_t v___x_2151_; 
v___x_2151_ = lean_nat_dec_le(v___y_2150_, v___x_2148_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; 
lean_dec(v___x_2148_);
lean_inc(v___y_2150_);
v___x_2152_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_2142_, v___x_2144_, v_m_2143_, v___y_2150_, v___y_2150_);
lean_dec(v___y_2150_);
return v___x_2152_;
}
else
{
lean_object* v___x_2153_; 
v___x_2153_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_2142_, v___x_2144_, v_m_2143_, v___y_2150_, v___x_2148_);
lean_dec(v___x_2148_);
return v___x_2153_;
}
}
}
else
{
return v_m_2143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel___boxed(lean_object* v_goal_2155_, lean_object* v_m_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_2155_, v_m_2156_);
lean_dec_ref(v_goal_2155_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(lean_object* v_goal_2158_, lean_object* v_n_2159_, lean_object* v_as_2160_, lean_object* v_lo_2161_, lean_object* v_hi_2162_, lean_object* v_w_2163_, lean_object* v_hlo_2164_, lean_object* v_hhi_2165_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_2158_, v_n_2159_, v_as_2160_, v_lo_2161_, v_hi_2162_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___boxed(lean_object* v_goal_2167_, lean_object* v_n_2168_, lean_object* v_as_2169_, lean_object* v_lo_2170_, lean_object* v_hi_2171_, lean_object* v_w_2172_, lean_object* v_hlo_2173_, lean_object* v_hhi_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(v_goal_2167_, v_n_2168_, v_as_2169_, v_lo_2170_, v_hi_2171_, v_w_2172_, v_hlo_2173_, v_hhi_2174_);
lean_dec(v_hi_2171_);
lean_dec(v_n_2168_);
lean_dec_ref(v_goal_2167_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(lean_object* v_goal_2176_, lean_object* v_n_2177_, lean_object* v_lo_2178_, lean_object* v_hi_2179_, lean_object* v_hhi_2180_, lean_object* v_pivot_2181_, lean_object* v_as_2182_, lean_object* v_i_2183_, lean_object* v_k_2184_, lean_object* v_ilo_2185_, lean_object* v_ik_2186_, lean_object* v_w_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_2176_, v_hi_2179_, v_pivot_2181_, v_as_2182_, v_i_2183_, v_k_2184_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___boxed(lean_object* v_goal_2189_, lean_object* v_n_2190_, lean_object* v_lo_2191_, lean_object* v_hi_2192_, lean_object* v_hhi_2193_, lean_object* v_pivot_2194_, lean_object* v_as_2195_, lean_object* v_i_2196_, lean_object* v_k_2197_, lean_object* v_ilo_2198_, lean_object* v_ik_2199_, lean_object* v_w_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(v_goal_2189_, v_n_2190_, v_lo_2191_, v_hi_2192_, v_hhi_2193_, v_pivot_2194_, v_as_2195_, v_i_2196_, v_k_2197_, v_ilo_2198_, v_ik_2199_, v_w_2200_);
lean_dec_ref(v_pivot_2194_);
lean_dec(v_hi_2192_);
lean_dec(v_lo_2191_);
lean_dec(v_n_2190_);
lean_dec_ref(v_goal_2189_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0_spec__0___redArg(lean_object* v_b_2202_, lean_object* v_acc_2203_, lean_object* v_i_2204_){
_start:
{
lean_object* v_a_2211_; lean_object* v_keyArray_2215_; lean_object* v_valueArray_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; 
v_keyArray_2215_ = lean_ctor_get(v_b_2202_, 1);
v_valueArray_2216_ = lean_ctor_get(v_b_2202_, 2);
v___x_2217_ = lean_array_get_size(v_keyArray_2215_);
v___x_2218_ = lean_nat_dec_lt(v_i_2204_, v___x_2217_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; 
lean_dec(v_i_2204_);
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v_acc_2203_);
return v___x_2219_;
}
else
{
lean_object* v___x_2220_; uint8_t v_isSome_2221_; 
v___x_2220_ = lean_array_fget_borrowed(v_keyArray_2215_, v_i_2204_);
v_isSome_2221_ = lean_noption_is_some(v___x_2220_);
if (v_isSome_2221_ == 0)
{
goto v___jp_2206_;
}
else
{
lean_object* v___x_2222_; uint8_t v_isSome_2223_; 
v___x_2222_ = lean_array_fget_borrowed(v_valueArray_2216_, v_i_2204_);
v_isSome_2223_ = lean_noption_is_some(v___x_2222_);
if (v_isSome_2223_ == 0)
{
goto v___jp_2206_;
}
else
{
lean_object* v_val_2224_; uint8_t v___x_2225_; 
lean_inc(v___x_2220_);
v_val_2224_ = lean_noption_get(v___x_2220_);
lean_inc(v_val_2224_);
v___x_2225_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_val_2224_);
if (v___x_2225_ == 0)
{
lean_object* v_val_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_inc(v___x_2222_);
v_val_2226_ = lean_noption_get(v___x_2222_);
v___x_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2227_, 0, v_val_2224_);
lean_ctor_set(v___x_2227_, 1, v_val_2226_);
v___x_2228_ = lean_array_push(v_acc_2203_, v___x_2227_);
v_a_2211_ = v___x_2228_;
goto v___jp_2210_;
}
else
{
lean_dec(v_val_2224_);
v_a_2211_ = v_acc_2203_;
goto v___jp_2210_;
}
}
}
}
v___jp_2206_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_unsigned_to_nat(1u);
v___x_2208_ = lean_nat_add(v_i_2204_, v___x_2207_);
lean_dec(v_i_2204_);
v_i_2204_ = v___x_2208_;
goto _start;
}
v___jp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = lean_unsigned_to_nat(1u);
v___x_2213_ = lean_nat_add(v_i_2204_, v___x_2212_);
lean_dec(v_i_2204_);
v_acc_2203_ = v_a_2211_;
v_i_2204_ = v___x_2213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0_spec__0___redArg___boxed(lean_object* v_b_2229_, lean_object* v_acc_2230_, lean_object* v_i_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0_spec__0___redArg(v_b_2229_, v_acc_2230_, v_i_2231_);
lean_dec_ref(v_b_2229_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(lean_object* v_init_2234_, lean_object* v_b_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_unsigned_to_nat(0u);
v___x_2242_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0_spec__0___redArg(v_b_2235_, v_init_2234_, v___x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___boxed(lean_object* v_init_2243_, lean_object* v_b_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(v_init_2243_, v_b_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec_ref(v_b_2244_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object* v_goal_2253_, lean_object* v_isTarget_2254_, lean_object* v_model_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_2253_, v_isTarget_2254_, v_model_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2273_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2261_, 1);
v___x_2263_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_finalizeModel___closed__0));
v___x_2264_ = l_Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(v___x_2263_, v_a_2262_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
lean_dec(v_a_2262_);
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2273_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2273_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2269_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_2253_, v_a_2265_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v___x_2269_);
v___x_2271_ = v___x_2267_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
v_a_2274_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2261_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2261_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel___boxed(lean_object* v_goal_2282_, lean_object* v_isTarget_2283_, lean_object* v_model_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_2282_, v_isTarget_2283_, v_model_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec_ref(v_goal_2282_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0_spec__0(lean_object* v_b_2291_, lean_object* v_acc_2292_, lean_object* v_i_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0_spec__0___redArg(v_b_2291_, v_acc_2292_, v_i_2293_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0_spec__0___boxed(lean_object* v_b_2300_, lean_object* v_acc_2301_, lean_object* v_i_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0_spec__0(v_b_2300_, v_acc_2301_, v_i_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec_ref(v_b_2300_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(lean_object* v_msgData_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; lean_object* v_env_2316_; lean_object* v___x_2317_; lean_object* v_mctx_2318_; lean_object* v_lctx_2319_; lean_object* v_options_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2315_ = lean_st_ref_get(v___y_2313_);
v_env_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc_ref(v_env_2316_);
lean_dec(v___x_2315_);
v___x_2317_ = lean_st_ref_get(v___y_2311_);
v_mctx_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc_ref(v_mctx_2318_);
lean_dec(v___x_2317_);
v_lctx_2319_ = lean_ctor_get(v___y_2310_, 2);
v_options_2320_ = lean_ctor_get(v___y_2312_, 2);
lean_inc_ref(v_options_2320_);
lean_inc_ref(v_lctx_2319_);
v___x_2321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2321_, 0, v_env_2316_);
lean_ctor_set(v___x_2321_, 1, v_mctx_2318_);
lean_ctor_set(v___x_2321_, 2, v_lctx_2319_);
lean_ctor_set(v___x_2321_, 3, v_options_2320_);
v___x_2322_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
lean_ctor_set(v___x_2322_, 1, v_msgData_2309_);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0___boxed(lean_object* v_msgData_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msgData_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2330_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2331_; double v___x_2332_; 
v___x_2331_ = lean_unsigned_to_nat(0u);
v___x_2332_ = lean_float_of_nat(v___x_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(lean_object* v_cls_2336_, lean_object* v_msg_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_ref_2343_; lean_object* v___x_2344_; lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2389_; 
v_ref_2343_ = lean_ctor_get(v___y_2340_, 5);
v___x_2344_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msg_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2389_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2389_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v_traceState_2350_; lean_object* v_env_2351_; lean_object* v_nextMacroScope_2352_; lean_object* v_ngen_2353_; lean_object* v_auxDeclNGen_2354_; lean_object* v_cache_2355_; lean_object* v_messages_2356_; lean_object* v_infoState_2357_; lean_object* v_snapshotTasks_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2388_; 
v___x_2349_ = lean_st_ref_take(v___y_2341_);
v_traceState_2350_ = lean_ctor_get(v___x_2349_, 4);
v_env_2351_ = lean_ctor_get(v___x_2349_, 0);
v_nextMacroScope_2352_ = lean_ctor_get(v___x_2349_, 1);
v_ngen_2353_ = lean_ctor_get(v___x_2349_, 2);
v_auxDeclNGen_2354_ = lean_ctor_get(v___x_2349_, 3);
v_cache_2355_ = lean_ctor_get(v___x_2349_, 5);
v_messages_2356_ = lean_ctor_get(v___x_2349_, 6);
v_infoState_2357_ = lean_ctor_get(v___x_2349_, 7);
v_snapshotTasks_2358_ = lean_ctor_get(v___x_2349_, 8);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2360_ = v___x_2349_;
v_isShared_2361_ = v_isSharedCheck_2388_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_snapshotTasks_2358_);
lean_inc(v_infoState_2357_);
lean_inc(v_messages_2356_);
lean_inc(v_cache_2355_);
lean_inc(v_traceState_2350_);
lean_inc(v_auxDeclNGen_2354_);
lean_inc(v_ngen_2353_);
lean_inc(v_nextMacroScope_2352_);
lean_inc(v_env_2351_);
lean_dec(v___x_2349_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2388_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
uint64_t v_tid_2362_; lean_object* v_traces_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2387_; 
v_tid_2362_ = lean_ctor_get_uint64(v_traceState_2350_, sizeof(void*)*1);
v_traces_2363_ = lean_ctor_get(v_traceState_2350_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_traceState_2350_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2365_ = v_traceState_2350_;
v_isShared_2366_ = v_isSharedCheck_2387_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_traces_2363_);
lean_dec(v_traceState_2350_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2387_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; double v___x_2368_; uint8_t v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2367_ = lean_box(0);
v___x_2368_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0);
v___x_2369_ = 0;
v___x_2370_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1));
v___x_2371_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2371_, 0, v_cls_2336_);
lean_ctor_set(v___x_2371_, 1, v___x_2367_);
lean_ctor_set(v___x_2371_, 2, v___x_2370_);
lean_ctor_set_float(v___x_2371_, sizeof(void*)*3, v___x_2368_);
lean_ctor_set_float(v___x_2371_, sizeof(void*)*3 + 8, v___x_2368_);
lean_ctor_set_uint8(v___x_2371_, sizeof(void*)*3 + 16, v___x_2369_);
v___x_2372_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2));
v___x_2373_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v_a_2345_);
lean_ctor_set(v___x_2373_, 2, v___x_2372_);
lean_inc(v_ref_2343_);
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v_ref_2343_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = l_Lean_PersistentArray_push___redArg(v_traces_2363_, v___x_2374_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2375_);
v___x_2377_ = v___x_2365_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2375_);
lean_ctor_set_uint64(v_reuseFailAlloc_2386_, sizeof(void*)*1, v_tid_2362_);
v___x_2377_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2379_; 
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 4, v___x_2377_);
v___x_2379_ = v___x_2360_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_env_2351_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_nextMacroScope_2352_);
lean_ctor_set(v_reuseFailAlloc_2385_, 2, v_ngen_2353_);
lean_ctor_set(v_reuseFailAlloc_2385_, 3, v_auxDeclNGen_2354_);
lean_ctor_set(v_reuseFailAlloc_2385_, 4, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2385_, 5, v_cache_2355_);
lean_ctor_set(v_reuseFailAlloc_2385_, 6, v_messages_2356_);
lean_ctor_set(v_reuseFailAlloc_2385_, 7, v_infoState_2357_);
lean_ctor_set(v_reuseFailAlloc_2385_, 8, v_snapshotTasks_2358_);
v___x_2379_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2380_ = lean_st_ref_put(v___y_2341_, v___x_2379_);
v___x_2381_ = lean_box(0);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v___x_2381_);
v___x_2383_ = v___x_2347_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___boxed(lean_object* v_cls_2390_, lean_object* v_msg_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_cls_2390_, v_msg_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
return v_res_2397_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0));
v___x_2400_ = l_Lean_stringToMessageData(v___x_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(lean_object* v_traceClass_2402_, lean_object* v_as_2403_, size_t v_sz_2404_, size_t v_i_2405_, lean_object* v_b_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
uint8_t v___x_2412_; 
v___x_2412_ = lean_usize_dec_lt(v_i_2405_, v_sz_2404_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; 
lean_dec(v_traceClass_2402_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v_b_2406_);
return v___x_2413_;
}
else
{
lean_object* v_a_2414_; lean_object* v_snd_2415_; lean_object* v_fst_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2451_; 
v_a_2414_ = lean_array_uget(v_as_2403_, v_i_2405_);
v_snd_2415_ = lean_ctor_get(v_a_2414_, 1);
v_fst_2416_ = lean_ctor_get(v_a_2414_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v_a_2414_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2418_ = v_a_2414_;
v_isShared_2419_ = v_isSharedCheck_2451_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_snd_2415_);
lean_inc(v_fst_2416_);
lean_dec(v_a_2414_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2451_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_num_2420_; lean_object* v_den_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2450_; 
v_num_2420_ = lean_ctor_get(v_snd_2415_, 0);
v_den_2421_ = lean_ctor_get(v_snd_2415_, 1);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_snd_2415_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2423_ = v_snd_2415_;
v_isShared_2424_ = v_isSharedCheck_2450_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_den_2421_);
lean_inc(v_num_2420_);
lean_dec(v_snd_2415_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2450_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2425_ = lean_box(0);
v___x_2426_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_2416_);
v___x_2427_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1);
if (v_isShared_2424_ == 0)
{
lean_ctor_set_tag(v___x_2423_, 7);
lean_ctor_set(v___x_2423_, 1, v___x_2427_);
lean_ctor_set(v___x_2423_, 0, v___x_2426_);
v___x_2429_ = v___x_2423_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___y_2431_; lean_object* v___x_2441_; uint8_t v___x_2442_; 
v___x_2441_ = lean_unsigned_to_nat(1u);
v___x_2442_ = lean_nat_dec_eq(v_den_2421_, v___x_2441_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2443_ = l_Int_repr(v_num_2420_);
lean_dec(v_num_2420_);
v___x_2444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2));
v___x_2445_ = lean_string_append(v___x_2443_, v___x_2444_);
v___x_2446_ = l_Nat_reprFast(v_den_2421_);
v___x_2447_ = lean_string_append(v___x_2445_, v___x_2446_);
lean_dec_ref(v___x_2446_);
v___y_2431_ = v___x_2447_;
goto v___jp_2430_;
}
else
{
lean_object* v___x_2448_; 
lean_dec(v_den_2421_);
v___x_2448_ = l_Int_repr(v_num_2420_);
lean_dec(v_num_2420_);
v___y_2431_ = v___x_2448_;
goto v___jp_2430_;
}
v___jp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2432_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2432_, 0, v___y_2431_);
v___x_2433_ = l_Lean_MessageData_ofFormat(v___x_2432_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set_tag(v___x_2418_, 7);
lean_ctor_set(v___x_2418_, 1, v___x_2433_);
lean_ctor_set(v___x_2418_, 0, v___x_2429_);
v___x_2435_ = v___x_2418_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2436_; 
lean_inc(v_traceClass_2402_);
v___x_2436_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_traceClass_2402_, v___x_2435_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
if (lean_obj_tag(v___x_2436_) == 0)
{
size_t v___x_2437_; size_t v___x_2438_; 
lean_dec_ref_known(v___x_2436_, 1);
v___x_2437_ = ((size_t)1ULL);
v___x_2438_ = lean_usize_add(v_i_2405_, v___x_2437_);
v_i_2405_ = v___x_2438_;
v_b_2406_ = v___x_2425_;
goto _start;
}
else
{
lean_dec(v_traceClass_2402_);
return v___x_2436_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___boxed(lean_object* v_traceClass_2452_, lean_object* v_as_2453_, lean_object* v_sz_2454_, lean_object* v_i_2455_, lean_object* v_b_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
size_t v_sz_boxed_2462_; size_t v_i_boxed_2463_; lean_object* v_res_2464_; 
v_sz_boxed_2462_ = lean_unbox_usize(v_sz_2454_);
lean_dec(v_sz_2454_);
v_i_boxed_2463_ = lean_unbox_usize(v_i_2455_);
lean_dec(v_i_2455_);
v_res_2464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2452_, v_as_2453_, v_sz_boxed_2462_, v_i_boxed_2463_, v_b_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec_ref(v_as_2453_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object* v_traceClass_2468_, lean_object* v_model_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_options_2478_; uint8_t v_hasTrace_2479_; 
v_options_2478_ = lean_ctor_get(v_a_2472_, 2);
v_hasTrace_2479_ = lean_ctor_get_uint8(v_options_2478_, sizeof(void*)*1);
if (v_hasTrace_2479_ == 0)
{
lean_dec(v_traceClass_2468_);
goto v___jp_2475_;
}
else
{
lean_object* v_inheritedTraceOptions_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v_inheritedTraceOptions_2480_ = lean_ctor_get(v_a_2472_, 13);
v___x_2481_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_traceModel___closed__1));
lean_inc(v_traceClass_2468_);
v___x_2482_ = l_Lean_Name_append(v___x_2481_, v_traceClass_2468_);
v___x_2483_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2480_, v_options_2478_, v___x_2482_);
lean_dec(v___x_2482_);
if (v___x_2483_ == 0)
{
lean_dec(v_traceClass_2468_);
goto v___jp_2475_;
}
else
{
lean_object* v___x_2484_; size_t v_sz_2485_; size_t v___x_2486_; lean_object* v___x_2487_; 
v___x_2484_ = lean_box(0);
v_sz_2485_ = lean_array_size(v_model_2469_);
v___x_2486_ = ((size_t)0ULL);
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2468_, v_model_2469_, v_sz_2485_, v___x_2486_, v___x_2484_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2494_ == 0)
{
lean_object* v_unused_2495_; 
v_unused_2495_ = lean_ctor_get(v___x_2487_, 0);
lean_dec(v_unused_2495_);
v___x_2489_ = v___x_2487_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_dec(v___x_2487_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v___x_2484_);
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2484_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
else
{
return v___x_2487_;
}
}
}
v___jp_2475_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_box(0);
v___x_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
return v___x_2477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel___boxed(lean_object* v_traceClass_2496_, lean_object* v_model_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_Meta_Grind_Arith_traceModel(v_traceClass_2496_, v_model_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec_ref(v_model_2497_);
return v_res_2503_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_Envelope(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* initialize_Init_Grind_Module_Envelope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
}
#ifdef __cplusplus
}
#endif
